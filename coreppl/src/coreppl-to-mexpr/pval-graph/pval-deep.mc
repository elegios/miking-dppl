include "pval-interface.mc"

-- A mildly unsafe interface for supplying a bunch of references in
-- such a way that the underlying implementation can be either mutable
-- or immutable.
lang RefArena
  -- Must be used affinely.
  syn RefArenaPrep =
  -- Must be used affinely.
  syn RefArena =
  syn RARef a =

  -- Note that the reference will be uninitialized; a value read from
  -- such a reference is _quite_ unsafe to use.
  sem ra_new : all a. RefArenaPrep -> (RefArenaPrep, RARef a)
  sem ra_prepareArena : () -> RefArenaPrep
  sem ra_finalizeArena : RefArenaPrep -> RefArena

  sem ra_read : all a. RARef a -> RefArena -> a
  sem ra_write : all a. a -> RARef a -> RefArena -> RefArena

  -- Copy an arena, getting two independent values. Note that an
  -- implementation may choose not to implement this operation.
  sem ra_copy : RefArena -> (RefArena, RefArena)
end

lang MutRefArena = RefArena
  syn RefArenaPrep = | RAP
  syn RefArena = | RA
  syn RARef a = | RARef (Ref a)

  sem ra_new = | prep -> (prep, RARef (ref (unsafeCoerce 0)))
  sem ra_prepareArena = | _ -> RAP ()
  sem ra_finalizeArena = | RAP _ -> RA ()

  sem ra_read ref = | _ -> match ref with RARef ref in deref ref
  sem ra_write a ref = | arena -> match ref with RARef ref in modref ref a; arena

  sem ra_copy = | RA _ -> error "Cannot copy a MutRefArena"
end

type Persistent
type Temporary

lang DeepPVal = PValInterface + RefArena + PValPPureSimpl + PValDefaultImpls
  type SourceId = Int

  type RunF a = RefArena -> a
  type PValRec a =
    { compiledRead : Ref (RefArena -> a)
    , block : Set SourceId
    , internalUses : Ref Int
    , externalUse : Ref Bool
    }
  syn PVal a = | PVal (PValRec a)

  syn PAssumeRef a = | PAR {sourceId : SourceId, aref : RARef a, driftRef : RARef (Option (a -> Dist a))}
  syn PExportRef a = | PER {eref : RARef a}
  syn PWeightRef = | PWR ()

  syn PValPrep st = | PVP
    { update : UpdateF
    , init : UpdateF
    , arena : RefArena
    , st : st
    }
  syn PValInstance complete st =
  | PVI
    { st : st
    , update : UpdateF
    , permanentWeight : Float
    , arena : RefArena
    }
  | PVIPart
    { st : st
    , update : UpdateF
    , prevPermanentWeight : Float
    , permanentWeight : Float
    , temporaryWeight : Float
    , updatedSources : Set SourceId
    , reset : RefArena -> RefArena
    , arena : RefArena
    }

  type RunState =
    { arena : RefArena
    , permanentWeight : Float
    , temporaryWeight : Float
    , updatedSources : Set SourceId
    , reset : RefArena -> RefArena
    }
  type UpdateF = RunState -> RunState

  type BlockCompileState =
    { arenaPrep : RefArenaPrep
    , update : Option UpdateF
    , init : Option UpdateF
    , getWeight : Option (RefArena -> Float)
    }
  type CompileF = BlockCompileState -> BlockCompileState

  syn PValState st = | PVS
    { nextSourceId : SourceId
    , blocks : Map (Set SourceId) CompileF
    , arenaPrep : RefArenaPrep
    , permanentWeight : Float
    , st : st
    }

  sem p_prepare f = | st ->
    let st = PVS
      { nextSourceId = 0
      , blocks = mapEmpty setCmp
      , arenaPrep = ra_prepareArena ()
      , permanentWeight = 0.0
      , st = st
      } in
    match f st with PVS st in
    -- NOTE(vipa, 2026-06-03): It is important to process the blocks
    -- in topological order. We take advantage of `SourceId` already
    -- being topologically sorted (i.e., if a source with id x
    -- depends on a source with id y, then y < x). We can get an
    -- appropriate sort by first looking at the highest `SourceId`
    -- for each block, then the next highest, etc.
    let blocks = map (lam pair. (reverse (setToSeq pair.0), pair.0, pair.1)) (mapBindings st.blocks) in
    let blocks = sort (lam a. lam b. seqCmpLexi subi a.0 b.0) blocks in
    let compileBlock
      : all x. {arenaPrep: RefArenaPrep, update : UpdateF, init : UpdateF}
      -> (x, Set SourceId, CompileF)
      -> {arenaPrep: RefArenaPrep, update : UpdateF, init : UpdateF}
      = lam acc. lam trip.
        match acc with {arenaPrep = arenaPrep, update = prevUpdate, init = prevInit} in
        match trip with (_, dependencies, f) in
        let dependencies = trip.1 in
        let cst : BlockCompileState =
          { arenaPrep = acc.arenaPrep
          , update = None ()
          , init = None ()
          , getWeight = None ()
          } in
        let cst = f cst in
        let init : UpdateF = switch (cst.init, cst.getWeight)
          case (Some init, Some getWeight) then lam rst.
            let rst = prevInit rst in
            let rst = init rst in
            {rst with permanentWeight = addf rst.permanentWeight (getWeight rst.arena)}
          case (Some init, None _) then lam rst.
            let rst = prevInit rst in
            let rst = init rst in
            rst
          case (None _, Some getWeight) then lam rst.
            let rst = prevInit rst in
            {rst with permanentWeight = addf rst.permanentWeight (getWeight rst.arena)}
          case (None _, None _) then prevInit
          end in
        let update : UpdateF = switch (cst.update, cst.getWeight)
          case (Some update, Some getWeight) then lam rst.
            let rst = prevUpdate rst in
            let rst = if setDisjoint rst.updatedSources dependencies then rst else update rst in
            {rst with permanentWeight = addf rst.permanentWeight (getWeight rst.arena)}
          case (Some update, None _) then lam rst.
            let rst = prevUpdate rst in
            let rst = if setDisjoint rst.updatedSources dependencies then rst else update rst in
            rst
          case (None _, Some getWeight) then lam rst.
            let rst = prevUpdate rst in
            {rst with permanentWeight = addf rst.permanentWeight (getWeight rst.arena)}
          case (None _, None _) then prevUpdate
          end in
        {arenaPrep = cst.arenaPrep, update = update, init = init}
    in
    let initialWeight : UpdateF =
      let permanentWeight = st.permanentWeight in
      lam rst. {rst with permanentWeight = permanentWeight} in
    let res = foldl compileBlock {arenaPrep = st.arenaPrep, update = initialWeight, init = initialWeight} blocks in
    let arena = ra_finalizeArena res.arenaPrep in
    PVP {st = st.st, update = res.update, init = res.init, arena = arena}

  sem instantiate = | PVP st ->
    let rst =
      { arena = st.arena
      , permanentWeight = 0.0
      , temporaryWeight = 0.0
      , reset = lam arena. arena
      , updatedSources = setEmpty subi
      } in
    let rst = st.init rst in
    PVI {st = st.st, update = st.update, permanentWeight = rst.permanentWeight, arena = rst.arena}

  sem startStep = | PVI st ->
    PVIPart
    { st = st.st
    , update = st.update
    , prevPermanentWeight = st.permanentWeight
    , permanentWeight = st.permanentWeight
    , temporaryWeight = 0.0
    , updatedSources = setEmpty subi
    , reset = lam arena. arena
    , arena = st.arena
    }

  sem resampleAssume oDrift par = | PVIPart st ->
    match par with PAR {sourceId = sourceId, driftRef = driftRef} in
    PVIPart
    { st with updatedSources = setInsert sourceId st.updatedSources
    , arena = ra_write oDrift driftRef st.arena
    }

  sem intermediateStep = | PVIPart st ->
    if setIsEmpty st.updatedSources then PVIPart st else
    let rst =
      { arena = st.arena
      , permanentWeight = 0.0
      , temporaryWeight = st.temporaryWeight
      , updatedSources = st.updatedSources
      , reset = st.reset
      } in
    let rst = st.update rst in
    PVIPart
    { st with updatedSources = mapEmpty subi
    , permanentWeight = rst.permanentWeight
    , temporaryWeight = rst.temporaryWeight
    , arena = rst.arena
    , reset = rst.reset
    }

  sem finalizeStep pred = | st ->
    match intermediateStep st with PVIPart st in
    let acceptProb = minf 0.0
      (addf
        (subf st.permanentWeight st.prevPermanentWeight)
        st.temporaryWeight) in
    if pred acceptProb then
      ( true
      , PVI
        { st = st.st
        , update = st.update
        , permanentWeight = st.permanentWeight
        , arena = st.arena
        }
      )
    else
      ( false
      , PVI
        { st = st.st
        , update = st.update
        , permanentWeight = st.prevPermanentWeight
        , arena = st.reset st.arena
        }
      )

  sem readPreviousExport per =
  | PVI st -> match per with PER x in ra_read x.eref st.arena
  | PVIPart st -> match per with PER x in ra_read x.eref st.arena

  sem getSt =
  | PVI st -> st.st
  | PVIPart st -> st.st

  sem getWeight =
  | PVI st -> st.permanentWeight
  | PVIPart st -> st.permanentWeight

  sem p_mapSt f = | PVS st -> PVS
    { nextSourceId = st.nextSourceId
    , blocks = st.blocks
    , arenaPrep = st.arenaPrep
    , permanentWeight = st.permanentWeight
    , st = f st.st
    }

  sem newPValRec : all a. Set SourceId -> PValRec a
  sem newPValRec = | block ->
    { compiledRead = ref (lam. error "Compiler error: accessed compiled version of node before its compilation")
    , block = block
    , internalUses = ref 0
    , externalUse = ref false
    }

  sem addCompile : all st. CompileF -> Set SourceId -> PValState st -> PValState st
  sem addCompile f block = | PVS st -> PVS
    { st with blocks = mapInsertWith (lam f1. lam f2. lam x. f2 (f1 x)) block f st.blocks
    }

  sem addUpdate : UpdateF -> BlockCompileState -> BlockCompileState
  sem addUpdate f = | cst ->
    { cst with update = match cst.update with Some update
      then Some (lam x. f (update x))
      else Some f
    }

  sem addInit : UpdateF -> BlockCompileState -> BlockCompileState
  sem addInit f = | cst ->
    { cst with init = match cst.init with Some init
      then Some (lam x. f (init x))
      else Some f
    }

  sem addGetWeight : (RefArena -> Float) -> BlockCompileState -> BlockCompileState
  sem addGetWeight f = | cst ->
    { cst with getWeight = match cst.getWeight with Some getWeight
      then Some (lam arena. addf (f arena) (getWeight arena))
      else Some f
    }

  sem newInternalRef : all a. BlockCompileState -> (BlockCompileState, RARef a)
  sem newInternalRef = | cst ->
    match ra_new cst.arenaPrep with (arenaPrep, ref) in
    ({cst with arenaPrep = arenaPrep}, ref)

  sem newPersistentRef : all a. BlockCompileState -> (BlockCompileState, RARef a)
  sem newPersistentRef = | cst ->
    match newInternalRef cst with (cst, ref) in
    let update : UpdateF = lam rst.
      let prev = ra_read ref rst.arena in
      let reset = rst.reset in
      {rst with reset = lam arena. ra_write prev ref (reset arena)} in
    (addUpdate update cst, ref)

  sem newExternalRef : all a. all st. PValState st -> (PValState st, RARef a)
  sem newExternalRef = | PVS st ->
    match ra_new st.arenaPrep with (arenaPrep, ref) in
    (PVS {st with arenaPrep = arenaPrep}, ref)

  sem newSource : all st. PValState st -> (PValState st, SourceId)
  sem newSource = | PVS st ->
    (PVS {st with nextSourceId = addi 1 st.nextSourceId}, st.nextSourceId)

  sem referencePVal : all a. Set SourceId -> PValRec a -> ()
  sem referencePVal source = | destination ->
    if setEq source destination.block then
      modref destination.internalUses (addi (deref destination.internalUses) 1)
    else
      modref destination.externalUse true

  sem emit : all a. (RefArena -> a) -> PValRec a -> BlockCompileState -> BlockCompileState
  sem emit f x = | cst ->
    switch (deref x.externalUse, deref x.internalUses)
    case (true, _) then
      match newPersistentRef cst with (cst, ref) in
      modref x.compiledRead (ra_read ref);
      let update : UpdateF = lam rst. {rst with arena = ra_write (f rst.arena) ref rst.arena} in
      addInit update (addUpdate update cst)
    case (_, 1) then
      modref x.compiledRead f;
      cst
    case (_, 0) then
      -- NOTE(vipa, 2026-06-03): This is technically dead code, but in
      -- case the user has some debug printing we want to run that
      -- code anyway, so we call it here.
      let update : UpdateF = lam rst. f rst.arena; rst in
      addInit update (addUpdate update cst)
    case _ then
      match newInternalRef cst with (cst, ref) in
      modref x.compiledRead (ra_read ref);
      let update : UpdateF = lam rst. {rst with arena = ra_write (f rst.arena) ref rst.arena} in
      addInit update (addUpdate update cst)
    end

  sem p_getSeq st xs = | PVal idx ->
    let block = foldl (lam acc. lam x. match x with PVal x then setUnion acc x.block else acc) idx.block xs in
    let r = newPValRec block in
    referencePVal block idx;
    let reference = lam x.
      match x with PVal x
      then referencePVal block x
      else () in
    for_ xs reference;
    let f : CompileF = lam cst.
      let readIdx = deref idx.compiledRead in
      let getRead = lam x. switch x
        case PPure x then lam. x
        case PVal x then deref x.compiledRead
        end in
      let readXs = map getRead xs in
      emit (lam arena. get readXs (readIdx arena) arena) r cst in
    (addCompile f block st, PVal r)

  sem p_cache st eq = | PVal x ->
    match newSource st with (st, sourceId) in
    referencePVal x.block x;
    let r = newPValRec (setSingleton subi sourceId) in
    let f : CompileF = lam cst.
      match newPersistentRef cst with (cst, ref) in
      let readValue = deref x.compiledRead in
      modref r.compiledRead (ra_read ref);
      let init : UpdateF = lam rst.
        {rst with arena = ra_write (readValue rst.arena) ref rst.arena} in
      let update : UpdateF = lam rst.
        let value = readValue rst.arena in
        if eq value (ra_read ref rst.arena) then rst else
        { rst with updatedSources = setInsert sourceId rst.updatedSources
        , arena = ra_write value ref rst.arena
        } in
      addInit init (addUpdate update cst) in
    (addCompile f x.block st, PVal r)

  sem p_export st store = | PVal x ->
    match newExternalRef st with (st, eref) in
    referencePVal x.block x;
    let f : CompileF = lam cst.
      let readValue = deref x.compiledRead in
      let init : UpdateF = lam rst.
        {rst with arena = ra_write (readValue rst.arena) eref rst.arena} in
      let update : UpdateF = lam rst.
        let prev = ra_read eref rst.arena in
        let reset = rst.reset in
        { rst with arena = ra_write (readValue rst.arena) eref rst.arena
        , reset = lam arena. ra_write prev eref (reset arena)
        } in
      addUpdate update (addInit init cst) in
    let st = addCompile f x.block st in
    let per = PER {eref = eref} in
    p_mapSt (lam st. store st per) st

  sem p_map st f = | PVal x ->
    let r = newPValRec x.block in
    referencePVal x.block x;
    let f : CompileF = lam cst.
      let readValue = deref x.compiledRead in
      emit (lam arena. f (readValue arena)) r cst in
    (addCompile f x.block st, PVal r)

  sem p_apply_ st = | (PVal f, PVal x) ->
    let block = setUnion f.block x.block in
    referencePVal block f;
    referencePVal block x;
    let r = newPValRec block in
    let f : CompileF = lam cst.
      let readF = deref f.compiledRead in
      let readX = deref x.compiledRead in
      emit (lam arena. readF arena (readX arena)) r cst in
    (addCompile f block st, PVal r)

  sem p_directWeight st store =
  | PPure w ->
    match st with PVS st in
    let st = PVS {st with permanentWeight = addf st.permanentWeight w} in
    p_mapSt (lam st. store st (PWR ())) st
  | PVal x ->
    referencePVal x.block x;
    let f : CompileF = lam cst.
      let readValue = deref x.compiledRead in
      match newPersistentRef cst with (cst, ref) in
      let update : UpdateF = lam rst.
        {rst with arena = ra_write (readValue rst.arena) ref rst.arena} in
      let getWeight : RefArena -> Float = lam arena.
        ra_read ref arena in
      addInit update (addUpdate update (addGetWeight getWeight cst)) in
    addCompile f x.block (p_mapSt (lam st. store st (PWR ())) st)

  sem p_assume st store = | dist ->
    match newSource st with (st, sourceId) in
    match newExternalRef st with (st, aref) in
    match newExternalRef st with (st, driftRef) in
    match newExternalRef st with (st, wref) in
    let r = newPValRec (setSingleton subi sourceId) in
    modref r.compiledRead (ra_read aref);
    let updateWeight : Float -> RunState -> (Float, RunState) = lam w. lam rst.
      let prev = ra_read wref rst.arena in
      let reset = rst.reset in
      ( prev
      , { rst with arena = ra_write w wref rst.arena
        , reset = lam arena. ra_write prev wref (reset arena)
        }
      ) in
    -- NOTE(vipa, 2026-06-03): Setup the update in the block of the
    -- distribution, updating temporaryWeight as needed
    match
      switch dist
      case PPure dist then
        ( st
        , lam. lam. dist
        )
      case PVal x then
        referencePVal x.block x;
        let f : CompileF = lam cst.
          let readDist = deref x.compiledRead in
          let update : UpdateF = lam rst.
            -- NOTE(vipa, 2026-06-03): We're going to redraw, no need
            -- to update temporaryWeight
            if setMem sourceId rst.updatedSources then rst else
            let newWeight = logObserve (readDist rst.arena) (ra_read aref rst.arena) in
            if eqf newWeight (negf inf) then
              -- NOTE(vipa, 2026-06-03): We got an impossible reuse,
              -- force a redraw without a drift kernel, don't update
              -- temporaryWeight
              { rst with updatedSources = setInsert sourceId rst.updatedSources
              , arena = ra_write (None ()) driftRef rst.arena
              }
            else
              -- NOTE(vipa, 2026-06-03): Normal case, just update
              -- temporaryWeight and the wref
              match updateWeight newWeight rst with (prevWeight, rst) in
              {rst with temporaryWeight = addf rst.temporaryWeight (subf newWeight prevWeight)} in
          addUpdate update cst in
        ( addCompile f x.block st
        , lam. deref x.compiledRead
        )
      end
    with (st, getDistRead) in
    -- NOTE(vipa, 2026-06-03): Redraw values
    let f : CompileF = lam cst.
      let readDist = getDistRead () in
      let init : UpdateF = lam rst.
        let dist = readDist rst.arena in
        let newValue = sample dist in
        let newWeight = logObserve dist newValue in
        let rst = (updateWeight newWeight rst).1 in
        {rst with arena = ra_write newValue aref rst.arena} in
      let update : UpdateF = lam rst.
        let prevValue = ra_read aref rst.arena in
        let reset = rst.reset in
        let dist = readDist rst.arena in
        match
          match ra_read driftRef rst.arena with Some drift then
            let kernel = drift prevValue in
            let proposal = sample kernel in
            let reverseKernel = drift proposal in

            let prevToProposalProb = logObserve kernel proposal in
            let proposalToPrevProb = logObserve reverseKernel prevValue in

            (proposal, subf proposalToPrevProb prevToProposalProb)
          else (sample dist, 0.0)
        with (newValue, newTemp) in
        let newWeight = logObserve dist newValue in
        match updateWeight newWeight rst with (prevWeight, rst) in
        { rst with reset = lam arena. ra_write prevValue aref (reset arena)
        , arena = ra_write newValue aref rst.arena
        , temporaryWeight = addf rst.temporaryWeight (addf newTemp (subf newWeight prevWeight))
        } in
      addUpdate update (addInit init cst) in
    let st = addCompile f r.block st in
    let eref = PAR {aref = aref, driftRef = driftRef, sourceId = sourceId} in
    (p_mapSt (lam st. store st eref) st, PVal r)
end
