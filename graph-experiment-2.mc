include "pval-interface.mc"
include "mut-pval.mc"
include "mut2-pval.mc"
include "mut3-pval.mc"
include "debug-pval.mc"
include "im2-pval.mc"






-- === General implementation of MCMC ===

lang MCMCPVal = PValInterfaceExp
  type MCMCConfig st a =
    { getSample : PValInstance Complete st -> a
    , step : PValInstance Partial st -> PValInstance Partial st
    , iterations : Int  -- TODO(vipa, 2025-09-24): Make this something more general
    }

  type MCMCResult st a =
    { samples : [a]
    , acceptanceRatio : Float
    , finalInstance : PValInstance Complete st
    }

  sem mcmc : all st. all a. MCMCConfig st a -> PValInstance Complete st -> MCMCResult st a
  sem mcmc config = | instance ->
    let acceptPred = lam. lam prob. bernoulliSample (exp prob) in
    recursive let work = lam acc.
      if eqi acc.iterations 0 then acc else
      match finalizeStep acceptPred (config.step (startStep acc.instance)) with (accepted, instance) in
      let acc =
        { iterations = subi acc.iterations 1
        , accepted = addi acc.accepted (if accepted then 1 else 0)
        , samples = snoc acc.samples (config.getSample instance)
        , instance = instance
        } in
      work acc in
    let res = work {iterations = config.iterations, accepted = 0, samples = [], instance = instance} in
    { samples = res.samples
    , acceptanceRatio = divf (int2float res.accepted) (int2float config.iterations)
    , finalInstance = res.instance
    }
end


-- === Helpers for writing models, timing execution, and printing/summarizing results ===

let timeF : all a. (() -> a) -> (Float, a)
  = lam f.
    let before = wallTimeMs () in
    let res = f () in
    let after = wallTimeMs () in
    (subf after before, res)

let resampleBehavior : all acc. Float -> acc -> Int -> (acc, ([Bool], Int))
  = lam globalProb. lam acc. lam len.
    ( acc
    , if assume (Bernoulli globalProb)
      then (create len (lam. false), negi 2)
      else (create len (lam. true), assume (UniformDiscrete 0 (subi len 1)))
    )

let continue = lam iterations. (lam. iterations, lam r. lam. lam. (subi r 1, neqi r 1))

let _chooseUniform : all a. [a] -> a
  = lam l. get l (uniformDiscreteSample 0 (subi (length l) 1))

let interval2string : (Float, Float) -> String
  = lam pair.
    join [float2string pair.0, "-", float2string pair.1]

let histogram : all a. (a -> a -> Int) -> [a] -> [(a, Float)]
  = lam cmp. lam l.
    let hist = foldl (lam acc. lam a. mapInsertWith addi a 1 acc) (mapEmpty cmp) l in
    let count = int2float (mapFoldWithKey (lam total. lam. lam count. addi total count) 0 hist) in
    let hist = mapMap (lam v. divf (int2float v) count) hist in
    mapBindings hist

let bucket : all a. Int -> Float -> Float -> [Float] -> [((Float, Float), Float)]
  = lam numBuckets. lam min. lam max. lam l.
    let bucketSize = divf (subf max min) (int2float numBuckets) in
    let hist = mapFromSeq subi (create numBuckets (lam i. (i, 0))) in
    let f = lam acc. lam x. mapInsertWith addi (floorfi (divf (subf x min) bucketSize)) 1 acc in
    let hist = foldl f hist l in
    let count = int2float (mapFoldWithKey (lam total. lam. lam count. addi total count) 0 hist) in
    let convPair = lam pair.
      let base = addf min (mulf bucketSize (int2float pair.0)) in
      ( (base, addf bucketSize base)
      , divf (int2float pair.1) count
      ) in
    map convPair (mapBindings hist)

let progressBarNoPad : Int -> Float -> String
  = lam width. lam fraction.
    let filled = roundfi (mulf (int2float width) fraction) in
    make filled '=' -- (make (subi width filled) ' ')

let hist2string : all a. (a -> String) -> [(a, Float)] -> String
  = lam toStr. lam l.
    strJoin "\n" (map (lam pair. join [toStr pair.0, "\t", float2string pair.1, "\t", progressBarNoPad 100 pair.1]) l)

type SomePAssumeRef
con SomePAssumeRef : all x. use PValInterfaceExp in PAssumeRef x -> SomePAssumeRef

lang SimpleResample = PValInterfaceExp
  type SimpleState x = ([SomePAssumeRef], x)

  sem simpleStore : all a. SimpleState () -> PAssumeRef a -> SimpleState ()
  sem simpleStore rs = | r -> (snoc rs.0 (SomePAssumeRef r), rs.1)

  sem simpleExport : all x2. SimpleState () -> PExportRef x2 -> SimpleState (PExportRef x2)
  sem simpleExport rs = | r -> (rs.0, r)

  sem simpleResample : all x. Float -> PValInstance Partial (SimpleState x) -> PValInstance Partial (SimpleState x)
  sem simpleResample globalProb = | instance ->
    let st = getSt instance in
    let doResample = lam instance. lam someAssume.
      match someAssume with SomePAssumeRef x in
      resampleAssume (lam d. lam. d) x instance in
    if bernoulliSample globalProb then
      foldl doResample instance st.0
    else
      doResample instance (_chooseUniform st.0)

  sem simpleRead : all x. all complete. PValInstance complete (SimpleState (PExportRef x)) -> x
  sem simpleRead = | instance ->
    readPreviousExport (getSt instance).1 instance
end

-- let p_driftExact : all a. (a -> a -> Bool) -> a -> a -> PDist a -> a -> PDist a = lam eq. lam prev. lam next. lam. lam here.
--   if eq here prev
--   then {sample = lam. next, logObserve = lam. 0.0}
--   else {sample = lam. prev, logObserve = lam. 0.0}

-- lang SmallBench = PValInterfaceExp
--   type State x = {assumes : [PAssumeRef (Int, Int)], export : x}
--   sem benchInput : all x. PValState (State x) -> (PValState (State x), PVal (Int, Int))
--   sem benchInput = | st ->
--     -- NOTE(vipa, 2026-01-08): This is not a valid distribution, but
--     -- the benchmarking won't look at that sort of thing, just
--     -- computational updates to the graph.
--     let idx = sym2hash (gensym ()) in
--     match p_pure st {sample = lam. (idx, 0), logObserve = lam. 0.0} with (st, dist) in
--     p_assume st (lam x. lam ref. {x with assumes = snoc x.assumes ref}) dist

--   sem benchExport : all x. all a. State x -> a -> State a
--   sem benchExport st = | a ->
--     { assumes = st.assumes
--     , export = a
--     }

--   sem driftPlusOne : all x. PValInstance Partial (State x) -> PAssumeRef (Int, Int) -> PDist (Int, Int) -> (Int, Int) -> PDist (Int, Int)
--   sem driftPlusOne instance = | aref ->
--     match readPreviousAssume aref instance with (idx, i) in
--     let eq = lam a. lam b. eqi a.1 b.1 in
--     p_driftExact eq (idx, i) (idx, addi i 1)

--   sem runOneTest : all x. PValInstance Complete (State x) -> Int -> PValInstance Complete (State x)
--   sem runOneTest instance =
--   | 0 -> instance
--   | n ->
--     let st = getSt instance in
--     let idx = modi n (length st.assumes) in
--     let instance = startStep instance in
--     let instance = resampleAssume (driftPlusOne instance (get st.assumes idx)) (get st.assumes idx) instance in
--     let instance = (finalizeStep (lam. lam. true) instance).1 in
--     runOneTest instance (subi n 1)

--   sem runAllTest : all x. PValInstance Complete (State x) -> Int -> PValInstance Complete (State x)
--   sem runAllTest instance =
--   | 0 -> instance
--   | n ->
--     let st = getSt instance in
--     let instance = startStep instance in
--     let instance = foldl (lam instance. lam aref. resampleAssume (driftPlusOne instance aref) aref instance) instance st.assumes in
--     let instance = (finalizeStep (lam. lam. true) instance).1 in
--     runAllTest instance (subi n 1)

--   sem bench : all x. all y. Int -> String -> [(String, PValState (State ()) -> PValState (State y))] -> ()
--   sem bench iterationsPerInput label = | inputs ->
--     let initState : State () = {assumes = [], export = ()} in
--     let inputSizes = setOfSeq subi (map (lam pair. length (getSt (instantiate pair.1 initState)).assumes) inputs) in
--     let shouldRunAllTest = setAny (leqi 2) inputSizes in
--     printLn (join ["=== ", label, " (inputs: ", strJoin ", " (map int2string (setToSeq inputSizes)), "; ", int2string iterationsPerInput, " iterations per input) ==="]);
--     (if shouldRunAllTest then printLn " == One input changed per iteration ==" else ());
--     let formatTable : [(String, String)] -> String = lam table.
--       -- TODO(vipa, 2026-01-08): Alignment
--       let len = maxOrElse (lam. 0) subi (map (lam x. length x.0) table) in
--       let table = map (lam x. (concat x.0 (make (subi len (length x.0)) ' '), x.1)) table in
--       join (map (lam pair. join ["  ", pair.0, " ", pair.1, "ms\n"]) table) in
--     let runOneTest = lam pair.
--       let instance = instantiate pair.1 initState in
--       let numInputs = length (getSt instance).assumes in
--       let iterations = muli iterationsPerInput numInputs in
--       let before = wallTimeMs () in
--       runOneTest instance iterations;
--       let after = wallTimeMs () in
--       (pair.0, float2string (divf (subf after before) (int2float iterations))) in
--     let runAllTest = lam pair.
--       let instance = instantiate pair.1 initState in
--       let before = wallTimeMs () in
--       runAllTest instance iterationsPerInput;
--       let after = wallTimeMs () in
--       (pair.0, float2string (divf (subf after before) (int2float iterationsPerInput))) in
--     print (formatTable (map runOneTest inputs));
--     (if shouldRunAllTest then
--        printLn " == All inputs changed each iteration ==";
--        print (formatTable (map runAllTest inputs))
--      else ());
--     printLn ""
-- end

let showHistogram : Bool = false

-- === Microbenchmarks ===
let lambda = 0.12
let mu = 0.06
let rho = 0.56
let maxAge = 34.940139089

-- lang Bench = SmallBench + MutPValExp3
--   sem survivesBind = | st ->
--     match benchInput st with (st, input) in
--     recursive let survives = lam st. lam tBeg.
--       match p_pure st (p_exponential (addf lambda mu)) with (st, dist) in
--       match p_assume_ st dist with (st, delta) in
--       match p_map st (subf tBeg) delta with (st, t) in
--       match p_map st (lam x. ltf x 0.) t with (st, cond) in
--       let outer = lam st. lam cond.
--         if cond then
--           match p_pure st (p_bernoulli rho) with (st, dist) in
--           p_assume_ st dist
--         else
--           match p_pure st (p_bernoulli (divf lambda (addf lambda mu))) with (st, dist) in
--           match p_assume_ st dist with (st, cond) in
--           let inner = lam st. lam cond.
--             if cond then
--               match p_bind_ st survives t with (st, cond) in
--               p_bind_ st (lam st. lam cond. if cond then p_pure st true else p_bind_ st survives t) cond
--             else p_pure st false in
--           p_bind_ st inner cond in
--       p_bind_ st outer cond in
--     match p_map st (lam. maxAge) input with (st, t) in
--     (p_bind_ st survives t).0

--   sem survivesMatch = | st ->
--     match benchInput st with (st, input) in
--     match p_map st (lam. maxAge) input with (st, t) in
--     recursive let survives : all st. PValState st -> PVal Float -> (PValState st, PVal Bool) = lam st. lam tBeg.
--       match p_pure st (p_exponential (addf lambda mu)) with (st, dist) in
--       match p_assume_ st dist with (st, delta) in
--       match p_map st subf tBeg with (st, t) in
--       match p_apply st t delta with (st, t) in
--       let outer = lam st. lam cond.
--         match cond with Some _ then
--           match p_pure st (p_bernoulli rho) with (st, dist) in
--           p_assume_ st dist
--         else
--           match p_pure st (p_bernoulli (divf lambda (addf lambda mu))) with (st, dist) in
--           let inner = lam st. lam cond.
--             match cond with Some _ then
--               let innerest = lam st. lam cond.
--                 match cond with Some _ then p_pure st true else survives st t in
--               match survives st t with (st, temp) in
--               p_match_ st temp (lam c. if c then Some () else None ()) innerest
--             else
--               p_pure st false in
--           match p_assume_ st dist with (st, cond) in
--           p_match_ st cond (lam c. if c then Some () else None ()) inner in
--       p_match_ st t (lam t. if ltf t 0. then Some () else None ()) outer in
--     (survives st t).0

--   sem survivesChunk = | st ->
--     match benchInput st with (st, input) in
--     match p_map st (lam. maxAge) input with (st, t) in
--     let f = lam st.
--       recursive let survives = lam tBeg.
--         let t = subf tBeg (p_sample (p_exponential (addf lambda mu))) in
--         if ltf t 0. then  -- 8 unaligned (2)
--           p_sample (p_bernoulli rho)
--         else
--           if p_sample (p_bernoulli (divf lambda (addf lambda mu))) then -- 8 unaligned (3)
--             if survives t then  -- 4 unaligned, 4 aligned (1)
--               true
--             else
--               survives t
--           else
--             false
--       in
--       let t = p_readPVal st t in
--       survives t in
--     (p_chunk st #frozen"f").0
-- end

-- let run =
--   use Bench in
--   bench 10000 "survives"
--     [ ("bind", survivesBind)
--     , ("chunk", survivesChunk)
--     , ("match", survivesMatch)
--     ];
--   let f1 = lam pair. (pair.0, addi pair.1 1) in
--   let f2 = lam pair. lam pair1. (pair.0, addi pair.1 pair1.1) in
--   bench 1000000 "empty"
--     [ ( "empty1"
--       , lam st.
--         match benchInput st with (st, input) in
--         p_export st benchExport input
--       )
--     , ( "empty2"
--       , lam st.
--         match benchInput st with (st, input) in
--         match benchInput st with (st, input) in
--         p_export st benchExport input
--       )
--     , ( "empty3"
--       , lam st.
--         match benchInput st with (st, input) in
--         match benchInput st with (st, input) in
--         match benchInput st with (st, input) in
--         p_export st benchExport input
--       )
--     , ( "empty4"
--       , lam st.
--         match benchInput st with (st, input) in
--         match benchInput st with (st, input) in
--         match benchInput st with (st, input) in
--         match benchInput st with (st, input) in
--         p_export st benchExport input
--       )
--     ];
--   bench 1000000 "map"
--     [ ( "map"
--       , lam st.
--         match benchInput st with (st, input) in
--         match p_map st f1 input with (st, output) in
--         p_export st benchExport output
--       )
--     , ( "submap"
--       , lam st.
--         match benchInput st with (st, input) in
--         match p_subMap_ st (lam st. lam a. (st, f1 a)) input with (st, output) in
--         p_export st benchExport output
--       )
--     , ( "bind-pure"
--       , lam st.
--         match benchInput st with (st, input) in
--         match p_bind_ st (lam st. lam a. p_pure st (f1 a)) input with (st, output) in
--         p_export st benchExport output
--       )
--     , ( "chunk"
--       , lam st.
--         match benchInput st with (st, input) in
--         let f = lam st. f1 (p_readPVal st input) in
--         match p_chunk st #frozen"f" with (st, output) in
--         p_export st benchExport output
--       )
--     ];
--   let mkMultiMapBench = lam n.
--     bench 1000000 (concat (int2string n) " maps")
--       [ ( "many maps"
--         , lam st.
--           recursive let addMap = lam input. lam n.
--             match n with 0 then input else
--             addMap (p_map input.0 f1 input.1) (subi n 1) in
--           match addMap (benchInput st) n with (st, output) in
--           p_export st benchExport output
--         )
--       , ( "one map"
--         , lam st.
--           match benchInput st with (st, input) in
--           recursive let work = lam acc. lam n.
--             match n with 0 then acc else
--             work (f1 acc) (subi n 1) in
--           match p_map st (lam input. work input n) input with (st, output) in
--           p_export st benchExport output
--         )
--       , ( "chunk"
--         , lam st.
--           match benchInput st with (st, input) in
--           let f = lam st.
--             recursive let work = lam acc. lam n.
--               match n with 0 then acc else
--               work (f1 acc) (subi n 1) in
--             work (p_readPVal st input) n in
--           match p_chunk st #frozen"f" with (st, output) in
--           p_export st benchExport output
--         )
--       ] in
--   repeati (lam i. mkMultiMapBench (muli 5 (addi i 3))) 3;
--   bench 1000000 "apply"
--     [ ( "apply"
--       , lam st.
--         match benchInput st with (st, input0) in
--         match benchInput st with (st, input1) in
--         match p_map st f2 input0 with (st, tmp) in
--         match p_apply st tmp input1 with (st, output) in
--         p_export st benchExport output
--       )
--     , ( "chunk"
--       , lam st.
--         match benchInput st with (st, input0) in
--         match benchInput st with (st, input1) in
--         let f = lam st. f2 (p_readPVal st input0) (p_readPVal st input1) in
--         match p_chunk st #frozen"f" with (st, output) in
--         p_export st benchExport output
--       )
--     ];
--   bench 1000000 "select"
--     [ ( "select"
--       , lam st.
--         match benchInput st with (st, input0) in
--         match benchInput st with (st, input1) in
--         match benchInput st with (st, input2) in
--         match benchInput st with (st, idx) in
--         let arr = [input0, input1, input2] in
--         match p_select st (lam pair. get arr (modi pair.1 (length arr))) idx with (st, output) in
--         p_export st benchExport output
--       )
--     , ( "bind"
--       , lam st.
--         match benchInput st with (st, input0) in
--         match benchInput st with (st, input1) in
--         match benchInput st with (st, input2) in
--         match benchInput st with (st, idx) in
--         let arr = [input0, input1, input2] in
--         match p_bind_ st (lam st. lam pair. (st, get arr (modi pair.1 (length arr)))) idx with (st, output) in
--         p_export st benchExport output
--       )
--     , ( "subMap-join"
--       , lam st.
--         match benchInput st with (st, input0) in
--         match benchInput st with (st, input1) in
--         match benchInput st with (st, input2) in
--         match benchInput st with (st, idx) in
--         let arr = [input0, input1, input2] in
--         match p_subMap_ st (lam st. lam pair. (st, get arr (modi pair.1 (length arr)))) idx with (st, output) in
--         match p_join st output with (st, output) in
--         p_export st benchExport output
--       )
--     , ( "map-join"
--       , lam st.
--         match benchInput st with (st, input0) in
--         match benchInput st with (st, input1) in
--         match benchInput st with (st, input2) in
--         match benchInput st with (st, idx) in
--         let arr = [input0, input1, input2] in
--         match p_map st (lam pair. get arr (modi pair.1 (length arr))) idx with (st, output) in
--         match p_join st output with (st, output) in
--         p_export st benchExport output
--       )
--     , ( "chunk"
--       , lam st.
--         match benchInput st with (st, input0) in
--         match benchInput st with (st, input1) in
--         match benchInput st with (st, input2) in
--         match benchInput st with (st, idx) in
--         let arr = [input0, input1, input2] in
--         let f = lam st. p_readPVal st (get arr (modi (p_readPVal st idx).1 (length arr))) in
--         match p_chunk st #frozen"f" with (st, output) in
--         p_export st benchExport output
--       )
--     ];
--   ()


-- === Bern and ==

let baseline = lam.
  let a = assume (Bernoulli 0.5) in
  let b = assume (Bernoulli 0.5) in
  and a b

lang BernAnd = SimpleResample
  sem run = | st ->
    match p_pure st (p_bernoulli 0.5) with (st, dist) in
    -- dist : PVal y (PDist Bool)
    match p_assume st simpleStore dist with (st, a) in
    match p_assume st simpleStore dist with (st, b) in
    match p_map st and a with (st, tmp) in
    -- match p_subMap_ st (lam st. lam a. (st, and a)) a with (st, tmp) in
    -- and : Bool -> (Bool -> Bool)
    --
    -- tmp : PVal y (Bool -> Bool)
    match p_apply st tmp b with (st, res) in
    p_export st simpleExport res
end

lang RunBernAndMut = BernAnd + MCMCPVal + MutPValExp
end

lang RunBernAndMut2 = BernAnd + MCMCPVal + MutPValExp2
end

lang RunBernAndMut3 = BernAnd + MCMCPVal + MutPValExp3
end

lang RunBernAndPersistent2 = BernAnd + MCMCPVal + SimplePersistentPVal2
end

let result =
  printLn "\n=== bern_and ===";
  let globalProb = 0.1 in
  let iterations = 1000000 in
  let toString = bool2string in
  let mkHisto = histogram cmpBool in
  let summarizePVal = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto res)) else () in
  let summarizeBaseline = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto (distEmpiricalSamples res).0)) else () in
  let run =
    use RunBernAndMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Mut" (timeF run);
  let run =
    use RunBernAndMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Mut2" (timeF run);
  let run =
    use RunBernAndMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Mut3" (timeF run);
  let run =
    use RunBernAndPersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent2" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "none", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw partial" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "full", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw full" (timeF run);
  let run = lam.
    infer (SimplePValGraph {run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline in
  summarizeBaseline "simple-pval-graph" (timeF run);
  ()


-- === Simple Bind ===

let baseline = lam.
  if assume (Bernoulli 0.5)
  then assume (Bernoulli 0.9)
  else assume (Bernoulli 0.5)

lang SimpleBind = SimpleResample
  sem run = | st ->
    match p_pure st (p_bernoulli 0.5) with (st, dist) in
    match p_assume st simpleStore dist with (st, c) in
    let f = lam st. lam c.
      if c then
        match p_pure st (p_bernoulli 0.9) with (st, dist) in
        p_assume_ st dist
      else
        match p_pure st (p_bernoulli 0.5) with (st, dist) in
        p_assume_ st dist in
    match p_bind_ st f c with (st, res) in
    p_export st simpleExport res
end

lang SimpleSubMap = SimpleResample
  sem run = | st ->
    match p_pure st (p_bernoulli 0.5) with (st, dist) in
    match p_assume st simpleStore dist with (st, c) in
    let f = lam st. lam c.
      if c then
        match p_pure st (p_bernoulli 0.9) with (st, dist) in
        p_assume_ st dist
      else
        match p_pure st (p_bernoulli 0.5) with (st, dist) in
        p_assume_ st dist in
    match p_subMap_ st f c with (st, res) in
    match p_join st res with (st, res) in
    p_export st simpleExport res
end

lang SimpleMatch = SimpleResample
  sem run = | st ->
    match p_pure st (p_bernoulli 0.5) with (st, dist) in
    match p_assume st simpleStore dist with (st, c) in
    let pick = lam b. if b then Some () else None () in
    let build = lam st. lam opt.
      match opt with Some _ then
        match p_pure st (p_bernoulli 0.9) with (st, dist) in
        p_assume_ st dist
      else
        match p_pure st (p_bernoulli 0.5) with (st, dist) in
        p_assume_ st dist in
    match p_match_ st c pick build with (st, res) in
    p_export st simpleExport res
end

lang RunSimpleBindMut = SimpleBind + MCMCPVal + MutPValExp
end

lang RunSimpleMatchMut = SimpleMatch + MCMCPVal + MutPValExp
end

lang RunSimpleBindMut2 = SimpleBind + MCMCPVal + MutPValExp2
end

lang RunSimpleMatchMut2 = SimpleMatch + MCMCPVal + MutPValExp2
end

lang RunSimpleBindMut3 = SimpleBind + MCMCPVal + MutPValExp3
end

lang RunSimpleSubMapMut3 = SimpleSubMap + MCMCPVal + MutPValExp3
end

lang RunSimpleMatchMut3 = SimpleMatch + MCMCPVal + MutPValExp3
end

lang RunSimpleBindPersistent2 = SimpleBind + MCMCPVal + SimplePersistentPVal2
end

let result =
  printLn "\n=== simple_bind ===";
  let globalProb = 0.1 in
  let iterations = 100000 in
  let toString = bool2string in
  let mkHisto = histogram cmpBool in
  let summarizePVal = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto res)) else () in
  let summarizeBaseline = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto (distEmpiricalSamples res).0)) else () in
  let run =
    use RunSimpleBindMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut" (timeF run);
  let run =
    use RunSimpleMatchMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut match" (timeF run);
  let run =
    use RunSimpleBindMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut2" (timeF run);
  let run =
    use RunSimpleMatchMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut2 match" (timeF run);
  let run =
    use RunSimpleBindMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3" (timeF run);
  let run =
    use RunSimpleSubMapMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 submap" (timeF run);
  let run =
    use RunSimpleMatchMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 match" (timeF run);
  let run =
    use RunSimpleBindPersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent2" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "none", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw partial" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "full", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw full" (timeF run);
  let run = lam.
    infer (SimplePValGraph {run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline in
  summarizeBaseline "simple-pval-graph" (timeF run);
  ()


-- === Manual Geometric ===

let baseline = lam.
  recursive let work = lam acc.
    if assume (Bernoulli 0.5)
    then work (addi acc 1)
    else acc in
  let c = assume (Bernoulli 0.5) in
  if c
  then work 1
  else 0

lang ManualGeometric = SimpleResample
  sem run = | st ->
    match p_pure st (p_bernoulli 0.5) with (st, dist) in
    match p_assume st simpleStore dist with (st, c) in
    recursive let f = lam i. lam st. lam c.
      let recur = lam x. lam y. f (addi i 1) x y in
      if c then
        match p_assume_ st dist with (st, c) in
        p_bind_ st recur c
      else
        p_pure st i in
    let start = lam x. f 0 x in
    match p_bind_ st start c with (st, res) in
    p_export st simpleExport res
end

lang ManualGeometricSubMap = SimpleResample
  sem run = | st ->
    match p_pure st (p_bernoulli 0.5) with (st, dist) in
    match p_assume st simpleStore dist with (st, c) in
    recursive let f = lam i. lam st. lam c.
      let recur = lam x. lam y. f (addi i 1) x y in
      if c then
        match p_assume_ st dist with (st, c) in
        match p_subMap_ st recur c with (st, res) in
        p_join st res
      else
        p_pure st i in
    let start = lam x. f 0 x in
    match p_subMap_ st start c with (st, res) in
    match p_join st res with (st, res) in
    p_export st simpleExport res
end

lang ManualGeometricMatch = SimpleResample
  sem run = | st ->
    match p_pure st (p_bernoulli 0.5) with (st, dist) in
    match p_assume st simpleStore dist with (st, c) in
    let pick = lam b. if b then Some () else None () in
    recursive let f = lam i. lam st. lam opt.
      let recur = lam x. lam y. f (addi i 1) x y in
      match opt with Some _ then
        match p_assume_ st dist with (st, c) in
        p_match_ st c pick recur
      else
        p_pure st i in
    let start = lam x. f 0 x in
    match p_match_ st c pick start with (st, res) in
    p_export st simpleExport res
end

lang ManualGeometricCache = SimpleResample
  sem run = | st ->
    match p_pure st (p_bernoulli 0.5) with (st, dist) in
    match p_assume st simpleStore dist with (st, c) in
    match p_cache st eqb c with (st, c) in
    recursive let f = lam i. lam st. lam c.
      let recur = lam x. lam y. f (addi i 1) x y in
      if c then
        match p_assume_ st dist with (st, c) in
        p_bind_ st recur c
      else
        p_pure st i in
    let start = lam x. f 0 x in
    match p_bind_ st start c with (st, res) in
    p_export st simpleExport res
end

lang ManualGeometricChunk = SimpleResample
  sem run = | st ->
    let dist = p_bernoulli 0.5 in
    recursive let f = lam i. lam c.
      if c then
        f (addi i 1) (p_sample dist)
      else i in
    match p_pure st dist with (st, dist) in
    match p_assume st simpleStore dist with (st, c) in
    let f = lam st. f 0 (p_readPVal st c) in
    match p_chunk st #frozen"f" with (st, res) in
    p_export st simpleExport res
end

lang RunManualGeometricMut = ManualGeometric + MCMCPVal + MutPValExp
end

lang RunManualGeometricCacheMut = ManualGeometricCache + MCMCPVal + MutPValExp
end

lang RunManualGeometricMatchMut = ManualGeometricMatch + MCMCPVal + MutPValExp
end

lang RunManualGeometricMut2 = ManualGeometric + MCMCPVal + MutPValExp2
end

lang RunManualGeometricCacheMut2 = ManualGeometricCache + MCMCPVal + MutPValExp2
end

lang RunManualGeometricMatchMut2 = ManualGeometricMatch + MCMCPVal + MutPValExp2
end

lang RunManualGeometricMut3 = ManualGeometric + MCMCPVal + MutPValExp3
end

lang RunManualGeometricSubMapMut3 = ManualGeometricSubMap + MCMCPVal + MutPValExp3
end

lang RunManualGeometricCacheMut3 = ManualGeometricCache + MCMCPVal + MutPValExp3
end

lang RunManualGeometricMatchMut3 = ManualGeometricMatch + MCMCPVal + MutPValExp3
end

lang RunManualGeometricChunkMut3 = ManualGeometricChunk + MCMCPVal + MutPValExp3
end

lang RunManualGeometricPersistent2 = ManualGeometric + MCMCPVal + SimplePersistentPVal2
end

lang RunManualGeometricCachePersistent2 = ManualGeometricCache + MCMCPVal + SimplePersistentPVal2
end

let result =
  printLn "\n=== manual_geometric ===";
  let globalProb = 0.1 in
  let iterations = 1000000 in
  let toString = int2string in
  let mkHisto = histogram subi in
  let summarizePVal = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto res)) else () in
  let summarizeBaseline = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto (distEmpiricalSamples res).0)) else () in
  let run =
    use RunManualGeometricMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut" (timeF run);
  let run =
    use RunManualGeometricCacheMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut cache" (timeF run);
  let run =
    use RunManualGeometricMatchMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut match" (timeF run);
  let run =
    use RunManualGeometricMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut2" (timeF run);
  let run =
    use RunManualGeometricCacheMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut2 cache" (timeF run);
  let run =
    use RunManualGeometricMatchMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut2 match" (timeF run);
  let run =
    use RunManualGeometricMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3" (timeF run);
  let run =
    use RunManualGeometricSubMapMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 submap" (timeF run);
  let run =
    use RunManualGeometricCacheMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 cache" (timeF run);
  let run =
    use RunManualGeometricMatchMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 match" (timeF run);
  let run =
    use RunManualGeometricChunkMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 Chunk" (timeF run);
  let run =
    use RunManualGeometricPersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent2" (timeF run);
  let run =
    use RunManualGeometricCachePersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent2 cache" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "none", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw partial" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "full", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw full" (timeF run);
  let run = lam.
    infer (SimplePValGraph {run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline in
  summarizeBaseline "simple-pval-graph" (timeF run);
  ()

-- === Coin ===

let observations = [true, true, true, false, true, true, false, true]

let baseline = lam.
  let p = assume (Beta 1.0 1.0) in
  for_ observations (lam o. observe o (Bernoulli p));
  p

lang CoinOneObserve = SimpleResample
  sem run = | st ->
    match p_pure st (p_beta 1.0 1.0) with (st, dist) in
    match p_assume st simpleStore dist with (st, p) in
    let st = p_weight_ st (lam p. foldl addf 0.0 (map (lam o. p_logObserve (p_bernoulli p) o) observations)) p in
    p_export st simpleExport p
end

lang CoinManyObserve = SimpleResample
  sem run = | st ->
    match p_pure st (p_beta 1.0 1.0) with (st, dist) in
    match p_assume st simpleStore dist with (st, p) in
    let f = lam st. lam o.
      p_weight_ st (lam p. p_logObserve (p_bernoulli p) o) p in
    let st = foldl f st observations in
    p_export st simpleExport p
end

lang RunCoinOneObserveMut = CoinOneObserve + MCMCPVal + MutPValExp
end

lang RunCoinManyObserveMut = CoinManyObserve + MCMCPVal + MutPValExp
end

lang RunCoinOneObserveMut2 = CoinOneObserve + MCMCPVal + MutPValExp2
end

lang RunCoinManyObserveMut2 = CoinManyObserve + MCMCPVal + MutPValExp2
end

lang RunCoinOneObserveMut3 = CoinOneObserve + MCMCPVal + MutPValExp3
end

lang RunCoinManyObserveMut3 = CoinManyObserve + MCMCPVal + MutPValExp3
end

lang RunCoinOneObservePersistent2 = CoinOneObserve + MCMCPVal + SimplePersistentPVal2
end

lang RunCoinManyObservePersistent2 = CoinManyObserve + MCMCPVal + SimplePersistentPVal2
end

let result =
  printLn "\n=== coin ===";
  let globalProb = 0.1 in
  let iterations = 100000 in
  let toString = interval2string in
  let mkHisto = bucket 10 0.0 1.0 in
  let summarizePVal = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto res)) else () in
  let summarizeBaseline = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto (distEmpiricalSamples res).0)) else () in
  let run =
    use RunCoinOneObserveMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut one observe" (timeF run);
  let run =
    use RunCoinManyObserveMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut many observe" (timeF run);
  let run =
    use RunCoinOneObserveMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut2 one observe" (timeF run);
  let run =
    use RunCoinManyObserveMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut2 many observe" (timeF run);
  let run =
    use RunCoinOneObserveMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 one observe" (timeF run);
  let run =
    use RunCoinManyObserveMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 many observe" (timeF run);
  let run =
    use RunCoinOneObservePersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent2 one observe" (timeF run);
  let run =
    use RunCoinManyObservePersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent2 many observe" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "none", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw partial" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "full", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw full" (timeF run);
  let run = lam.
    infer (SimplePValGraph {run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline in
  summarizeBaseline "simple-pval-graph" (timeF run);
  ()


-- === Tree Inference ===

type Tree
con Leaf : {id : Int, x : Float} -> Tree
con Node : {left : Tree, right : Tree, x : Float} -> Tree

recursive let asShape = lam t. switch t
  case Leaf x then int2string x.id
  case Node x then join ["(", asShape x.left, ", ", asShape x.right, ")"]
  end
end

let initTrees =
  [ Leaf {id = 0, x = 0.0}
  , Leaf {id = 1, x = 5.0}
  , Leaf {id = 2, x = 10.0}
  , Leaf {id = 3, x = 15.0}
  -- , Leaf {id = 4, x = 20.0}
  ]

recursive let minId = lam t. switch t
  case Leaf x then x.id
  case Node x then mini (minId x.left) (minId x.right)
  end
end
let getX = lam t. switch t
  case Leaf x then x.x
  case Node x then x.x
  end
let mkNode = lam x. lam l. lam r.
  if lti (minId l) (minId r)
  then Node {left = l, right = r, x = x}
  else Node {left = r, right = l, x = x}

let baseline = lam.
  let pickpair = lam n.
    let i = assume (UniformDiscrete 0 (subi n 1)) in
    let j = assume (UniformDiscrete 0 (subi n 2)) in
    if lti j i then (i,j) else (i,addi j 1) in

  let rootValue = assume (Gaussian 0.0 10.0) in
  let deviateFromDist = lam x. Gaussian x 10.0 in
  let rootDist = deviateFromDist rootValue in
  let cancelRootDist = lam x.
    weight (negf (logObserve (Gaussian rootValue 10.0) x)) in
    -- cancel (observe x rootDist) in

  recursive let cluster = lam nTrees. lam trees.
    if eqi nTrees 1 then head trees else
    let pair = pickpair nTrees in
    let i = pair.0 in
    let j = pair.1 in
    -- match pickpair nTrees with (i, j) in
    let l = get trees i in
    let r = get trees j in
    let trees = mapiOption
      (lam idx. lam v. if or (eqi idx i) (eqi idx j) then None () else Some v)
      trees in
    let here = assume rootDist in
    cancelRootDist (getX l);
    cancelRootDist (getX r);
    observe (getX l) (deviateFromDist here);
    observe (getX r) (deviateFromDist here);
    cluster (subi nTrees 1) (snoc trees (mkNode here l r)) in

  for_ initTrees (lam t. observe (getX t) rootDist);
  cluster (length initTrees) initTrees

let baseline2 = lam.
  let sortedPickPair = lam n.
    let i = assume (UniformDiscrete 0 (subi n 1)) in
    let j = assume (UniformDiscrete 0 (subi n 2)) in
    if lti j i then (j,i) else (i,addi j 1) in

  let rootValue = assume (Gaussian 0.0 10.0) in
  let deviateFromDist = lam x. Gaussian x 10.0 in
  let rootDist = deviateFromDist rootValue in
  let cancelRootDist = lam x.
    weight (negf (logObserve (Gaussian rootValue 10.0) x)) in
    -- cancel (observe x rootDist) in

  recursive let cluster = lam trees.
    match trees with [tree] then tree else
    let pair = sortedPickPair (length trees) in
    let i = pair.0 in
    let j = pair.1 in
    -- match pickpair nTrees with (i, j) in
    let l = get trees i in
    let r = get trees j in
    let fetchAt = lam idx.
      let idx = addi idx (if geqi idx i then 1 else 0) in
      let idx = addi idx (if geqi idx j then 1 else 0) in
      get trees idx in
    let trees = create (subi (length trees) 2) fetchAt in
    let here = assume rootDist in
    cancelRootDist (getX l);
    cancelRootDist (getX r);
    observe (getX l) (deviateFromDist here);
    observe (getX r) (deviateFromDist here);
    cluster (snoc trees (mkNode here l r)) in

  for_ initTrees (lam t. observe (getX t) rootDist);
  if true then cluster initTrees else mkNode 0.0 (Leaf {x = 0.0, id = 7}) (Leaf {x = 0.0, id = 8}); cluster initTrees

let baseline3 = lam.
  let sortedPickPair = lam n.
    let i = assume (UniformDiscrete 0 (subi n 1)) in
    let j = assume (UniformDiscrete 0 (subi n 2)) in
    if lti j i then (j,i) else (i,addi j 1) in

  let rootValue = assume (Gaussian 0.0 10.0) in
  let deviateFromDist = lam x. Gaussian x 10.0 in
  let rootDist = deviateFromDist rootValue in
  let cancelRootDist = lam x.
    weight (negf (logObserve (Gaussian rootValue 10.0) x)) in
    -- cancel (observe x rootDist) in

  recursive let cluster = lam trees.
    match trees with [tree] then tree else
    let pair = sortedPickPair (length trees) in
    let i = pair.0 in
    let j = pair.1 in
    -- match pickpair nTrees with (i, j) in
    let l = get trees i in
    let r = get trees j in
    let fetchAt = lam idx.
      match splitAt trees idx with (_, [idx0, idx1, idx2] ++ _) in
      if leqi i idx then
        if leqi j (addi idx 1)
        then idx2
        else idx1
      else idx0 in
    let trees = create (subi (length trees) 2) fetchAt in
    let here = assume rootDist in
    cancelRootDist (getX l);
    cancelRootDist (getX r);
    observe (getX l) (deviateFromDist here);
    observe (getX r) (deviateFromDist here);
    cluster (snoc trees (mkNode here l r)) in

  for_ initTrees (lam t. observe (getX t) rootDist);
  if true then cluster initTrees else mkNode 0.0 (Leaf {x = 0.0, id = 7}) (Leaf {x = 0.0, id = 8}); cluster initTrees



-- lang TreeInferenceQuoteAutoQuote = SimpleResample
--   sem run = | st ->
--   let pickpair_p = lam st. lam n.
--     match p_pure st (p_uniformDiscrete 0 (subi n 1)) with (st, tmp) in
--     match p_assume st simpleStore tmp with (st, i) in
--     match p_pure st (p_uniformDiscrete 0 (subi n 2)) with (st, tmp) in
--     match p_assume st simpleStore tmp with (st, j) in
--     match p_map st lti j with (st, tmp) in
--     match p_apply st tmp i with (st, tmp) in
--     let f : all z. PValState () z -> Bool -> PValHList z Unknown -> (Unknown, PVal z (Int, Int)) = lam st. lam c. lam l.
--       match l with PVHCons (i, PVHCons (j, PVHNil ())) in
--       if c then
--         match p_map st (lam a. lam b. (a, b)) i with (st, tmp) in
--         match p_apply st tmp j with (st, ret) in
--         (st, ret)
--       else
--         match p_map st (lam a. lam b. (a, b)) i with (st, tmp) in
--         match p_map st addi j with (st, tmp2) in
--         match p_map st (lam f. f 1) tmp2 with (st, tmp2) in
--         match p_apply st tmp tmp2 with (st, ret) in
--         (st, ret) in
--     p_bind_ st #frozen"f" tmp (PVHCons (i, PVHCons (j, PVHNil ()))) in

--   let mapiOption
--     : all a. all a_. all b. all b_. (V x1 Int -> V F (V a_ a -> V x3 (Option (V b_ b))))
--     -> V x4 [V a_ a]
--     -> V x5 [V b_ b]
--     = lam f.
--       recursive let work = lam st. lam idx. lam as.

--   match p_pure st (p_gaussian 0.0 10.0) with (st, tmp) in
--   match p_assume st simpleStore tmp with (st, rootValue) in
--   let deviateFromDist_l = lam st. lam x. p_map st (lam x. p_gaussian x 10.0) x in
--   match deviateFromDist_l st rootValue with (st, rootDist) in
--   let cancelRootDist_l = lam st. lam x.
--     -- TODO(vipa, 2025-10-06): When converting a function we need to
--     -- figure out if it's going to be used in p_bind or p_map, for how
--     -- to handle free variables. Maybe we'll never convert a function
--     -- wholesale, rather just `if` expressions?
--     match p_map st p_logObserve rootDist with (st, tmp) in
--     match p_apply st tmp x with (st, tmp) in
--     (p_weight_ st negf tmp, ()) in
--   let cancelRootDist_p = lam st. lam x.
--     match p_map st p_logObserve rootDist with (st, tmp) in
--     match p_map st (lam f. f x) tmp with (st, tmp) in
--     (p_weight_ st negf tmp, ()) in

--   -- recursive
--   --   let cluster_p = lam st. lam nTrees. lam trees.
--   --     if eqi nTrees 1 then p_pure st (head trees) else
--   --     -- NOTE(vipa, 2025-10-06): This assumes special handling for
--   --     -- `match ... in`, with the assumption that such patterns are
--   --     -- infallible and thus don't require branching or `p_bind`
--   --     match pickpair_p st nTrees with (st, tmp) in
--   --     match p_map st (lam x. match x with (i, j) in i) tmp with (st, i) in
--   --     match p_map st (lam x. match x with (i, j) in j) tmp with (st, j) in
--   --     match p_map st (get trees) i with (st, l) in
--   --     match p_map st (get trees) j with (st, r) in
--   never
-- end

lang TreeInferenceTreeBind = SimpleResample
  sem run = | st ->
    let pickpair = lam st. lam n.
      match p_pure st (p_uniformDiscrete 0 (subi n 1)) with (st, dist) in
      match p_assume st simpleStore dist with (st, i) in
      match p_pure st (p_uniformDiscrete 0 (subi n 2)) with (st, dist) in
      match p_assume st simpleStore dist with (st, j) in
      let f = lam i. lam j. if lti j i then (j,i) else (i, addi j 1) in
      match p_map st f i with (st, tmp) in
      p_apply st tmp j in

    match p_pure st (p_gaussian 0.0 10.0) with (st, dist) in
    match p_assume st simpleStore dist with (st, rootValue) in
    let deviateFromDist = lam x. p_gaussian x 10.0 in
    match p_map st deviateFromDist rootValue with (st, rootDist) in

    recursive let cluster = lam st. lam trees.
      match trees with [tree] then (st, tree) else
      match pickpair st (length trees) with (st, pair) in
      match p_assume st simpleStore rootDist with (st, here) in
      let mkCarryOn = lam idx. lam st.
        match splitAt trees idx with (_, [idx0, idx1, idx2] ++ _) in
        let f = lam trip. lam st. lam pair.
          match trip with (idx0, idx1, idx2) in
          match if lti pair.0 pair.1 then (pair.0, pair.1) else (pair.1, pair.0)
          with (l, r) in
          if leqi l idx then
            if leqi r (addi idx 1)
            then (st, idx2)
            else (st, idx1)
          else (st, idx0)
        in
        p_bind_ st (f (idx0, idx1, idx2)) pair in
      match mapAccumL (lam st. lam f. f st) st (create (subi (length trees) 2) mkCarryOn) with (st, carryOns) in
      let f = lam trees. lam st. lam pair.
        match p_map st (lam l. lam r. (l, r)) (get trees pair.0) with (st, tmp) in
        p_apply st tmp (get trees pair.1) in
      match p_bind_ st (f trees) pair with (st, treePair) in
      let f = lam rootDist. lam here. lam treePair.
        let l = treePair.0 in
        let r = treePair.1 in
        let calcWeight = lam t. addf
          (negf (p_logObserve rootDist (getX t)))
          (p_logObserve (deviateFromDist here) (getX t)) in
        addf (calcWeight l) (calcWeight r) in
      match p_map st f rootDist with (st, tmp) in
      match p_apply st tmp here with (st, tmp) in
      match p_apply st tmp treePair with (st, tmp) in
      let st = p_weight_ st (lam w. w) tmp in
      let f = lam here. lam treePair.
        mkNode here treePair.0 treePair.1 in
      match p_map st f here with (st, tmp) in
      match p_apply st tmp treePair with (st, merged) in
      cluster st (snoc carryOns merged)
    in

    let f = lam rootDist.
      foldl addf 0.0 (map (lam t. p_logObserve rootDist (getX t)) initTrees) in
    let st = p_weight_ st f rootDist in
    match mapAccumL p_pure st initTrees with (st, initTrees) in
    match cluster st initTrees with (st, tree) in
    p_export st simpleExport tree
end

lang RunTreeInferenceTreeBindMut = TreeInferenceTreeBind + MCMCPVal + MutPValExp
end

lang RunTreeInferenceTreeBindMut2 = TreeInferenceTreeBind + MCMCPVal + MutPValExp2
end

lang RunTreeInferenceTreeBindMut3 = TreeInferenceTreeBind + MCMCPVal + MutPValExp3
end

lang RunTreeInferenceTreeBindDebug = TreeInferenceTreeBind + DebugPValExp
end

lang RunTreeInferenceTreeBindPersistent2 = TreeInferenceTreeBind + MCMCPVal + SimplePersistentPVal2
end

lang TreeInferenceTreeSelect = SimpleResample
  sem run = | st ->
    let pickpair = lam st. lam n.
      match p_pure st (p_uniformDiscrete 0 (subi n 1)) with (st, dist) in
      match p_assume st simpleStore dist with (st, i) in
      match p_pure st (p_uniformDiscrete 0 (subi n 2)) with (st, dist) in
      match p_assume st simpleStore dist with (st, j) in
      let f = lam i. lam j. if lti j i then (j,i) else (i, addi j 1) in
      match p_map st f i with (st, tmp) in
      p_apply st tmp j in

    match p_pure st (p_gaussian 0.0 10.0) with (st, dist) in
    match p_assume st simpleStore dist with (st, rootValue) in
    let deviateFromDist = lam x. p_gaussian x 10.0 in
    match p_map st deviateFromDist rootValue with (st, rootDist) in

    recursive let cluster = lam st. lam trees.
      match trees with [tree] then (st, tree) else
      match pickpair st (length trees) with (st, pair) in
      match p_assume st simpleStore rootDist with (st, here) in
      let mkCarryOn = lam idx. lam st.
        match splitAt trees idx with (_, [idx0, idx1, idx2] ++ _) in
        let f = lam trip. lam pair.
          match trip with (idx0, idx1, idx2) in
          match if lti pair.0 pair.1 then (pair.0, pair.1) else (pair.1, pair.0)
          with (l, r) in
          if leqi l idx then
            if leqi r (addi idx 1)
            then idx2
            else idx1
          else idx0
        in
        p_select st (f (idx0, idx1, idx2)) pair in
      match mapAccumL (lam st. lam f. f st) st (create (subi (length trees) 2) mkCarryOn) with (st, carryOns) in
      let f = lam trees. lam pair. get trees pair.0 in
      match p_select st (f trees) pair with (st, l) in
      let f = lam trees. lam pair. get trees pair.1 in
      match p_select st (f trees) pair with (st, r) in
      let f = lam rootDist. lam here. lam t. addf
        (negf (p_logObserve rootDist (getX t)))
        (p_logObserve (deviateFromDist here) (getX t)) in
      match p_map st f rootDist with (st, tmp) in
      match p_apply st tmp here with (st, tmp) in
      match p_apply st tmp l with (st, lWeight) in
      let st = p_weight_ st (lam x. x) lWeight in
      match p_apply st tmp r with (st, rWeight) in
      let st = p_weight_ st (lam x. x) rWeight in
      let f = lam here. lam l. lam r.
        mkNode here l r in
      match p_map st f here with (st, tmp) in
      match p_apply st tmp l with (st, tmp) in
      match p_apply st tmp r with (st, merged) in
      cluster st (snoc carryOns merged)
    in

    let f = lam rootDist.
      foldl addf 0.0 (map (lam t. p_logObserve rootDist (getX t)) initTrees) in
    let st = p_weight_ st f rootDist in
    match mapAccumL p_pure st initTrees with (st, initTrees) in
    match cluster st initTrees with (st, tree) in
    p_export st simpleExport tree
end

lang RunTreeInferenceTreeSelectMut = TreeInferenceTreeSelect + MCMCPVal + MutPValExp
end

lang RunTreeInferenceTreeSelectMut2 = TreeInferenceTreeSelect + MCMCPVal + MutPValExp2
end

lang RunTreeInferenceTreeSelectMut3 = TreeInferenceTreeSelect + MCMCPVal + MutPValExp3
end

lang RunTreeInferenceTreeSelectPersistent2 = TreeInferenceTreeSelect + MCMCPVal + SimplePersistentPVal2
end

lang TreeInferenceTreeSelectJoin = SimpleResample
  sem run = | st ->
    let pickpair = lam st. lam n.
      match p_pure st (p_uniformDiscrete 0 (subi n 1)) with (st, dist) in
      match p_assume st simpleStore dist with (st, i) in
      match p_pure st (p_uniformDiscrete 0 (subi n 2)) with (st, dist) in
      match p_assume st simpleStore dist with (st, j) in
      let f = lam i. lam j. if lti j i then (j,i) else (i, addi j 1) in
      match p_map st f i with (st, tmp) in
      p_apply st tmp j in

    match p_pure st (p_gaussian 0.0 10.0) with (st, dist) in
    match p_assume st simpleStore dist with (st, rootValue) in
    let deviateFromDist = lam x. p_gaussian x 10.0 in
    match p_map st deviateFromDist rootValue with (st, rootDist) in

    recursive let cluster = lam st. lam trees.
      match trees with [tree] then (st, tree) else
      match pickpair st (length trees) with (st, pair) in
      match p_assume st simpleStore rootDist with (st, here) in
      let mkCarryOn = lam idx. lam st.
        match splitAt trees idx with (_, [idx0, idx1, idx2] ++ _) in
        let f = lam trip. lam pair.
          match trip with (idx0, idx1, idx2) in
          match if lti pair.0 pair.1 then (pair.0, pair.1) else (pair.1, pair.0)
          with (l, r) in
          if leqi l idx then
            if leqi r (addi idx 1)
            then idx2
            else idx1
          else idx0
        in
        match p_map st (f (idx0, idx1, idx2)) pair with (st, pair) in
        p_join st pair in
      match mapAccumL (lam st. lam f. f st) st (create (subi (length trees) 2) mkCarryOn) with (st, carryOns) in
      let f = lam trees. lam pair. get trees pair.0 in
      match p_map st (f trees) pair with (st, l) in
      match p_join st l with (st, l) in
      let f = lam trees. lam pair. get trees pair.1 in
      match p_map st (f trees) pair with (st, r) in
      match p_join st r with (st, r) in
      let f = lam rootDist. lam here. lam t. addf
        (negf (p_logObserve rootDist (getX t)))
        (p_logObserve (deviateFromDist here) (getX t)) in
      match p_map st f rootDist with (st, tmp) in
      match p_apply st tmp here with (st, tmp) in
      match p_apply st tmp l with (st, lWeight) in
      let st = p_weight_ st (lam x. x) lWeight in
      match p_apply st tmp r with (st, rWeight) in
      let st = p_weight_ st (lam x. x) rWeight in
      let f = lam here. lam l. lam r.
        mkNode here l r in
      match p_map st f here with (st, tmp) in
      match p_apply st tmp l with (st, tmp) in
      match p_apply st tmp r with (st, merged) in
      cluster st (snoc carryOns merged)
    in

    let f = lam rootDist.
      foldl addf 0.0 (map (lam t. p_logObserve rootDist (getX t)) initTrees) in
    let st = p_weight_ st f rootDist in
    match mapAccumL p_pure st initTrees with (st, initTrees) in
    match cluster st initTrees with (st, tree) in
    p_export st simpleExport tree
end

lang RunTreeInferenceTreeSelectJoinMut = TreeInferenceTreeSelectJoin + MCMCPVal + MutPValExp
end

lang RunTreeInferenceTreeSelectJoinMut2 = TreeInferenceTreeSelectJoin + MCMCPVal + MutPValExp2
end

lang RunTreeInferenceTreeSelectJoinMut3 = TreeInferenceTreeSelectJoin + MCMCPVal + MutPValExp3
end

lang RunTreeInferenceTreeSelectJoinPersistent2 = TreeInferenceTreeSelectJoin + MCMCPVal + SimplePersistentPVal2
end

let result =
  printLn "\n=== tree_inference ===";
  let globalProb = 0.1 in
  let iterations = 100000 in
  let toString = lam x. x in
  let mkHisto = lam x. histogram cmpString (map asShape x) in
  let summarizePVal = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto res)) else () in
  let summarizeBaseline = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto (distEmpiricalSamples res).0)) else () in
  let run =
    use RunTreeInferenceTreeBindMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut tree bind" (timeF run);
  let run =
    use RunTreeInferenceTreeBindDebug in
    let instance = instantiate #frozen"run" ([], ()) in
    writeFile "build/tree-bind.json" (json2string (graphToJson instance));
    lam. [] in
  summarizePVal "pval mcmc mut tree bind json" (timeF run);
  let run =
    use RunTreeInferenceTreeSelectMut in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut tree select" (timeF run);
  let run =
    use RunTreeInferenceTreeBindMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut2 tree bind" (timeF run);
  let run =
    use RunTreeInferenceTreeSelectMut2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut2 tree select" (timeF run);
  let run =
    use RunTreeInferenceTreeBindMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 tree bind" (timeF run);
  let run =
    use RunTreeInferenceTreeSelectMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 tree select" (timeF run);
  let run =
    use RunTreeInferenceTreeSelectJoinMut3 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut3 tree selectJoin" (timeF run);
  let run =
    use RunTreeInferenceTreeBindPersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam.
      let samples = (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
      samples in
  summarizePVal "pval mcmc Persistent2 tree bind" (timeF run);
  let run =
    use RunTreeInferenceTreeSelectPersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent2 tree select" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "none", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw partial" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "full", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline in
  summarizeBaseline "mcmc-lw full" (timeF run);
  let run = lam.
    infer (SimplePValGraph {run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline in
  summarizeBaseline "simple-pval-graph" (timeF run);
  let run = lam.
    infer (SimplePValGraph {debugOutput = "build/baseline-simple.json", run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline in
  summarizeBaseline "simple-pval-graph json" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "none", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline2 in
  summarizeBaseline "baseline2 mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline2 in
  summarizeBaseline "baseline2 mcmc-lw partial" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "full", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline2 in
  summarizeBaseline "baseline2 mcmc-lw full" (timeF run);
  let run = lam.
    infer (SimplePValGraph {run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline2 in
  summarizeBaseline "baseline2 simple-pval-graph" (timeF run);
  let run = lam.
    infer (SimplePValGraph {debugOutput = "build/baseline2-simple.json", run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline2 in
  summarizeBaseline "baseline2 simple-pval-graph json" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "none", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline3 in
  summarizeBaseline "baseline3 mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline3 in
  summarizeBaseline "baseline3 mcmc-lw partial" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "full", resampleBehavior = resampleBehavior globalProb, continue = continue iterations}) baseline3 in
  summarizeBaseline "baseline3 mcmc-lw full" (timeF run);
  let run = lam.
    infer (SimplePValGraph {run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline3 in
  summarizeBaseline "baseline3 simple-pval-graph" (timeF run);
  let run = lam.
    infer (SimplePValGraph {debugOutput = "build/baseline3-simple.json", run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline3 in
  summarizeBaseline "baseline3 simple-pval-graph json" (timeF run);
  ()

mexpr
-- TODO(vipa, 2025-09-25): For whatever reason we end up with a Decl
-- without an info field if we have `infer` above but not here. I have
-- no idea why.
let x = infer (Default ()) (lam. ()) in
printLn "\n\nDone";
()
