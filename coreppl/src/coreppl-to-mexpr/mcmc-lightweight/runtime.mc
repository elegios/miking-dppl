include "common.mc"

include "ext/dist-ext.mc"
include "ext/math-ext.mc"
include "math.mc"
include "seq.mc"
include "string.mc"
include "option.mc"
include "map.mc"

include "../runtime-common.mc"
include "../runtime-dists.mc"

include "./config.mc"

-- Any-type, used for samples
type Any = ()

-- An address is a list of integers. The first element in the tuple is the
-- length of the list (to speed up addrCmp), and the second element is the list
-- itself.
type Address = (Int, [Int])

-- In lightweight MCMC, the state is the accumulated weight, a map of samples for the current run, and a map of samples from the previous run to potentially reuse.
type State = {

  -- The weight of the current execution
  weight: Ref Float,

  -- The weight of reused values in the current execution
  prevWeightReused: Ref Float,
  weightReused: Ref Float,

  -- The sample database for this execution
  db: Ref (Map Address (Any,Float)),

  -- Number of encountered assumes
  traceLength: Ref Int,

  -- The previous database, with potentially invalidated samples
  oldDb: Ref (Map Address (Option (Any,Float)))

}

let emptyAddress = (0,toList [])

-- Address comparison
let addrCmp : Address -> Address -> Int = lam a1. lam a2.
  recursive let work = lam l1. lam l2.
    match (l1, l2) with ([h1] ++ t1, [h2] ++ t2) then
      let c = subi h1 h2 in
      if eqi c 0 then work t1 t2
      else c
    else match (l1, l2) with ([_] ++ _, []) then
      1
    else match (l1, l2) with ([], [_] ++ _) then
      negi 1
    else
      0
  in
  let n1 = a1.0 in
  let n2 = a2.0 in
  let ndiff = subi n1 n2 in
  let res = if eqi ndiff 0 then
    work a1.1 a2.1
  else ndiff in
  res

-- OPT(dlunde,2023-05-25): Wrap in lambda due to value restriction. Possible
-- that the type checker can handle this in the future though.
let emptyAddressMap = lam. mapEmpty addrCmp

let constructAddress: Address -> Int -> Address = lam prev. lam sym.
  (addi prev.0 1, cons sym prev.1)

-- State (reused throughout inference)
let state: State = {
  weight = ref 0.,
  prevWeightReused = ref 0.,
  weightReused = ref 0.,
  db = ref (emptyAddressMap ()),
  traceLength = ref 0,
  oldDb = ref (emptyAddressMap ())
}

let updateWeight = lam v.
  modref state.weight (addf (deref state.weight) v)

let incrTraceLength: () -> () = lam.
  modref state.traceLength (addi (deref state.traceLength) 1)

-- Procedure at samples
let sample: all a. Address -> use RuntimeDistBase in Dist a -> a = lam addr. lam dist.
  use RuntimeDist in
  let oldDb: Map Address (Option (Any,Float)) = deref state.oldDb in
  let newSample: () -> (Any,Float) = lam.
    let s = sample dist in
    let w = logObserve dist s in
    (unsafeCoerce s, w)
  in
  let sample: (Any,Float) =
    match mapLookup addr oldDb with Some (Some (sample,w)) then
      let s: a = unsafeCoerce sample in
      let wNew = logObserve dist s in
      modref state.weightReused (addf (deref state.weightReused) wNew);
      modref state.prevWeightReused (addf (deref state.prevWeightReused) w);
      (sample, wNew)
    else
      newSample ()
  in
  incrTraceLength ();
  modref state.db (mapInsert addr sample (deref state.db));
  unsafeCoerce (sample.0)

-- Function to propose db changes between MH iterations.
let modDb: all acc. all dAcc. all res. Config res acc dAcc -> () = lam config.

  let db = deref state.db in

  -- Enable global modifications with probability gProb
  let gProb = config.globalProb in
  let modGlobal: Bool = bernoulliSample gProb in

  if modGlobal then
    -- modref state.oldDb (mapMap (lam. None ()) db)
    modref state.oldDb (emptyAddressMap ())
  else
    -- One item in the db (chosen at random) must always change
    let invalidIndex: Int = uniformDiscreteSample 0 (subi (deref state.traceLength) 1) in
    let currentIndex: Ref Int = ref 0 in
    modref state.oldDb
      (mapMap (lam sample: (Any,Float).
         -- Invalidate sample if it has the invalid index
         let sample = if eqi invalidIndex (deref currentIndex) then
                        None ()
                      else Some sample in
         modref currentIndex (addi (deref currentIndex) 1);
         sample
      ) db)

let run : all acc. all dAcc. all a. Config a acc dAcc -> (State -> a) -> use RuntimeDistBase in Dist a =
  lam config. lam model.

  recursive let mh : [a] -> Float -> a -> dAcc -> (acc, Bool) -> Int -> [a] =
    lam samples. lam prevWeight. lam prevSample. lam debugState. lam continueState. lam iter.
      match continueState with (continueState, true) then
        let prevDb = deref state.db in
        let prevTraceLength = deref state.traceLength in
        modDb config;
        modref state.weight 0.;
        modref state.weightReused 0.;
        modref state.prevWeightReused 0.;
        modref state.db (emptyAddressMap ());
        modref state.traceLength 0;
        let sample = model state in
        let traceLength = deref state.traceLength in
        let weight = deref state.weight in
        let weightReused = deref state.weightReused in
        let prevWeightReused = deref state.prevWeightReused in
        let logMhAcceptProb =
          minf 0. (addf (addf
                    (subf weight prevWeight)
                    (subf weightReused prevWeightReused))
                    (subf (log (int2float prevTraceLength))
                              (log (int2float traceLength))))
        in
        -- print "logMhAcceptProb: "; printLn (float2string logMhAcceptProb);
        -- print "weight: "; printLn (float2string weight);
        -- print "prevWeight: "; printLn (float2string prevWeight);
        -- print "weightReused: "; printLn (float2string weightReused);
        -- print "prevWeightReused: "; printLn (float2string prevWeightReused);
        -- print "prevTraceLength: "; printLn (float2string (int2float prevTraceLength));
        -- print "traceLength: "; printLn (float2string (int2float traceLength));
        match
          if bernoulliSample (exp logMhAcceptProb) then
            mcmcAccept ();
            (true, weight, sample)
          else
          -- NOTE(dlunde,2022-10-06): VERY IMPORTANT: Restore previous database
          -- and trace length as we reject and reuse the old sample.
            modref state.db prevDb;
            modref state.traceLength prevTraceLength;
            (false, prevWeight, prevSample)
        with (accepted, weight, sample) in
        let samples = if config.keepSample iter then snoc samples sample else samples in
        let debugInfo =
          { accepted = accepted
          } in
        mh samples weight sample (config.debug.1 debugState debugInfo) (config.continue.1 continueState sample) (addi iter 1)
      else samples
  in

  -- Used to keep track of acceptance ratio
  mcmcAcceptInit ();

  -- First sample
  let sample = model state in
  let weight = deref state.weight in

  let iter = 0 in
  let samples = if config.keepSample iter then [sample] else [] in

  let debugInfo =
    { accepted = true
    } in

  -- Sample the rest
  let samples = mh samples weight sample (config.debug.1 config.debug.0 debugInfo) (config.continue.1 config.continue.0 sample) (addi iter 1) in

  -- Return
  let numSamples = length samples in
  use RuntimeDist in
  constructDistEmpirical samples (make numSamples 1.)
    (EmpMCMC { acceptRate = mcmcAcceptRate numSamples })
