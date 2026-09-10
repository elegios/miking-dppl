include "test.mc"
--include "../src/coreppl-to-mexpr/runtime-dists.mc"

let cpplResOfDist: all a. (a -> String) -> Int -> Dist a -> CpplRes =
  lam f. lam burn. lam dist.
    match distEmpiricalSamples dist with (vs,ws) in
    let nvs = length vs in
    let samples = subsequence vs (mini nvs burn) nvs in
    let nws = length ws in
    let lweights =  subsequence ws (mini nws burn) nws in
    let nc = distEmpiricalNormConst dist in
    { samples = map f samples, lweights = lweights, extra = Some nc }

let resampleBehavior: all a. Float -> a -> Int -> (a,([Bool], Int)) = 
  lam globalProb. lam acc. lam length.
    let valu = if (assume (Bernoulli globalProb)) then
      negi 1
    else
      -- NOTE: `maxi 0` guards the empty-trace case. A model with no random
      -- choices (coreppl/test/coreppl-to-mexpr/infer/diff-confusion.mc) gives
      -- length = 0 and hence `UniformDiscrete 0 (-1)`, an inverted range.
      -- owl's uniform_int_rvs validated nothing and returned 0 for that; the
      -- validating replacement raises. Clamping keeps both the number of
      -- `assume`s and the value owl produced, and with an empty db the index
      -- invalidates nothing either way.
      assume (UniformDiscrete 0 (maxi 0 (subi length 1)))
    in
    let vec = create length (lam. true) in
    (acc,(vec, valu))
