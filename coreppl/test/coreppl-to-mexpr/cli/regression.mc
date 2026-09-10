include "../../test.mc"

include "seq.mc"
include "sys.mc"
include "string.mc"
include "common.mc"
include "stats.mc"

mexpr

let s = 0.3 in
let e = eqRegression s s in
let rhs = regressionTruth in
let r = resRegression in
-- NOTE: The importance/SMC configurations below ran 1000 particles, which is
-- far too few for this model: sampling k,m from N(0,5) priors gives an
-- effective sample size of 1-10, so the weighted mean of m had a
-- seed-to-seed sd of ~0.35 against the 0.3 tolerance -- a coin flip that
-- owl's stream happened to win and the replacement's happened to lose. The
-- estimator itself is unbiased (mean of m over ten seeds: 0.609 at 1000
-- particles, 0.6125 at 10000, against a truth of 0.621), so the fix is
-- particles, not tolerance. At 100000 a run still takes well under a second.
let t = testCpplMExpr "regression.mc" in

utest r (t 100000 0 "-m is-lw --cps none"                                              ) with rhs using e in
utest r (t 100000 0 "-m is-lw --cps partial"                                           ) with rhs using e in
utest r (t 100000 0 "-m is-lw --cps partial --no-early-stop"                           ) with rhs using e in
utest r (t 100000 0 "-m is-lw --cps full"                                              ) with rhs using e in
utest r (t 100000 0 "-m is-lw --cps full --no-early-stop"                              ) with rhs using e in
-- utest r (t 100000 0 "-m smc-bpf --cps partial --resample manual"                       ) with rhs using e in
utest r (t 100000 0 "-m smc-bpf --cps partial --resample align"                        ) with rhs using e in
utest r (t 100000 0 "-m smc-bpf --cps partial --resample likelihood"                   ) with rhs using e in
-- utest r (t 100000 0 "-m smc-bpf --cps full --resample manual"                          ) with rhs using e in
utest r (t 100000 0 "-m smc-bpf --cps full --resample align"                           ) with rhs using e in
utest r (t 100000 0 "-m smc-bpf --cps full --resample likelihood"                      ) with rhs using e in
-- utest r (t 100000 0 "-m smc-apf --cps partial --resample manual"                       ) with rhs using e in
utest r (t 100000 0 "-m smc-apf --cps partial --resample align"                        ) with rhs using e in
utest r (t 100000 0 "-m smc-apf --cps partial --resample likelihood"                   ) with rhs using e in
-- utest r (t 100000 0 "-m smc-apf --cps full --resample manual"                          ) with rhs using e in
utest r (t 100000 0 "-m smc-apf --cps full --resample align"                           ) with rhs using e in
utest r (t 100000 0 "-m smc-apf --cps full --resample likelihood"                      ) with rhs using e in
-- NOTE: 1000 iterations gave m an sd of 0.58 against the 0.3 tolerance. At
-- 100000/10000 the chain reaches m = 0.6013 (sd 0.047) against a truth of
-- 0.621, i.e. ~6 sd of headroom, for about half a second.
utest r (t 100000 10000 "-m pmcmc-pimh"                                               ) with rhs using e in
utest r (t 10000 1000 "-m mcmc-trace"                                                 ) with rhs using e in
utest r (t 10000 1000 "-m mcmc-naive"                                                 ) with rhs using e in
utest r (t 10000 1000 "-m mcmc-lightweight"                                           ) with rhs using e in
utest r (t 10000 1000 "-m mcmc-lightweight --align --cps partial --mcmc-lw-gprob 0.1" ) with rhs using e in
-- NOTE: as above -- 10000 iterations gave sd 0.22; 200000/20000 gives
-- m = 0.5942 (sd 0.033). The other mcmc configurations on this model pass at
-- 10000 but are fragile for the same reason, and are left alone here.
utest r (t 200000 20000 "-m mcmc-lightweight --align --cps none --mcmc-lw-gprob 0.1" ) with rhs using e in

()
