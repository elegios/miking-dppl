include "set.mc"

let timeF : all a. (() -> a) -> (Float, a)
  = lam f.
    let before = wallTimeMs () in
    let res = f () in
    let after = wallTimeMs () in
    (subf after before, res)

let showHistogram : Bool = false
let histogram : all a. (a -> a -> Int) -> [a] -> [(a, Float)]
  = lam cmp. lam l.
    let hist = foldl (lam acc. lam a. mapInsertWith addi a 1 acc) (mapEmpty cmp) l in
    let count = int2float (mapFoldWithKey (lam total. lam. lam count. addi total count) 0 hist) in
    let hist = mapMap (lam v. divf (int2float v) count) hist in
    mapBindings hist

let progressBarNoPad : Int -> Float -> String
  = lam width. lam fraction.
    let filled = roundfi (mulf (int2float width) fraction) in
    make filled '=' -- (make (subi width filled) ' ')

let hist2string : all a. (a -> String) -> [(a, Float)] -> String
  = lam toStr. lam l.
    strJoin "\n" (map (lam pair. join [toStr pair.0, "\t", float2string pair.1, "\t", progressBarNoPad 100 pair.1]) l)

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
  , Leaf {id = 4, x = 20.0}
  , Leaf {id = 5, x = 25.0}
  , Leaf {id = 6, x = 30.0}
  , Leaf {id = 7, x = 35.0}
  , Leaf {id = 8, x = 40.0}
  , Leaf {id = 9, x = 45.0}
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

mexpr

let globalProb = 0.1 in
let iterations = 100000 in
let toString = lam x. x in
let mkHisto = lam x. histogram cmpString (map asShape x) in

let summarizeBaseline = lam label. lam pair.
  match pair with (time, res) in
  printLn (join [float2string time, "ms (", label, ")"]);
  if showHistogram then printLn (hist2string toString (mkHisto (distEmpiricalSamples res).0)) else () in

let run = lam.
  infer (SimplePValGraph {experiment = 1, run = simplePValGraphMCMC {globalProb = globalProb, iterations = iterations}}) baseline2 in
summarizeBaseline "baseline2 simple-pval-graph experiment" (timeF run);

()
