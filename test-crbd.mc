include "math.mc"

type Tree
con Node: {left: Tree, right: Tree, age: Float} -> Tree
con Leaf: {age: Float} -> Tree

recursive let logFactorial = lam n.
  if eqi n 1 then 0. else addf (log (int2float n)) (logFactorial (subi n 1))
end

recursive let countLeaves = lam tree.
  match tree with Node r then addi (countLeaves r.left) (countLeaves r.right) else 1
end

let getAge = lam n. match n with Node r then r.age else match n with Leaf r then r.age else never

let crbd: Tree -> Float -> Float = lam tree. lam rho.

  -- Priors
  let lambda = assume (Gamma 1.0 1.0) in
  let mu = assume (Gamma 1.0 0.5) in

  recursive let survives = lam tBeg.
    let t = subf tBeg (assume (Exponential (addf lambda mu))) in
    if ltf t 0. then  -- 8 unaligned (2)
      assume (Bernoulli rho)
    else
      if assume (Bernoulli (divf lambda (addf lambda mu))) then -- 8 unaligned (3)
        if survives t then  -- 4 unaligned, 4 aligned (1)
          true
        else
          survives t
      else
        false
  in

  recursive let simHiddenSpeciation = lam nodeAge. lam tBeg.
    let t = subf tBeg (assume (Exponential lambda)) in
    if gtf t nodeAge then  -- 12 unaligned (4)
      if survives t then  -- 12 unaligned (5)
        -- NOTE: We bind weights and observes to wX (where X is an integer)
        -- just for identification purposes when testing the alignment
        -- analysis.
        let w1 = weight (negf inf) in
        w1
      else
        let w2 = weight (log 2.) in
        simHiddenSpeciation nodeAge t
    else ()
  in

  recursive let walk = lam node. lam parentAge.
    let nodeAge = getAge node in
    simHiddenSpeciation nodeAge parentAge;
    let w3 = observe 0 (Poisson (mulf mu (subf parentAge nodeAge))) in
    match node with Node n then
      let w4 = observe 0. (Exponential lambda) in
      walk n.left nodeAge;
      walk n.right nodeAge
    else match node with Leaf _ then
      let w5 = observe true (Bernoulli rho) in
      w5
    else never
  in

  let numLeaves = countLeaves tree in
  weight (subf (mulf (subf (int2float numLeaves) 1.) (log 2.)) (logFactorial numLeaves));
  match tree with Node root in
  walk root.left root.age;
  walk root.right root.age;
  lambda

-- alcedinidae
let tree = Node {left = Node {left = Node {left = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 5.635787971}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 4.788021775}, age = 7.595901077}, age = 9.436625313}, age = 12.344087935000001}, right = Node {left = Node {left = Leaf {age = 0.0}, right = Node {left = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 3.934203877}, right = Node {left = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 3.151799953}, right = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 5.054547857}, age = 6.284896356999999}, age = 7.815689970999999}, age = 10.32243059}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 1.519406055}, age = 4.987038163}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 0.6302632958}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 1.962579854}, age = 3.732932004}, age = 5.5933070698}, age = 6.096453021}, age = 8.265483252}, age = 10.86835485}, age = 12.551924091}, age = 13.472886809}, right = Node {left = Node {left = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 4.534421013}, age = 12.46869821}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 6.306427821}, age = 9.40050129}, age = 13.85876825}, age = 20.68766993}, age = 22.82622451}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 4.220057646}, age = 8.451051062}, age = 11.54072627}, age = 15.28839572}, right = Node {left = Node {left = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 8.614086751}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 0.9841688636}, right = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 1.04896206}, age = 1.7140599232}, age = 3.786162534}, age = 8.788450495}, age = 11.05846217}, age = 15.008504768}, right = Node {left = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 11.15685875}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 1.900561313}, age = 3.100150132}, age = 6.043650727}, age = 12.38252513}, age = 12.61785812}, age = 15.396725736}, age = 16.828404506}, age = 20.368109703000002}, age = 23.74299959}, age = 32.145876657}, age = 34.940139089}
let rho = 0.5684210526315789

-- synthetic
-- let rho = 1.0
-- let tree = Node {left = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 4.862406452197589}, right = Node {left = Node {left = Node {left = Leaf {age = 0.0}, right = Leaf {age = 0.0}, age = 0.302169162393619}, right = Leaf {age = 0.0}, age = 1.2350618429801936}, right = Leaf {age = 0.0}, age = 2.0866037802290065}, age = 5.0}

mexpr
crbd tree rho
