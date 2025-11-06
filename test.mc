mexpr
-- assume (Gaussian 0.0 1.0)

-- let x = 0.0 in
-- assume (Gaussian x 1.0)

-- let x = assume (Gaussian 0.0 1.0) in
-- assume (Gaussian x 1.0)

-- addf (assume (Gaussian 0.0 1.0)) (assume (Gaussian 1.0 1.0))

-- addf (addf (assume (Gaussian 0.0 1.0)) (assume (Gaussian 1.0 1.0))) 2.0

-- let f = lam a. addf a 1.0 in
-- f 1.0

-- let f = lam a. addf a 1.0 in
-- addf (f 1.0) (f (assume (Gaussian 0.0 1.0)))

-- let f = lam a. assume (Gaussian a 1.0) in
-- let g = lam a. f a in
-- addf (g 1.0) (g (assume (Gaussian 0.0 1.0)))

-- recursive let sum : Float -> Float = lam x. sum (assume (Gaussian x 1.0)) in
-- sum 1.0

-- recursive
--   let odd : Float -> Bool = lam x. even (assume (Gaussian x 1.0))
--   let even = lam x. odd x
-- in even 1.0

-- [1.0, 2.0]

-- [1.0, assume (Gaussian 0.0 1.0)]

-- if true then 1 else 2

-- if true then assume (Gaussian 0.0 1.0) else 42.0

-- match (assume (Gaussian 0.0 1.0), 2.0) with (a, b) in addf a b

-- if assume (Bernoulli 0.5) then false else true

-- if assume (Bernoulli 0.5) then assume (Bernoulli 0.9) else false

-- if true then (1, 2.0) else (2, assume (Gaussian 0.0 1.0))

-- if assume (Bernoulli 0.5) then [1.0, 2.0] else [assume (Gaussian 0.0 1.0)]

-- if true then [1., 2.] else [assume (Gaussian 0.0 1.0)]

-- type Either a b in
-- con Left : all a. all b. a -> Either a b in
-- con Right : all a. all b. b -> Either a b in
-- if true then Left 1 else Right 2.0

-- type Either a b in
-- con Left : all a. all b. a -> Either a b in
-- con Right : all a. all b. b -> Either a b in
-- if true then Left 1.0 else let x = assume (Gaussian 1.0 0.0) in Left x

-- type Either a b in
-- con Left : all a. all b. a -> Either a b in
-- con Right : all a. all b. b -> Either a b in
-- if true then Left 1.0 else if assume (Bernoulli 0.5) then Left 2.0 else Left 3.0

-- type Either a b in
-- con Left : all a. all b. a -> Either a b in
-- con Right : all a. all b. b -> Either a b in
-- if true then
--   let x = assume (Gaussian 1.0 0.0) in
--   Left x
-- else
--   if assume (Bernoulli 0.5) then Left 2.0 else Left 3.0

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- Node {x = 1.0, left = Leaf {x = 2.0}, right = Leaf {x = 3.0}}

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- let x = assume (Gaussian 0.0 1.0) in
-- Node {x = 1.0, left = Leaf {x = x}, right = Leaf {x = 3.0}}

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- let x = assume (Gaussian 0.0 1.0) in
-- let l = if assume (Bernoulli 0.5) then Leaf {x = x} else Leaf {x = 2.0} in
-- Node {x = 1.0, left = l, right = Leaf {x = 3.0}}

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- let merge = lam l. lam r.
--   let x = assume (Gaussian 0.0 1.0) in
--   Node {x = x, left = l, right = r} in
-- merge (merge (Leaf {x = 1.0}) (Leaf {x = 2.0})) (Leaf {x = 3.0})

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- if assume (Bernoulli 0.5)
-- then let x = assume (Gaussian 0.0 1.0) in Node {x = x, left = Leaf {x = 1.0}, right = Leaf {x = 2.0}}
-- else Leaf {x = 1.0}

-- This is manually written to use shallow patterns
type List a in
con Nil : all a. () -> List a in
con Cons : all a. (a, List a) -> List a in
type Tree in
con Leaf : {x : Float} -> Tree in
con Node : {x : Float, left : Tree, right : Tree} -> Tree in
recursive let cluster = lam trees.
  match trees with Cons tmp in
  match tmp with (tree, rest) in
  match rest with Cons tmp then
    match tmp with (r, trees) in
    let newX = assume (Gaussian 0.0 1.0) in
    cluster (Cons (Node {x = newX, left = tree, right = r}, trees))
  else tree in
cluster (Cons (Leaf {x = 0.0}, Cons (Leaf {x = 1.0}, Cons (Leaf {x = 2.0}, Nil ()))));
()

---- TODO ----
-- * Figure out why the manual shallow example drops a let binding (probably something about a specialization request being removed when it's passed in one instance)
-- * Ensure `lowerAll` preserves enough types.
-- * Ensure we handle polymorphic constants properly:
--   * See if there's wrappedness that can't be swallowed by polymorphism
--   * Find all occurrences of each type variable in the inputs, `lub` them
--   * Reconstruct arguments _and return_ with new versions of type variables
--   * If unswallowed wrappedness, `ensureWrapped` on all arguments and return, `pure` on const, `apply` arguments
--   * Otherwise normal app

-- -- This is written with nested patterns
-- type List a in
-- con Nil : all a. () -> List a in
-- con Cons : all a. (a, List a) -> List a in
-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- recursive let cluster = lam trees.
--   match trees with Cons (tree, Nil ()) then tree else
--   match trees with Cons (l, Cons (r, trees)) in
--   let newX = assume (Gaussian 0.0 1.0) in
--   cluster (Cons (Node {x = newX, left = l, right = r}, trees)) in
-- cluster (Cons (Leaf {x = 0.0}, Cons (Leaf {x = 1.0}, Cons (Leaf {x = 2.0}, Nil ()))));
-- ()

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- recursive let cluster = lam trees.
--   match trees with [tree] then tree else
--   match trees with [l, r] ++ trees in
--   let newX = assume (Gaussian 0.0 1.0) in
--   cluster (cons (Node {x = newX, left = l, right = r}) trees) in
-- cluster [Leaf {x = 0.0}, Leaf {x = 1.0}, Leaf {x = 2.0}]
