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

-- === TODO ===

if true then (1, 2.0) else (2, assume (Gaussian 0.0 1.0))
