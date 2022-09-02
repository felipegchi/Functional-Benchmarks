{-# OPTIONS --type-in-type #-}

module Base where

-- Types
-- =====

-- Equality
-- --------

data Equal {t : Set} (a : t) : (b : t) -> Set where
  refl : Equal {t} a a

-- Boolean
-- -------

data Bool : Set where
  true : Bool
  false : Bool

-- Natural Number
-- --------------

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

-- Binary Tree
-- -----------

data Tree : Set where
  leaf : Tree
  node : Tree -> Tree -> Tree

-- Vector
-- ------

data Vector : (t : Set) (len : Nat) -> Set where
  cons : {t : Set} -> {len : Nat} -> (head : t) -> (tail : Vector t len) -> Vector t (succ len)
  nil : {t : Set} -> Vector t zero

-- Church Boolean
-- --------------

Church-Bool : Set
Church-Bool = (p : Set) -> (t : p) -> (f : p) -> p

Church-true : Church-Bool
Church-true = λ p t f -> t

Church-false : Church-Bool
Church-false = λ p t f -> f

-- Church Natural Number
-- ---------------------

Church-Nat : Set
Church-Nat = (p : Set) -> (f : p -> p) -> (z : p) -> p

Church-zero : Church-Nat
Church-zero = λ p f z -> z

Church-succ : (n : Church-Nat) -> Church-Nat
Church-succ n = λ p f z -> f (n p f z)

-- Church Tree
-- -----------

Church-Tree : Set
Church-Tree = (p : Set) -> (n : p -> p -> p) -> (l : p) -> p

Church-leaf : Church-Tree
Church-leaf = λ p n l -> l

Church-node : Church-Tree -> Church-Tree -> Church-Tree
Church-node a b = λ p n l -> n (a p n l) (b p n l)

-- Church Vector
-- -------------

Church-Vector : (t : Set) -> (len : Church-Nat) -> Set
Church-Vector t n = (p : Church-Nat -> Set) -> (cons : (len : Church-Nat) -> (head : t) -> (tail : p len) -> p (Church-succ len)) -> (nil : p Church-zero) -> p n

Church-nil : {t : Set} -> (p : Church-Nat -> Set) -> (cons : (len : Church-Nat) -> (head : t) -> (tail : p len) -> p (Church-succ len)) -> (nil : p Church-zero) -> p Church-zero
Church-nil {t} = λ p cons nil -> nil

Church-cons : {t : Set} -> {len : Church-Nat} -> (head : t) -> (tail : Church-Vector t len) -> Church-Vector t (Church-succ len)
Church-cons {t} {len} head tail = λ p cons nil -> cons len head (tail p cons nil)

-- Functions
-- ---------

not : Bool -> Bool
not true  = false
not false = true

and : Bool -> Bool -> Bool
and false false = false
and false true  = false
and true  false = false
and true  true  = true

add : Nat -> Nat -> Nat
add a zero     = a
add a (succ b) = succ (add a b)

mul : Nat -> Nat -> Nat
mul a zero     = zero
mul a (succ b) = add a (mul a b)

exp : Nat -> Nat -> Nat
exp a zero     = succ zero
exp a (succ b) = mul a (exp a b)

is-even : Nat -> Bool
is-even zero     = true
is-even (succ a) = not (is-even a)

full-tree : Nat -> Tree
full-tree zero     = leaf
full-tree (succ d) = let branch = full-tree d in node branch branch

tree-fold : Tree -> (p : Set) -> (n : p -> p -> p) -> (l : p) -> p
tree-fold leaf       p n l = l
tree-fold (node a b) p n l = n (tree-fold a p n l) (tree-fold b p n l)

force-tree : Tree -> Bool
force-tree t = tree-fold t Bool (λ a b -> and a b) true

Church-not : Church-Bool -> Church-Bool
Church-not b = λ p t f -> b p f t

Church-and : Church-Bool -> Church-Bool -> Church-Bool
Church-and a b = λ p t f -> a p (b p t f) f

Church-add : Church-Nat -> Church-Nat -> Church-Nat
Church-add a b = λ p f z -> a p f (b p f z)

Church-mul : Church-Nat -> Church-Nat -> Church-Nat
Church-mul a b = λ p f -> a p (b p f)

Church-exp : Church-Nat -> Church-Nat -> Church-Nat
Church-exp a b = λ p -> b (p -> p) (a p)

Church-is-even : Church-Nat -> Church-Bool
Church-is-even a = a Church-Bool (λ x -> Church-not x) Church-true

Church-full-tree : Church-Nat -> Church-Tree
Church-full-tree k = λ p n l -> k p (λ t -> n t t) l

Church-tree-fold : Church-Tree -> (p : Set) (n : p -> p -> p) (l : p) -> p
Church-tree-fold t p n l = t p n l

Church-force-tree : Church-Tree -> Church-Bool
Church-force-tree t = Church-tree-fold t Church-Bool (λ a b -> Church-and a b) Church-true

-- Constants
-- ---------

N0  : Nat; N0  = zero
N1  : Nat; N1  = succ N0
N2  : Nat; N2  = succ N1
N3  : Nat; N3  = succ N2
N4  : Nat; N4  = succ N3
N5  : Nat; N5  = succ N4
N6  : Nat; N6  = succ N5
N7  : Nat; N7  = succ N6
N8  : Nat; N8  = succ N7
N9  : Nat; N9  = succ N8
N10 : Nat; N10 = succ N9
N11 : Nat; N11 = succ N10
N12 : Nat; N12 = succ N11
N13 : Nat; N13 = succ N12
N14 : Nat; N14 = succ N13
N15 : Nat; N15 = succ N14
N16 : Nat; N16 = succ N15
N17 : Nat; N17 = succ N16
N18 : Nat; N18 = succ N17
N19 : Nat; N19 = succ N18
N20 : Nat; N20 = succ N19
N21 : Nat; N21 = succ N20
N22 : Nat; N22 = succ N21
N23 : Nat; N23 = succ N22
N24 : Nat; N24 = succ N23
N25 : Nat; N25 = succ N24
N26 : Nat; N26 = succ N25
N27 : Nat; N27 = succ N26
N28 : Nat; N28 = succ N27
N29 : Nat; N29 = succ N28
N30 : Nat; N30 = succ N29
N31 : Nat; N31 = succ N30
N32 : Nat; N32 = succ N31

Church-N0  : Church-Nat; Church-N0  = Church-zero
Church-N1  : Church-Nat; Church-N1  = Church-succ Church-N0
Church-N2  : Church-Nat; Church-N2  = Church-succ Church-N1
Church-N3  : Church-Nat; Church-N3  = Church-succ Church-N2
Church-N4  : Church-Nat; Church-N4  = Church-succ Church-N3
Church-N5  : Church-Nat; Church-N5  = Church-succ Church-N4
Church-N6  : Church-Nat; Church-N6  = Church-succ Church-N5
Church-N7  : Church-Nat; Church-N7  = Church-succ Church-N6
Church-N8  : Church-Nat; Church-N8  = Church-succ Church-N7
Church-N9  : Church-Nat; Church-N9  = Church-succ Church-N8
Church-N10 : Church-Nat; Church-N10 = Church-succ Church-N9
Church-N11 : Church-Nat; Church-N11 = Church-succ Church-N10
Church-N12 : Church-Nat; Church-N12 = Church-succ Church-N11
Church-N13 : Church-Nat; Church-N13 = Church-succ Church-N12
Church-N14 : Church-Nat; Church-N14 = Church-succ Church-N13
Church-N15 : Church-Nat; Church-N15 = Church-succ Church-N14
Church-N16 : Church-Nat; Church-N16 = Church-succ Church-N15
Church-N17 : Church-Nat; Church-N17 = Church-succ Church-N16
Church-N18 : Church-Nat; Church-N18 = Church-succ Church-N17
Church-N19 : Church-Nat; Church-N19 = Church-succ Church-N18
Church-N20 : Church-Nat; Church-N20 = Church-succ Church-N19
Church-N21 : Church-Nat; Church-N21 = Church-succ Church-N20
Church-N22 : Church-Nat; Church-N22 = Church-succ Church-N21
Church-N23 : Church-Nat; Church-N23 = Church-succ Church-N22
Church-N24 : Church-Nat; Church-N24 = Church-succ Church-N23
Church-N25 : Church-Nat; Church-N25 = Church-succ Church-N24
Church-N26 : Church-Nat; Church-N26 = Church-succ Church-N25
Church-N27 : Church-Nat; Church-N27 = Church-succ Church-N26
Church-N28 : Church-Nat; Church-N28 = Church-succ Church-N27
Church-N29 : Church-Nat; Church-N29 = Church-succ Church-N28
Church-N30 : Church-Nat; Church-N30 = Church-succ Church-N29
Church-N31 : Church-Nat; Church-N31 = Church-succ Church-N30
Church-N32 : Church-Nat; Church-N32 = Church-succ Church-N31
