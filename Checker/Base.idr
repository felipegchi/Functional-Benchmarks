module Base

public export
data Equal : {t: Type} -> (a: t) -> (b: t) -> Type where
  Refl : Equal a a

public export
data Bool = True | False

public export
data Nat = Zero | Suc Base.Nat

public export
data Tree = Leaf | Node Tree Tree

public export
data Vector : (t: Type) -> (len: Base.Nat) -> Type where
  Cons : (head: t) -> (tail: Vector t len) -> Vector t (Suc len)
  Nil : Vector t Zero

-- Church Boolean
-- --------------

public export
Church_Bool : Type
Church_Bool = (p : Type) -> (t: p) -> (f: p) -> p

public export
church_true : Church_Bool
church_true = \p => \t => \f => t

public export
church_false : Church_Bool
church_false = \p => \t => \f => f

-- Church Natural Number
-- ---------------------

public export
Church_Nat : Type
Church_Nat = (p : Type) -> (t: p -> p) -> (f: p) -> p

public export
church_zero : Church_Nat
church_zero = \p => \s => \z => z

public export
church_succ : Church_Nat -> Church_Nat
church_succ n = \p => \s => \z => s (n p s z)

-- Church Tree
-- -----------

public export
Church_Tree : Type
Church_Tree = (p : Type) -> (t: p -> p -> p) -> (f: p) -> p

public export
church_leaf : Church_Tree
church_leaf = \p => \n => \l => l

public export
church_node : Church_Tree -> Church_Tree -> Church_Tree
church_node a b = \p => \n => \l => n (a p n l) (b p n l)

-- Church Vector
-- -------------

public export
Church_Vector : (t: Type) -> (l: Church_Nat) -> Type
Church_Vector t n =
  (p : Church_Nat -> Type)
    -> (cons: (len: Church_Nat) -> (head: t) -> (tail: p len) -> p (church_succ len))
    -> (nil: p church_zero)
    -> p n

public export
church_nil : (p: Church_Nat -> Type) -> (cons: (len: Church_Nat) -> (head: t) -> (tail: p len) -> p (Base.church_succ len)) -> (nil: p Base.church_zero) -> p Base.church_zero
church_nil p cons nil = nil

public export
church_cons : (len: Church_Nat) -> (head: t) -> (tail: Church_Vector t len) -> Church_Vector t (Base.church_succ len)
church_cons len head tail p cons nil = cons len head (tail p cons nil)

-- Functions
-- ---------

public export
not : Base.Bool -> Base.Bool
not True  = False
not False = True

public export
and : Base.Bool -> Base.Bool -> Base.Bool
and False False = False
and False True  = False
and True False  = False
and True True   = True

public export
add : Base.Nat -> Base.Nat -> Base.Nat
add a Zero    = a
add a (Suc b) = Suc (add a b)

public export
mul : Base.Nat -> Base.Nat -> Base.Nat
mul a Zero    = Zero
mul a (Suc b) = add a (mul a b)

public export
exp : Base.Nat -> Base.Nat -> Base.Nat
exp a Zero    = Suc Zero
exp a (Suc b) = mul a (exp a b)

public export
is_even : Base.Nat -> Base.Bool
is_even Zero    = True
is_even (Suc b) = not (is_even b)

public export
full_tree : Base.Nat -> Base.Tree
full_tree Zero    = Leaf
full_tree (Suc n) = let branch = full_tree n in Node branch branch

public export
tree_fold : Base.Tree -> (p: Type) -> (n: p -> p -> p) -> (l: p) -> p
tree_fold Leaf       p n l = l
tree_fold (Node a b) p n l = n (tree_fold a p n l) (tree_fold b p n l)

public export
force_tree : Base.Tree -> Base.Bool
force_tree t = tree_fold t Base.Bool (\a => \b => and a b) True

public export
church_not : Church_Bool -> Church_Bool
church_not b = \p => \t => \f => b p f t

public export
church_and : Church_Bool -> Church_Bool -> Church_Bool
church_and a b = \p => \t => \f => a p (b p t f) f

public export
church_add : Church_Nat -> Church_Nat -> Church_Nat
church_add a b = \p => \f => \z => a p f (b p f z)

public export
church_mul : Church_Nat -> Church_Nat -> Church_Nat
church_mul a b = \p => \f => a p (b p f)

public export
church_exp : Church_Nat -> Church_Nat -> Church_Nat
church_exp a b = \p => b (p -> p) (a p)

public export
church_is_even : Church_Nat -> Church_Bool
church_is_even a = a Church_Bool (\x => church_not x) church_true

public export
church_full_tree : Church_Nat -> Church_Tree
church_full_tree k = \p => \n => \l => k p (\t => n t t) l

public export
church_tree_fold : Church_Tree -> (p: Type) -> (n: p -> p -> p) -> (l: p) -> p
church_tree_fold t p n l = t p n l

public export
church_force_tree : Church_Tree -> Church_Bool
church_force_tree t = church_tree_fold t Church_Bool (\a => \b => church_and a b) church_true

public export
N0 : Base.Nat
N0 = Zero

public export
N1 : Base.Nat
N1 = Suc N0

public export
N2 : Base.Nat
N2 = Suc N1

public export
N3 : Base.Nat
N3 = Suc N2

public export
N4 : Base.Nat
N4 = Suc N3

public export
N5 : Base.Nat
N5 = Suc N4

public export
N6 : Base.Nat
N6 = Suc N5

public export
N7 : Base.Nat
N7 = Suc N6

public export
N8 : Base.Nat
N8 = Suc N7

public export
N9 : Base.Nat
N9 = Suc N8

public export
N10 : Base.Nat
N10 = Suc N9

public export
N11 : Base.Nat
N11 = Suc N10

public export
N12 : Base.Nat
N12 = Suc N11

public export
N13 : Base.Nat
N13 = Suc N12

public export
N14 : Base.Nat
N14 = Suc N13

public export
N15 : Base.Nat
N15 = Suc N14

public export
N16 : Base.Nat
N16 = Suc N15

public export
N17 : Base.Nat
N17 = Suc N16

public export
N18 : Base.Nat
N18 = Suc N17

public export
N19 : Base.Nat
N19 = Suc N18

public export
N20 : Base.Nat
N20 = Suc N19

public export
N21 : Base.Nat
N21 = Suc N20

public export
N22 : Base.Nat
N22 = Suc N21

public export
N23 : Base.Nat
N23 = Suc N22

public export
N24 : Base.Nat
N24 = Suc N23

public export
N25 : Base.Nat
N25 = Suc N24

public export
N26 : Base.Nat
N26 = Suc N25

public export
N27 : Base.Nat
N27 = Suc N26

public export
N28 : Base.Nat
N28 = Suc N27

public export
N29 : Base.Nat
N29 = Suc N28

public export
N30 : Base.Nat
N30 = Suc N29

public export
N31 : Base.Nat
N31 = Suc N30

public export
N32 : Base.Nat
N32 = Suc N31

public export
Church_N0 : Church_Nat
Church_N0 = church_zero

public export
Church_N1 : Church_Nat
Church_N1 = church_succ Church_N0

public export
Church_N2 : Church_Nat
Church_N2 = church_succ Church_N1

public export
Church_N3 : Church_Nat
Church_N3 = church_succ Church_N2

public export
Church_N4 : Church_Nat
Church_N4 = church_succ Church_N3

public export
Church_N5 : Church_Nat
Church_N5 = church_succ Church_N4

public export
Church_N6 : Church_Nat
Church_N6 = church_succ Church_N5

public export
Church_N7 : Church_Nat
Church_N7 = church_succ Church_N6

public export
Church_N8 : Church_Nat
Church_N8 = church_succ Church_N7

public export
Church_N9 : Church_Nat
Church_N9 = church_succ Church_N8

public export
Church_N10 : Church_Nat
Church_N10 = church_succ Church_N9

public export
Church_N11 : Church_Nat
Church_N11 = church_succ Church_N10

public export
Church_N12 : Church_Nat
Church_N12 = church_succ Church_N11

public export
Church_N13 : Church_Nat
Church_N13 = church_succ Church_N12

public export
Church_N14 : Church_Nat
Church_N14 = church_succ Church_N13

public export
Church_N15 : Church_Nat
Church_N15 = church_succ Church_N14

public export
Church_N16 : Church_Nat
Church_N16 = church_succ Church_N15

public export
Church_N17 : Church_Nat
Church_N17 = church_succ Church_N16

public export
Church_N18 : Church_Nat
Church_N18 = church_succ Church_N17

public export
Church_N19 : Church_Nat
Church_N19 = church_succ Church_N18

public export
Church_N20 : Church_Nat
Church_N20 = church_succ Church_N19

public export
Church_N21 : Church_Nat
Church_N21 = church_succ Church_N20

public export
Church_N22 : Church_Nat
Church_N22 = church_succ Church_N21

public export
Church_N23 : Church_Nat
Church_N23 = church_succ Church_N22

public export
Church_N24 : Church_Nat
Church_N24 = church_succ Church_N23

public export
Church_N25 : Church_Nat
Church_N25 = church_succ Church_N24

public export
Church_N26 : Church_Nat
Church_N26 = church_succ Church_N25

public export
Church_N27 : Church_Nat
Church_N27 = church_succ Church_N26

public export
Church_N28 : Church_Nat
Church_N28 = church_succ Church_N27

public export
Church_N29 : Church_Nat
Church_N29 = church_succ Church_N28

public export
Church_N30 : Church_Nat
Church_N30 = church_succ Church_N29

public export
Church_N31 : Church_Nat
Church_N31 = church_succ Church_N30

public export
Church_N32 : Church_Nat
Church_N32 = church_succ Church_N31
