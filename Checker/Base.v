Inductive Equal : forall (t: Type), t -> t -> Type :=
| Refl : forall (t: Type) (a: t), Equal t a a.

Inductive Bool : Type :=
| True
| False.

Inductive Nat : Type :=
| Zero
| Succ : Nat -> Nat.

Inductive Tree : Type :=
| Leaf
| Node : Tree -> Tree -> Tree.

Inductive Vector : Type -> Nat -> Type :=
| nil  : forall {t}, Vector t Zero
| cons : forall {t} {l: Nat}, t -> Vector t l -> Vector t (Succ l).

Definition Church_Bool : Type :=
  forall (p: Type), p -> p -> p.

Definition church_true : Church_Bool :=
  fun p => fun t => fun f => t.

Definition church_false : Church_Bool :=
  fun p => fun t => fun f => f.

Definition Church_Nat : Type :=
  forall (p: Type), (p -> p) -> p -> p.

Definition church_zero : Church_Nat :=
  fun f s z => z.

Definition church_succ : Church_Nat -> Church_Nat :=
  fun n => fun p => fun f => fun z => f (n p f z).

Definition Church_Tree : Type :=
  forall (p: Type), (p -> p -> p) -> p -> p.

Definition Church_leaf : Church_Tree :=
  fun p => fun n => fun l => l.

Definition Church_node (a: Church_Tree) (b: Church_Tree): Church_Tree :=
  fun p => fun n => fun l => n (a p n l) (b p n l).

Definition Church_Vector (t: Type) (n: Church_Nat): Type :=
  forall (p: Church_Nat -> Type),
    (forall (len: Church_Nat), t -> p len -> p (church_succ len))
    -> p church_zero
    -> p n.

Definition church_nil : forall t, Church_Vector t church_zero :=
    fun _ => fun _ => fun _ => fun n => n.

Definition church_cons : forall t (len: Church_Nat), t -> Church_Vector t len -> Church_Vector t (church_succ len) :=
  fun t len head tail p cons nil => cons len head (tail p cons nil).

Definition not (a: Bool): Bool :=
  match a with
  | True  => False
  | False => True
  end.

Definition and (a: Bool) (b: Bool): Bool :=
    match (a,b) with
    | (False, False) => False
    | (False, True)  => False
    | (True, False)  => False
    | (True, True)   => True
    end.

Fixpoint add (a: Nat) (b: Nat): Nat :=
  match (a,b) with
  | (x, Zero)    => x
  | (x, Succ y)  => Succ (add x y)
  end.

Fixpoint mul (a: Nat) (b: Nat): Nat :=
  match (a,b) with
  | (x, Zero)    => Zero
  | (x, Succ y)  => add y (mul x y)
  end.

Fixpoint exp (a: Nat) (b: Nat): Nat :=
  match (a,b) with
  | (x, Zero)    => Succ Zero
  | (x, Succ y)  => mul y (exp x y)
  end.

Fixpoint is_even (b: Nat): Bool :=
  match b with
  | Zero   => True
  | Succ y => not (is_even y)
  end.

Fixpoint full_tree (b: Nat): Tree :=
  match b with
  | Zero   => Leaf
  | Succ y => let branch := full_tree y in Node branch branch
  end.

Fixpoint tree_fold (b: Tree) (p: Type) (n: p -> p -> p) (l: p): p :=
  match b with
  | Leaf     => l
  | Node a b => n (tree_fold a p n l) (tree_fold b p n l)
  end.

Definition force_tree : Tree -> Bool := fun t =>
  tree_fold t Bool and True.

Definition church_not (b: Church_Bool): Church_Bool :=
  fun p t f => b p f t.

Definition church_and (a: Church_Bool) (b: Church_Bool): Church_Bool :=
  fun p => fun t => fun f => a p (b p t f) f.

Definition church_add (a: Church_Nat) (b: Church_Nat): Church_Nat :=
  fun p => fun s => fun z => a p s (b p s z).

Definition church_mul (a: Church_Nat) (b: Church_Nat): Church_Nat :=
  fun p => fun s => a p (b p s).

Definition church_exp (a: Church_Nat) (b: Church_Nat): Church_Nat :=
  fun p => b (p -> p) (a p).

Definition church_is_even (a: Church_Nat): Church_Bool :=
  a Church_Bool church_not church_true.

Definition church_full_tree (d: Church_Nat): Church_Tree :=
  fun p n l => d p (fun t => n t t) l.

Definition church_tree_fold (t: Church_Tree) (p: Type) (n: p -> p -> p) (l: p): p :=
  t p n l.

Definition church_force_tree (d: Church_Tree): Church_Bool :=
  church_tree_fold d Church_Bool church_and church_true.

Definition Base_N0  : Nat := Zero.
Definition Base_N1  : Nat := Succ Base_N0.
Definition Base_N2  : Nat := Succ Base_N1.
Definition Base_N3  : Nat := Succ Base_N2.
Definition Base_N4  : Nat := Succ Base_N3.
Definition Base_N5  : Nat := Succ Base_N4.
Definition Base_N6  : Nat := Succ Base_N5.
Definition Base_N7  : Nat := Succ Base_N6.
Definition Base_N8  : Nat := Succ Base_N7.
Definition Base_N9  : Nat := Succ Base_N8.
Definition Base_N10 : Nat := Succ Base_N9.
Definition Base_N11 : Nat := Succ Base_N10.
Definition Base_N12 : Nat := Succ Base_N11.
Definition Base_N13 : Nat := Succ Base_N12.
Definition Base_N14 : Nat := Succ Base_N13.
Definition Base_N15 : Nat := Succ Base_N14.
Definition Base_N16 : Nat := Succ Base_N15.
Definition Base_N17 : Nat := Succ Base_N16.
Definition Base_N18 : Nat := Succ Base_N17.
Definition Base_N19 : Nat := Succ Base_N18.
Definition Base_N20 : Nat := Succ Base_N19.
Definition Base_N21 : Nat := Succ Base_N20.
Definition Base_N22 : Nat := Succ Base_N21.
Definition Base_N23 : Nat := Succ Base_N22.
Definition Base_N24 : Nat := Succ Base_N23.
Definition Base_N25 : Nat := Succ Base_N24.
Definition Base_N26 : Nat := Succ Base_N25.
Definition Base_N27 : Nat := Succ Base_N26.
Definition Base_N28 : Nat := Succ Base_N27.
Definition Base_N29 : Nat := Succ Base_N28.
Definition Base_N30 : Nat := Succ Base_N29.
Definition Base_N31 : Nat := Succ Base_N30.
Definition Base_N32 : Nat := Succ Base_N31.

Definition Church_Base_N0  : Church_Nat := church_zero.
Definition Church_Base_N1  : Church_Nat := church_succ Church_Base_N0.
Definition Church_Base_N2  : Church_Nat := church_succ Church_Base_N1.
Definition Church_Base_N3  : Church_Nat := church_succ Church_Base_N2.
Definition Church_Base_N4  : Church_Nat := church_succ Church_Base_N3.
Definition Church_Base_N5  : Church_Nat := church_succ Church_Base_N4.
Definition Church_Base_N6  : Church_Nat := church_succ Church_Base_N5.
Definition Church_Base_N7  : Church_Nat := church_succ Church_Base_N6.
Definition Church_Base_N8  : Church_Nat := church_succ Church_Base_N7.
Definition Church_Base_N9  : Church_Nat := church_succ Church_Base_N8.
Definition Church_Base_N10 : Church_Nat := church_succ Church_Base_N9.
Definition Church_Base_N11 : Church_Nat := church_succ Church_Base_N10.
Definition Church_Base_N12 : Church_Nat := church_succ Church_Base_N11.
Definition Church_Base_N13 : Church_Nat := church_succ Church_Base_N12.
Definition Church_Base_N14 : Church_Nat := church_succ Church_Base_N13.
Definition Church_Base_N15 : Church_Nat := church_succ Church_Base_N14.
Definition Church_Base_N16 : Church_Nat := church_succ Church_Base_N15.
Definition Church_Base_N17 : Church_Nat := church_succ Church_Base_N16.
Definition Church_Base_N18 : Church_Nat := church_succ Church_Base_N17.
Definition Church_Base_N19 : Church_Nat := church_succ Church_Base_N18.
Definition Church_Base_N20 : Church_Nat := church_succ Church_Base_N19.
Definition Church_Base_N21 : Church_Nat := church_succ Church_Base_N20.
Definition Church_Base_N22 : Church_Nat := church_succ Church_Base_N21.
Definition Church_Base_N23 : Church_Nat := church_succ Church_Base_N22.
Definition Church_Base_N24 : Church_Nat := church_succ Church_Base_N23.
Definition Church_Base_N25 : Church_Nat := church_succ Church_Base_N24.
Definition Church_Base_N26 : Church_Nat := church_succ Church_Base_N25.
Definition Church_Base_N27 : Church_Nat := church_succ Church_Base_N26.
Definition Church_Base_N28 : Church_Nat := church_succ Church_Base_N27.
Definition Church_Base_N29 : Church_Nat := church_succ Church_Base_N28.
Definition Church_Base_N30 : Church_Nat := church_succ Church_Base_N29.
Definition Church_Base_N31 : Church_Nat := church_succ Church_Base_N30.
Definition Church_Base_N32 : Church_Nat := church_succ Church_Base_N31.