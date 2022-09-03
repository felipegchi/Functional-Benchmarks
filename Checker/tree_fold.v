Require Base.

Definition Size : Base.Nat := Base.N1 .
Definition Main : Base.Equal (Base.force_tree (Base.full_tree Size)) Base.True := Base.Refl .
