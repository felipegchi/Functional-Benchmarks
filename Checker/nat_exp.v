Require Base.

Definition Size : Base.Nat := Base.N1 .
Definition Main : Base.Equal (Base.is_even (Base.exp Base.N2 Size)) Base.True := Base.Refl .
