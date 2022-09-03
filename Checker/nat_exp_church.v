Require Base.

Definition Size : Base.Church_Nat := Base.Church_N1 .
Definition Main : Base.Equal (Base.church_is_even (Base.church_exp Base.Church_N2 Size)) Base.church_true := Base.Refl .
