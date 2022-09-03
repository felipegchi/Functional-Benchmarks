Require Base .

Definition Size : Base.Church_Nat := Base.Church_N1 .
Definition Main : Base.Equal (Base.church_force_tree (Base.church_full_tree Size)) Base.church_true := Base.Refl .
