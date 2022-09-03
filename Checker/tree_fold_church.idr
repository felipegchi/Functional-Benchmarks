import Base

Size : Base.Church_Nat
Size = Base.Church_N1

Main : Base.Equal (Base.church_force_tree (Base.church_full_tree Size)) Base.church_true
Main = Base.Refl
