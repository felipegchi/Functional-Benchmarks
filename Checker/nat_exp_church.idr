import Base

Size : Base.Church_Nat
Size = Base.Church_N1

Main : Base.Equal (Base.church_is_even (Base.church_exp Base.Church_N2 Size)) Base.church_true
Main = Base.Refl
