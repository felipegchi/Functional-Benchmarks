import Base

Size : Base.Nat
Size = Base.N1

Main : Base.Equal (Base.force_tree (Base.full_tree Size)) Base.True
Main = Base.Refl
