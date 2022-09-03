import Base

Size : Base.Nat
Size = Base.N1

Main : Base.Equal (Base.is_even (Base.exp Base.N2 Size)) Base.True
Main = Base.Refl
