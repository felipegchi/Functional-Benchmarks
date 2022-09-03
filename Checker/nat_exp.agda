{-# OPTIONS --type-in-type #-}

import Base

Size : Base.Nat
Size = Base.N1

Main : Base.Equal (Base.is-even (Base.exp Base.N2 Size)) Base.true
Main = Base.refl
