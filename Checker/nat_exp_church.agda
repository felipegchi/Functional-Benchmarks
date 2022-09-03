{-# OPTIONS --type-in-type #-}

import Base

Size : Base.Church-Nat
Size = Base.Church-N1

Main : Base.Equal (Base.Church-is-even (Base.Church-exp Base.Church-N2 Size)) Base.Church-true
Main = Base.refl
