{-# OPTIONS --type-in-type #-}

import Base

Size : Base.Church-Nat
Size = Base.Church-N1

Main :
  let a = Base.Church-is-even (Base.Church-exp Base.Church-N2 Size) in
  let b = Base.Church-true in
  Base.Equal a b
Main = Base.refl
