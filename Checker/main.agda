{-# OPTIONS --type-in-type #-}

import Base

Size : Base.Nat
Size = Base.N6

Main :
  let a = Base.is-even (Base.exp Base.N2 Size) in
  let b = Base.true in
  Base.Equal a b
Main = Base.refl

