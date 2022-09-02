{-# OPTIONS --type-in-type #-}

import Base

Size : Base.Nat
Size = Base.N1

Main :
  let a = Base.force-tree (Base.full-tree Size) in
  let b = Base.true in
  Base.Equal a b
Main = Base.refl
