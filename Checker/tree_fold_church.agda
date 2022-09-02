{-# OPTIONS --type-in-type #-}

import Base

Size : Base.Church-Nat
Size = Base.Church-N1

Main :
  let a = Base.Church-force-tree (Base.Church-full-tree Size) in
  let b = Base.Church-true in
  Base.Equal a b
Main = Base.refl
