{-# OPTIONS --type-in-type #-}

import Base

Size : Base.Nat
Size = Base.N1

Main : Base.Equal (Base.force-tree (Base.full-tree Size)) Base.true
Main = Base.refl
