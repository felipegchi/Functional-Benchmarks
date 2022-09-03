{-# OPTIONS --type-in-type #-}

import Base

Size : Base.Church-Nat
Size = Base.Church-N1

Main : Base.Equal (Base.Church-force-tree (Base.Church-full-tree Size)) Base.Church-true
Main = Base.refl
