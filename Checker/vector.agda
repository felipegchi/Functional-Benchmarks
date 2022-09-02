{-# OPTIONS --type-in-type #-}

import Base

Main = 
  let vec = Base.nil in
  let vec = Base.cons Set vec in --REPEAT
  vec
