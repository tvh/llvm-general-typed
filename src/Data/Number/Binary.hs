{-# LANGUAGE DataKinds, TypeFamilies, TypeOperators, UndecidableInstances, TemplateHaskell, PolyKinds, GADTs #-}
-- | The implementations of all functions except for rem, quot, div, mod are 
--   supposed to be as non-strict as possible.
module Data.Number.Binary where

import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Singletons.TypeLits

data Binary
  -- | Constructor representing zero
  = Zero  
  -- | A natural number 
  | Pos Binary1

-- | A binary representation of natural numbers which starts with the least
--   significant bit.
data Binary1
  -- | This constructor represents the most significant bit. There are no 
  --   leading zero bits. 
  = IHi
  -- | A zero bit
  | O Binary1 
  -- | A one bit
  | I Binary1

genSingletons [
  ''Binary,
  ''Binary1
  ]

promote [d|
  fromBinary Zero = 0
  fromBinary (Pos n) = fromBinary1 n

  fromBinary1 IHi = 1
  fromBinary1 (O n) = 2*fromBinary1 n
  fromBinary1 (I n) = 2*fromBinary1 n + 1
                      
  toBinary 0 = Zero
  toBinary n = Pos (toBinary1 n)

  toBinary1 1 = IHi
  toBinary1 n =
    let (n',m) = divmod n 2
        n'' = toBinary1 n'
    in case m of
      0 -> O n''
      1 -> I n''

  divmod n m =
    case m > n of
      True  -> (0,m)
      False ->
        let (n',m') = divmod (n - m) m
        in (n' + 1,m')

  succ Zero    = Pos IHi
  succ (Pos n) = Pos (succ1 n)

  succ1 IHi   = O IHi
  succ1 (O n) = I n
  succ1 (I n) = O (succ1 n)

  pred (Pos IHi) = Zero
  pred (Pos n) = Pos (pred1 n)

  pred1 IHi         = error "predecessor of 1"
  pred1 (O IHi)     = IHi
  pred1 (O x@(O _)) = I (pred1 x)
  pred1 (O (I x))   = I (O x) 
  pred1 (I x)       = O x
                
  u n = toBinary n

  index :: [a] -> Binary -> a
  index (x:_) Zero = x
  index (_:xs) n = index xs (pred n)
  |]
  
