module prelude where

data Nat : Set where
  zero : Nat 
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
0        + y = y
(succ x) + y = succ (x + y)
infixr 2 _+_

data Vec (A : Set) : Nat → Set where
  []   : Vec A 0
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (succ n)
  fsucc : {n : Nat} → Fin n → Fin (succ n)

lookupVec : {A : Set}{n : Nat} → Vec A n → Fin n → A
lookupVec []        ()
lookupVec (x :: xs) fzero     = x
lookupVec (x :: xs) (fsucc n) = lookupVec xs n
