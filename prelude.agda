module prelude where

-- Function composition
_∘_ : {A : Set}{B : A -> Set}{C : {x : A} -> B x -> Set}
      (f : {x : A}(y : B x) -> C y)(g : (x : A) -> B x)(x : A) -> C (g x)
(f ∘ g) x = f (g x)

-- Natural numbers
data Nat : Set where
  zero : Nat 
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
0        + y = y
(succ x) + y = succ (x + y)
infixr 2 _+_

-- Finite sets
data Fin : Nat → Set where
  zero : {n : Nat} → Fin (succ n)
  succ : {n : Nat} → Fin n → Fin (succ n)

-- Vectors
data Vec (A : Set) : Nat → Set where
  []   : Vec A 0
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

lookup : {A : Set}{n : Nat} → Vec A n → Fin n → A
lookup (x :: xs) zero    = x
lookup (x :: xs) (succ i) = lookup xs i

tabulate : {A : Set}{n : Nat} → (Fin n → A) → Vec A n
tabulate {n = zero}  f = []
tabulate {n = succ n} f = f zero :: tabulate (f ∘ succ)
