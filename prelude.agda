module prelude where

-- Natural numbers
data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
0      + y = y
succ x + y = succ (x + y)
infixr 2 _+_

-- Booleans
data Bool : Set where
  true  : Bool
  false : Bool

-- Finite sets
variable
  n m k : Nat

data Fin : Nat → Set where
  zero : Fin (succ n)
  succ : Fin n → Fin (succ n)

-- Vectors
variable
  A B : Set

data Vec A : Nat → Set where
  []   : Vec A 0
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)
infixr 3 _::_

lookup : Vec A n → Fin n → A
lookup (x :: xs) zero    = x
lookup (x :: xs) (succ i) = lookup xs i

tabulate : (Fin n → A) → Vec A n
tabulate {n = zero}  f = []
tabulate {n = succ n} f = f zero :: tabulate (λ x → f (succ x))

-- Pairs
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

-- Proofs
data _≡_ : A → A → Set where
  refl : {x : A} → x ≡ x
infixr 1 _≡_

cong : {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl
