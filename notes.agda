-- This file contains functions that were not needed in prelude.agda
module notes where
open import prelude

-- Functions
_∘_ : {A : Set}{B : A -> Set}{C : {x : A} -> B x -> Set}
      (f : {x : A}(y : B x) -> C y)(g : (x : A) -> B x)(x : A) -> C (g x)
(f ∘ g) x = f (g x)
infixr 4 _∘_

id : Set → Set
id x = x

-- Booleans
if_then_else_ : {A : Set} → Bool → A  → A → A
if true then t else _ = t
if false then _ else e = e

_==_ : ℕ → ℕ → Bool
zero == zero = true
succ x == succ y = x == y
_ == _ = false

-- Finite sets
fromℕ : (n : ℕ) → Fin (succ n)
fromℕ zero     = zero
fromℕ (succ n) = succ (fromℕ n)

_==?_ : {n : ℕ} → Fin n → Fin n → Bool
zero   ==? zero   = true
succ x ==? succ y = x ==? y
_      ==? _      = false

-- Vectors
_++_ : {A : Set}{n m : ℕ} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)
infixr 3 _++_

zeroes : (n : ℕ) → Vec ℕ n
zeroes zero = []
zeroes (succ n) = zero ∷ zeroes n

-- Proofs
record ⊤ : Set where
  constructor tt

data ⊥ : Set where

sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl
