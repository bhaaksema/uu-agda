module prelude where

-- Natural numbers
data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
0      + y = y
succ x + y = succ (x + y)
infixr 3 _+_

_-_ : ℕ → ℕ → ℕ
x      - zero   = x
zero   - succ y = zero
succ x - succ y = x - y
infixl 3 _-_

_*_ : ℕ → ℕ → ℕ
zero   * y = zero
succ x * y = y + (x * y)
infixr 4 _*_

-- Booleans
data Bool : Set where
  true  : Bool
  false : Bool

-- Finite sets
data Fin : ℕ → Set where
  zero : {n : ℕ} → Fin (succ n)
  succ : {n : ℕ} → Fin n → Fin (succ n)

-- Pairs
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

-- Vectors
data Vec (A : Set) : ℕ → Set where
  []   : Vec A 0
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (succ n)
infixr 2 _∷_

lookup : {A : Set}{n : ℕ} → Vec A n → Fin n → A
lookup (x ∷ xs) zero    = x
lookup (x ∷ xs) (succ i) = lookup xs i

tabulate : {A : Set}{n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = zero}  f = []
tabulate {n = succ n} f = f zero ∷ tabulate (λ x → f (succ x))

-- Proof constructs
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
infix 1 _≡_

cong : {A B : Set}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong _ refl = refl

cong₂ : {A B C : Set}{x₁ x₂ : A}{y₁ y₂ : B}
      → (f : A → B → C) → x₁ ≡ x₂ → y₁ ≡ y₂ → f x₁ y₁ ≡ f x₂ y₂
cong₂ _ refl refl = refl

trans : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

_⟨_⟩_ : {A : Set} → (x : A) {y z : A} → (x ≡ y) → (y ≡ z) → x ≡ z
_ ⟨ p ⟩ q = trans p q
infixr 1 _⟨_⟩_

_■ : {A : Set} → (x : A) → x ≡ x
_■ _ = refl
