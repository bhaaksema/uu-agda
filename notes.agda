module notes where
open import prelude
open import resit

-- This file contains functions that were not needed in prelude.agda,
-- but also lemmas that I didn't use in resit.agda.

-- Functions
_∘_ : {A : Set}{B : A -> Set}{C : {x : A} -> B x -> Set}
      (f : {x : A}(y : B x) -> C y)(g : (x : A) -> B x)(x : A) -> C (g x)
(f ∘ g) x = f (g x)
infixr 4 _∘_

id : Set → Set
id x = x

-- Natural numbers
_*_ : Nat → Nat → Nat
zero   * y = zero
succ x * y = y + (x * y)
infixr 3 _*_

-- Booleans
if_then_else_ : Bool → A  → A → A
if true then t else _ = t
if false then _ else e = e

_==_ : Nat → Nat → Bool
zero == zero = true
succ x == succ y = x == y
_ == _ = false

-- Finite sets
fromNat : (n : Nat) → Fin (succ n)
fromNat zero     = zero
fromNat (succ n) = succ (fromNat n)

_==?_ : Fin n → Fin n → Bool
zero   ==? zero   = true
succ x ==? succ y = x ==? y
_      ==? _      = false

-- Pairs
data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

-- Vectors
_++_ : {A : Set}{n m : Nat} → Vec A m → Vec A n → Vec A (m + n)
[]       ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)
infixr 3 _++_

zeroes : (n : Nat) → Vec Nat n
zeroes zero = []
zeroes (succ n) = zero :: zeroes n

-- Proofs
record ⊤ : Set where
  constructor tt

data ⊥ : Set where

sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

bin-cong : {A B C : Set}{a c : A}{b d : B}
         → (f : A → B → C) → a ≡ c → b ≡ d → f a b ≡ f c d
bin-cong _ refl refl = refl

cong-lookup : {x y : Fin n}{xs ys : Vec A n} → x ≡ y → xs ≡ ys → lookup xs x ≡ lookup ys y
cong-lookup p1 p2 = bin-cong lookup p2 p1

first : {x : A}{xs : Vec A n} → lookup (x :: xs) zero ≡ x
first = refl

cong-rename : {x y : Expr n}{ope : OPE n m} → x ≡ y → rename ope x ≡ rename ope y
cong-rename refl = refl

cong-ope : (ope : OPE n m) → a ≡ b → ⟦ ope ⟧ a ≡ ⟦ ope ⟧ b
cong-ope ope p = cong ⟦ ope ⟧ p
