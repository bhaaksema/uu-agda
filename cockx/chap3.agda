module cockx.chap3 where
open import cockx.chap1
open import cockx.chap2

-- Propositional Logic
data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

cases : {A B C : Set} → Either A B → (A → C) → (B → C) → C
cases (left x)  f g = f x
cases (right x) f g = g x

data ⊤ : Set where
  tt : ⊤

data ⊥ : Set where

absurd : {A : Set} → ⊥ → A
absurd ()

proof1 : {P : Set} → P → P
proof1 = id

proof2 : {P Q R : Set} → (P → Q) × (Q → R) → (P → R)
proof2 (f , g) x = g (f x)

proof3 : {P Q R : Set} → (Either P Q → R) → (P → R) × (Q → R)
proof3 f = (λ x → f (left x)) , (λ x → f (right x))

proof4 : {A B : Set} → A → (B → A)
proof4 x y = x

proof5 : {A : Set} → A × ⊤ → Either A ⊥
proof5 (x , _) = left x

proof6 : {A B C : Set} → (A → (B → C)) → A × B → C
proof6 f (x , y) = f x y

proof7 : {A B C : Set} → A × (Either B C) → Either (A × B) (A × C)
proof7 (x , left  y) = left  (x , y)
proof7 (x , right y) = right (x , y)

proof8 : {A B C D : Set} → (A → C) × (B → D) → (A × B → C × D)
proof8 (f , g) (x , y) = f x , g y

proof9 : {P : Set} → (Either P (P → ⊥) → ⊥) → ⊥
proof9 f = proof9' (proof3 f)
  where
    proof9' : {P : Set} → (P → ⊥) × ((P → ⊥) → ⊥) → ⊥
    proof9' (x , f) = f x


-- Predicate Logic
data IsEven : Nat → Set where
  even-zero : IsEven zero
  even-succ2 : {n : Nat} → IsEven n → IsEven (succ (succ n))

6-is-even : IsEven 6
6-is-even = even-succ2 (even-succ2 (even-succ2 even-zero))

7-is-not-even : IsEven 7 → ⊥
7-is-not-even (even-succ2 (even-succ2 (even-succ2 ())))

data IsTrue : Bool → Set where
  is-true : IsTrue true

IsTrue' : Bool → Set
IsTrue' true  = ⊤
IsTrue' false = ⊥

_==_ : Nat → Nat → Bool
zero   == zero   = true
succ x == succ y = x == y
_      == _      = false
infixr 1 _==_

length-is-3 : IsTrue (length (1 :: 2 :: 3 :: []) == 3)
length-is-3 = is-true

double : Nat → Nat
double zero     = zero
double (succ n) = succ (succ (double n))

double-is-even : (n : Nat) → IsEven (double n)
double-is-even zero     = even-zero
double-is-even (succ n) = even-succ2 (double-is-even n)

n-equals-n : (n : Nat) → IsTrue (n == n)
n-equals-n zero     = is-true
n-equals-n (succ n) = n-equals-n n

half-a-dozen : Σ Nat (λ n → IsTrue (n + n == 12))
half-a-dozen = 6 , is-true

zero-or-succ : (n : Nat) → Either (IsTrue (n == 0)) (Σ Nat (λ m → IsTrue (n == succ m)))
zero-or-succ zero     = left is-true
zero-or-succ (succ n) = right (n , n-equals-n n)


-- The identity type
data _≡_ {A : Set} : A → A → Set where
  refl : {x : A} → x ≡ x
infixr 1 _≡_

one-plus-one : 1 + 1 ≡ 2
one-plus-one = refl

zero-not-one : 0 ≡ 1 → ⊥
zero-not-one = λ ()

id-returns-input : {A : Set} → (x : A) → id x ≡ x
id-returns-input x = refl

sym : {A : Set}{x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : {A B : Set}{x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl
