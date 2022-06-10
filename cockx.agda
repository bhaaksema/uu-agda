-- Chapter 1

data Nat : Set where
  zero : Nat 
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}

_+_ : Nat → Nat → Nat
0        + y = y
(succ x) + y = succ (x + y)

halve : Nat → Nat
halve (succ (succ x)) = succ (halve x)
halve _               = 0

_*_ : Nat → Nat → Nat
zero   * y = zero
succ x * y = y + (x * y)

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool → Bool
not true  = false
not false = true

_&&_ : Bool → Bool → Bool
true  && y = y
false && _ = false

_||_ : Bool → Bool → Bool
true  || _ = true
false || y = y

id : {A : Set} → A → A
id x = x 

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

data List (A : Set) : Set where
  []   : List A
  _::_ : A → List A → List A
infixr 5 _::_

data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B
infixr 4 _,_

fst : {A B : Set} → A × B → A
fst (x , y) = x

snd : {A B : Set} → A × B → B
snd (x , y) = y

length : {A : Set} → List A → Nat
length []        = 0
length (x :: xs) = succ (length xs)

_++_ : {A : Set} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

map : {A B : Set} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: (map f xs)

data Maybe (A : Set) : Set where
  just    : A → Maybe A
  nothing : Maybe A

lookup : {A : Set} → List A → Nat → Maybe A
lookup [] n = nothing
lookup (x :: xs) zero = just x
lookup (x :: xs) (succ n) = lookup xs n
