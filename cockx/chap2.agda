module cockx.chap2 where
open import cockx.chap1

data Vec (A : Set) : Nat → Set where
  []   : Vec A 0
  _::_ : {n : Nat} → A → Vec A n → Vec A (succ n)

zeroes : (n : Nat) → Vec Nat n
zeroes zero     = []
zeroes (succ n) = 0 :: zeroes n

prepend : {A : Set}{n : Nat} → A → Vec A n → Vec A (succ n)
prepend x xs = x :: xs

downFrom : (n : Nat) → Vec Nat n
downFrom zero     = []
downFrom (succ n) = n :: downFrom n

_++Vec_ : {A : Set}{n m : Nat} → Vec A n → Vec A m → Vec A (n + m)
[]        ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

head : {A : Set}{n : Nat} → Vec A (succ n) → A
head (x :: xs) = x

tail : {A : Set}{n : Nat} → Vec A (succ n) → Vec A n
tail (x :: xs) = xs

dotProduct : {n : Nat} → Vec Nat n → Vec Nat n → Nat
dotProduct [] [] = zero
dotProduct (x :: xs) (y :: ys) = x * y + (dotProduct xs ys)

data Fin : Nat → Set where
  zero : {n : Nat} → Fin (succ n)
  succ : {n : Nat} → Fin n → Fin (succ n)

lookupVec : {A : Set}{n : Nat} → Vec A n → Fin n → A
lookupVec []        ()
lookupVec (x :: xs) zero     = x
lookupVec (x :: xs) (succ n) = lookupVec xs n

putVec : {A : Set}{n : Nat} → Fin n → A → Vec A n → Vec A n
putVec zero     y (x :: xs) = y :: xs
putVec (succ n) y (x :: xs) = x :: putVec n y xs

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

_×'_ : (A B : Set) → Set
A ×' B = Σ A (λ _ → B)

convertPair : {A B : Set} → A × B → A ×' B
convertPair (x , y) = x , y

convertPair' : {A B : Set} → A ×' B → A × B
convertPair' (x , y) = x , y

fstΣ : {A : Set}{B : A → Set} → Σ A B → A
fstΣ (x , y) = x

sndΣ : {A : Set}{B : A → Set} → (z : Σ A B) → B (fstΣ z)
sndΣ (x , y) = y

List' : (A : Set) → Set
List' A = Σ Nat (Vec A)

convertList : {A : Set} → List A → List' A
convertList [] = zero , []
convertList (x :: xs) = succ (fstΣ next) , x :: sndΣ next
  where next = convertList xs

convertList' : {A : Set} → List' A → List A
convertList' (_ , []) = []
convertList' (succ n , (x :: xs)) = x :: convertList' (n , xs)
