module cockx.chap2 where
open import cockx.chap1 

variable
  n m : Nat
  A B : Set

data Vec (A : Set) : Nat → Set where
  []   : Vec A 0
  _::_ : A → Vec A n → Vec A (succ n)

zeroes : (n : Nat) → Vec Nat n
zeroes zero     = []
zeroes (succ n) = 0 :: zeroes n

prepend : A → Vec A n → Vec A (succ n)
prepend x xs = x :: xs

downFrom : (n : Nat) → Vec Nat n
downFrom zero     = []
downFrom (succ n) = n :: downFrom n

_++Vec_ : Vec A n → Vec A m → Vec A (n + m)
[]        ++Vec ys = ys
(x :: xs) ++Vec ys = x :: (xs ++Vec ys)

head : Vec A (succ n) → A
head (x :: xs) = x

tail : Vec A (succ n) → Vec A n
tail (x :: xs) = xs

dotProduct : Vec Nat n → Vec Nat n → Nat
dotProduct [] [] = zero
dotProduct (x :: xs) (y :: ys) = x * y + (dotProduct xs ys)

data Fin : Nat → Set where
  zero : Fin (succ n)
  succ : Fin n → Fin (succ n)

lookupVec : Vec A n → Fin n → A
lookupVec []        ()
lookupVec (x :: xs) zero     = x
lookupVec (x :: xs) (succ n) = lookupVec xs n

putVec : Fin n → A → Vec A n → Vec A n
putVec zero     y (x :: xs) = y :: xs
putVec (succ n) y (x :: xs) = x :: putVec n y xs

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (x : A) → B x → Σ A B

_×'_ : (A B : Set) → Set
A ×' B = Σ A (λ _ → B)

convertPair : A × B → A ×' B
convertPair (x , y) = x , y

convertPair' : A ×' B → A × B
convertPair' (x , y) = x , y

fstΣ : {B : A → Set} → Σ A B → A
fstΣ (x , y) = x

sndΣ : {B : A → Set} → (z : Σ A B) → B (fstΣ z)
sndΣ (x , y) = y

List' : (A : Set) → Set
List' A = Σ Nat (Vec A)

convertList : List A → List' A
convertList [] = zero , []
convertList (x :: xs) = succ (fstΣ next) , x :: sndΣ next
  where next = convertList xs

convertList' : List' A → List A
convertList' (_ , []) = []
convertList' (succ n , (x :: xs)) = x :: convertList' (n , xs)
