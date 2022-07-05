{-# OPTIONS --allow-unsolved-metas #-}
module resit where
open import prelude

data Expr : Nat → Set where
  -- constants
  val : Nat → Expr n
  -- addition
  add : Expr n → Expr n → Expr n
  -- variables
  var : Fin n → Expr n
  -- let bindings: 'bind e₁ e₂' corresponds to 'let x = e₁ in e₂' note
  --  that e₂ has one additional variable in scope (x in the example
  --  above)
  bind : Expr n → Expr (succ n) → Expr n

-- Define an evaluation function
eval : Expr n → Vec Nat n → Nat
eval (val x)      _    = x
eval (add e₁ e₂)  args = eval e₁ args + eval e₂ args
eval (var x)      args = lookup args x
eval (bind e₁ e₂) args = eval e₂ (eval e₁ args :: args)

-- A datatype for representing 'order preserving embedings'
--   think of OPE n m as a function from Fin n → Fin m
--   that is order preserving, i.e. if i ≤ j (in Fin n)
--   than applying the OPE maintains this order.
data OPE : Nat → Nat → Set where
  done : OPE zero zero
  skip : OPE n m → OPE n (succ m)
  keep : OPE n m → OPE (succ n) (succ m)

-- Prove that these order preserving embeddings are reflexive and transitive
ope-refl : {n : Nat} → OPE n n
ope-refl {zero}   = done
ope-refl {succ n} = keep ope-refl

ope-trans : OPE n m → OPE m k → OPE n k
ope-trans done g            = g
ope-trans f        (skip g) = skip (ope-trans f g)
ope-trans (skip f) (keep g) = skip (ope-trans f g)
ope-trans (keep f) (keep g) = keep (ope-trans f g)

-- Show how each OPE n m determines a map from Fin n → Fin m
⟦_⟧ : OPE n m → Fin n → Fin m
⟦ skip ope ⟧ i = succ (⟦ ope ⟧ i)
⟦ keep ope ⟧ zero = zero
⟦ keep ope ⟧ (succ i) = succ (⟦ ope ⟧ i)

-- Use this ⟦_⟧ function to define a renaming operation on expressions
rename : OPE n m → Expr n → Expr m
rename ope (val x)      = val x
rename ope (add e₁ e₂)  = add (rename ope e₁) (rename ope e₂)
rename ope (var x)      = var (⟦ ope ⟧ x)
rename ope (bind e₁ e₂) = bind (rename ope e₁) (rename (keep ope) e₂)

-- But this can also be used to project information out of a vector
--  (this is something that you couldn't do easily if we were working
--  with functions Fin n -> Fin m directly)
project : OPE n m → Vec Nat m → Vec Nat n
project ope xs = tabulate (λ x → lookup xs (⟦ ope ⟧ x))

-- Formulate a lemma and prove that renaming preserves semantics
-- (i.e. the eval function above)
adjust : OPE n m → Vec Nat n → Vec Nat m
adjust done [] = []
adjust (skip ope) xs = zero :: adjust ope xs
adjust (keep ope) (x :: xs) = x :: adjust ope xs

cong-add : {a b c d : Nat} → a ≡ c → b ≡ d → (a + b) ≡ (c + d)
cong-add refl refl = refl

correctness : (ope : OPE n m) → (e : Expr n) → (xs : Vec Nat n)
            → eval e xs ≡ eval (rename ope e) (adjust ope xs)
correctness ope (val x) xs = refl
correctness ope (add e₁ e₂) xs = cong-add (correctness ope e₁ xs) (correctness ope e₂ xs)
correctness ope (var x) xs = {!!}
correctness ope (bind e₁ e₂) xs = {!!}

-- # Further ideas/projects:

-- * extend the Expr language with boolean constants, if then else,
-- and a _<_ operator - how can you change the types to still write a
-- total evaluator? Instead of tracking the number of bound variables,
-- you will need to keep track of the list of types of variables in
-- scope. How can you update the OPE accordingly?

-- * formulate an ordering on Fin n and show that each OPE preserves
-- this ordering (a soundness result)

-- * show that each function Fin n → Fin m that is order preserving
-- gives rise to a unique OPE n m (a completeness result)

-- * prove that ope-refl and ope-trans behave 'as expected' with
-- respect to their semantics ⟦_⟧ (i.e. they correspond to the
-- identity function and function composition)

-- * write a 'dead binding analysis' that maps each (e : Expr n) to a
-- pair (e' : Expr m) and (ope : OPE m n) such that: for any (env :
-- Vec n), evaluating e and e' with this environment returns the same
-- result.

variable
  a b : Fin n

-- Ordering on finite sets
data _≤_ : Fin n → Fin n → Set where
  base : zero ≤ b
  step : a ≤ b → succ a ≤ succ b
infixr 4 _≤_

_≤?_ : Fin n → Fin n → Bool
zero ≤? y = true
succ x ≤? zero = false
succ x ≤? succ y = x ≤? y

soundness-≤ : {a ≤? b ≡ true} → a ≤ b
soundness-≤ {a = zero} = base
soundness-≤ {a = succ a} {b = succ b} {p} = step (soundness-≤ {a = a} {b = b} {p})

-- Soundness proof: each OPE is order preserving
soundness-ope : (ope : OPE n m) → a ≤ b → ⟦ ope ⟧ a ≤ ⟦ ope ⟧ b
soundness-ope ope p = {!   !}

-- Completeness proof:
-- each order preserving function (Fin n → Fin m) gives rise to a unique OPE n m
completeness : {f : Fin n → Fin m} → {a ≤ b} → {f a ≤ f b} → OPE n m
completeness = {!   !}

-- Identity proof: ope-refl corresponds to identity
identity : ⟦ ope-refl ⟧ a ≡ a
identity {a = zero} = refl
identity {a = succ a} = cong succ identity

-- Composition proof: ope-trans corresponds to function composition
composition : (f : OPE n m) → (g : OPE m k) → ⟦ ope-trans f g ⟧ a ≡ ⟦ g ⟧ (⟦ f ⟧ a)
composition (skip f) (skip g) = cong succ (composition (skip f) g)
composition (skip f) (keep g) = cong succ (composition f g)
composition (keep f) (skip g) = cong succ (composition (keep f) g)
composition {a = zero} (keep _) (keep _) = refl
composition {a = succ _} (keep f) (keep g) = cong succ (composition f g)
