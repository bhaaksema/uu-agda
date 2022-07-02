module resit where

open import prelude

variable
  n m k : Nat

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
ope-trans o1        done      = o1
ope-trans o1        (skip o2) = skip (ope-trans o1 o2)
ope-trans (skip o1) (keep o2) = skip (ope-trans o1 o2)
ope-trans (keep o1) (keep o2) = keep (ope-trans o1 o2)

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
project ope xs = tabulate (lookup xs ∘ ⟦ ope ⟧)

-- Formulate a lemma and prove that renaming preserves semantics
-- (i.e. the eval function above)
correctness : {!!}
correctness = {!!}

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

