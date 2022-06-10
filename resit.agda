module resit where

open import Data.Nat using (ℕ ; zero) renaming (suc to succ)
open import Data.Fin using (Fin)
open import Data.Vec using (Vec)

variable
  n m k : ℕ

data Expr : ℕ → Set where
  -- constants
  val : ℕ → Expr n
  -- addition
  add : Expr n → Expr n → Expr n
  -- variables
  var : Fin n → Expr n
  -- let bindings: 'bind e₁ e₂' corresponds to 'let x = e₁ in e₂' note
  --  that e₂ has one additional variable in scope (x in the example
  --  above)
  let-binding : Expr n → Expr (succ n) → Expr n
  -- (feel free to come up with a better name for this last
  -- constructor, unfortunately 'let' is a keyword)

-- Define an evaluation function
eval : Expr n → Vec ℕ n → ℕ
eval = {!!}

-- A datatype for representing 'order preserving embedings'
--   think of OPE n m as a function from Fin n → Fin m
--   that is order preserving, i.e. if i ≤ j (in Fin n)
--   than applying the OPE maintains this order.
data OPE : ℕ → ℕ → Set where
  done : OPE zero zero
  skip : OPE n m → OPE n (succ m)
  keep : OPE n m → OPE (succ n) (succ m)

-- Prove that these order preserving embeddings are reflexive and transitive
ope-refl : {n : ℕ} → OPE n n
ope-refl = {!!}

ope-trans : OPE n m → OPE m k → OPE n k
ope-trans o1 o2 = {!!}

-- Show how each OPE n m determines a map from Fin n → Fin m
⟦_⟧ : OPE n m → Fin n → Fin m
⟦ ope ⟧ i = {!!}

-- Use this ⟦_⟧ function to define a renaming operation on expressions
rename : OPE n m → Expr n → Expr m
rename = {!!}

-- But this can also be used to project information out of a vector
--  (this is something that you couldn't do easily if we were working
--  with functions Fin n -> Fin m directly)
project : OPE n m → Vec ℕ {!!} → Vec ℕ {!!}
project ope xs = {!!}

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

