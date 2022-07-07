{-# OPTIONS --allow-unsolved-metas #-}
module resit where
open import prelude

variable
  n m k : ℕ

data Expr : ℕ → Set where
  -- constants
  val : ℕ → Expr n
  -- binary operator
  bin : (ℕ → ℕ → ℕ) → Expr n → Expr n → Expr n
  -- variables
  var : Fin n → Expr n
  -- let bindings: 'bind e₁ e₂' corresponds to 'let x = e₁ in e₂' note
  --  that e₂ has one additional variable in scope (x in the example
  --  above)
  bind : Expr n → Expr (succ n) → Expr n

-- Define an evaluation function
eval : Expr n → Vec ℕ n → ℕ
eval (val x)        _   = x
eval (bin op e₁ e₂) env = op (eval e₁ env) (eval e₂ env)
eval (var x)        env = lookup env x
eval (bind e₁ e₂)   env = eval e₂ (eval e₁ env ∷ env)

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
rename ope (val x)        = val x
rename ope (bin op e₁ e₂) = bin op (rename ope e₁) (rename ope e₂)
rename ope (var x)        = var (⟦ ope ⟧ x)
rename ope (bind e₁ e₂)   = bind (rename ope e₁) (rename (keep ope) e₂)

-- But this can also be used to project information out of a vector
--  (this is something that you couldn't do easily if we were working
--  with functions Fin n -> Fin m directly)
project : OPE n m → Vec ℕ m → Vec ℕ n
project ope xs = tabulate (λ x → lookup xs (⟦ ope ⟧ x))

-- Formulate a lemma and prove that renaming preserves semantics
-- (i.e. the eval function above)
cong-add : {a b c d : ℕ} → a ≡ c → b ≡ d → (a + b) ≡ (c + d)
cong-add refl refl = refl

correctness : (ope : OPE n m) → (e : Expr n) → (env : Vec ℕ m)
            → eval e (project ope env) ≡ eval (rename ope e) env
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

soundness-ope : (ope : OPE n m) → a ≤ b → ⟦ ope ⟧ a ≤ ⟦ ope ⟧ b
soundness-ope ope p = {!!}

-- * show that each function Fin n → Fin m that is order preserving
-- gives rise to a unique OPE n m (a completeness result)
completeness : {f : Fin n → Fin m} → {a ≤ b} → {f a ≤ f b} → OPE n m
completeness = {!!}

-- * prove that ope-refl and ope-trans behave 'as expected' with
-- respect to their semantics ⟦_⟧ (i.e. they correspond to the
-- identity function and function composition)
identity : ⟦ ope-refl ⟧ a ≡ a
identity {a = zero} = refl
identity {a = succ a} = cong succ identity

composition : (f : OPE n m) → (g : OPE m k) → ⟦ ope-trans f g ⟧ a ≡ ⟦ g ⟧ (⟦ f ⟧ a)
composition (skip f) (skip g) = cong succ (composition (skip f) g)
composition (skip f) (keep g) = cong succ (composition f g)
composition (keep f) (skip g) = cong succ (composition (keep f) g)
composition {a = zero} (keep _) (keep _) = refl
composition {a = succ _} (keep f) (keep g) = cong succ (composition f g)

-- * write a 'dead binding analysis' that maps each (e : Expr n) to a
-- pair (e' : Expr m) and (ope : OPE m n) such that: for any (env :
-- Vec n), evaluating e and e' with this environment returns the same
-- result.
dba : Expr n → Expr m × OPE m n
dba e = {!!}
