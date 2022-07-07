module resit where
open import prelude

variable
  n m k : ℕ

-- Addition has been replaced by binary operator (ℕ → ℕ → ℕ)
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

{-          BASIC ASSIGNMENT 1          -}
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

{-          BASIC ASSIGNMENT 2          -}
-- Prove that these order preserving embeddings are reflexive and transitive
ope-refl : {n : ℕ} → OPE n n
ope-refl {zero}   = done
ope-refl {succ n} = keep ope-refl

ope-trans : OPE n m → OPE m k → OPE n k
ope-trans done g            = g
ope-trans f        (skip g) = skip (ope-trans f g)
ope-trans (skip f) (keep g) = skip (ope-trans f g)
ope-trans (keep f) (keep g) = keep (ope-trans f g)

{-          BASIC ASSIGNMENT 3          -}
-- Show how each OPE n m determines a map from Fin n → Fin m
⟦_⟧ : OPE n m → Fin n → Fin m
⟦ skip ope ⟧ i        = succ (⟦ ope ⟧ i)
⟦ keep ope ⟧ zero     = zero
⟦ keep ope ⟧ (succ i) = succ (⟦ ope ⟧ i)

{-          BASIC ASSIGNMENT 4          -}
-- Use this ⟦_⟧ function to define a renaming operation on expressions
rename : OPE n m → Expr n → Expr m
rename ope (val x)        = val x
rename ope (bin op e₁ e₂) = bin op (rename ope e₁) (rename ope e₂)
rename ope (var x)        = var (⟦ ope ⟧ x)
rename ope (bind e₁ e₂)   = bind (rename ope e₁) (rename (keep ope) e₂)

{-          BASIC ASSIGNMENT 5          -}
-- But this can also be used to project information out of a vector
--  (this is something that you couldn't do easily if we were working
--  with functions Fin n -> Fin m directly)
project : OPE n m → Vec ℕ m → Vec ℕ n
project ope xs = tabulate (λ x → lookup xs (⟦ ope ⟧ x))

{-          BASIC ASSIGNMENT 6          -}
-- Formulate a lemma and prove that renaming preserves semantics
-- (i.e. the eval function above)
helper : (ope : OPE n m) → (y : Fin n) → (xs : Vec ℕ m)
       → lookup (project ope xs) y ≡ lookup xs (⟦ ope ⟧ y)
helper _          zero      _       = refl
helper (skip ope) (succ y) (x ∷ xs) = helper ope (succ y) xs
helper (keep ope) (succ y) (x ∷ xs) = helper ope y xs

correct : (ope : OPE n m) → (e : Expr n) → (env : Vec ℕ m)
        → eval e (project ope env) ≡ eval (rename ope e) env
correct _   (val _)        _  = refl
correct ope (bin op e₁ e₂) xs = cong₂ op (correct ope e₁ xs) (correct ope e₂ xs)
correct ope (var y)        xs = helper ope y xs
correct ope (bind e₁ e₂)   xs =
  let
    ih₁ = correct ope e₁ xs
    ih₂ = correct (keep ope) e₂ (x ∷ xs)
  in
    eval e₂ (eval e₁ (project ope xs) ∷ project ope xs)
      ⟨ cong₂ {x₁ = e₂} eval refl (cong₂ _∷_ ih₁ refl) ⟩
    eval e₂ (x ∷ project ope xs)
      ⟨ cong₂ {x₁ = e₂} eval refl refl ⟩
    eval e₂ (project (keep ope) (x ∷ xs))
      ⟨ ih₂ ⟩
    eval (rename (keep ope) e₂) (x ∷ xs) ■
  where
    x = eval (rename ope e₁) xs

{-          BONUS ASSIGNMENT 1          -}
-- * prove that ope-refl and ope-trans behave 'as expected' with
-- respect to their semantics ⟦_⟧ (i.e. they correspond to the
-- identity function and function composition)
variable
  a b : Fin n

identity : ⟦ ope-refl ⟧ a ≡ a
identity {a = zero}   = refl
identity {a = succ a} = cong succ identity

compose : (f : OPE n m) → (g : OPE m k) → ⟦ ope-trans f g ⟧ a ≡ ⟦ g ⟧ (⟦ f ⟧ a)
compose (skip f) (skip g) = cong succ (compose (skip f) g)
compose (skip f) (keep g) = cong succ (compose f g)
compose (keep f) (skip g) = cong succ (compose (keep f) g)
compose {a = zero}   (keep _) (keep _) = refl
compose {a = succ _} (keep f) (keep g) = cong succ (compose f g)

{-          BONUS ASSIGNMENT 2          -}
-- * formulate an ordering on Fin n
data _≤_ : Fin n → Fin n → Set where
  base : zero ≤ b
  step : a ≤ b → succ a ≤ succ b

_≤?_ : Fin n → Fin n → Bool
zero   ≤? y      = true
succ x ≤? zero   = false
succ x ≤? succ y = x ≤? y

sound-≤ : {a ≤? b ≡ true} → a ≤ b
sound-≤ {a = zero} = base
sound-≤ {a = succ a} {b = succ b} {p} = step (sound-≤ {a = a} {b = b} {p})

-- * show that each OPE preserves ≤ (a soundness result)
sound-ope : (ope : OPE n m) → a ≤ b → ⟦ ope ⟧ a ≤ ⟦ ope ⟧ b
sound-ope (skip ope) base     = step (sound-ope ope base)
sound-ope (skip ope) (step p) = step (sound-ope ope (step p))
sound-ope (keep ope) base     = base
sound-ope (keep ope) (step p) = step (sound-ope ope p)

{-          BONUS ASSIGNMENT 3          -}
-- * show that each function Fin n → Fin m that is order preserving
-- gives rise to a unique OPE n m (a completeness result)
complete : (f : Fin n → Fin m) → a ≤ b → f a ≤ f b → OPE n m
complete f p q = {! q  !}

-- # Further ideas/projects:

-- * extend the Expr language with boolean constants, if then else,
-- and a _<_ operator - how can you change the types to still write a
-- total evaluator? Instead of tracking the number of bound variables,
-- you will need to keep track of the list of types of variables in
-- scope. How can you update the OPE accordingly?

-- * write a 'dead binding analysis' that maps each (e : Expr n) to a
-- pair (e' : Expr m) and (ope : OPE m n) such that: for any (env :
-- Vec n), evaluating e and e' with this environment returns the same
-- result.
