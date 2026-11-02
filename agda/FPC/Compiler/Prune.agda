{-

  Prune (Closμ → Closμ), as typed prune (Compiler/Prune.agda):
  a closure stops capturing the free variables that its code does not
  use, provided that they are variables (closures are strict, so a free
  variable that is not a variable could err or diverge; capture
  captures only variables).

  The flags (true: keep) say which free variables a closure keeps; its
  code's context becomes the argument and the kept free variables
  (Mu/Framework/AllUtil.agda). Since the free variables have different
  types, an unused variable cannot be sent to the argument, as the
  typed pass does: the renaming is only defined on the variables a term
  uses (Ren u, given a proof that u holds of the variable), and the
  pass carries one for the variables in scope. For a closure's code, it
  is squeeze, which is defined on the kept variables, and the variables
  the code uses are kept (covers).

-}

module Mu.Compiler.Prune where

open import Mu.Language.Type
open import Mu.Language.Clos
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; Flags; kept; select; Kept; squeeze; ∨-l; ∨-r)

open import Data.Bool using (Bool; true; false; T; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_≟_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (isYes; fromWitness)

{- whether a term uses a variable: a closure's code is closed -}
uses : ∀ {Γ A C} → Tm Γ A → Γ ∋ C → Bool
usesA : ∀ {Γ Δ C} → All (Tm Γ) Δ → Γ ∋ C → Bool
uses (` y) x = isYes (idx x ≟ idx y)
uses (clos N Ms) x = usesA Ms x
uses (app L M) x = uses L x ∨ uses M x
uses (lit B c) x = false
uses (tuple Ms) x = usesA Ms x
uses (get i M) x = uses M x
uses (inl M) x = uses M x
uses (inr M) x = uses M x
uses (case L M N) x = uses L x ∨ (uses M (S x) ∨ uses N (S x))
uses (prim p L M) x = uses L x ∨ uses M x
uses (let′ M N) x = uses M x ∨ uses N (S x)
uses (fold M) x = uses M x
uses (unfold M) x = uses M x
usesA [] x = false
usesA (M ∷ Ms) x = uses M x ∨ usesA Ms x

{- keep a free variable M when the code uses it (u) or it is not a variable -}
keep? : ∀ {Γ C} → Tm Γ C → Bool → Bool
keep? M true = true
keep? (` x) false = false
keep? M false = true

flags : ∀ {Γ Δ} → (∀ {C} → Δ ∋ C → Bool) → All (Tm Γ) Δ → Flags Δ
flags u [] = []
flags u (M ∷ Ms) = keep? M (u Z) ∷ flags (λ x → u (S x)) Ms

{- the flags of a closure of code N and free variables Ms -}
keeps : ∀ {Γ Δ A B} → Tm (A ∷ Δ) B → All (Tm Γ) Δ → Flags Δ
keeps N = flags (λ x → uses N (S x))

{- the code uses only the argument and kept free variables -}
covers : ∀ {Γ Δ A B C} (N : Tm (A ∷ Δ) B) (Ms : All (Tm Γ) Δ) (x : (A ∷ Δ) ∋ C) → T (uses N x) → Kept (keeps N Ms) x
covers N Ms Z _ = tt
covers N Ms (S i) = used (λ x → uses N (S x)) Ms i
  where
  used : ∀ {Γ Δ C} (u : ∀ {C} → Δ ∋ C → Bool) (Ms : All (Tm Γ) Δ) (i : Δ ∋ C) → T (u i) → T (lookup (flags u Ms) i)
  used u (M ∷ Ms) Z t with u Z
  ... | true = tt
  used u (M ∷ Ms) (S i) t = used (λ x → u (S x)) Ms i t

{- a renaming of the variables in Γ that u holds of -}
Ren : ∀ {Γ} → (∀ {C} → Γ ∋ C → Bool) → Ctx → Set
Ren {Γ} u Γ' = ∀ {C} (x : Γ ∋ C) → T (u x) → Γ' ∋ C

{- the renaming for the body of a binder -}
ext : ∀ {Γ Γ' A} {u : ∀ {C} → (A ∷ Γ) ∋ C → Bool} → Ren (λ x → u (S x)) Γ' → Ren u (A ∷ Γ')
ext r Z _ = Z
ext r (S x) t = S (r x t)

opt : ∀ {Γ Γ' A} (M : Tm Γ A) → Ren (uses M) Γ' → Tm Γ' A
opts : ∀ {Γ Γ' Δ} (Ms : All (Tm Γ) Δ) → Ren (usesA Ms) Γ' → All (Tm Γ') Δ
opt (` x) r = ` r x (fromWitness refl)
opt (clos N Ms) r = clos (opt N λ x u → squeeze (keeps N Ms) x (covers N Ms x u)) (select (keeps N Ms) (opts Ms r))
opt (app L M) r = app (opt L λ x u → r x (∨-l _ u)) (opt M λ x u → r x (∨-r (uses L x) u))
opt (lit B c) r = lit B c
opt (tuple Ms) r = tuple (opts Ms r)
opt (get i M) r = get i (opt M r)
opt (inl M) r = inl (opt M r)
opt (inr M) r = inr (opt M r)
opt (case L M N) r =
  case (opt L λ x u → r x (∨-l _ u))
       (opt M (ext {u = uses M} λ x u → r x (∨-r (uses L x) (∨-l (uses N (S x)) u))))
       (opt N (ext {u = uses N} λ x u → r x (∨-r (uses L x) (∨-r (uses M (S x)) u))))
opt (prim p L M) r = prim p (opt L λ x u → r x (∨-l _ u)) (opt M λ x u → r x (∨-r (uses L x) u))
opt (let′ M N) r = let′ (opt M λ x u → r x (∨-l _ u)) (opt N (ext {u = uses N} λ x u → r x (∨-r (uses M x) u)))
opt (fold M) r = fold (opt M r)
opt (unfold M) r = unfold (opt M r)
opts [] r = []
opts (M ∷ Ms) r = opt M (λ x u → r x (∨-l _ u)) ∷ opts Ms (λ x u → r x (∨-r (uses M x) u))

prune-program : ∀ {A} → Tm [] A → Tm [] A
prune-program M = opt M (λ ())

{- What a flag says (for the proofs): a free variable is kept, or it is
   a variable -}
data Fl {Γ C} : Bool → Tm Γ C → Set where
  kept-fv : ∀ {M} → Fl true M
  var-fv : ∀ {x} → Fl false (` x)

fl-ok : ∀ {Γ C} (M : Tm Γ C) b → Fl (keep? M b) M
fl-ok M true = kept-fv
fl-ok (` x) false = var-fv
fl-ok (clos _ _) false = kept-fv
fl-ok (app _ _) false = kept-fv
fl-ok (lit _ _) false = kept-fv
fl-ok (tuple _) false = kept-fv
fl-ok (get _ _) false = kept-fv
fl-ok (inl _) false = kept-fv
fl-ok (inr _) false = kept-fv
fl-ok (case _ _ _) false = kept-fv
fl-ok (prim _ _ _) false = kept-fv
fl-ok (let′ _ _) false = kept-fv
fl-ok (fold _) false = kept-fv
fl-ok (unfold _) false = kept-fv
