{-

  Typed optimize (Clos2ᵀ → Clos2ᵀ): a closure stops capturing the free
  variables that its code does not use, as the untyped pass
  (Untyped/Compiler/Optimize.agda).

  Closures are strict (they evaluate their free variables, which may
  err or diverge), so a free variable is dropped only when its code
  does not use it and it is a variable (enclose captures only
  variables). The flags (true: keep) say which free variables a closure
  keeps; its code is renamed by squeeze (Framework/Select.agda), which
  sends a kept variable to its new position, the argument to itself and
  the others (unused) to the argument. The pass carries a renaming r of
  the variables in scope.

-}

module Compiler.Optimize where

open import Language.Typed.Type using (Any)
open import Language.Typed.Clos2
open import Framework.VecSelect

open import Data.Bool using (Bool; true; false; T; _∨_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Nullary.Decidable using (isYes)

{- whether a term uses a variable: a closure's code is closed -}
uses : ∀ {k A} → Tm k A → Fin k → Bool
usesV : ∀ {k n} → Vec (Tm k Any) n → Fin k → Bool
uses (` y) x = isYes (x ≟ y)
uses (clos N Ms) x = usesV Ms x
uses (app L M) x = uses L x ∨ uses M x
uses (lit B c) x = false
uses (tuple Ms) x = usesV Ms x
uses (get i M) x = uses M x
uses (inl M) x = uses M x
uses (inr M) x = uses M x
uses (case L M N) x = uses L x ∨ (uses M (suc x) ∨ uses N (suc x))
uses (prim p L M) x = uses L x ∨ uses M x
uses (let′ M N) x = uses M x ∨ uses N (suc x)
uses (inject G M) x = uses M x
uses (project t M) x = uses M x
usesV [] x = false
usesV (M ∷ Ms) x = uses M x ∨ usesV Ms x

{- keep a free variable M when the code uses it (u) or it is not a variable -}
keep? : ∀ {k} → Tm k Any → Bool → Bool
keep? M true = true
keep? (` x) false = false
keep? M false = true

flags : ∀ {k n} → (Fin n → Bool) → Vec (Tm k Any) n → Vec Bool n
flags u [] = []
flags u (M ∷ Ms) = keep? M (u zero) ∷ flags (λ i → u (suc i)) Ms

{- the flags of a closure of code N and free variables Ms -}
keeps : ∀ {k n} → Tm (suc n) Any → Vec (Tm k Any) n → Vec Bool n
keeps N = flags (λ i → uses N (suc i))

opt : ∀ {k k' A} → (Fin k → Fin k') → Tm k A → Tm k' A
opts : ∀ {k k' n} → (Fin k → Fin k') → Vec (Tm k Any) n → Vec (Tm k' Any) n
opt r (` x) = ` r x
opt r (clos N Ms) = clos (opt (squeeze (keeps N Ms)) N) (select (keeps N Ms) (opts r Ms))
opt r (app L M) = app (opt r L) (opt r M)
opt r (lit B c) = lit B c
opt r (tuple Ms) = tuple (opts r Ms)
opt r (get i M) = get i (opt r M)
opt r (inl M) = inl (opt r M)
opt r (inr M) = inr (opt r M)
opt r (case L M N) = case (opt r L) (opt (ext r) M) (opt (ext r) N)
opt r (prim p L M) = prim p (opt r L) (opt r M)
opt r (let′ M N) = let′ (opt r M) (opt (ext r) N)
opt r (inject G M) = inject G (opt r M)
opt r (project t M) = project t (opt r M)
opts r [] = []
opts r (M ∷ Ms) = opt r M ∷ opts r Ms

optimize-program : ∀ {A} → Tm 0 A → Tm 0 A
optimize-program = opt (λ x → x)

{- What the flags say (for the proofs): a free variable is kept, or it
   is a variable that the code does not use -}
data Fl {k} : Bool → Bool → Tm k Any → Set where
  kept : ∀ {u M} → Fl u true M
  var : ∀ {u x} → ¬ T u → Fl u false (` x)

flags-ok : ∀ {k n} (u : Fin n → Bool) (Ms : Vec (Tm k Any) n) i → Fl (u i) (lookup (flags u Ms) i) (lookup Ms i)
flags-ok u (M ∷ Ms) zero = ok M (u zero)
  where ok : ∀ M u → Fl u (keep? M u) M
        ok M true = kept
        ok (` x) false = var (λ ())
        ok (app _ _) false = kept
        ok (get _ _) false = kept
        ok (case _ _ _) false = kept
        ok (let′ _ _) false = kept
        ok (inject _ _) false = kept
flags-ok u (M ∷ Ms) (suc i) = flags-ok (λ i → u (suc i)) Ms i

{- the code uses only the argument and kept free variables -}
covers : ∀ {k n fl} {N : Tm (suc n) Any} {Ms : Vec (Tm k Any) n}
  → (∀ i → Fl (uses N (suc i)) (lookup fl i) (lookup Ms i)) → ∀ x → T (uses N x) → Kept fl x
covers s zero _ = tt
covers s (suc i) = used (s i)
  where used : ∀ {u b M} → Fl u b M → T u → T b
        used kept _ = tt
        used (var ¬u) u = ⊥-elim (¬u u)
