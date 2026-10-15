{-

  The clocked interpreters of ISWIMμ and X86μ never err: a closed
  well-typed program only times out or returns a value, whose
  observation is an answer. The interpreters have no error case (their
  values are typed, so they take them apart with total functions), so
  the proof only follows their recursion: an interpreter is Safe at
  every clock (bind-safe), and no value is observed as o-error.

-}

module Mu.proof.Semantics.Interp.NoError where

open import Mu.Language.Type
open import Mu.Language.ISWIM using (Tm)
open import Mu.Language.X86 using (DSig; sig; called; Program; program; body; Body; Blocks; _▷_; Seq; _∷_; retq; jmp; case;
  movq; subq; cmpq; sete; alloc; load; loadfst; loadsnd; callq)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Observation using (Obs; o-error; Answer)
open import Semantics.Interp.Clock
import Mu.Semantics.Interp.Values as Values
import Mu.Semantics.Interp.ISWIM as I
import Mu.Semantics.Interp.Clos5 as C5
import Mu.Semantics.Interp.X86 as X

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

{- a result that is not an error -}
data Safe {A : Set} : Result A → Set where
  timeout : Safe timeout
  ret : ∀ v → Safe (ret v)

bind-safe : ∀ {A B : Set} {r : Result A} {f : A → Result B} → Safe r → (∀ v → Safe (f v)) → Safe (r >>= f)
bind-safe timeout h = timeout
bind-safe (ret v) h = h v

{- a semantics that is safe at every clock, and observes no value as an
   error, never terminates with o-error -}
no-error : ∀ {V} {obs : V → Obs} {r : ℕ → Result V} → (∀ v → Answer (obs v)) → (∀ ck → Safe (r ck))
  → ¬ Terminates (semantics V obs r) o-error
no-error {obs = obs} {r} ans safe (ck , t) = go (safe ck) t
  where
  go : ∀ {x} → Safe x → outcome obs x ≡ just o-error → _
  go timeout ()
  go (ret v) e = ans v (just-inj e)
    where
    just-inj : ∀ {a b : Obs} → just a ≡ just b → a ≡ b
    just-inj refl = refl

module Ans (C : Ctx → Type → Type → Set) where
  open Values C

  obs-answer : ∀ {A} (v : Val A) → Answer (obs v)
  obs-answer (code _) ()
  obs-answer (pack _ _) ()
  obs-answer (const _) ()
  obs-answer (tup _) ()
  obs-answer (inl _) ()
  obs-answer (inr _) ()
  obs-answer (fold v) = obs-answer v

  either-safe : ∀ {A B X} (u : Val (A ⊹ B)) {f : Val A → Result X} {g : Val B → Result X}
    → (∀ v → Safe (f v)) → (∀ v → Safe (g v)) → Safe (either u f g)
  either-safe (inl v) hf hg = hf v
  either-safe (inr v) hf hg = hg v

{- ISWIMμ ----------------------------------------------------------------------}

module _ where
  open import Mu.Language.ISWIM
  open I
  open Ans (λ Δ A B → Tm (A ∷ Δ) B)

  eval-safe : ∀ {Γ A} ck (ρ : Env Γ) (M : Tm Γ A) → Safe (eval ck ρ M)
  evals-safe : ∀ {Γ Δ} ck (ρ : Env Γ) (Ms : All (Tm Γ) Δ) → Safe (evals ck ρ Ms)
  call-safe : ∀ {A B} ck (f : Val (A ⇒ B)) (w : Val A) → Safe (call ck f w)

  eval-safe ck ρ (` x) = ret _
  eval-safe ck ρ (lam N) = ret _
  eval-safe ck ρ (app L M) =
    bind-safe (eval-safe ck ρ L) λ f → bind-safe (eval-safe ck ρ M) λ w → call-safe ck f w
  eval-safe ck ρ (lit B c) = ret _
  eval-safe ck ρ (tuple Ms) = bind-safe (evals-safe ck ρ Ms) λ _ → ret _
  eval-safe ck ρ (get i M) = bind-safe (eval-safe ck ρ M) λ _ → ret _
  eval-safe ck ρ (inl M) = bind-safe (eval-safe ck ρ M) λ _ → ret _
  eval-safe ck ρ (inr M) = bind-safe (eval-safe ck ρ M) λ _ → ret _
  eval-safe ck ρ (case L M N) =
    bind-safe (eval-safe ck ρ L) λ u → either-safe u (λ v → eval-safe ck (v ∷ ρ) M) (λ v → eval-safe ck (v ∷ ρ) N)
  eval-safe ck ρ (prim p L M) =
    bind-safe (eval-safe ck ρ L) λ _ → bind-safe (eval-safe ck ρ M) λ _ → ret _
  eval-safe ck ρ (let′ M N) = bind-safe (eval-safe ck ρ M) λ v → eval-safe ck (v ∷ ρ) N
  eval-safe ck ρ (fold M) = bind-safe (eval-safe ck ρ M) λ _ → ret _
  eval-safe ck ρ (unfold M) = bind-safe (eval-safe ck ρ M) λ _ → ret _

  evals-safe ck ρ [] = ret _
  evals-safe ck ρ (M ∷ Ms) = bind-safe (eval-safe ck ρ M) λ _ → bind-safe (evals-safe ck ρ Ms) λ _ → ret _

  call-safe zero f w = timeout
  call-safe (suc ck) (pack (code N) (tup ρ)) w = eval-safe ck (w ∷ ρ) N

  iswim-no-error : ∀ {A} (M : Tm [] A) → ¬ Terminates (sem M) o-error
  iswim-no-error M = no-error obs-answer λ ck → eval-safe ck [] M

{- X86μ ------------------------------------------------------------------------}

module _ {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ) where
  open C5.Vals Σ
  open Ans (λ Δ A B → Σ ∋ sig Δ A B)
  open X using (Mach; rv; ⟨_,_,_,_⟩)

  run-safe : ∀ {n R Bs ψ} ck (bs : Blocks Σ n R Bs) η (m : Mach Σ η ψ) (k : Seq Σ n R Bs ψ) → Safe (X.run ds ck bs η m k)
  jump-safe : ∀ {n R Bs Δ} ck (bs : Blocks Σ n R Bs) η (l : Bs ∋ Δ) (φ : Env Δ) → Safe (X.jump ds ck bs η l φ)
  callx-safe : ∀ {η A B} ck (c : Val (code η A B)) (e : Val (tup η)) (w : Val A) → Safe (X.call ds ck c e w)

  run-safe ck bs η m (movq a d ∷ k) = run-safe ck bs η _ k
  run-safe ck bs η m (subq a r e ∷ k) = run-safe ck bs η _ k
  run-safe ck bs η m (cmpq a₂ a₁ ∷ k) = run-safe ck bs η _ k
  run-safe ck bs η m (sete d ∷ k) = run-safe ck bs η _ k
  run-safe ck bs η m (alloc o d ∷ k) = run-safe ck bs η _ k
  run-safe ck bs η m (load i a d ∷ k) = run-safe ck bs η _ k
  run-safe ck bs η m (loadfst x r ∷ k) = run-safe ck bs _ _ k
  run-safe ck bs η m (loadsnd r ∷ k) = run-safe ck bs η _ k
  run-safe ck bs η m (callq a e₁ e₂ ∷ k) =
    bind-safe (callx-safe ck (X.arg a m) _ _) λ v → run-safe ck bs η ⟨ rv v _ _ , _ , _ , _ ⟩ k
  run-safe ck bs η m (retq e) = ret _
  run-safe ck bs η m (jmp l) = jump-safe ck bs η l _
  run-safe ck bs η m (case x p _ l₁ l₂) =
    either-safe (lookup (X.frame m) x) (λ v → jump-safe ck bs η l₁ _) (λ v → jump-safe ck bs η l₂ _)

  jump-safe ck (bs ▷ k) η Z φ = run-safe ck bs η _ k
  jump-safe ck (bs ▷ k) η (S l) φ = jump-safe ck bs η l φ

  callx-safe zero c e w = timeout
  callx-safe {η} (suc ck) (code f) e w = run-safe ck (Body.blocks (lookup ds f)) η _ (Body.start (lookup ds f))

x86-no-error : ∀ {A} (P : Program A) → ¬ Terminates (X.sem P) o-error
x86-no-error {A} (program {Σ} ds (body n bs k)) =
  no-error (Ans.obs-answer (λ Δ A B → Σ ∋ sig Δ A B)) λ ck → run-safe ds ck bs [] _ k
