{-

  Soundness of the reduction semantics of FPC
  (FPC/Semantics/ReductionSemantics/FPC.agda) with respect to the graph
  model (FPC/Semantics/GraphModel/FPC.agda), as Plotkin's for PCF: one
  step of reduction preserves the meaning of a closed term (step-≃),
  so a run does too (run-≃); and a closed term that does not reduce is
  a value (progress), which denotes a nonempty set (val-ne).

  A step is a congruence, whose meaning follows from the congruences of
  the graph model's operators (as for simplify,
  FPC/proof/Correctness/GraphModel/SimplifyCorrect.agda), or a redex.
  The redexes that bind (β, let, case) substitute a value for a
  variable, which the substitution lemma (sub-≃) turns into binding the
  value's denotation in the environment, and the graph model's β laws
  of simplify (let-β, case-inl, case-inr) then apply: a value denotes
  a nonempty, consistent set. The other redexes are those of simplify
  too: a component of a tuple, a primitive on two integers, and an
  unfold of a fold.

-}

module FPC.proof.Adequacy.ReductionSemantics.Soundness where

open import proof.Framework.GraphModel.Prelude hiding (ρ₀)
open import FPC.Semantics.GraphModel.Closed using (ρ₀)
open import proof.Framework.GraphModel.Ops using (⋆-≃; 𝒯-≃; proj-≃; inl-≃; inr-≃; nthD)
open import proof.Framework.GraphModel.TypedGraph using (proj-𝒯)
open import proof.Framework.GraphModel.Env using (nonempty-env)
open import proof.Semantics.Graph.Prim using (primD-≃)
import Language.Prim as P
open import Framework.Primitives using (Int)
open import FPC.Language.Type hiding (_[_])
open import FPC.Language.FPC
open import FPC.Language.FPCSubst using (exts; tmK; travs)
open import FPC.Compiler.Simplify using (prim-term)
open import FPC.proof.Compiler.SimplifyFacts using (SV; SVs)
import FPC.proof.Compiler.SimplifyFacts as F
open import FPC.proof.Semantics.GraphModel.FPC using (⟦_⟧; ⟦_⟧s; con)
open import FPC.proof.Semantics.GraphModel.Binders using (lam-≃; let-≃; case-≃)
open import FPC.proof.Correctness.GraphModel.SimplifyCorrect
  using (shift-≃; let-β; case-inl; case-inr; sv-ne; svs-ne; nth-lookup; prim-term-≃; prim-fold)
open import FPC.proof.Semantics.ReductionSemantics.FPC
  using (red; reds; sub; _[_]; β; get?; case?; prim?; unfold?; out; value-red; lam; lit; tuple; inl; inr; fold)
  renaming (Value to Val; _•_ to _•ₛ_; ∅ to ∅ₛ)
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup; pos)
open import Semantics.Observation using (Obs; o-error)
open import FPC.proof.Framework.ReductionAll Obs o-error using (Each; []; _∷_)
open import Semantics.Reduction.Smallstep using (Red; val; error; to; step-in)
open import proof.Framework.Reduction Obs o-error using (Star*; ε; _◅_; val-in)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (zero; suc)
open import Data.List using ([]; _∷_; length)
open import Data.Product using (Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

{- The substitution lemma --------------------------------------------------------}

{- as renaming (ren-≃, FPC/proof/Correctness/GraphModel/SimplifyCorrect.agda):
   a substitution σ, in an environment ρ', means binding each variable x
   to the meaning of σ x in ρ' -}
sub-≃ : ∀ {Γ Δ A} (σ : ∀ {B} → Γ ∋ B → Tm Δ B) (M : Tm Γ A) {ρ ρ'}
  → (∀ {B} (x : Γ ∋ B) → ⟦ σ x ⟧ ρ' ≃ ρ (idx x)) → ⟦ sub σ M ⟧ ρ' ≃ ⟦ M ⟧ ρ
subs-nth : ∀ {Γ Δ Δ'} (σ : ∀ {B} → Γ ∋ B → Tm Δ B) (Ms : All (Tm Γ) Δ') {ρ ρ'}
  → (∀ {B} (x : Γ ∋ B) → ⟦ σ x ⟧ ρ' ≃ ρ (idx x)) → ∀ i → nthD (⟦ travs tmK σ Ms ⟧s ρ') i ≃ nthD (⟦ Ms ⟧s ρ) i
sub-ext : ∀ {Γ Δ C} (σ : ∀ {B} → Γ ∋ B → Tm Δ B) {ρ ρ' X} → (∀ {B} (x : Γ ∋ B) → ⟦ σ x ⟧ ρ' ≃ ρ (idx x))
  → ∀ {B} (x : (C ∷ Γ) ∋ B) → ⟦ exts tmK σ x ⟧ (X • ρ') ≃ (X • ρ) (idx x)
sub-ext σ h Z = ≃-refl
sub-ext σ h (S x) = ≃-trans (shift-≃ (σ x) _ _) (h x)
sub-≃ σ (` x) h = h x
sub-≃ σ (lam N) {ρ} {ρ'} h = lam-≃ λ X _ _ → sub-≃ (exts tmK σ) N {X • ρ} {X • ρ'} (sub-ext σ h)
sub-≃ σ (app L M) h = ⋆-≃ (sub-≃ σ L h) (sub-≃ σ M h)
sub-≃ σ (lit B c) h = ≃-refl
sub-≃ σ (tuple {Δ} Ms) h = 𝒯-≃ (length Δ) (subs-nth σ Ms h)
sub-≃ σ (get i M) h = proj-≃ (pos i) (sub-≃ σ M h)
sub-≃ σ (inl M) h = inl-≃ (sub-≃ σ M h)
sub-≃ σ (inr M) h = inr-≃ (sub-≃ σ M h)
sub-≃ σ (case L M N) {ρ} {ρ'} h = case-≃ (sub-≃ σ L h)
  (λ X _ _ → sub-≃ (exts tmK σ) M {X • ρ} {X • ρ'} (sub-ext σ h)) (λ X _ _ → sub-≃ (exts tmK σ) N {X • ρ} {X • ρ'} (sub-ext σ h))
sub-≃ σ (prim p L M) h = primD-≃ p (sub-≃ σ L h) (sub-≃ σ M h)
sub-≃ σ (let′ M N) {ρ} {ρ'} h = let-≃ (sub-≃ σ M h) λ X _ _ → sub-≃ (exts tmK σ) N {X • ρ} {X • ρ'} (sub-ext σ h)
sub-≃ σ (fold M) h = sub-≃ σ M h
sub-≃ σ (unfold M) h = sub-≃ σ M h
subs-nth σ (M ∷ Ms) h zero = sub-≃ σ M h
subs-nth σ (M ∷ Ms) h (suc i) = subs-nth σ Ms h i

{- substituting a closed W for the variable of N -}
[]-≃ : ∀ {A B} (N : Tm (A ∷ []) B) (W : Tm [] A) → ⟦ N [ W ] ⟧ ρ₀ ≃ ⟦ N ⟧ (⟦ W ⟧ ρ₀ • ρ₀)
[]-≃ N W = sub-≃ (W •ₛ ∅ₛ) N (λ { Z → ≃-refl })

{- Values ---------------------------------------------------------------------------}

ne₀ : nonempty-env ρ₀
ne₀ _ = ⟨ ⟨⟩ , refl ⟩

con₀ : Con-env ρ₀
con₀ _ = Con-⌈⌉ ⟨⟩

{- a value of the reduction semantics is one of simplify -}
val-sv : ∀ {A} {V : Tm [] A} → Val V → SV V
vals-svs : ∀ {Δ} {Vs : All (Tm []) Δ} → Each Val Vs → SVs Vs
val-sv lam = F.lam
val-sv lit = F.lit
val-sv (tuple vs) = F.tuple (vals-svs vs)
val-sv (inl v) = F.inl (val-sv v)
val-sv (inr v) = F.inr (val-sv v)
val-sv (fold v) = F.fold (val-sv v)
vals-svs [] = F.[]
vals-svs (v ∷ vs) = val-sv v F.∷ vals-svs vs

{- so it denotes a nonempty set -}
val-ne : ∀ {A} {V : Tm [] A} → Val V → nonempty (⟦ V ⟧ ρ₀)
val-ne v = sv-ne (val-sv v) ne₀

{- Progress -------------------------------------------------------------------------}

in-ctx : ∀ {X Y : Set} {f : X → Y} {r : Red X} {k M} → r ≡ to M → step-in f r k ≡ to (f M)
in-ctx refl = refl

{- a closed term is a value, or it reduces (it is never stuck) -}
progress : ∀ {A} (M : Tm [] A) → Val M ⊎ Σ[ N ∈ Tm [] A ] red M ≡ to N
progresses : ∀ {Δ} (Ms : All (Tm []) Δ) → Each Val Ms ⊎ Σ[ Ns ∈ All (Tm []) Δ ] reds Ms ≡ to Ns
progress (` ())
progress (lam N) = inj₁ lam
progress (app L M) with progress L
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
... | inj₁ (lam {N = N}) with progress M
...   | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx {f = app (lam N)} e ⟩
...   | inj₁ w = inj₂ ⟨ N [ M ] , val-in (value-red w) ⟩
progress (lit B c) = inj₁ lit
progress (tuple Ms) with progresses Ms
... | inj₁ vs = inj₁ (tuple vs)
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
progress (get i M) with progress M
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
... | inj₁ (tuple {Vs = Vs} vs) = inj₂ ⟨ lookup Vs i , val-in (value-red (tuple vs)) ⟩
progress (inl M) with progress M
... | inj₁ v = inj₁ (inl v)
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
progress (inr M) with progress M
... | inj₁ v = inj₁ (inr v)
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
progress (case L M N) with progress L
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
... | inj₁ (inl {V = V} v) =
  inj₂ ⟨ M [ V ] , val-in (value-red (inl v)) ⟩
... | inj₁ (inr {V = V} v) =
  inj₂ ⟨ N [ V ] , val-in (value-red (inr v)) ⟩
progress (prim p L M) with progress L
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
... | inj₁ (lit {c = n}) with progress M
...   | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx {f = prim p (lit _ n)} e ⟩
...   | inj₁ (lit {c = m}) = inj₂ ⟨ out p n m , refl ⟩
progress (let′ M N) with progress M
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
... | inj₁ v = inj₂ ⟨ N [ M ] , val-in (value-red v) ⟩
progress (fold M) with progress M
... | inj₁ v = inj₁ (fold v)
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
progress (unfold M) with progress M
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
... | inj₁ (fold {V = V} v) = inj₂ ⟨ V , val-in (value-red (fold v)) ⟩
progresses [] = inj₁ []
progresses (M ∷ Ms) with progress M
... | inj₂ ⟨ _ , e ⟩ = inj₂ ⟨ _ , in-ctx e ⟩
... | inj₁ v with progresses Ms
...   | inj₁ vs = inj₁ (v ∷ vs)
...   | inj₂ ⟨ _ , e ⟩ =
  inj₂ ⟨ _ , trans (val-in (value-red v)) (in-ctx e) ⟩

{- a closed term that reduces to val is a value -}
val-value : ∀ {A} (M : Tm [] A) → red M ≡ val → Val M
val-value M e with progress M
... | inj₁ v = v
... | inj₂ ⟨ _ , e' ⟩ with trans (sym e) e'
...   | ()

{- One step preserves meaning -------------------------------------------------------}

{- the output of a primitive is simplify's -}
out-≡ : ∀ {Γ} p n m → out {Γ} p n m ≡ prim-term p n m
out-≡ P.sub n m = refl
out-≡ P.eq n m = refl

β-≃ : ∀ {A B} (N : Tm (A ∷ []) B) (W : Tm [] A) → Val W → ⟦ app (lam N) W ⟧ ρ₀ ≃ ⟦ N [ W ] ⟧ ρ₀
β-≃ N W w = ≃-trans (let-β N ρ₀ (⟦ W ⟧ ρ₀) ne₀ (val-ne w) (con W con₀)) (≃-sym ([]-≃ N W))

step-≃ : ∀ {A} (M : Tm [] A) {N} → red M ≡ to N → ⟦ M ⟧ ρ₀ ≃ ⟦ N ⟧ ρ₀
steps-≃ : ∀ {Δ} (Ms : All (Tm []) Δ) {Ns} → reds Ms ≡ to Ns → ∀ i → nthD (⟦ Ms ⟧s ρ₀) i ≃ nthD (⟦ Ns ⟧s ρ₀) i
step-≃ (` ())
step-≃ (lam N) ()
step-≃ (app L M) e with red L in eL
step-≃ (app L M) refl | to L' = ⋆-≃ (step-≃ L eL) (≃-refl {D = ⟦ M ⟧ ρ₀})
step-≃ (app L M) () | error
step-≃ (app L M) e | val with val-value L eL
step-≃ (app (lam N) M) e | val | lam with red M in eM
step-≃ (app (lam N) M) refl | val | lam | to M' = ⋆-≃ (≃-refl {D = ⟦ lam N ⟧ ρ₀}) (step-≃ M eM)
step-≃ (app (lam N) M) () | val | lam | error
step-≃ (app (lam N) M) refl | val | lam | val = β-≃ N M (val-value M eM)
step-≃ (lit B c) ()
step-≃ (tuple {Δ} Ms) e with reds Ms in eMs
step-≃ (tuple {Δ} Ms) refl | to Ms' = 𝒯-≃ (length Δ) (steps-≃ Ms eMs)
step-≃ (tuple Ms) () | error
step-≃ (tuple Ms) () | val
step-≃ (get i M) e with red M in eM
step-≃ (get i M) refl | to M' = proj-≃ (pos i) (step-≃ M eM)
step-≃ (get i M) () | error
step-≃ (get i M) e | val with val-value M eM
step-≃ (get {Δ} i (tuple Vs)) refl | val | tuple vs =
  ≃-trans (proj-𝒯 (length Δ) (svs-ne (vals-svs vs) ne₀) (pos i)) (≃-reflexive (nth-lookup Vs i ρ₀))
step-≃ (inl M) e with red M in eM
step-≃ (inl M) refl | to M' = inl-≃ (step-≃ M eM)
step-≃ (inl M) () | error
step-≃ (inl M) () | val
step-≃ (inr M) e with red M in eM
step-≃ (inr M) refl | to M' = inr-≃ (step-≃ M eM)
step-≃ (inr M) () | error
step-≃ (inr M) () | val
step-≃ (case L M N) e with red L in eL
step-≃ (case L M N) refl | to L' = case-≃ {F = λ X → ⟦ M ⟧ (X • ρ₀)} {G = λ X → ⟦ N ⟧ (X • ρ₀)} (step-≃ L eL)
  (λ _ _ _ → ≃-refl) (λ _ _ _ → ≃-refl)
step-≃ (case L M N) () | error
step-≃ (case L M N) e | val with val-value L eL
step-≃ (case (inl V) M N) refl | val | inl v =
  ≃-trans (case-inl (inl V) M N ρ₀ (⟦ V ⟧ ρ₀) ≃-refl ne₀ (val-ne v) (con V con₀)) (≃-sym ([]-≃ M V))
step-≃ (case (inr V) M N) refl | val | inr v =
  ≃-trans (case-inr (inr V) M N ρ₀ (⟦ V ⟧ ρ₀) ≃-refl ne₀ (val-ne v) (con V con₀)) (≃-sym ([]-≃ N V))
step-≃ (prim p L M) e with red L in eL
step-≃ (prim p L M) refl | to L' = primD-≃ p (step-≃ L eL) (≃-refl {D = ⟦ M ⟧ ρ₀})
step-≃ (prim p L M) () | error
step-≃ (prim p L M) e | val with val-value L eL
step-≃ (prim p (lit _ n) M) e | val | lit with red M in eM
step-≃ (prim p (lit _ n) M) refl | val | lit | to M' = primD-≃ p (≃-refl {D = ⟦ lit {[]} Int n ⟧ ρ₀}) (step-≃ M eM)
step-≃ (prim p (lit _ n) M) () | val | lit | error
step-≃ (prim p (lit _ n) M) e | val | lit | val with val-value M eM
step-≃ (prim p (lit _ n) (lit _ m)) refl | val | lit | val | lit =
  ≃-trans (prim-fold p n m) (≃-trans (prim-term-≃ p n m ρ₀) (≃-reflexive (cong (λ T → ⟦ T ⟧ ρ₀) (sym (out-≡ p n m)))))
step-≃ (let′ M N) e with red M in eM
step-≃ (let′ M N) refl | to M' = let-≃ {F = λ X → ⟦ N ⟧ (X • ρ₀)} (step-≃ M eM) (λ _ _ _ → ≃-refl)
step-≃ (let′ M N) () | error
step-≃ (let′ M N) refl | val = β-≃ N M (val-value M eM)
step-≃ (fold M) e with red M in eM
step-≃ (fold M) refl | to M' = step-≃ M eM
step-≃ (fold M) () | error
step-≃ (fold M) () | val
step-≃ (unfold M) e with red M in eM
step-≃ (unfold M) refl | to M' = step-≃ M eM
step-≃ (unfold M) () | error
step-≃ (unfold M) e | val with val-value M eM
step-≃ (unfold (fold V)) refl | val | fold v = ≃-refl
steps-≃ [] ()
steps-≃ (M ∷ Ms) e i with red M in eM
steps-≃ (M ∷ Ms) refl zero | to M' = step-≃ M eM
steps-≃ (M ∷ Ms) refl (suc i) | to M' = ≃-refl
steps-≃ (M ∷ Ms) () i | error
steps-≃ (M ∷ Ms) e i | val with reds Ms in eMs
steps-≃ (M ∷ Ms) refl zero | val | to Ms' = ≃-refl
steps-≃ (M ∷ Ms) refl (suc i) | val | to Ms' = steps-≃ Ms eMs i
steps-≃ (M ∷ Ms) () i | val | error
steps-≃ (M ∷ Ms) () i | val | val

{- and so does a run -}
run-≃ : ∀ {A} {M N : Tm [] A} → Star* red M N → ⟦ M ⟧ ρ₀ ≃ ⟦ N ⟧ ρ₀
run-≃ ε = ≃-refl
run-≃ {M = M} (s ◅ σ) = ≃-trans (step-≃ M s) (run-≃ σ)
