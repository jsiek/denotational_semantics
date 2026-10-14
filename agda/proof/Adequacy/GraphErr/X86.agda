{-

  Soundness and adequacy of the graph model with errors
  (Semantics/GraphErr/Typed/X86.agda, ⟦_⟧ₜ) for the X86ᵀ machine
  (Semantics/CEK/Typed/X86.agda): as for ISWIM (GraphErr/ISWIM.agda),
  the denotation tells all three outcomes of the machine apart:

    error-iff     : ω ∈ ⟦ P ⟧ₜ exactly when the machine stops with an
                    error;
    const-iff     : const k ∈ ⟦ P ⟧ₜ exactly when it stops with k;
    converges-iff : ⟦ P ⟧ₜ has an element other than ω exactly when it
                    stops with an answer;
    diverges-iff  : ⟦ P ⟧ₜ is empty exactly when it diverges.

  X86ᵀ is intrinsically typed, so there is no condition on its labels or
  slots, but the semantics gives each definition the meanings of the
  older ones only, while the machine calls any: these hold for a program
  whose definitions' code depends only on the older ones (Indep), as
  for the programs of the compiler, and whose table is consistent, which
  the binders of the graph model need (OK; for compile-x86, see
  GraphErr/EndToEnd.agda).

  Soundness is in GraphErr/X86Soundness.agda, adequacy (the logical
  relation) in GraphErr/X86LogRel.agda. Divergence from emptiness is
  constructive, as for ISWIM.

-}

module proof.Adequacy.GraphErr.X86 where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; Con) renaming (const to dconst)
open import Language.Typed.X86 using (Program; program; body)
open import Semantics.GraphErr.Typed.X86 using (⟦_⟧ₜ)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep
  using (Terminates; Diverges; diverges-not-terminates; never-final-diverges)
open import Semantics.CEK.Typed.X86 using (sem; obs; Val)
import proof.Adequacy.GraphErr.X86Common as C
import proof.Adequacy.GraphErr.X86LogRel as LR
import proof.Adequacy.GraphErr.X86Soundness as S

open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_)

{- the table is consistent, and the code of each definition depends only on the older ones -}
OK : Program → Set₁
OK (program ds _) = (∀ k → Con (C.T⁺ ds k)) × C.Indep ds

{- every element is witnessed by a run: ω by one to an error, any other by one to a related value -}
adequacy : ∀ P → OK P → ∀ {d} → d ∈ ⟦ P ⟧ₜ
  → (d ≡ ω × Terminates (sem P) o-error) ⊎ Σ[ v ∈ Val _ _ ] Terminates (sem P) (obs v) × LR.𝕍 (Program.defs P) d v
adequacy (program ds (body n bs k)) ⟨ TC , ind ⟩ d∈ with LR.main-adeq ds TC ind (body n bs k) _ d∈
... | inj₁ ⟨ e , er ⟩ = let ⟨ t , ⟨ τ , q ⟩ ⟩ = er _ in inj₁ ⟨ e , ⟨ t , ⟨ C.↠→star ds τ , q ⟩ ⟩ ⟩
... | inj₂ ⟨ v , ⟨ ⟨ t , ⟨ τ , r ⟩ ⟩ , rv ⟩ ⟩ = inj₂ ⟨ v , ⟨ ⟨ t , ⟨ C.↠→star ds τ , C.ret-stop ds r ⟩ ⟩ , rv ⟩ ⟩

{- every run that stops gives an element: ω for an error, pt v for an answer v -}
soundness : ∀ P → (ok : OK P) → ∀ {o} → Terminates (sem P) o
  → (o ≡ o-error × ω ∈ ⟦ P ⟧ₜ) ⊎ Σ[ v ∈ Val _ _ ] o ≡ obs v × S.pt (Program.defs P) (proj₁ ok) (proj₂ ok) v ∈ ⟦ P ⟧ₜ
soundness (program ds (body n bs k)) ⟨ TC , ind ⟩ ⟨ s , ⟨ σ , q ⟩ ⟩ with S.final ds TC ind s q
... | inj₁ ⟨ e , ω∈ ⟩ = inj₁ ⟨ e , S.start-⊆ ds TC ind k bs _ (S.↠-⊆ ds TC ind tt (C.star→↠ ds σ) _ ω∈) ⟩
... | inj₂ ⟨ v , ⟨ e , p∈ ⟩ ⟩ = inj₂ ⟨ v , ⟨ e , S.start-⊆ ds TC ind k bs _ (S.↠-⊆ ds TC ind tt (C.star→↠ ds σ) _ p∈) ⟩ ⟩

{- Characterizations -----------------------------------------------------------------}

error-iff : ∀ P → OK P → (ω ∈ ⟦ P ⟧ₜ) ⇔ Terminates (sem P) o-error
error-iff P ok = ⟨ A , B ⟩
  where
  A : ω ∈ ⟦ P ⟧ₜ → Terminates (sem P) o-error
  A ω∈ with adequacy P ok ω∈
  ... | inj₁ ⟨ _ , t ⟩ = t
  ... | inj₂ ⟨ v , ⟨ _ , r ⟩ ⟩ = ⊥-elim (LR.𝕍-ω (Program.defs P) v r)
  B : Terminates (sem P) o-error → ω ∈ ⟦ P ⟧ₜ
  B t with soundness P ok t
  ... | inj₁ ⟨ _ , ω∈ ⟩ = ω∈
  ... | inj₂ ⟨ v , ⟨ e , _ ⟩ ⟩ = ⊥-elim (C.obs≢err (Program.defs P) v (sym e))

const-iff : ∀ P → OK P → ∀ {B} {k : base-rep B} → (dconst k ∈ ⟦ P ⟧ₜ) ⇔ Terminates (sem P) (o-const B k)
const-iff P ok {B} {k} = ⟨ A , G ⟩
  where
  A : dconst k ∈ ⟦ P ⟧ₜ → Terminates (sem P) (o-const B k)
  A k∈ with adequacy P ok k∈
  ... | inj₁ ⟨ () , _ ⟩
  ... | inj₂ ⟨ v , ⟨ t , r ⟩ ⟩ = subst (Terminates (sem P)) (LR.𝕍-const (Program.defs P) v r) t
  G : Terminates (sem P) (o-const B k) → dconst k ∈ ⟦ P ⟧ₜ
  G t with soundness P ok t
  ... | inj₁ ⟨ () , _ ⟩
  ... | inj₂ ⟨ v , ⟨ e , p∈ ⟩ ⟩ = subst (_∈ ⟦ P ⟧ₜ) (S.pt-const (Program.defs P) (proj₁ ok) (proj₂ ok) v e) p∈

converges-iff : ∀ P → OK P → (Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₜ × d ≢ ω) ⇔ Converges (Terminates (sem P))
converges-iff P ok = ⟨ A , B ⟩
  where
  A : (Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₜ × d ≢ ω) → Converges (Terminates (sem P))
  A ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ with adequacy P ok d∈
  ... | inj₁ ⟨ e , _ ⟩ = ⊥-elim (d≢ e)
  ... | inj₂ ⟨ v , ⟨ t , _ ⟩ ⟩ = ⟨ obs v , ⟨ C.obs≢err (Program.defs P) v , t ⟩ ⟩
  B : Converges (Terminates (sem P)) → Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₜ × d ≢ ω
  B ⟨ o , ⟨ ans , t ⟩ ⟩ with soundness P ok t
  ... | inj₁ ⟨ e , _ ⟩ = ⊥-elim (ans e)
  ... | inj₂ ⟨ v , ⟨ _ , p∈ ⟩ ⟩ = ⟨ _ , ⟨ p∈ , S.noω (Program.defs P) (proj₁ ok) (proj₂ ok) (S.pt∈ (Program.defs P) (proj₁ ok) (proj₂ ok) v) ⟩ ⟩

diverges-iff : ∀ P → OK P → Diverges (sem P) ⇔ (∀ d → ¬ (d ∈ ⟦ P ⟧ₜ))
diverges-iff P ok =
  ⟨ (λ div d d∈ → diverges-not-terminates div (proj₂ (terminates d∈)))
  , (λ empty → never-final-diverges (λ σ fin → [ (λ { ⟨ _ , ω∈ ⟩ → empty ω ω∈ }) , (λ { ⟨ _ , ⟨ _ , p∈ ⟩ ⟩ → empty _ p∈ }) ]′
                                                   (soundness P ok ⟨ _ , ⟨ σ , fin ⟩ ⟩))) ⟩
  where
  terminates : ∀ {d} → d ∈ ⟦ P ⟧ₜ → Σ[ o ∈ Obs ] Terminates (sem P) o
  terminates d∈ with adequacy P ok d∈
  ... | inj₁ ⟨ _ , t ⟩ = ⟨ o-error , t ⟩
  ... | inj₂ ⟨ v , ⟨ t , _ ⟩ ⟩ = ⟨ obs v , t ⟩
