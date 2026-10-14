{-

  Correctness of cast insertion (ISWIM → ISWIMᵀ, Compiler/Typed/Cast.agda)
  in the graph model with errors: the untyped semantics
  (Semantics/GraphErr/ISWIM.agda) and the typed one
  (Semantics/GraphErr/Typed/ISWIM.agda) are equal.

  By induction on the term, for environments that agree up to the
  renaming r of the pass. The kind errors move: the untyped operators
  check the kind of an operand in their kernel, the typed ones leave
  it to a project of the operand. One law relates the two (proj-≫=):
  a bind of project G D is a bind of D whose continuation is checked,
  by associativity and the check commuting with bind, when D is
  consistent and the kernel needs a value of the kind: then the values
  of D all have the kind, or none has, and both sides are the error
  (project-check; the typed meanings are consistent, as the untyped
  ones they equal). Then a typed
  app, get and case on a projected operand is the untyped ⋆ᵐ, projᵐ
  and 𝒞ᵐ (by definition), and the typed primitive on projected
  let-bound variables is the checked kernel of primᵐ. The untyped let
  is a bind (letᵐ-≫=) when the environment is nonempty and consistent
  (Wf), which holds under the binders.

-}

module proof.Correctness.Typed.GraphErr.CastCorrect where

open import Framework.Primitives using (Int)
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Ops using (⋆; proj; 𝒞; ⋆-mono; proj-mono)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env)
open import proof.Semantics.GraphErr.Prim
open import proof.Semantics.Graph.Prim using (primD-mono)
open import Language.ISWIM
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import proof.Semantics.GraphErr.ISWIM
open import Language.Typed.Type using (Flat; base; tup; sum; fun; _≟_)
open import Semantics.GraphErr.Typed.Ops using (kindᶠ; projectᵗ; primᵗ; appᵗ; getᵗ; caseᵗ)
import Semantics.GraphErr.Typed.ISWIM as T
open import Compiler.Typed.Cast

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.List using (replicate)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Language.Prim using (Prim)
open import Data.Empty using (⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (map′)

{- Checks and projects ----------------------------------------------------------}

⌊⌋-≃ : ∀ {D D'} → D ≃ D' → ⌊ D ⌋ ≃ ⌊ D' ⌋
⌊⌋-≃ e = ⟨ ⌊⌋-mono (proj₁ e) , ⌊⌋-mono (proj₂ e) ⟩

chk-≃ : ∀ {k X A A'} → A ≃ A' → checked k X A ≃ checked k X A'
chk-≃ e = ⟨ checked-mono (λ _ z → z) (proj₁ e) , checked-mono (λ _ z → z) (proj₂ e) ⟩

{- the kinds of the flat types are decidable -}
flat : Kind → Maybe Flat
flat fun = just fun
flat inj = just sum
flat (tup n) = just (tup n)
flat (base B) = just (base B)
flat _ = nothing

from-flat : ∀ k G → flat k ≡ just G → k ≡ kindᶠ G
from-flat fun _ refl = refl
from-flat inj _ refl = refl
from-flat (tup n) _ refl = refl
from-flat (base B) _ refl = refl

to-flat : ∀ G → flat (kindᶠ G) ≡ just G
to-flat (base B) = refl
to-flat (tup n) = refl
to-flat sum = refl
to-flat fun = refl

kind? : ∀ k G → Dec (k ≡ kindᶠ G)
kind? k G = map′ (from-flat k G) (λ { refl → to-flat G }) (≡-dec _≟_ (flat k) (just G))

{- on a consistent set of values, the check of a project is the check of
   a kernel that needs a value of that kind: either all values have the
   kind, or none, and then both are the error -}
project-check : ∀ G {X} K → Mono₁ K → Needs (kindᶠ G) X (K X) → Con X → Val X
  → checked (kindᶠ G) X ((X ⇂ λ d → kind d ≡ kindᶠ G) ≫= K) ≃ checked (kindᶠ G) X (K X)
project-check G K m nd c ⟨ cl , ⟨ d , d∈ ⟩ ⟩ with kind? (kind d) G
... | yes dk = chk-≃ (≃-trans (≫=-β m (λ e e∈ → cl e (proj₁ e∈)) ⟨ d , ⟨ d∈ , dk ⟩ ⟩)
                       ⟨ m ⇂-⊆ , m (λ e e∈ → ⟨ e∈ , trans (~-kind e d (c e d e∈ d∈)) dk ⟩) ⟩)
... | no dk = ⟨ (λ { w (inj₁ b) → inj₁ b ; w (inj₂ (inj₁ ⟨ _ , ⟨ ω∈ , _ ⟩ ⟩)) → ⊥-elim (cl ω ω∈ refl)
                   ; w (inj₂ (inj₂ ⟨ ⟨ e , ⟨ ⟨ e∈ , ek ⟩ , _ ⟩ ⟩ , _ ⟩)) → ⊥-elim (dk (trans (~-kind d e (c d e d∈ e∈)) ek)) })
              , (λ { w (inj₁ b) → inj₁ b ; w (inj₂ w∈) → [ (λ { refl → inj₁ ⟨ refl , ⟨ d , ⟨ d∈ , dk ⟩ ⟩ ⟩ })
                   , (λ { ⟨ u , ⟨ u∈ , uk ⟩ ⟩ → ⊥-elim (dk (trans (~-kind d u (c d u d∈ u∈)) uk)) }) ]′ (nd w w∈) }) ⟩

{- a bind of a project is a checked bind -}
proj-≫= : ∀ G {D} K → Mono₁ K → (∀ {X} → Needs (kindᶠ G) X (K X)) → Con D
  → (projectᵗ (kindᶠ G) D ≫= K) ≃ (D ≫= λ X → checked (kindᶠ G) X (K X))
proj-≫= G {D} K m nd cD = ≃-trans (≫=-assoc {D} {λ X → checked k X (X ⇂ λ d → kind d ≡ k)} m)
  (≫=-cong {D} {λ X → checked k X (X ⇂ λ d → kind d ≡ k) ≫= K} {λ X → checked k X (K X)} λ c →
     ≃-trans (checked-≫= {G = K} m) (project-check G K m nd (Con-⊆ cD ⌊⌋-⊆) ⟨ (λ _ d∈ → proj₂ d∈) , c ⟩))
  where k = kindᶠ G

proj-val : ∀ G {X} K → Mono₁ K → (∀ {X} → Needs (kindᶠ G) X (K X)) → Con X → Val X
  → (projectᵗ (kindᶠ G) X ≫= K) ≃ checked (kindᶠ G) X (K X)
proj-val G K m nd c ⟨ cl , ne ⟩ =
  ≃-trans (proj-≫= G K m nd c) (≫=-β {F = λ X → checked (kindᶠ G) X (K X)} (λ X⊆ → checked-mono X⊆ (m X⊆)) cl ne)

pmono : ∀ p {X X' Y Y'} → X ⊆ X' → Y ⊆ Y' → primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩ ⊆ primD p ⟨ X' , ⟨ Y' , ptt ⟩ ⟩
pmono p X⊆ Y⊆ = lower (primD-mono p _ _ ⟨ lift X⊆ , ⟨ lift Y⊆ , ptt ⟩ ⟩)

{- the kernel of primᵐ -}
Pk : Prim → 𝒫 Value → 𝒫 Value → 𝒫 Value
Pk p X Y = checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩))

Pk-≃ : ∀ p {X X' Y Y'} → X ≃ X' → Y ≃ Y' → Pk p X Y ≃ Pk p X' Y'
Pk-≃ p e f = ⟨ checked-mono (proj₁ e) (checked-mono (proj₁ f) (pmono p (proj₁ e) (proj₁ f)))
             , checked-mono (proj₂ e) (checked-mono (proj₂ f) (pmono p (proj₂ e) (proj₂ f))) ⟩

prim-proj : ∀ p {X Y} → Con X → Con Y → Val X → Val Y
  → primᵗ p (projectᵗ (base Int) X) (projectᵗ (base Int) Y) ≃ Pk p X Y
prim-proj p {X} {Y} cX cY vX vY =
  ≃-trans (proj-val (base Int) (λ A → projectᵗ (base Int) Y ≫= λ B → primD p ⟨ A , ⟨ B , ptt ⟩ ⟩)
             (λ {A} {A'} A⊆ → ≫=-mono {F = λ B → primD p ⟨ A , ⟨ B , ptt ⟩ ⟩} {λ B → primD p ⟨ A' , ⟨ B , ptt ⟩ ⟩}
                                         (λ _ z → z) (pmono p A⊆))
             (λ {A} → ≫=-needs {D = projectᵗ (base Int) Y} {λ B → primD p ⟨ A , ⟨ B , ptt ⟩ ⟩} λ { _ ⟨ n , ⟨ _ , ⟨ n∈ , _ ⟩ ⟩ ⟩ → inj₂ ⟨ const n , ⟨ n∈ , refl ⟩ ⟩ }) cX vX)
          (chk-≃ (proj-val (base Int) (λ B → primD p ⟨ X , ⟨ B , ptt ⟩ ⟩) (pmono p {X} {X} (λ _ z → z))
                    (λ { _ ⟨ _ , ⟨ m , ⟨ _ , ⟨ m∈ , _ ⟩ ⟩ ⟩ ⟩ → inj₂ ⟨ const m , ⟨ m∈ , refl ⟩ ⟩ }) cY vY))

{- the typed operators on a projected operand are the checked untyped ones -}
app-proj : ∀ {D} E → Con D → appᵗ (projectᵗ fun D) E ≃ ⋆ᵐ ⟨ D , ⟨ E , ptt ⟩ ⟩
app-proj E = proj-≫= fun (λ F → E ≫= λ X → ⋆ ⟨ F , ⟨ X , ptt ⟩ ⟩)
  (λ {F} {F'} F⊆ → ≫=-mono {F = λ X → ⋆ ⟨ F , ⟨ X , ptt ⟩ ⟩} {λ X → ⋆ ⟨ F' , ⟨ X , ptt ⟩ ⟩} (λ _ z → z)
                     λ X⊆ → lower (⋆-mono _ _ ⟨ lift F⊆ , ⟨ lift X⊆ , ptt ⟩ ⟩))
  (λ {F} → ≫=-needs {D = E} {λ X → ⋆ ⟨ F , ⟨ X , ptt ⟩ ⟩} λ {X} → ⋆-needs {F} {X})

get-proj : ∀ {n} (i : Fin n) {D} → Con D → getᵗ i (projectᵗ (tup n) D) ≃ projᵐ i ⟨ D , ptt ⟩
get-proj i = proj-≫= (tup _) (λ X → proj i ⟨ X , ptt ⟩) (λ X⊆ → lower (proj-mono i _ _ ⟨ lift X⊆ , ptt ⟩))
  (λ _ d∈ → inj₂ ⟨ _ , ⟨ d∈ , refl ⟩ ⟩)

case-proj : ∀ {D} F G → Con D → caseᵗ (projectᵗ inj D) F G ≃ 𝒞ᵐ ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
case-proj F G = proj-≫= sum (λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩)
  (λ X⊆ → 𝒞⇂-⊆ {A = F} {F} {G} {G} X⊆ (λ _ _ _ _ _ z → z) (λ _ _ _ _ _ z → z)) (λ {X} → 𝒞-needs {X} {ValPayload} {F} {G})

{- Environments --------------------------------------------------------------------}

Wf : Env Value → Set
Wf ρ = nonempty-env ρ × Con-env ρ

wf-• : ∀ {X ρ} → Wf ρ → nonempty X → Con X → Wf (X • ρ)
wf-• ⟨ ne , c ⟩ neX cX = ⟨ extend-nonempty-env ne neX , Con-• cX c ⟩

Agree : ∀ {k k'} → (Fin k → Fin k') → Env Value → Env Value → Set
Agree r ρ σ = ∀ x → ρ (toℕ x) ≃ σ (toℕ (r x))

agree-• : ∀ {k k'} {r : Fin k → Fin k'} {ρ σ X X'} → Agree r ρ σ → X ≃ X' → Agree (ext r) (X • ρ) (X' • σ)
agree-• R e zero = e
agree-• R e (suc x) = R x

{- The main lemma --------------------------------------------------------------------}

cc : ∀ {k k'} (r : Fin k → Fin k') M (w : WS k M) {ρ σ} → Wf ρ → Agree r ρ σ → ⟦ M ⟧ ρ ≃ T.⟦ cast r M w ⟧ σ
ccs : ∀ {k k' n} (r : Fin k → Fin k') (Ms : Args (replicate n ■)) (ws : WS-args k Ms) {ρ σ} → Wf ρ → Agree r ρ σ
  → ∀ i → nthD (⟦ Ms ⟧₊ ρ) i ≃ nthD (T.⟦ casts r Ms ws ⟧s σ) i

{- the typed meaning is consistent, as the untyped one is -}
con : ∀ {k k'} {r : Fin k → Fin k'} M (w : WS k M) {ρ σ} → Wf ρ → Agree r ρ σ → Con (T.⟦ cast r M w ⟧ σ)
con M w wf R = Con-⊆ (ISWIMᵐ-con M (proj₂ wf)) (proj₂ (cc _ M w wf R))

⌊con⌋ : ∀ {k k'} {r : Fin k → Fin k'} M (w : WS k M) {ρ σ} → Wf ρ → Agree r ρ σ → Con ⌊ T.⟦ cast r M w ⟧ σ ⌋
⌊con⌋ M w wf R = Con-⊆ (con M w wf R) ⌊⌋-⊆

{- a binder: the body on a finite consistent set of values -}
body : ∀ {k k'} (r : Fin k → Fin k') N (w : WS (suc k) N) {ρ σ} → Wf ρ → Agree r ρ σ
  → BodyEq (λ X → ⟦ N ⟧ (X • ρ)) (λ X → T.⟦ cast (ext r) N w ⟧ (X • σ))
body r N w wf R V ne c n = cc (ext r) N w (wf-• wf (proj₂ (noerr-val V ne n)) (≈⇒Con c)) (agree-• R ≃-refl)

cc r (` x) x<k {ρ} wf R = ≃-trans (≃-reflexive (cong ρ (sym (toℕ-fromℕ< x<k)))) (R _)
cc r (lam ⦅ ⟩ N ,, Nil ⦆) ⟨ w , _ ⟩ wf R = Λᵐ-≃ (body r N w wf R)
cc r (app ⦅ L ,, M ,, Nil ⦆) ⟨ wL , ⟨ wM , _ ⟩ ⟩ wf R =
  ≃-trans (⋆ᵐ-≃ (cc r L wL wf R) (cc r M wM wf R)) (≃-sym (app-proj _ (con L wL wf R)))
cc r (lit B k ⦅ Nil ⦆) _ wf R = ≃-refl
cc r (tuple n ⦅ Ms ⦆) w wf R = 𝒯ᵐ-≃ n (ccs r Ms w wf R)
cc r (get {n} i ⦅ M ,, Nil ⦆) ⟨ w , _ ⟩ wf R =
  ≃-trans (projᵐ-≃ i (cc r M w wf R)) (≃-sym (get-proj i (con M w wf R)))
cc r (inl-op ⦅ M ,, Nil ⦆) ⟨ w , _ ⟩ wf R = inlᵐ-≃ (cc r M w wf R)
cc r (inr-op ⦅ M ,, Nil ⦆) ⟨ w , _ ⟩ wf R = inrᵐ-≃ (cc r M w wf R)
cc r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟨ wL , ⟨ wM , ⟨ wN , _ ⟩ ⟩ ⟩ {ρ} {σ} wf R =
  ≃-trans (𝒞ᵐ-≃ {F = λ X → ⟦ M ⟧ (X • ρ)} {F'} {λ X → ⟦ N ⟧ (X • ρ)} {G'}
                 (cc r L wL wf R) (body r M wM wf R) (body r N wN wf R)) (≃-sym (case-proj F' G' (con L wL wf R)))
  where F' = λ X → T.⟦ cast (ext r) M wM ⟧ (X • σ)
        G' = λ X → T.⟦ cast (ext r) N wN ⟧ (X • σ)
cc r (prim p ⦅ L ,, M ,, Nil ⦆) ⟨ wL , ⟨ wM , _ ⟩ ⟩ {ρ} {σ} wf R =
  ≫=-≃ {F = λ X → ⟦ M ⟧ ρ ≫= λ Y → Pk p X Y}
       {λ X → T.⟦ cast (λ x → suc (r x)) M wM ⟧ (X • σ) ≫= λ Y → primᵗ p (projectᵗ (base Int) X) (projectᵗ (base Int) Y)}
       eL λ _ cL' → ≫=-≃ {F = Pk p ⌊ ⟦ L ⟧ ρ ⌋} {λ Y → primᵗ p (projectᵗ (base Int) ⌊ T.⟦ cast r L wL ⟧ σ ⌋) (projectᵗ (base Int) Y)}
         eM λ _ cM' →
    ≃-trans (Pk-≃ p (⌊⌋-≃ eL) (⌊⌋-≃ eM))
            (≃-sym (prim-proj p (⌊con⌋ L wL wf R) (⌊con⌋ M wM wf R) ⟨ (λ _ d∈ → proj₂ d∈) , cL' ⟩ ⟨ (λ _ d∈ → proj₂ d∈) , cM' ⟩))
  where eL = cc r L wL wf R
        eM = cc (λ x → suc (r x)) M wM wf R
cc r (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ⟨ wM , ⟨ wN , _ ⟩ ⟩ {ρ} {σ} wf R =
  ≃-trans (letᵐ-≫= (body-mono N ρ) cM λ c → body-continuous N ρ (proj₁ wf) _ c)
    (≫=-≃ {F = λ X → ⟦ N ⟧ (X • ρ)} {λ X → T.⟦ cast (ext r) N wN ⟧ (X • σ)} eM λ c _ →
       cc (ext r) N wN (wf-• wf c (Con-⊆ cM ⌊⌋-⊆)) (agree-• R (⌊⌋-≃ eM)))
  where eM = cc r M wM wf R
        cM = ISWIMᵐ-con M (proj₂ wf)

ccs {n = suc n} r (M ,, Ms) ⟨ w , ws ⟩ wf R zero = cc r M w wf R
ccs {n = suc n} r (M ,, Ms) ⟨ w , ws ⟩ wf R (suc i) = ccs r Ms ws wf R i

{- The end theorem: closed programs ----------------------------------------------}

cast-correct : ∀ (M : AST) (w : WS 0 M) → ⟦ M ⟧ ρ₀ ≃ T.⟦ cast-program M w ⟧ ρ₀
cast-correct M w = cc (λ x → x) M w ⟨ (λ _ → ⟨ ω , refl ⟩) , (λ _ → Con-⌈⌉ ω) ⟩ (λ ())
