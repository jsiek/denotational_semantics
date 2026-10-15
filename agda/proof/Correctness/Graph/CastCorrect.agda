{-

  Correctness of cast insertion (ISWIM → ISWIMᵀ, Compiler/Cast.agda)
  in the graph model: the untyped semantics (Semantics/Graph/ISWIM.agda)
  and the typed one (Semantics/Graph/Typed/ISWIM.agda) are equal.

  By induction on the term, for environments that agree up to the
  renaming r of the pass. A project is a guard (it keeps its operand
  when the operand has an element of the tag), and the untyped operators
  use only such elements: ⋆ the entries of a function, proj i the
  components i, 𝒞 the injections and primD the integers. So a typed
  app, get, case or primitive on projected operands is the untyped one.
  The two lets of a primitive bind its operands, which it needs one
  element of each (let-single).

-}

module proof.Correctness.Graph.CastCorrect where

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.TypedGraph using (let-single)
open import proof.Semantics.Graph.Prim using (primD; primD-≃; primD-mono)
open import Language.ISWIM
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import proof.Semantics.Graph.ISWIM
open import Compiler.EncloseScope using (Closed)
open import proof.Compiler.SimplifyScope using (closed-ws)
open import proof.Compiler.CastScope using (cast-closed-≡)
open import Language.Typed.Type using (tfun; tint; tsum; ttup)
open import Semantics.Graph.Typed.Ops using (projectᵍ; fun₂)
import Semantics.Graph.Typed.ISWIM as T
open import Compiler.Cast

open import Data.Nat using (suc)
open import Data.Fin using (Fin; zero; suc; toℕ)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.List using (replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym)

{- The untyped operators on projected operands ----------------------------------}

G : _ → 𝒫 Value → 𝒫 Value
G t = projectᵍ fun₂ t

app-proj : ∀ {D E} → ⋆ ⟨ G tfun D , ⟨ E , ptt ⟩ ⟩ ≃ ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩
app-proj = ⟨ (λ { w ⟨ V , ⟨ ⟨ _ , e∈ ⟩ , r ⟩ ⟩ → ⟨ V , ⟨ e∈ , r ⟩ ⟩ })
           , (λ { w ⟨ V , ⟨ e∈ , r ⟩ ⟩ → ⟨ V , ⟨ ⟨ ⟨ V ↦ w , ⟨ e∈ , tt ⟩ ⟩ , e∈ ⟩ , r ⟩ ⟩ }) ⟩

get-proj : ∀ {n} (i : Fin (suc n)) {D} → proj i ⟨ G (ttup n i) D , ptt ⟩ ≃ proj i ⟨ D , ptt ⟩
get-proj i = ⟨ (λ _ d∈ → proj₂ d∈) , (λ d d∈ → ⟨ ⟨ tup[ i ] d , ⟨ d∈ , ⟨ d , refl ⟩ ⟩ ⟩ , d∈ ⟩) ⟩

case-proj : ∀ {D F F'} → 𝒞 ⟨ G tsum D , ⟨ F , ⟨ F' , ptt ⟩ ⟩ ⟩ ≃ 𝒞 ⟨ D , ⟨ F , ⟨ F' , ptt ⟩ ⟩ ⟩
case-proj = ⟨ (λ { w (inj₁ ⟨ v , ⟨ V , ⟨ all , r ⟩ ⟩ ⟩) → inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ (all d d∈)) , r ⟩ ⟩ ⟩
                 ; w (inj₂ ⟨ v , ⟨ V , ⟨ all , r ⟩ ⟩ ⟩) → inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → proj₂ (all d d∈)) , r ⟩ ⟩ ⟩ })
            , (λ { w (inj₁ ⟨ v , ⟨ V , ⟨ all , r ⟩ ⟩ ⟩) →
                     inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → ⟨ ⟨ left v , ⟨ all v (here refl) , inj₁ ⟨ v , refl ⟩ ⟩ ⟩ , all d d∈ ⟩) , r ⟩ ⟩ ⟩
                 ; w (inj₂ ⟨ v , ⟨ V , ⟨ all , r ⟩ ⟩ ⟩) →
                     inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → ⟨ ⟨ right v , ⟨ all v (here refl) , inj₂ ⟨ v , refl ⟩ ⟩ ⟩ , all d d∈ ⟩) , r ⟩ ⟩ ⟩ }) ⟩

prim-proj : ∀ p {X Y} → primD p ⟨ G tint X , ⟨ G tint Y , ptt ⟩ ⟩ ≃ primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩
prim-proj p = ⟨ (λ { w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , e ⟩ ⟩ ⟩ ⟩ → ⟨ n , ⟨ m , ⟨ proj₂ n∈ , ⟨ proj₂ m∈ , e ⟩ ⟩ ⟩ ⟩ })
              , (λ { w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , e ⟩ ⟩ ⟩ ⟩ →
                  ⟨ n , ⟨ m , ⟨ ⟨ ⟨ _ , ⟨ n∈ , ⟨ n , refl ⟩ ⟩ ⟩ , n∈ ⟩ , ⟨ ⟨ ⟨ _ , ⟨ m∈ , ⟨ m , refl ⟩ ⟩ ⟩ , m∈ ⟩ , e ⟩ ⟩ ⟩ ⟩ }) ⟩

pmono : ∀ p {X X' Y Y'} → X ⊆ X' → Y ⊆ Y' → primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩ ⊆ primD p ⟨ X' , ⟨ Y' , ptt ⟩ ⟩
pmono p X⊆ Y⊆ = lower (primD-mono p _ _ ⟨ lift X⊆ , ⟨ lift Y⊆ , ptt ⟩ ⟩)

{- a primitive needs one integer of each operand -}
let-prim₁ : ∀ p {D E} → letD ⟨ D , ⟨ (λ X → primD p ⟨ X , ⟨ E , ptt ⟩ ⟩) , ptt ⟩ ⟩ ≃ primD p ⟨ D , ⟨ E , ptt ⟩ ⟩
let-prim₁ p {D} {E} = let-single {F = λ X → primD p ⟨ X , ⟨ E , ptt ⟩ ⟩} (λ {X} {X'} X⊆ → pmono p {X} {X'} {E} {E} X⊆ (λ _ z → z))
  λ { w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , e ⟩ ⟩ ⟩ ⟩ → ⟨ _ , ⟨ n∈ , ⟨ n , ⟨ m , ⟨ here refl , ⟨ m∈ , e ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ }

let-prim₂ : ∀ p {D E} → letD ⟨ E , ⟨ (λ Y → primD p ⟨ D , ⟨ Y , ptt ⟩ ⟩) , ptt ⟩ ⟩ ≃ primD p ⟨ D , ⟨ E , ptt ⟩ ⟩
let-prim₂ p {D} {E} = let-single {F = λ Y → primD p ⟨ D , ⟨ Y , ptt ⟩ ⟩} (λ {Y} {Y'} Y⊆ → pmono p {D} {D} {Y} {Y'} (λ _ z → z) Y⊆)
  λ { w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , e ⟩ ⟩ ⟩ ⟩ → ⟨ _ , ⟨ m∈ , ⟨ n , ⟨ m , ⟨ n∈ , ⟨ here refl , e ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ }

{- Environments --------------------------------------------------------------------}

Agree : ∀ {k k'} → (Fin k → Fin k') → Env Value → Env Value → Set
Agree r ρ σ = ∀ x → ρ (toℕ x) ≃ σ (toℕ (r x))

agree-• : ∀ {k k'} {r : Fin k → Fin k'} {ρ σ X} → Agree r ρ σ → Agree (ext r) (X • ρ) (X • σ)
agree-• R zero = ≃-refl
agree-• R (suc x) = R x

{- The main lemma --------------------------------------------------------------------}

cc : ∀ {k k'} (r : Fin k → Fin k') M (w : WS k M) {ρ σ} → Agree r ρ σ → ⟦ M ⟧ ρ ≃ T.⟦ cast r M w ⟧ σ
ccs : ∀ {k k' n} (r : Fin k → Fin k') (Ms : Args (replicate n ■)) (ws : WS-args k Ms) {ρ σ} → Agree r ρ σ
  → ∀ i → nthD (⟦ Ms ⟧₊ ρ) i ≃ nthD (T.⟦ casts r Ms ws ⟧s σ) i

cc r (` x) x<k {ρ} R = ≃-trans (≃-reflexive (cong ρ (sym (toℕ-fromℕ< x<k)))) (R _)
cc r (lam ⦅ ⟩ N ,, Nil ⦆) ⟨ w , _ ⟩ R = Λ-≃ λ _ _ _ → cc (ext r) N w (agree-• R)
cc r (app ⦅ L ,, M ,, Nil ⦆) ⟨ wL , ⟨ wM , _ ⟩ ⟩ R = ≃-trans (⋆-≃ (cc r L wL R) (cc r M wM R)) (≃-sym app-proj)
cc r (lit B k ⦅ Nil ⦆) _ R = ≃-refl
cc r (tuple n ⦅ Ms ⦆) w R = 𝒯-≃ n (ccs r Ms w R)
cc r (get {suc n} i ⦅ M ,, Nil ⦆) ⟨ w , _ ⟩ R = ≃-trans (proj-≃ i (cc r M w R)) (≃-sym (get-proj i))
cc r (inl-op ⦅ M ,, Nil ⦆) ⟨ w , _ ⟩ R = inl-≃ (cc r M w R)
cc r (inr-op ⦅ M ,, Nil ⦆) ⟨ w , _ ⟩ R = inr-≃ (cc r M w R)
cc r (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟨ wL , ⟨ wM , ⟨ wN , _ ⟩ ⟩ ⟩ {ρ} {σ} R =
  ≃-trans (𝒞-≃ {F = λ X → ⟦ M ⟧ (X • ρ)} {λ X → T.⟦ cast (ext r) M wM ⟧ (X • σ)}
                {λ X → ⟦ N ⟧ (X • ρ)} {λ X → T.⟦ cast (ext r) N wN ⟧ (X • σ)}
                (cc r L wL R) (λ _ _ _ → cc (ext r) M wM (agree-• R)) (λ _ _ _ → cc (ext r) N wN (agree-• R)))
    (≃-sym (case-proj {F = λ X → T.⟦ cast (ext r) M wM ⟧ (X • σ)} {λ X → T.⟦ cast (ext r) N wN ⟧ (X • σ)}))
cc r (prim p ⦅ L ,, M ,, Nil ⦆) ⟨ wL , ⟨ wM , _ ⟩ ⟩ {ρ} {σ} R =
  ≃-sym (≃-trans (letD-≃ {F = λ X → letD ⟨ M' X , ⟨ (λ Y → primD p ⟨ G tint X , ⟨ G tint Y , ptt ⟩ ⟩) , ptt ⟩ ⟩}
                          {λ X → primD p ⟨ X , ⟨ ⟦ M ⟧ ρ , ptt ⟩ ⟩} (≃-sym (cc r L wL R)) inner)
                 (let-prim₁ p {⟦ L ⟧ ρ} {⟦ M ⟧ ρ}))
  where
  M' = λ X → T.⟦ cast (λ x → suc (r x)) M wM ⟧ (X • σ)
  inner = λ V _ _ → ≃-trans (letD-≃ {F = λ Y → primD p ⟨ G tint (mem V) , ⟨ G tint Y , ptt ⟩ ⟩}
                                     {λ Y → primD p ⟨ mem V , ⟨ Y , ptt ⟩ ⟩}
                                     (≃-sym (cc (λ x → suc (r x)) M wM R)) (λ _ _ _ → prim-proj p))
                            (let-prim₂ p {mem V} {⟦ M ⟧ ρ})
cc r (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ⟨ wM , ⟨ wN , _ ⟩ ⟩ {ρ} {σ} R =
  letD-≃ {F = λ X → ⟦ N ⟧ (X • ρ)} {λ X → T.⟦ cast (ext r) N wN ⟧ (X • σ)} (cc r M wM R)
    (λ _ _ _ → cc (ext r) N wN (agree-• R))

ccs {n = suc n} r (M ,, Ms) ⟨ w , ws ⟩ R zero = cc r M w R
ccs {n = suc n} r (M ,, Ms) ⟨ w , ws ⟩ R (suc i) = ccs r Ms ws R i

{- The end theorems -----------------------------------------------------------------}

{- well-scoped programs -}
cast-program-correct : ∀ (M : AST) (w : WS 0 M) → ⟦ M ⟧ ρ₀ ≃ T.⟦ cast-program M w ⟧ ρ₀
cast-program-correct M w = cc (λ x → x) M w (λ ())

{- closed programs -}
cast-correct : ∀ (M : AST) → Closed M → ⟦ M ⟧ ρ₀ ≃ T.⟦ cast-closed M ⟧ ρ₀
cast-correct M c rewrite cast-closed-≡ M (closed-ws {M} c) = cast-program-correct M (closed-ws {M} c)
