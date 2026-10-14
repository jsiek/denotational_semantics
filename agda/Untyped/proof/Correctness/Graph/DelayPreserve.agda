{-

  Forward (preserve) direction of the correctness of the delay pass
  (Clos3 → Clos4), by a logical relation between single source values
  and target sets, defined by structural recursion on the value:

    v ⊑ D'   "the target set D' exhibits the source value v"

  A source function entry U ↦ w is exhibited by D' when D', applied to
  its own environment and to any consistent E' that exhibits the
  arguments U, exhibits the result w. The other clauses follow the projections of
  the target operators, so that the cases for get, inl and inr are
  immediate. No fuel or finite lists of observations are needed, unlike
  the backward direction (DelayReflectFinite): there the observed side is
  the target, where a call takes its code from car C and its free
  variables from cdr C separately, so a single target value cannot be
  related on its own.

  The end theorem at the bottom combines both directions.

-}

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Untyped.Language.Clos3
import Untyped.Language.Clos4 as L4
open import Untyped.proof.Semantics.Graph.Clos3Iswim as S3
import Untyped.proof.Semantics.Graph.Clos4Iswim as S4
open S4 using (Clos4-con) renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧₊ to ⟦_⟧₊')
open import Untyped.Compiler.Delay using (delay; del-map-args)
open import proof.Framework.GraphModel.Env using (nonempty-env; extend-nonempty-env)
open import Untyped.proof.Correctness.Graph.DelayFiniteCommon
  using (Env; _⊙_; Nth; Lefts; Rights; Init; ρ₀; ⊙-mono-l; ne-mem; ℬ-flat; Untag-con; leftT; rightT;
         Data; flat-data; out-data)
open import Untyped.proof.Correctness.Graph.DelayApp using (let-app-≃)
import Untyped.proof.Correctness.Graph.DelayReflectFinite as Reflect

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Polymorphic using () renaming (⊤ to pTrue; tt to ptt)
open import Level using (Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Language.Prim using (δ)

module Untyped.proof.Correctness.Graph.DelayPreserve where

{- The relation -----------------------------------------------------------------}

infix 4 _⊑_ _⊑*_
_⊑_ : Value → 𝒫 Value → Set₁
_⊑*_ : List Value → 𝒫 Value → Set₁
ν ⊑ D' = Lift (lsuc lzero) (nonempty D')
(U ↦ w) ⊑ D' = Lift (lsuc lzero) (nonempty D') × (∀ E' → Con E' → U ⊑* E' → w ⊑ D' ⊙ E')
(tup[ i ] d) ⊑ D' = d ⊑ Nth i D'
left d ⊑ D' = d ⊑ Lefts D'
right d ⊑ D' = d ⊑ Rights D'
v ⊑ D' = Lift (lsuc lzero) (v ∈ D')
[] ⊑* E' = pTrue
(u ∷ U) ⊑* E' = u ⊑ E' × U ⊑* E'

_⊑ₑ_ : Env → Env → Set₁
ρ ⊑ₑ ρ' = ∀ x v → v ∈ ρ x → v ⊑ ρ' x

⊑-mono : ∀ v {D₁ D₂} → D₁ ⊆ D₂ → v ⊑ D₁ → v ⊑ D₂
⊑-mono ν D⊆ (lift ⟨ d , d∈ ⟩) = lift ⟨ d , D⊆ d d∈ ⟩
⊑-mono (U ↦ w) D⊆ ⟨ lift ⟨ d , d∈ ⟩ , f ⟩ =
  ⟨ lift ⟨ d , D⊆ d d∈ ⟩ , (λ E' cE U⊑ → ⊑-mono w (⊙-mono-l D⊆) (f E' cE U⊑)) ⟩
⊑-mono (tup[ i ] d) D⊆ = ⊑-mono d (λ d → D⊆ (tup[ i ] d))
⊑-mono (left d) D⊆ = ⊑-mono d (λ d → D⊆ (left d))
⊑-mono (right d) D⊆ = ⊑-mono d (λ d → D⊆ (right d))
⊑-mono (const k) D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ω D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ⦅ u , v ⦆ D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ⟨⟩ D⊆ (lift v∈) = lift (D⊆ _ v∈)

⊑-ne : ∀ v {D'} → v ⊑ D' → nonempty D'
⊑-ne ν (lift ne) = ne
⊑-ne (U ↦ w) ⟨ lift ne , _ ⟩ = ne
⊑-ne (tup[ i ] d) d⊑ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ tup[ i ] d' , d'∈ ⟩
⊑-ne (left d) d⊑ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ left d' , d'∈ ⟩
⊑-ne (right d) d⊑ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ right d' , d'∈ ⟩
⊑-ne (const k) (lift v∈) = ⟨ _ , v∈ ⟩
⊑-ne ω (lift v∈) = ⟨ _ , v∈ ⟩
⊑-ne ⦅ u , v ⦆ (lift v∈) = ⟨ _ , v∈ ⟩
⊑-ne ⟨⟩ (lift v∈) = ⟨ _ , v∈ ⟩

data-⊑ : ∀ v {D'} → Data v → v ∈ D' → v ⊑ D'
data-⊑ (left d) dd v∈ = data-⊑ d dd v∈
data-⊑ (right d) dd v∈ = data-⊑ d dd v∈
data-⊑ (const k) _ v∈ = lift v∈
data-⊑ ω _ v∈ = lift v∈
data-⊑ ⟨⟩ _ v∈ = lift v∈

⊑*-intro : ∀ U {D E'} → mem U ⊆ D → (∀ v → v ∈ D → v ⊑ E') → U ⊑* E'
⊑*-intro [] U⊆ f = ptt
⊑*-intro (u ∷ U) U⊆ f = ⟨ f u (U⊆ u (here refl)) , ⊑*-intro U (λ d d∈ → U⊆ d (there d∈)) f ⟩

⊑*-elim : ∀ {U E'} → U ⊑* E' → ∀ u → u ∈ mem U → u ⊑ E'
⊑*-elim ⟨ u⊑ , _ ⟩ u (here refl) = u⊑
⊑*-elim ⟨ _ , U⊑ ⟩ u (there u∈) = ⊑*-elim U⊑ u u∈

{- The beta rule for target closures --------------------------------------------}

{- applied to its own environment T' and to E', a target closure behaves
   like its body (using the continuity of the body) -}
clos-β⊙ : ∀ (N' : L4.AST) {T' E'} → nonempty T' → nonempty E' → Con T' → Con E'
  → ⟦ N' ⟧' (E' • T' • (λ _ → Init))
    ⊆ (pair ⟨ ΛΛ ⟨ (λ X Y → ⟦ N' ⟧' (Y • X • (λ _ → Init))) , ptt ⟩ , ⟨ T' , ptt ⟩ ⟩ ⊙ E')
clos-β⊙ N' NE-T' NE-E' cT cE y y∈ with S4.clos-β N' (λ _ → ⟨ ω , refl ⟩) NE-T' NE-E' cT cE y y∈
... | ⟨ U , ⟨ ⟨ V , ⟨ f∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , U⊆ ⟩ ⟩ =
  ⟨ U , ⟨ ⟨ V , ⟨ ⟨ proj₁ NE-T' , ⟨ f∈ , proj₂ NE-T' ⟩ ⟩ , ⟨ (λ d d∈ → ⟨ ν , ⟨ tt , V⊆ d d∈ ⟩ ⟩) , neV ⟩ ⟩ ⟩ , U⊆ ⟩ ⟩

{- The fundamental lemma ------------------------------------------------------}

preserve : ∀ (M : AST) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ'
  → ∀ v → v ∈ ⟦ M ⟧ ρ → v ⊑ ⟦ delay M ⟧' ρ'
preserve-nth : ∀ {n} (args : Args (replicate n ■)) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ'
  → ∀ i v → v ∈ nthD (⟦ args ⟧₊ ρ) i → v ⊑ nthD (⟦ del-map-args args ⟧₊' ρ') i
preserve-𝒯 : ∀ {n} (args : Args (replicate n ■)) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ'
  → ∀ v → v ∈ 𝒯 n (⟦ args ⟧₊ ρ) → v ⊑ 𝒯 n (⟦ del-map-args args ⟧₊' ρ')

preserve (` x) NE C' ρ⊑ = ρ⊑ x
preserve (app ⦅ L ,, N ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ v ⟨ U , ⟨ U↦v∈ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ =
  ⊑-mono v (proj₂ (let-app-≃ (delay L) (delay N) ρ' (Clos4-con (delay L) C')))
    (proj₂ (preserve L NE C' ρ⊑ (U ↦ v) U↦v∈) _ (Clos4-con (delay N) C') (⊑*-intro U U⊆ (preserve N NE C' ρ⊑)))
preserve (lit B k ⦅ Nil ⦆) NE C' ρ⊑ v v∈ = data-⊑ v (flat-data (ℬ-flat v v∈)) v∈
preserve (prim p ⦅ L ,, M ,, Nil ⦆) {ρ' = ρ'} NE C' ρ⊑ _ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
  data-⊑ (out (δ p n m)) {⟦ delay (prim p ⦅ L ,, M ,, Nil ⦆) ⟧' ρ'} (out-data (δ p n m))
    ⟨ n , ⟨ m , ⟨ lower (preserve L NE C' ρ⊑ _ n∈) , ⟨ lower (preserve M NE C' ρ⊑ _ m∈) , refl ⟩ ⟩ ⟩ ⟩
preserve (tuple n ⦅ args ⦆) = preserve-𝒯 args
preserve (get i ⦅ M ,, Nil ⦆) NE C' ρ⊑ v v∈ = preserve M NE C' ρ⊑ (tup[ i ] v) v∈
preserve (inl-op ⦅ M ,, Nil ⦆) NE C' ρ⊑ (left v) v∈ = preserve M NE C' ρ⊑ v v∈
preserve (inr-op ⦅ M ,, Nil ⦆) NE C' ρ⊑ (right v) v∈ = preserve M NE C' ρ⊑ v v∈
preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ v
    (inj₁ ⟨ u , ⟨ U , ⟨ U⊆ , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
  ⊑-mono v (𝒞-left {⟦ delay L ⟧' ρ'} {λ X → ⟦ delay M ⟧' (X • ρ')} {λ X → ⟦ delay N ⟧' (X • ρ')}
              (S4.body-continuous (delay M) ρ' NE _ (⊑-ne u (u⊑ u (here refl)))) cS)
    (preserve M NE' (Con-• cS C') ρ⊑' v v∈)
  where
  cS = Untag-con leftT (λ c → c) (Clos4-con (delay L) C')
  u⊑ : ∀ d → d ∈ mem (u ∷ U) → d ⊑ Lefts (⟦ delay L ⟧' ρ')
  u⊑ d d∈ = preserve L NE C' ρ⊑ (left d) (U⊆ d d∈)
  NE' = extend-nonempty-env NE (⊑-ne u (u⊑ u (here refl)))
  ρ⊑' : (mem (u ∷ U) • ρ) ⊑ₑ (Lefts (⟦ delay L ⟧' ρ') • ρ')
  ρ⊑' zero = u⊑
  ρ⊑' (suc x) = ρ⊑ x
preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ v
    (inj₂ ⟨ u , ⟨ U , ⟨ U⊆ , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
  ⊑-mono v (𝒞-right {⟦ delay L ⟧' ρ'} {λ X → ⟦ delay M ⟧' (X • ρ')} {λ X → ⟦ delay N ⟧' (X • ρ')}
              (S4.body-continuous (delay N) ρ' NE _ (⊑-ne u (u⊑ u (here refl)))) cS)
    (preserve N NE' (Con-• cS C') ρ⊑' v v∈)
  where
  cS = Untag-con rightT (λ c → c) (Clos4-con (delay L) C')
  u⊑ : ∀ d → d ∈ mem (u ∷ U) → d ⊑ Rights (⟦ delay L ⟧' ρ')
  u⊑ d d∈ = preserve L NE C' ρ⊑ (right d) (U⊆ d d∈)
  NE' = extend-nonempty-env NE (⊑-ne u (u⊑ u (here refl)))
  ρ⊑' : (mem (u ∷ U) • ρ) ⊑ₑ (Rights (⟦ delay L ⟧' ρ') • ρ')
  ρ⊑' zero = u⊑
  ρ⊑' (suc x) = ρ⊑ x
preserve (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ v ⟨ U , ⟨ ⟨ v∈ , _ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  ⊑-mono v (proj₂ (S4.let-β (delay N) ρ' _ NE NE-M cM)) (preserve N NE' (Con-• cM C') ρ⊑' v v∈)
  where
  cM = Clos4-con (delay M) C'
  u⊑ : ∀ d → d ∈ mem U → d ⊑ ⟦ delay M ⟧' ρ'
  u⊑ d d∈ = preserve M NE C' ρ⊑ d (U⊆ d d∈)
  NE-M = let ⟨ u , u∈ ⟩ = ne-mem neU (λ d d∈ → d∈) in ⊑-ne u (u⊑ u u∈)
  NE' = extend-nonempty-env NE NE-M
  ρ⊑' : (mem U • ρ) ⊑ₑ (⟦ delay M ⟧' ρ' • ρ')
  ρ⊑' zero = u⊑
  ρ⊑' (suc x) = ρ⊑ x
preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) {ρ}{ρ'} NE C' ρ⊑ v
    ⟨ FV , ⟨ ⟨ v∈ , _ ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ = G v v∈
  where
  T' = 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ')
  cT' = Clos4-con (L4.tuple n L4.⦅ del-map-args fvs ⦆) C'
  P' = ⟦ delay (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ⟧' ρ'
  fv⊑ : ∀ fv → fv ∈ mem FV → fv ⊑ T'
  fv⊑ fv fv∈ = preserve-𝒯 fvs NE C' ρ⊑ fv (FV⊆ fv fv∈)
  NE-T' : nonempty T'
  NE-T' = let ⟨ fv , fv∈ ⟩ = ne-mem neFV (λ d d∈ → d∈) in ⊑-ne fv (fv⊑ fv fv∈)
  NE-P' : nonempty P'
  NE-P' = ⟨ ⦅ ν , proj₁ NE-T' ⦆ , ⟨ tt , proj₂ NE-T' ⟩ ⟩

  G : ∀ v → v ∈ Λ ⟨ (λ Y → ⟦ N ⟧ (Y • mem FV • (λ _ → Init))) , ptt ⟩
    → v ⊑ P'
  G ν _ = lift NE-P'
  G (U ↦ w) ⟨ w∈ , ⟨ neU , _ ⟩ ⟩ = ⟨ lift NE-P' , call ⟩
    where
    call : ∀ E' → Con E' → U ⊑* E' → w ⊑ P' ⊙ E'
    call E' cE' U⊑ = ⊑-mono w (clos-β⊙ (delay N) NE-T' NE-E' cT' cE')
                  (preserve N NE-ρt (Con-• cE' (Con-• cT' (λ _ → Con-⌈⌉ ω))) ρs⊑ρt w w∈)
      where
      NE-E' : nonempty E'
      NE-E' = let ⟨ u , u∈ ⟩ = ne-mem neU (λ d d∈ → d∈) in ⊑-ne u (⊑*-elim U⊑ u u∈)
      NE-ρt = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) NE-T') NE-E'
      ρs⊑ρt : (mem U • mem FV • (λ _ → Init)) ⊑ₑ (E' • T' • (λ _ → Init))
      ρs⊑ρt zero = ⊑*-elim U⊑
      ρs⊑ρt (suc zero) = fv⊑
      ρs⊑ρt (suc (suc x)) .ω refl = lift refl

preserve-nth (M ,, args) NE C' ρ⊑ zero = preserve M NE C' ρ⊑
preserve-nth (M ,, args) NE C' ρ⊑ (suc i) = preserve-nth args NE C' ρ⊑ i

preserve-𝒯 {zero} args NE C' ρ⊑ ⟨⟩ tt = lift tt
preserve-𝒯 {suc n} args NE C' ρ⊑ (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
  ⊑-mono d (λ d' d'∈ → ⟨ refl , ⟨ d'∈ , ne' ⟩ ⟩) (preserve-nth args NE C' ρ⊑ i d d∈)
  where
  ne' = λ j → ⊑-ne (proj₁ (ne j)) (preserve-nth args NE C' ρ⊑ j _ (proj₂ (ne j)))

{- The end theorem ------------------------------------------------------------}

ρ₀⊑ρ₀ : ρ₀ ⊑ₑ ρ₀
ρ₀⊑ρ₀ x .ω refl = lift refl

preserve-const : ∀ (M : AST) {B} (c : base-rep B)
  → const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay M ⟧' ρ₀
preserve-const M c c∈ = lower (preserve M (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) ρ₀⊑ρ₀ (const c) c∈)

preserve-nonempty : ∀ (M : AST) → nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ delay M ⟧' ρ₀)
preserve-nonempty M ⟨ v , v∈ ⟩ = ⊑-ne v (preserve M (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) ρ₀⊑ρ₀ v v∈)

{- For a closed program, the delay pass preserves and reflects the constants
   it produces and whether it produces anything at all. -}
delay-correct-const : ∀ (M : AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay M ⟧' ρ₀)
  × (const c ∈ ⟦ delay M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
delay-correct-const M c = ⟨ preserve-const M c , Reflect.reflect-const M c ⟩

delay-correct-nonempty : ∀ (M : AST)
  → (nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ delay M ⟧' ρ₀))
  × (nonempty (⟦ delay M ⟧' ρ₀) → nonempty (⟦ M ⟧ ρ₀))
delay-correct-nonempty M = ⟨ preserve-nonempty M , Reflect.reflect-nonempty M ⟩
