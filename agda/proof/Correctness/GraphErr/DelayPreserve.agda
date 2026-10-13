{-

  Forward (preserve) direction of the correctness of the delay pass
  (Clos3 → Clos4) in the graph model with errors, by the logical
  relation of proof/Correctness/Graph/DelayPreserve.agda between single
  source values and target sets (v ⊑ D'), with errors:

  * ω is exhibited by a target set that holds ω;
  * a source function (ν or an entry U ↦ w) by a target set that holds a
    closure, a pair of values: that is what a call checks, before it
    looks at its argument (fst), so an error of the argument is an error
    of the target call too;
  * a source value of another kind by target values of the same kind
    (⊑-wit), so a source value of the wrong kind gives a target one.

  The end theorem at the bottom combines both directions.

-}

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Semantics.GraphErr.Prim
open import Language.Clos3
import Language.Clos4 as L4
open import proof.Semantics.GraphErr.Clos3 as S3
import proof.Semantics.GraphErr.Clos4 as S4
open S4 using (Clos4ᵉ-con) renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧₊ to ⟦_⟧₊')
open import Compiler.Delay using (delay; del-map-args)
open import proof.Framework.GraphModel.Env using (nonempty-env; extend-nonempty-env)
open import proof.Correctness.GraphErr.DelayRel
  using (Env; _⊙_; ⊙-mono-l; Corr; out-data)
open import proof.Correctness.GraphErr.DelayApp using (let-app-≃)
import proof.Correctness.GraphErr.DelayReflect as Reflect

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using () renaming (⊤ to pTrue; tt to ptt)
open import Level using (Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Relation.Nullary using (¬_)
open import Language.Prim using (δ)

module proof.Correctness.GraphErr.DelayPreserve where

{- The relation -----------------------------------------------------------------}

{- a pair of values: a target closure -}
PairV : 𝒫 Value → Set
PairV D' = Σ[ u ∈ Value ] Σ[ t ∈ Value ] ⦅ u , t ⦆ ∈ D' × u ≢ ω × t ≢ ω

infix 4 _⊑_ _⊑*_
_⊑_ : Value → 𝒫 Value → Set₁
_⊑*_ : List Value → 𝒫 Value → Set₁
ν ⊑ D' = Lift (lsuc lzero) (PairV D')
(U ↦ w) ⊑ D' = Lift (lsuc lzero) (PairV D') × (∀ E' → Con E' → U ⊑* E' → w ⊑ D' ⊙ E')
(tup[ i ] d) ⊑ D' = d ⊑ Nth i D'
left d ⊑ D' = d ⊑ Lefts D'
right d ⊑ D' = d ⊑ Rights D'
⦅ u , v ⦆ ⊑ D' = Lift (lsuc lzero) ⊥
v ⊑ D' = Lift (lsuc lzero) (v ∈ D')
[] ⊑* E' = pTrue
(u ∷ U) ⊑* E' = u ⊑ E' × U ⊑* E'

_⊑ₑ_ : Env → Env → Set₁
ρ ⊑ₑ ρ' = ∀ x v → v ∈ ρ x → v ⊑ ρ' x

PairV-mono : ∀ {D₁ D₂} → D₁ ⊆ D₂ → PairV D₁ → PairV D₂
PairV-mono D⊆ ⟨ u , ⟨ t , ⟨ p∈ , r ⟩ ⟩ ⟩ = ⟨ u , ⟨ t , ⟨ D⊆ _ p∈ , r ⟩ ⟩ ⟩

⊑-mono : ∀ v {D₁ D₂} → D₁ ⊆ D₂ → v ⊑ D₁ → v ⊑ D₂
⊑-mono ν D⊆ (lift p) = lift (PairV-mono D⊆ p)
⊑-mono (U ↦ w) D⊆ ⟨ lift p , f ⟩ =
  ⟨ lift (PairV-mono D⊆ p) , (λ E' cE U⊑ → ⊑-mono w (⊙-mono-l D⊆) (f E' cE U⊑)) ⟩
⊑-mono (tup[ i ] d) D⊆ = ⊑-mono d (λ d → D⊆ (tup[ i ] d))
⊑-mono (left d) D⊆ = ⊑-mono d (λ d → D⊆ (left d))
⊑-mono (right d) D⊆ = ⊑-mono d (λ d → D⊆ (right d))
⊑-mono (const k) D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ω D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ⦅ u , v ⦆ D⊆ (lift ())
⊑-mono ⟨⟩ D⊆ (lift v∈) = lift (D⊆ _ v∈)

{- a source value other than ω is exhibited by a target value of its kind -}
⊑-ne : ∀ v {D'} → v ⊑ D' → nonempty D'
⊑-ne ν (lift ⟨ u , ⟨ t , ⟨ p∈ , _ ⟩ ⟩ ⟩) = ⟨ _ , p∈ ⟩
⊑-ne (U ↦ w) ⟨ lift ⟨ u , ⟨ t , ⟨ p∈ , _ ⟩ ⟩ ⟩ , _ ⟩ = ⟨ _ , p∈ ⟩
⊑-ne (tup[ i ] d) d⊑ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ tup[ i ] d' , d'∈ ⟩
⊑-ne (left d) d⊑ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ left d' , d'∈ ⟩
⊑-ne (right d) d⊑ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ right d' , d'∈ ⟩
⊑-ne (const k) (lift v∈) = ⟨ _ , v∈ ⟩
⊑-ne ω (lift v∈) = ⟨ _ , v∈ ⟩
⊑-ne ⦅ u , v ⦆ (lift ())
⊑-ne ⟨⟩ (lift v∈) = ⟨ _ , v∈ ⟩

⊑-wit : ∀ v {D'} → v ⊑ D' → v ≢ ω → Σ[ d' ∈ Value ] d' ∈ D' × d' ≢ ω × Corr d' v
⊑-wit ν (lift ⟨ u , ⟨ t , ⟨ p∈ , _ ⟩ ⟩ ⟩) _ = ⟨ _ , ⟨ p∈ , ⟨ (λ ()) , tt ⟩ ⟩ ⟩
⊑-wit (U ↦ w) ⟨ lift ⟨ u , ⟨ t , ⟨ p∈ , _ ⟩ ⟩ ⟩ , _ ⟩ _ = ⟨ _ , ⟨ p∈ , ⟨ (λ ()) , tt ⟩ ⟩ ⟩
⊑-wit (tup[ i ] d) d⊑ _ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ tup[ i ] d' , ⟨ d'∈ , ⟨ (λ ()) , ⟨ d , refl ⟩ ⟩ ⟩ ⟩
⊑-wit (left d) d⊑ _ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ left d' , ⟨ d'∈ , ⟨ (λ ()) , ⟨ d , refl ⟩ ⟩ ⟩ ⟩
⊑-wit (right d) d⊑ _ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ right d' , ⟨ d'∈ , ⟨ (λ ()) , ⟨ d , refl ⟩ ⟩ ⟩ ⟩
⊑-wit (const k) (lift v∈) _ = ⟨ _ , ⟨ v∈ , ⟨ (λ ()) , refl ⟩ ⟩ ⟩
⊑-wit ω _ ne = ⊥-elim (ne refl)
⊑-wit ⦅ u , v ⦆ (lift ())
⊑-wit ⟨⟩ (lift v∈) _ = ⟨ _ , ⟨ v∈ , ⟨ (λ ()) , refl ⟩ ⟩ ⟩

⊑-val : ∀ v {D'} → v ⊑ D' → v ≢ ω → val∈ D'
⊑-val v v⊑ v≢ = let ⟨ d' , ⟨ d'∈ , ⟨ d'≢ , _ ⟩ ⟩ ⟩ = ⊑-wit v v⊑ v≢ in ⟨ d' , ⟨ d'∈ , d'≢ ⟩ ⟩

{- a source value of the wrong kind gives a target value of the wrong kind -}
wrong-⊑ : ∀ {D D'} {P P' : Value → Set} → (∀ d s → Corr d s → P' d → P s)
  → (∀ v → v ∈ D → v ⊑ D') → wrong P D → wrong P' D'
wrong-⊑ corr f ⟨ s , ⟨ s∈ , ⟨ s≢ , np ⟩ ⟩ ⟩ with ⊑-wit s (f s s∈) s≢
... | ⟨ d' , ⟨ d'∈ , ⟨ d'≢ , c ⟩ ⟩ ⟩ = ⟨ d' , ⟨ d'∈ , ⟨ d'≢ , (λ p → np (corr d' s c p)) ⟩ ⟩ ⟩

pair→fun : ∀ d s → Corr d s → IsPair d → IsFun s
pair→fun ⦅ u , t ⦆ s c _ = c

tup→tup : ∀ {n} d s → Corr d s → IsTup n d → IsTup n s
tup→tup (tup[ i ] x) .(tup[ i ] y) ⟨ y , refl ⟩ t = t
tup→tup ⟨⟩ .⟨⟩ refl t = t

inj→inj : ∀ d s → Corr d s → IsInj d → IsInj s
inj→inj (left x) .(left y) ⟨ y , refl ⟩ _ = tt
inj→inj (right x) .(right y) ⟨ y , refl ⟩ _ = tt

int→int : ∀ d s → Corr d s → IsInt d → IsInt s
int→int (const k) .(const k) refl i = i

{- a function exhibited by D' gives a closure: its code and environment have values -}
fun-pair : ∀ f {D'} → IsFun f → f ⊑ D' → PairV D'
fun-pair ν _ (lift p) = p
fun-pair (U ↦ w) _ ⟨ lift p , _ ⟩ = p

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

clos-β⊙ : ∀ (N' : L4.AST) {T' E'} → nonempty T' → nonempty E' → Con T' → Con E' → Clean T' → Clean E'
  → ⟦ N' ⟧' (E' • T' • (λ _ → ⌈ ω ⌉))
    ⊆ (pairᵉ ⟨ ΛΛᵉ ⟨ (λ X Y → ⟦ N' ⟧' (Y • X • (λ _ → ⌈ ω ⌉))) , ptt ⟩ , ⟨ T' , ptt ⟩ ⟩ ⊙ E')
clos-β⊙ N' {T'} NE-T' NE-E' cT cE clT clE y y∈
    with S4.body2-continuous N' (λ _ → ⌈ ω ⌉) (λ _ → ⟨ ω , refl ⟩) NE-T' NE-E' y y∈
... | ⟨ V , ⟨ U , ⟨ neV , ⟨ neU , ⟨ V⊆ , ⟨ U⊆ , y∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  inj₁ ⟨ V , ⟨ U , ⟨ inj₁ ⟨ t , ⟨ ⟨ ⟨ y∈′ , ⟨ neU , ⟨ Con⇒≈ U cE U⊆ , nU ⟩ ⟩ ⟩ , ⟨ neV , ⟨ Con⇒≈ V cT V⊆ , nV ⟩ ⟩ ⟩
                                       , ⟨ t∈ , ⟨ (λ ()) , clT t t∈ ⟩ ⟩ ⟩ ⟩
                 , ⟨ (λ d d∈ → inj₁ ⟨ ν , ⟨ tt , ⟨ V⊆ d d∈ , ⟨ (λ ()) , clT d (V⊆ d d∈) ⟩ ⟩ ⟩ ⟩)
                 , ⟨ U⊆ , ⟨ neV , ⟨ neU , ⟨ nV , nU ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  t = proj₁ NE-T'
  t∈ = proj₂ NE-T'
  nV = Clean-NoErr V clT V⊆
  nU = Clean-NoErr U clE U⊆

{- The fundamental lemma ------------------------------------------------------}

preserve : ∀ (M : AST) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ'
  → ∀ v → v ∈ ⟦ M ⟧ ρ → v ⊑ ⟦ delay M ⟧' ρ'
preserve-nth : ∀ {n} (args : Args (replicate n ■)) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ'
  → ∀ i v → v ∈ nthD (⟦ args ⟧₊ ρ) i → v ⊑ nthD (⟦ del-map-args args ⟧₊' ρ') i
preserve-𝒯 : ∀ {n} (args : Args (replicate n ■)) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ'
  → ∀ v → v ∈ 𝒯ᵉ n (⟦ args ⟧₊ ρ) → v ⊑ 𝒯ᵉ n (⟦ del-map-args args ⟧₊' ρ')
preserve-errs : ∀ {n} (args : Args (replicate n ■)) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ'
  → errs n (⟦ args ⟧₊ ρ) → errs n (⟦ del-map-args args ⟧₊' ρ')

preserve (` x) NE C' ρ⊑ = ρ⊑ x
preserve (app ⦅ L ,, N ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ v v∈ =
  ⊑-mono v (proj₂ (let-app-≃ (delay L) (delay N) ρ' NE (Clos4ᵉ-con (delay L) C'))) (G v v∈)
  where
  L' = ⟦ delay L ⟧' ρ'
  N' = ⟦ delay N ⟧' ρ'
  G : ∀ v → v ∈ ⟦ app ⦅ L ,, N ,, Nil ⦆ ⟧ ρ → v ⊑ (L' ⊙ N')
  G v (inj₁ ⟨ U , ⟨ U↦v∈ , ⟨ U⊆ , _ ⟩ ⟩ ⟩) =
    proj₂ (preserve L NE C' ρ⊑ (U ↦ v) U↦v∈) _ (Clos4ᵉ-con (delay N) C') (⊑*-intro U U⊆ (preserve N NE C' ρ⊑))
  G _ (inj₂ ⟨ refl , inj₁ ω∈ ⟩) =
    lift (inj₂ ⟨ refl , inj₁ (inj₁ (inj₂ ⟨ refl , inj₁ (lower (preserve L NE C' ρ⊑ ω ω∈)) ⟩)) ⟩)
  G _ (inj₂ ⟨ refl , inj₂ (inj₁ wr) ⟩) =
    lift (inj₂ ⟨ refl , inj₁ (inj₁ (inj₂ ⟨ refl , inj₂ (wrong-⊑ pair→fun (preserve L NE C' ρ⊑) wr) ⟩)) ⟩)
  G _ (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ f , ⟨ f∈ , isf ⟩ ⟩ , ω∈ ⟩) ⟩)
      with fun-pair f isf (preserve L NE C' ρ⊑ f f∈)
  ... | ⟨ u , ⟨ t , ⟨ p∈ , ⟨ u≢ , t≢ ⟩ ⟩ ⟩ ⟩ =
    lift (inj₂ ⟨ refl , inj₁ (inj₂ ⟨ ⟨ u , ⟨ inj₁ ⟨ t , p∈ ⟩ , u≢ ⟩ ⟩
                                   , inj₂ ⟨ ⟨ t , ⟨ inj₁ ⟨ u , p∈ ⟩ , t≢ ⟩ ⟩
                                          , inj₁ (lower (preserve N NE C' ρ⊑ ω ω∈)) ⟩ ⟩) ⟩)
preserve (lit B k ⦅ Nil ⦆) NE C' ρ⊑ (const k') v∈ = lift v∈
preserve (prim p ⦅ L ,, M ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ _ (inj₁ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩) =
  data-⊑ (out (δ p n m)) {⟦ delay (prim p ⦅ L ,, M ,, Nil ⦆) ⟧' ρ'} (out-data (δ p n m))
    (inj₁ ⟨ n , ⟨ m , ⟨ lower (preserve L NE C' ρ⊑ _ n∈) , ⟨ lower (preserve M NE C' ρ⊑ _ m∈) , refl ⟩ ⟩ ⟩ ⟩)
preserve (prim p ⦅ L ,, M ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ _ (inj₂ ⟨ refl , e ⟩) = lift (inj₂ ⟨ refl , G e ⟩)
  where
  fL = preserve L NE C' ρ⊑
  fM = preserve M NE C' ρ⊑
  val' : ∀ {D D'} → (∀ v → v ∈ D → v ⊑ D') → val∈ D → val∈ D'
  val' f ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = ⊑-val d (f d d∈) d≢
  G : _ → _
  G (inj₁ (inj₁ ω∈)) = inj₁ (inj₁ (lower (fL ω ω∈)))
  G (inj₁ (inj₂ ⟨ vL , inj₁ ω∈ ⟩)) = inj₁ (inj₂ ⟨ val' fL vL , inj₁ (lower (fM ω ω∈)) ⟩)
  G (inj₁ (inj₂ ⟨ _ , inj₂ () ⟩))
  G (inj₂ (inj₁ ⟨ wr , vM ⟩)) = inj₂ (inj₁ ⟨ wrong-⊑ int→int fL wr , val' fM vM ⟩)
  G (inj₂ (inj₂ ⟨ vL , wr ⟩)) = inj₂ (inj₂ ⟨ val' fL vL , wrong-⊑ int→int fM wr ⟩)
preserve (tuple n ⦅ args ⦆) = preserve-𝒯 args
preserve (get i ⦅ M ,, Nil ⦆) NE C' ρ⊑ v (inj₁ t∈) =
  ⊑-mono v (λ d d∈ → inj₁ d∈) (preserve M NE C' ρ⊑ (tup[ i ] v) t∈)
preserve (get i ⦅ M ,, Nil ⦆) NE C' ρ⊑ _ (inj₂ ⟨ refl , inj₁ ω∈ ⟩) =
  lift (inj₂ ⟨ refl , inj₁ (lower (preserve M NE C' ρ⊑ ω ω∈)) ⟩)
preserve (get i ⦅ M ,, Nil ⦆) NE C' ρ⊑ _ (inj₂ ⟨ refl , inj₂ wr ⟩) =
  lift (inj₂ ⟨ refl , inj₂ (wrong-⊑ tup→tup (preserve M NE C' ρ⊑) wr) ⟩)
preserve (inl-op ⦅ M ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ (left v) ⟨ v∈ , v≢ ⟩ =
  ⊑-mono v (λ d d∈ → ⟨ d∈ , cl d d∈ ⟩) v⊑
  where
  v⊑ = preserve M NE C' ρ⊑ v v∈
  cl = con-val-clean (Clos4ᵉ-con (delay M) C') (⊑-val v v⊑ v≢)
preserve (inl-op ⦅ M ,, Nil ⦆) NE C' ρ⊑ ω ω∈ = lift (lower (preserve M NE C' ρ⊑ ω ω∈))
preserve (inr-op ⦅ M ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ (right v) ⟨ v∈ , v≢ ⟩ =
  ⊑-mono v (λ d d∈ → ⟨ d∈ , cl d d∈ ⟩) v⊑
  where
  v⊑ = preserve M NE C' ρ⊑ v v∈
  cl = con-val-clean (Clos4ᵉ-con (delay M) C') (⊑-val v v⊑ v≢)
preserve (inr-op ⦅ M ,, Nil ⦆) NE C' ρ⊑ ω ω∈ = lift (lower (preserve M NE C' ρ⊑ ω ω∈))
preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ v
    (inj₁ ⟨ u , ⟨ U , ⟨ U⊆ , ⟨ v∈ , ⟨ _ , nU ⟩ ⟩ ⟩ ⟩ ⟩) =
  ⊑-mono v (𝒞ᵉ-left {⟦ delay L ⟧' ρ'} {λ X → ⟦ delay M ⟧' (X • ρ')} {λ X → ⟦ delay N ⟧' (X • ρ')}
              (S4.body-continuous (delay M) ρ' NE _ (⊑-ne u (u⊑ u (here refl)))) cS clS)
    (preserve M NE' (Con-• cS C') ρ⊑' v v∈)
  where
  cS = Untag-con leftT (λ c → c) (Clos4ᵉ-con (delay L) C')
  u⊑ : ∀ d → d ∈ mem (u ∷ U) → d ⊑ Lefts (⟦ delay L ⟧' ρ')
  u⊑ d d∈ = preserve L NE C' ρ⊑ (left d) (U⊆ d d∈)
  clS = con-val-clean cS (⊑-val u (u⊑ u (here refl)) (λ { refl → nU (here refl) }))
  NE' = extend-nonempty-env NE (⊑-ne u (u⊑ u (here refl)))
  ρ⊑' : (mem (u ∷ U) • ρ) ⊑ₑ (Lefts (⟦ delay L ⟧' ρ') • ρ')
  ρ⊑' zero = u⊑
  ρ⊑' (suc x) = ρ⊑ x
preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ v
    (inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ U⊆ , ⟨ v∈ , ⟨ _ , nU ⟩ ⟩ ⟩ ⟩ ⟩)) =
  ⊑-mono v (𝒞ᵉ-right {⟦ delay L ⟧' ρ'} {λ X → ⟦ delay M ⟧' (X • ρ')} {λ X → ⟦ delay N ⟧' (X • ρ')}
              (S4.body-continuous (delay N) ρ' NE _ (⊑-ne u (u⊑ u (here refl)))) cS clS)
    (preserve N NE' (Con-• cS C') ρ⊑' v v∈)
  where
  cS = Untag-con rightT (λ c → c) (Clos4ᵉ-con (delay L) C')
  u⊑ : ∀ d → d ∈ mem (u ∷ U) → d ⊑ Rights (⟦ delay L ⟧' ρ')
  u⊑ d d∈ = preserve L NE C' ρ⊑ (right d) (U⊆ d d∈)
  clS = con-val-clean cS (⊑-val u (u⊑ u (here refl)) (λ { refl → nU (here refl) }))
  NE' = extend-nonempty-env NE (⊑-ne u (u⊑ u (here refl)))
  ρ⊑' : (mem (u ∷ U) • ρ) ⊑ₑ (Rights (⟦ delay L ⟧' ρ') • ρ')
  ρ⊑' zero = u⊑
  ρ⊑' (suc x) = ρ⊑ x
preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) NE C' ρ⊑ _ (inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩)) =
  lift (inj₂ (inj₂ ⟨ refl , inj₁ (lower (preserve L NE C' ρ⊑ ω ω∈)) ⟩))
preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) NE C' ρ⊑ _ (inj₂ (inj₂ ⟨ refl , inj₂ wr ⟩)) =
  lift (inj₂ (inj₂ ⟨ refl , inj₂ (wrong-⊑ inj→inj (preserve L NE C' ρ⊑) wr) ⟩))
preserve (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ}{ρ'} NE C' ρ⊑ v (inj₁ ⟨ U , ⟨ ⟨ v∈ , _ ⟩ , ⟨ U⊆ , ⟨ neU , nU ⟩ ⟩ ⟩ ⟩) =
  ⊑-mono v (proj₂ (letᵉ-β (S4.body-mono (delay N) ρ') (S4.body-continuous (delay N) ρ' NE _ NE-M) cM clM))
    (preserve N NE' (Con-• cM C') ρ⊑' v v∈)
  where
  cM = Clos4ᵉ-con (delay M) C'
  u⊑ : ∀ d → d ∈ mem U → d ⊑ ⟦ delay M ⟧' ρ'
  u⊑ d d∈ = preserve M NE C' ρ⊑ d (U⊆ d d∈)
  u₀ = proj₁ (ne-mem neU (λ d d∈ → d∈))
  u₀∈ = proj₂ (ne-mem neU (λ d d∈ → d∈))
  NE-M = ⊑-ne u₀ (u⊑ u₀ u₀∈)
  clM = con-val-clean cM (⊑-val u₀ (u⊑ u₀ u₀∈) (λ eq → nU (subst (λ x → x ∈ mem U) eq u₀∈)))
  NE' = extend-nonempty-env NE NE-M
  ρ⊑' : (mem U • ρ) ⊑ₑ (⟦ delay M ⟧' ρ' • ρ')
  ρ⊑' zero = u⊑
  ρ⊑' (suc x) = ρ⊑ x
preserve (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) NE C' ρ⊑ _ (inj₂ ⟨ refl , inj₁ () ⟩)
preserve (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) NE C' ρ⊑ _ (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) =
  ⊥-elim (nf (Λᵉ-fun d d∈))
preserve (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) NE C' ρ⊑ _ (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩) =
  lift (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , lower (preserve M NE C' ρ⊑ ω ω∈) ⟩) ⟩)
preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) {ρ}{ρ'} NE C' ρ⊑ v
    (inj₁ ⟨ FV , ⟨ ⟨ v∈ , _ ⟩ , ⟨ FV⊆ , ⟨ neFV , nFV ⟩ ⟩ ⟩ ⟩) = G v v∈
  where
  T' = 𝒯ᵉ n (⟦ del-map-args fvs ⟧₊' ρ')
  cT' = Clos4ᵉ-con (L4.tuple n L4.⦅ del-map-args fvs ⦆) C'
  P' = ⟦ delay (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ⟧' ρ'
  fv⊑ : ∀ fv → fv ∈ mem FV → fv ⊑ T'
  fv⊑ fv fv∈ = preserve-𝒯 fvs NE C' ρ⊑ fv (FV⊆ fv fv∈)
  fv₀ = proj₁ (ne-mem neFV (λ d d∈ → d∈))
  fv₀∈ = proj₂ (ne-mem neFV (λ d d∈ → d∈))
  valT' = ⊑-val fv₀ (fv⊑ fv₀ fv₀∈) (λ eq → nFV (subst (λ x → x ∈ mem FV) eq fv₀∈))
  NE-T' : nonempty T'
  NE-T' = ⟨ proj₁ valT' , proj₁ (proj₂ valT') ⟩
  clT' = con-val-clean cT' valT'
  PV : PairV P'
  PV = ⟨ ν , ⟨ proj₁ valT' , ⟨ ⟨ tt , ⟨ proj₁ (proj₂ valT') , ⟨ (λ ()) , proj₂ (proj₂ valT') ⟩ ⟩ ⟩ , ⟨ (λ ()) , proj₂ (proj₂ valT') ⟩ ⟩ ⟩ ⟩

  G : ∀ v → v ∈ Λᵉ ⟨ (λ Y → ⟦ N ⟧ (Y • mem FV • (λ _ → ⌈ ω ⌉))) , ptt ⟩ → v ⊑ P'
  G ν _ = lift PV
  G (U ↦ w) ⟨ w∈ , ⟨ neU , ⟨ _ , nU ⟩ ⟩ ⟩ = ⟨ lift PV , call ⟩
    where
    call : ∀ E' → Con E' → U ⊑* E' → w ⊑ P' ⊙ E'
    call E' cE' U⊑ = ⊑-mono w (clos-β⊙ (delay N) NE-T' NE-E' cT' cE' clT' clE')
                  (preserve N NE-ρt (Con-• cE' (Con-• cT' (λ _ → Con-⌈⌉ ω))) ρs⊑ρt w w∈)
      where
      u₀ = proj₁ (ne-mem neU (λ d d∈ → d∈))
      u₀∈ = proj₂ (ne-mem neU (λ d d∈ → d∈))
      valE' = ⊑-val u₀ (⊑*-elim U⊑ u₀ u₀∈) (λ eq → nU (subst (λ x → x ∈ mem U) eq u₀∈))
      NE-E' : nonempty E'
      NE-E' = ⟨ proj₁ valE' , proj₁ (proj₂ valE') ⟩
      clE' = con-val-clean cE' valE'
      NE-ρt = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) NE-T') NE-E'
      ρs⊑ρt : (mem U • mem FV • (λ _ → ⌈ ω ⌉)) ⊑ₑ (E' • T' • (λ _ → ⌈ ω ⌉))
      ρs⊑ρt zero = ⊑*-elim U⊑
      ρs⊑ρt (suc zero) = fv⊑
      ρs⊑ρt (suc (suc x)) .ω refl = lift refl
preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) NE C' ρ⊑ _ (inj₂ ⟨ refl , inj₁ () ⟩)
preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) NE C' ρ⊑ _
    (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) NE C' ρ⊑ _
    (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , e ⟩) ⟩) =
  lift (inj₂ ⟨ ⟨ ν , ⟨ tt , (λ ()) ⟩ ⟩ , inj₁ (preserve-errs fvs NE C' ρ⊑ e) ⟩)

preserve-nth (M ,, args) NE C' ρ⊑ zero = preserve M NE C' ρ⊑
preserve-nth (M ,, args) NE C' ρ⊑ (suc i) = preserve-nth args NE C' ρ⊑ i

preserve-errs {suc n} (M ,, args) NE C' ρ⊑ (inj₁ ω∈) = inj₁ (lower (preserve M NE C' ρ⊑ ω ω∈))
preserve-errs {suc n} (M ,, args) NE C' ρ⊑ (inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , e ⟩) =
  inj₂ ⟨ ⊑-val d (preserve M NE C' ρ⊑ d d∈) d≢ , preserve-errs args NE C' ρ⊑ e ⟩

preserve-𝒯 {n} args NE C' ρ⊑ ω e = lift (preserve-errs args NE C' ρ⊑ e)
preserve-𝒯 {zero} args NE C' ρ⊑ ⟨⟩ tt = lift tt
preserve-𝒯 {suc n} args NE C' ρ⊑ (tup[ i ] d) ⟨ refl , ⟨ d∈ , vs ⟩ ⟩ =
  ⊑-mono d (λ d' d'∈ → ⟨ refl , ⟨ d'∈ , vs' ⟩ ⟩) (preserve-nth args NE C' ρ⊑ i d d∈)
  where
  vs' = λ j → let ⟨ e , ⟨ e∈ , e≢ ⟩ ⟩ = vs j in ⊑-val e (preserve-nth args NE C' ρ⊑ j e e∈) e≢

{- The end theorem ------------------------------------------------------------}

ρ₀⊑ρ₀ : ρ₀ ⊑ₑ ρ₀
ρ₀⊑ρ₀ x .ω refl = lift refl

preserve₀ : ∀ (M : AST) v → v ∈ ⟦ M ⟧ ρ₀ → v ⊑ ⟦ delay M ⟧' ρ₀
preserve₀ M = preserve M (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) ρ₀⊑ρ₀

{- For every program, the delay pass preserves and reflects an error, the
   constants it produces, and whether it produces a value -}
delay-correct-error : ∀ (M : AST) → (ω ∈ ⟦ M ⟧ ρ₀ → ω ∈ ⟦ delay M ⟧' ρ₀) × (ω ∈ ⟦ delay M ⟧' ρ₀ → ω ∈ ⟦ M ⟧ ρ₀)
delay-correct-error M = ⟨ (λ ω∈ → lower (preserve₀ M ω ω∈)) , Reflect.reflect-error M ⟩

delay-correct-const : ∀ (M : AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay M ⟧' ρ₀)
  × (const c ∈ ⟦ delay M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
delay-correct-const M c = ⟨ (λ c∈ → lower (preserve₀ M (const c) c∈)) , Reflect.reflect-const M c ⟩

delay-correct-val : ∀ (M : AST) → (val∈ (⟦ M ⟧ ρ₀) → val∈ (⟦ delay M ⟧' ρ₀))
  × (val∈ (⟦ delay M ⟧' ρ₀) → val∈ (⟦ M ⟧ ρ₀))
delay-correct-val M =
  ⟨ (λ { ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ → ⊑-val v (preserve₀ M v v∈) v≢ }) , Reflect.reflect-val M ⟩
