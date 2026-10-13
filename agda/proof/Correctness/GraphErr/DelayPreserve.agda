{-

  Forward (preserve) direction of the correctness of the delay pass
  (Clos3 → Clos4) in the graph model with errors, by the logical
  relation of proof/Correctness/Graph/DelayPreserve.agda between single
  source values and target sets (v ⊑ D'): ω is exhibited by a target set
  that holds ω, a source function by a target closure, a pair of values.

  The relation lifts through the monad (≫=-lift, binds-lift; ⊑-check
  for the check of a kernel), so each construct is its kernel, as in the
  graph model. The end theorem at the bottom combines both directions.

-}

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.Ops using (⋆; 𝒯; proj; inl; inr; 𝒞; pair; car; cdr; 𝒞-left; 𝒞-right)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Semantics.GraphErr.Prim using (primD; out)
open import Language.Clos3
import Language.Clos4 as L4
open import proof.Semantics.GraphErr.Clos3 as S3
import proof.Semantics.GraphErr.Clos4 as S4
open S4 using (Clos4ᵐ-con) renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧₊ to ⟦_⟧₊')
open import Compiler.Delay using (delay; del-map-args)
open import proof.Framework.GraphModel.Env using (nonempty-env; extend-nonempty-env)
open import proof.Correctness.GraphErr.DelayRel using (Env; _⊙_; ⊙-mono-l; tgt; tgt-inj; out-data)
open import proof.Correctness.GraphErr.DelayApp using (let-app-≃)
import proof.Correctness.GraphErr.DelayReflect as Reflect

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt; ⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using () renaming (⊤ to pTrue; tt to ptt)
open import Level using (Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
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

⊑-mono : ∀ v {D₁ D₂} → D₁ ⊆ D₂ → v ⊑ D₁ → v ⊑ D₂
⊑-mono ν D⊆ (lift ⟨ u , ⟨ t , ⟨ p∈ , r ⟩ ⟩ ⟩) = lift ⟨ u , ⟨ t , ⟨ D⊆ _ p∈ , r ⟩ ⟩ ⟩
⊑-mono (U ↦ w) D⊆ ⟨ lift ⟨ u , ⟨ t , ⟨ p∈ , r ⟩ ⟩ ⟩ , f ⟩ =
  ⟨ lift ⟨ u , ⟨ t , ⟨ D⊆ _ p∈ , r ⟩ ⟩ ⟩ , (λ E' cE U⊑ → ⊑-mono w (⊙-mono-l D⊆) (f E' cE U⊑)) ⟩
⊑-mono (tup[ i ] d) D⊆ = ⊑-mono d (λ d → D⊆ (tup[ i ] d))
⊑-mono (left d) D⊆ = ⊑-mono d (λ d → D⊆ (left d))
⊑-mono (right d) D⊆ = ⊑-mono d (λ d → D⊆ (right d))
⊑-mono (const k) D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ω D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ⦅ u , v ⦆ D⊆ (lift ())
⊑-mono ⟨⟩ D⊆ (lift v∈) = lift (D⊆ _ v∈)

{- a source value other than ω is exhibited by a target value of its kind -}
⊑-wit : ∀ v {D'} → v ⊑ D' → v ≢ ω → Σ[ d' ∈ Value ] d' ∈ ⌊ D' ⌋ × kind d' ≡ tgt (kind v) × kind v ≢ prod
⊑-ne : ∀ v {D'} → v ⊑ D' → nonempty D'
⊑-ne v {D'} v⊑ with ω? v
... | inj₁ refl = ⟨ ω , lower v⊑ ⟩
... | inj₂ v≢ = let ⟨ d' , ⟨ d'∈ , _ ⟩ ⟩ = ⊑-wit v v⊑ v≢ in ⟨ d' , proj₁ d'∈ ⟩
⊑-wit ν (lift ⟨ u , ⟨ t , ⟨ p∈ , _ ⟩ ⟩ ⟩) _ = ⟨ _ , ⟨ ⟨ p∈ , (λ ()) ⟩ , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
⊑-wit (U ↦ w) ⟨ lift ⟨ u , ⟨ t , ⟨ p∈ , _ ⟩ ⟩ ⟩ , _ ⟩ _ = ⟨ _ , ⟨ ⟨ p∈ , (λ ()) ⟩ , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
⊑-wit (tup[ i ] d) d⊑ _ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ tup[ i ] d' , ⟨ ⟨ d'∈ , (λ ()) ⟩ , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
⊑-wit (left d) d⊑ _ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ left d' , ⟨ ⟨ d'∈ , (λ ()) ⟩ , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
⊑-wit (right d) d⊑ _ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ right d' , ⟨ ⟨ d'∈ , (λ ()) ⟩ , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
⊑-wit (const k) (lift v∈) _ = ⟨ _ , ⟨ ⟨ v∈ , (λ ()) ⟩ , ⟨ refl , (λ ()) ⟩ ⟩ ⟩
⊑-wit ω _ ne = ⊥-elim (ne refl)
⊑-wit ⦅ u , v ⦆ (lift ())
⊑-wit ⟨⟩ (lift v∈) _ = ⟨ _ , ⟨ ⟨ v∈ , (λ ()) ⟩ , ⟨ refl , (λ ()) ⟩ ⟩ ⟩

⊑-val : ∀ {v D'} → v ≢ ω → v ⊑ D' → Conv D'
⊑-val {v} v≢ v⊑ = let ⟨ d' , ⟨ d'∈ , _ ⟩ ⟩ = ⊑-wit v v⊑ v≢ in ⟨ d' , d'∈ ⟩

⊑-lift : LiftRel _⊑_
⊑-lift = record { ω→ = lower ; →ω = lift ; S-mono = λ {d} → ⊑-mono d ; S-val = ⊑-val }

{- a source value of the wrong kind gives a target value of the wrong kind -}
bad-⊑ : ∀ {k X X'} → k ≢ prod → Clean X → Lifted _⊑_ X X' → Bad k X → Bad (tgt k) X'
bad-⊑ {k} np clX h ⟨ s , ⟨ s∈ , sk ⟩ ⟩ with ⊑-wit s (h s s∈) (clX s s∈)
... | ⟨ d' , ⟨ d'∈ , ⟨ dk , ns ⟩ ⟩ ⟩ = ⟨ d' , ⟨ proj₁ d'∈ , (λ eq → sk (tgt-inj _ k ns np (Relation.Binary.PropositionalEquality.trans (sym dk) eq))) ⟩ ⟩
  where import Relation.Binary.PropositionalEquality

⊑-check : ∀ {k X X' A A'} → k ≢ prod → Clean X → Lifted _⊑_ X X' → Lifted _⊑_ A A'
  → Lifted _⊑_ (checked k X A) (checked (tgt k) X' A')
⊑-check np clX hX hA w (inj₁ ⟨ refl , b ⟩) = lift (inj₁ ⟨ refl , bad-⊑ np clX hX b ⟩)
⊑-check np clX hX hA w (inj₂ w∈) = ⊑-mono w (λ x x∈ → inj₂ x∈) (hA w w∈)

data-⊑ : ∀ v {D'} → Data v → v ∈ D' → v ⊑ D'
data-⊑ (left d) dd v∈ = data-⊑ d dd v∈
data-⊑ (right d) dd v∈ = data-⊑ d dd v∈
data-⊑ (const k) _ v∈ = lift v∈
data-⊑ ω _ v∈ = lift v∈
data-⊑ ⟨⟩ _ v∈ = lift v∈

⊑*-intro : ∀ U {D E'} → mem U ⊆ D → Lifted _⊑_ D E' → U ⊑* E'
⊑*-intro [] U⊆ f = ptt
⊑*-intro (u ∷ U) U⊆ f = ⟨ f u (U⊆ u (here refl)) , ⊑*-intro U (λ d d∈ → U⊆ d (there d∈)) f ⟩

⊑*-elim : ∀ {U E'} → U ⊑* E' → Lifted _⊑_ (mem U) E'
⊑*-elim ⟨ u⊑ , _ ⟩ u (here refl) = u⊑
⊑*-elim ⟨ _ , U⊑ ⟩ u (there u∈) = ⊑*-elim U⊑ u u∈

{- a function exhibited by D' gives a closure: its code and environment are values -}
fun-pair : ∀ f {D'} → kind f ≡ fun → f ⊑ D' → PairV D'
fun-pair ν _ (lift p) = p
fun-pair (U ↦ w) _ ⟨ lift p , _ ⟩ = p

fun? : ∀ k → k ≡ fun ⊎ k ≢ fun
fun? fun = inj₁ refl
fun? inj = inj₂ (λ ())
fun? prod = inj₂ (λ ())
fun? error = inj₂ (λ ())
fun? (tup n) = inj₂ (λ ())
fun? (base B) = inj₂ (λ ())

{- The fundamental lemma ------------------------------------------------------}

preserve : ∀ (M : AST) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ' → Lifted _⊑_ (⟦ M ⟧ ρ) (⟦ delay M ⟧' ρ')
preserve-nth : ∀ {n} (args : Args (replicate n ■)) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ'
  → ∀ i → Lifted _⊑_ (nthD (⟦ args ⟧₊ ρ) i) (nthD (⟦ del-map-args args ⟧₊' ρ') i)
preserve-𝒯 : ∀ {n} (args : Args (replicate n ■)) {ρ ρ'} → nonempty-env ρ' → Con-env ρ' → ρ ⊑ₑ ρ'
  → Lifted _⊑_ (𝒯ᵐ n (⟦ args ⟧₊ ρ)) (𝒯ᵐ n (⟦ del-map-args args ⟧₊' ρ'))

args-con' : ∀ {n} (args : Args (replicate n ■)) {ρ} → Con-env ρ → ∀ i → Con (nthD (⟦ del-map-args args ⟧₊' ρ) i)
args-con' {suc n} (M ,, args) c zero = Clos4ᵐ-con (delay M) c
args-con' {suc n} (M ,, args) c (suc i) = args-con' args c i

clean⌊⌋ : ∀ {D} → Clean ⌊ D ⌋
clean⌊⌋ d d∈ = proj₂ d∈

preserve (` x) NE C' ρ⊑ = ρ⊑ x

preserve (lit B k ⦅ Nil ⦆) NE C' ρ⊑ (const k') v∈ = lift v∈

preserve (prim p ⦅ L ,, M ,, Nil ⦆) {ρ} {ρ'} NE C' ρ⊑ =
  ≫=-lift {F = λ X → ⟦ M ⟧ ρ ≫= K X} {F' = λ X → ⟦ delay M ⟧' ρ' ≫= K X} ⊑-lift (Clos4ᵐ-con (delay L) C') (preserve L NE C' ρ⊑)
    λ _ _ hX → ≫=-lift {F = K _} {F' = K _} ⊑-lift (Clos4ᵐ-con (delay M) C') (preserve M NE C' ρ⊑)
    λ _ _ hY → ⊑-check (λ ()) clean⌊⌋ hX (⊑-check (λ ()) clean⌊⌋ hY (kernel hX hY))
  where
  K = λ X Y → checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩))
  kernel : ∀ {X X' Y Y'} → Lifted _⊑_ X X' → Lifted _⊑_ Y Y'
    → Lifted _⊑_ (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩) (primD p ⟨ X' , ⟨ Y' , ptt ⟩ ⟩)
  kernel hX hY _ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
    data-⊑ (out (δ p n m)) (out-data (δ p n m)) ⟨ n , ⟨ m , ⟨ lower (hX _ n∈) , ⟨ lower (hY _ m∈) , refl ⟩ ⟩ ⟩ ⟩

preserve (tuple n ⦅ args ⦆) = preserve-𝒯 args

preserve (get {n} i ⦅ M ,, Nil ⦆) NE C' ρ⊑ =
  ≫=-lift {F = λ X → checked (tup n) X (proj i ⟨ X , ptt ⟩)} {F' = λ X → checked (tup n) X (proj i ⟨ X , ptt ⟩)}
    ⊑-lift (Clos4ᵐ-con (delay M) C') (preserve M NE C' ρ⊑)
    λ _ _ hX → ⊑-check (λ ()) clean⌊⌋ hX (λ v t∈ → hX _ t∈)

preserve (inl-op ⦅ M ,, Nil ⦆) NE C' ρ⊑ =
  ≫=-lift {F = λ X → inl ⟨ X , ptt ⟩} {F' = λ X → inl ⟨ X , ptt ⟩} ⊑-lift (Clos4ᵐ-con (delay M) C') (preserve M NE C' ρ⊑)
    λ { _ _ hX (left v) v∈ → hX v v∈ }

preserve (inr-op ⦅ M ,, Nil ⦆) NE C' ρ⊑ =
  ≫=-lift {F = λ X → inr ⟨ X , ptt ⟩} {F' = λ X → inr ⟨ X , ptt ⟩} ⊑-lift (Clos4ᵐ-con (delay M) C') (preserve M NE C' ρ⊑)
    λ { _ _ hX (right v) v∈ → hX v v∈ }

preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ} {ρ'} NE C' ρ⊑ =
  ≫=-lift {F = λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)}
          {F' = λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁' , ⟨ F₂' , ptt ⟩ ⟩ ⟩)}
    ⊑-lift (Clos4ᵐ-con (delay L) C') (preserve L NE C' ρ⊑)
    λ _ _ hX → ⊑-check (λ ()) clean⌊⌋ hX (kernel hX)
  where
  F₁ = λ Y → ⟦ M ⟧ (Y • ρ)
  F₂ = λ Y → ⟦ N ⟧ (Y • ρ)
  F₁' = λ Y → ⟦ delay M ⟧' (Y • ρ')
  F₂' = λ Y → ⟦ delay N ⟧' (Y • ρ')
  X' = ⌊ ⟦ delay L ⟧' ρ' ⌋ ⇂ ValPayload
  cX' : Con X'
  cX' = Con-⊆ (Clos4ᵐ-con (delay L) C') (λ d d∈ → proj₁ (proj₁ d∈))
  {- the branch B on the side s of the scrutinee -}
  branch : ∀ (s : Tag) (B : AST) {Cs} → (∀ {a b} → tag s a ~ tag s b → a ~ b)
    → (∀ {y} → y ≢ ω → ValPayload (tag s y))
    → (nonempty (Untag s X') → Con (Untag s X') → ⟦ delay B ⟧' (Untag s X' • ρ') ⊆ Cs)
    → ∀ u U → (∀ d → d ∈ mem (u ∷ U) → d ⊑ Untag s ⌊ ⟦ delay L ⟧' ρ' ⌋) → NoErr (u ∷ U)
    → ∀ v → v ∈ ⟦ B ⟧ (mem (u ∷ U) • ρ) → v ⊑ Cs
  branch s B {Cs} s~ vp B⊆ u U u⊑ nU v v∈ =
    ⊑-mono v (B⊆ ne cS) (preserve B (extend-nonempty-env NE ne) (Con-• cS C') ρ⊑' v v∈)
    where
    cS = Untag-con s s~ cX'
    clU : Clean (Untag s ⌊ ⟦ delay L ⟧' ρ' ⌋)
    clU = con-clean (Untag-con s s~ (Con-⊆ (Clos4ᵐ-con (delay L) C') ⌊⌋-⊆))
                    (⊑-val {u} (λ { refl → nU (here refl) }) (u⊑ u (here refl)))
    u⊑' : Lifted _⊑_ (mem (u ∷ U)) (Untag s X')
    u⊑' d d∈ = ⊑-mono d (λ y y∈ → ⟨ y∈ , vp (clU y y∈) ⟩) (u⊑ d d∈)
    ne : nonempty (Untag s X')
    ne = let ⟨ y , y∈ ⟩ = ⊑-val {u} {Untag s X'} (λ { refl → nU (here refl) }) (u⊑' u (here refl)) in ⟨ y , proj₁ y∈ ⟩
    ρ⊑' : (mem (u ∷ U) • ρ) ⊑ₑ (Untag s X' • ρ')
    ρ⊑' zero = u⊑'
    ρ⊑' (suc x) = ρ⊑ x
  kernel : Lifted _⊑_ ⌊ ⟦ L ⟧ ρ ⌋ ⌊ ⟦ delay L ⟧' ρ' ⌋
    → Lifted _⊑_ (𝒞 ⟨ ⌊ ⟦ L ⟧ ρ ⌋ ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) (𝒞 ⟨ X' , ⟨ F₁' , ⟨ F₂' , ptt ⟩ ⟩ ⟩)
  kernel hX v (inj₁ ⟨ u , ⟨ U , ⟨ all , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
    branch leftT M (λ c → c) (λ y≢ → y≢)
      (λ ne c → 𝒞-left {X'} {F₁'} {F₂'} (S4.body-continuous (delay M) ρ' NE _ ne) c)
      u U (λ d d∈ → hX (left d) (proj₁ (all d d∈))) (λ ω∈ → proj₂ (all ω ω∈) refl) v v∈
  kernel hX v (inj₂ ⟨ u , ⟨ U , ⟨ all , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
    branch rightT N (λ c → c) (λ y≢ → y≢)
      (λ ne c → 𝒞-right {X'} {F₁'} {F₂'} (S4.body-continuous (delay N) ρ' NE _ ne) c)
      u U (λ d d∈ → hX (right d) (proj₁ (all d d∈))) (λ ω∈ → proj₂ (all ω ω∈) refl) v v∈

preserve (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ} {ρ'} NE C' ρ⊑ v v∈ =
  ⊑-mono v (proj₂ (letᵐ-unfold {⟦ delay M ⟧' ρ'} {F'}))
    (≫=-lift {F = λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} {F' = λ X → ⋆ ⟨ Λᵐ ⟨ F' , ptt ⟩ , ⟨ X , ptt ⟩ ⟩}
       ⊑-lift (Clos4ᵐ-con (delay M) C') (preserve M NE C' ρ⊑) kernel v (proj₁ (letᵐ-unfold {⟦ M ⟧ ρ} {F}) v v∈))
  where
  F = λ Y → ⟦ N ⟧ (Y • ρ)
  F' = λ Y → ⟦ delay N ⟧' (Y • ρ')
  kernel : Conv (⟦ M ⟧ ρ) → Conv (⟦ delay M ⟧' ρ') → Lifted _⊑_ ⌊ ⟦ M ⟧ ρ ⌋ ⌊ ⟦ delay M ⟧' ρ' ⌋
    → Lifted _⊑_ (⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ ⌊ ⟦ M ⟧ ρ ⌋ , ptt ⟩ ⟩) (⋆ ⟨ Λᵐ ⟨ F' , ptt ⟩ , ⟨ ⌊ ⟦ delay M ⟧' ρ' ⌋ , ptt ⟩ ⟩)
  kernel _ ⟨ m , m∈ ⟩ hX v ⟨ U , ⟨ ⟨ ⟨ v∈ , _ ⟩ , _ ⟩ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ =
    ⊑-mono v (proj₂ (Λᵐ-β (S4.body-mono (delay N) ρ') (S4.body-continuous (delay N) ρ' NE _ ⟨ m , m∈ ⟩) cM clean⌊⌋))
      (preserve N (extend-nonempty-env NE ⟨ m , m∈ ⟩) (Con-• cM C') ρ⊑' v v∈)
    where
    cM = Con-⊆ (Clos4ᵐ-con (delay M) C') ⌊⌋-⊆
    ρ⊑' : (mem U • ρ) ⊑ₑ (⌊ ⟦ delay M ⟧' ρ' ⌋ • ρ')
    ρ⊑' zero d d∈ = hX d (U⊆ d d∈)
    ρ⊑' (suc x) = ρ⊑ x

preserve (app ⦅ L ,, N ,, Nil ⦆) {ρ} {ρ'} NE C' ρ⊑ v v∈ =
  ⊑-mono v (proj₂ (let-app-≃ (delay L) (delay N) ρ' NE (Clos4ᵐ-con (delay L) C')))
    (≫=-lift {F = λ X → checked fun X (Nₛ ≫= λ Y → ⋆ ⟨ X , ⟨ Y , ptt ⟩ ⟩)} {F' = λ X → X ⊙ N'}
       ⊑-lift (Clos4ᵐ-con (delay L) C') (preserve L NE C' ρ⊑) APP v v∈)
  where
  N' = ⟦ delay N ⟧' ρ'
  Nₛ = ⟦ N ⟧ ρ
  APP : Conv (⟦ L ⟧ ρ) → Conv (⟦ delay L ⟧' ρ') → Lifted _⊑_ ⌊ ⟦ L ⟧ ρ ⌋ ⌊ ⟦ delay L ⟧' ρ' ⌋
    → Lifted _⊑_ (checked fun ⌊ ⟦ L ⟧ ρ ⌋ (Nₛ ≫= λ Y → ⋆ ⟨ ⌊ ⟦ L ⟧ ρ ⌋ , ⟨ Y , ptt ⟩ ⟩)) (⌊ ⟦ delay L ⟧' ρ' ⌋ ⊙ N')
  APP ⟨ f , f∈ ⟩ cL' hX = G
    where
    X' = ⌊ ⟦ delay L ⟧' ρ' ⌋
    carω : Bad fun ⌊ ⟦ L ⟧ ρ ⌋ → ω ∈ (X' ⊙ N')
    carω b = inj₁ ⟨ refl , inj₂ ⟨ ⌊⌋-conv , inj₁ ⟨ refl , ⟨ d , ⟨ ⟨ d∈ , proj₂ d∈ ⟩ , dk ⟩ ⟩ ⟩ ⟩ ⟩
      where
      ⌊⌋-conv = let ⟨ d , d∈ ⟩ = cL' in ⟨ d , ⟨ d∈ , proj₂ d∈ ⟩ ⟩
      bd = bad-⊑ {fun} (λ ()) clean⌊⌋ hX b
      d = proj₁ bd
      d∈ = proj₁ (proj₂ bd)
      dk = proj₂ (proj₂ bd)
    G : Lifted _⊑_ (checked fun ⌊ ⟦ L ⟧ ρ ⌋ (Nₛ ≫= λ Y → ⋆ ⟨ ⌊ ⟦ L ⟧ ρ ⌋ , ⟨ Y , ptt ⟩ ⟩)) (X' ⊙ N')
    G w (inj₁ ⟨ refl , b ⟩) = lift (carω b)
    G w (inj₂ (inj₁ ⟨ refl , ω∈ ⟩)) with fun? (kind f)
    ... | inj₂ nf = lift (carω ⟨ f , ⟨ f∈ , nf ⟩ ⟩)
    ... | inj₁ isf with fun-pair f isf (hX f f∈)
    ...   | ⟨ u , ⟨ t , ⟨ p∈ , ⟨ u≢ , t≢ ⟩ ⟩ ⟩ ⟩ =
      lift (inj₂ ⟨ ⟨ u , ⟨ inj₂ ⟨ cX' , inj₂ ⟨ t , ⟨ p∈ , (λ ()) ⟩ ⟩ ⟩ , u≢ ⟩ ⟩
           , inj₂ ⟨ ⟨ t , ⟨ inj₂ ⟨ cX' , inj₂ ⟨ u , ⟨ p∈ , (λ ()) ⟩ ⟩ ⟩ , t≢ ⟩ ⟩
                  , inj₁ ⟨ refl , lower (preserve N NE C' ρ⊑ ω ω∈) ⟩ ⟩ ⟩)
      where cX' = ⟨ _ , ⟨ p∈ , (λ ()) ⟩ ⟩
    G w (inj₂ (inj₂ ⟨ _ , ⟨ U , ⟨ e∈ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ ⟩)) =
      proj₂ (hX (U ↦ w) e∈) N' (Clos4ᵐ-con (delay N) C')
        (⊑*-intro U (λ d d∈ → proj₁ (U⊆ d d∈)) (preserve N NE C' ρ⊑))

preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) {ρ} {ρ'} NE C' ρ⊑ v v∈ =
  ⊑-mono v (proj₂ (strict-β (strict₂-good (pair-good {⊤})) ⟨ lift (λ d z → z) , ptt ⟩ ⟨ (λ { .ω ⟨ () , _ ⟩ refl }) , ⟨ ν , ⟨ tt , tt ⟩ ⟩ ⟩))
    (≫=-lift {F = λ Y → ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ Y , ptt ⟩ ⟩} {F' = λ Y → pair ⟨ ΛΛᵐ ⟨ F' , ptt ⟩ , ⟨ Y , ptt ⟩ ⟩}
       ⊑-lift cT' (preserve-𝒯 fvs NE C' ρ⊑) kernel v
       (proj₁ (⋆ᵐ-val {ΛΛᵐ ⟨ F , ptt ⟩} {T} (λ { .ω ⟨ () , _ ⟩ refl }) ⟨ ν , ⟨ tt , tt ⟩ ⟩ ΛΛᵐ-fun) v v∈))
  where
  open import proof.Framework.GraphModel.Continuity using (pair-good)
  F = λ X Y → ⟦ N ⟧ (Y • X • (λ _ → ⌈ ω ⌉))
  F' = λ X Y → ⟦ delay N ⟧' (Y • X • (λ _ → ⌈ ω ⌉))
  T = 𝒯ᵐ n (⟦ fvs ⟧₊ ρ)
  T' = 𝒯ᵐ n (⟦ del-map-args fvs ⟧₊' ρ')
  cT' = Clos4ᵐ-con (L4.tuple n L4.⦅ del-map-args fvs ⦆) C'
  kernel : Conv T → Conv T' → Lifted _⊑_ ⌊ T ⌋ ⌊ T' ⌋
    → Lifted _⊑_ (⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ ⌊ T ⌋ , ptt ⟩ ⟩) (pair ⟨ ΛΛᵐ ⟨ F' , ptt ⟩ , ⟨ ⌊ T' ⌋ , ptt ⟩ ⟩)
  kernel _ ⟨ t' , t'∈ ⟩ hT = G
    where
    P = pair ⟨ ΛΛᵐ ⟨ F' , ptt ⟩ , ⟨ ⌊ T' ⌋ , ptt ⟩ ⟩
    PV : PairV P
    PV = ⟨ ν , ⟨ t' , ⟨ ⟨ ⟨ tt , tt ⟩ , t'∈ ⟩ , ⟨ (λ ()) , proj₂ t'∈ ⟩ ⟩ ⟩ ⟩
    vT' = con-val (Con-⊆ cT' ⌊⌋-⊆) ⟨ t' , ⟨ t'∈ , proj₂ t'∈ ⟩ ⟩
    G : Lifted _⊑_ (⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ ⌊ T ⌋ , ptt ⟩ ⟩) P
    G ν _ = lift PV
    G (U ↦ w) ⟨ FV , ⟨ ⟨ ⟨ ⟨ w∈ , ⟨ neU , _ ⟩ ⟩ , _ ⟩ , ⟨ _ , nU ⟩ ⟩ , ⟨ FV⊆ , _ ⟩ ⟩ ⟩ = ⟨ lift PV , call ⟩
      where
      call : ∀ E' → Con E' → U ⊑* E' → w ⊑ P ⊙ E'
      call E' cE' U⊑ =
        ⊑-mono w (pair-call-β {F'} (Con-⊆ cT' ⌊⌋-⊆) cE' vT' vE'
                    (S4.body2-continuous (delay N) (λ _ → ⌈ ω ⌉) (λ _ → ⟨ ω , refl ⟩) (proj₂ vT') (proj₂ vE')))
          (preserve N NE-ρ (Con-• cE' (Con-• (Con-⊆ cT' ⌊⌋-⊆) (λ _ → Con-⌈⌉ ω))) ρs⊑ w w∈)
        where
        u₀ = proj₁ (ne-mem neU (λ d d∈ → d∈))
        u₀∈ = proj₂ (ne-mem neU (λ d d∈ → d∈))
        vE' = con-val cE' (⊑-val (λ eq → nU (subst (λ x → x ∈ mem U) eq u₀∈)) (⊑*-elim U⊑ u₀ u₀∈))
        NE-ρ = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (proj₂ vT')) (proj₂ vE')
        ρs⊑ : (mem U • mem FV • (λ _ → ⌈ ω ⌉)) ⊑ₑ (E' • ⌊ T' ⌋ • (λ _ → ⌈ ω ⌉))
        ρs⊑ zero = ⊑*-elim U⊑
        ρs⊑ (suc zero) d d∈ = hT d (FV⊆ d d∈)
        ρs⊑ (suc (suc x)) .ω refl = lift refl

preserve-nth (M ,, args) NE C' ρ⊑ zero = preserve M NE C' ρ⊑
preserve-nth (M ,, args) NE C' ρ⊑ (suc i) = preserve-nth args NE C' ρ⊑ i

preserve-𝒯 {n} args NE C' ρ⊑ =
  binds-lift n ⊑-lift (args-con' args C') (preserve-nth args NE C' ρ⊑) (kernel n)
  where
  kernel : ∀ m {Xs Xs'} → (∀ i → Clean (nthD Xs i)) → (∀ i → Lifted _⊑_ (nthD Xs i) (nthD Xs' i))
    → Lifted _⊑_ (𝒯 m Xs) (𝒯 m Xs')
  kernel zero cl hs ⟨⟩ tt = lift tt
  kernel (suc m) cl hs (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
    ⊑-mono d (λ d' d'∈ → ⟨ refl , ⟨ d'∈ , ne' ⟩ ⟩) (hs i d d∈)
    where
    ne' = λ j → let ⟨ e , e∈ ⟩ = ne j ; ⟨ e' , e'∈ ⟩ = ⊑-val (cl j e e∈) (hs j e e∈) in ⟨ e' , proj₁ e'∈ ⟩

{- The end theorem ------------------------------------------------------------}

ρ₀⊑ρ₀ : ρ₀ ⊑ₑ ρ₀
ρ₀⊑ρ₀ x .ω refl = lift refl

preserve₀ : ∀ (M : AST) → Lifted _⊑_ (⟦ M ⟧ ρ₀) (⟦ delay M ⟧' ρ₀)
preserve₀ M = preserve M (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) ρ₀⊑ρ₀

{- For every program, the delay pass preserves and reflects an error, the
   constants it produces, and whether it produces a value -}
delay-correct-error : ∀ (M : AST) → (ω ∈ ⟦ M ⟧ ρ₀ → ω ∈ ⟦ delay M ⟧' ρ₀) × (ω ∈ ⟦ delay M ⟧' ρ₀ → ω ∈ ⟦ M ⟧ ρ₀)
delay-correct-error M = ⟨ (λ ω∈ → lower (preserve₀ M ω ω∈)) , Reflect.reflect-error M ⟩

delay-correct-const : ∀ (M : AST) {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay M ⟧' ρ₀)
  × (const c ∈ ⟦ delay M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀)
delay-correct-const M c = ⟨ (λ c∈ → lower (preserve₀ M (const c) c∈)) , Reflect.reflect-const M c ⟩

delay-correct-val : ∀ (M : AST) → (Conv (⟦ M ⟧ ρ₀) → Conv (⟦ delay M ⟧' ρ₀)) × (Conv (⟦ delay M ⟧' ρ₀) → Conv (⟦ M ⟧ ρ₀))
delay-correct-val M = ⟨ (λ { ⟨ v , ⟨ v∈ , v≢ ⟩ ⟩ → ⊑-val v≢ (preserve₀ M v v∈) }) , Reflect.reflect-val M ⟩
