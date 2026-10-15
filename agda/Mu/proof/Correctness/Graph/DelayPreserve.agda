{-

  Forward (preserve) direction of delay (Clos3μ → Clos4μ) in the graph
  model, as for typed delay (proof/Correctness/Graph/DelayPreserve.agda),
  by the logical relation between single source values and target sets
  (v ⊑ D'), by recursion on the value: a source function is exhibited
  by a target closure, a set with a pair, whose calls (⊙, callc)
  exhibit its results. There is no project, so no acc-preserve; fold
  and unfold are the identity on both sides.

-}

open import proof.Framework.GraphModel.Prelude
open import Framework.Primitives
open import proof.Framework.GraphModel.Ops using (⋆; Λ; 𝒯; nthD; pair; car; cdr; 𝒞-left; 𝒞-right; Λ-β; ΛΛ-β; ⋆₂-mono)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env)
open import proof.Semantics.Graph.Prim using (out)
open import Mu.Language.Type using (Ctx; _∋_; Z; S; idx)
open import Mu.Language.Clos3
import Mu.Language.Clos4 as T
import Mu.proof.Semantics.Graph.Clos3 as S3
import Mu.proof.Semantics.Graph.Clos4 as S4
open S3 using (⟦_⟧; ⟦_⟧s)
open S4 using () renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧s to ⟦_⟧s')
open import proof.Framework.GraphModel.TypedOkBase using (fin₁; fin₂)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Mu.Compiler.Delay using (Ren; ext; delay; delays; delay-program)
open import Mu.proof.Correctness.Graph.DelayRel using (_●_; _⊙_; out-data)
open import Mu.proof.Correctness.Graph.DelayReflect using (mono₁)
open import Language.Prim using (δ)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (⊤ to pTrue; tt to ptt)
open import Level using (Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (refl)

module Mu.proof.Correctness.Graph.DelayPreserve where

{- The relation -----------------------------------------------------------------}

⋆⋆-mono : ∀ {C C' Y Y' X X'} → C ⊆ C' → Y ⊆ Y' → X ⊆ X' → (C ● Y) ● X ⊆ (C' ● Y') ● X'
⋆⋆-mono {C} {C'} {Y} {Y'} {X} {X'} C⊆ Y⊆ X⊆ =
  lower (⋆₂-mono ⟨ C , ⟨ Y , ⟨ X , ptt ⟩ ⟩ ⟩ ⟨ C' , ⟨ Y' , ⟨ X' , ptt ⟩ ⟩ ⟩ ⟨ lift C⊆ , ⟨ lift Y⊆ , ⟨ lift X⊆ , ptt ⟩ ⟩ ⟩)

⊙-mono-l : ∀ {D₁ D₂ E} → D₁ ⊆ D₂ → (D₁ ⊙ E) ⊆ (D₂ ⊙ E)
⊙-mono-l {D₁} {D₂} D⊆ = ⋆⋆-mono {car ⟨ D₁ , ptt ⟩} {car ⟨ D₂ , ptt ⟩} {cdr ⟨ D₁ , ptt ⟩} {cdr ⟨ D₂ , ptt ⟩} (λ { u ⟨ v , p ⟩ → ⟨ v , D⊆ _ p ⟩ }) (λ { v ⟨ u , p ⟩ → ⟨ u , D⊆ _ p ⟩ }) (λ d z → z)

{- a closure: a set with a pair -}
PairV : 𝒫 Value → Set
PairV D' = Σ[ u ∈ Value ] Σ[ t ∈ Value ] ⦅ u , t ⦆ ∈ D'

infix 4 _⊑_ _⊑*_
_⊑_ : Value → 𝒫 Value → Set₁
_⊑*_ : List Value → 𝒫 Value → Set₁
ν ⊑ D' = Lift (lsuc lzero) (PairV D')
(U ↦ w) ⊑ D' = Lift (lsuc lzero) (PairV D') × (∀ E' → Con E' → U ⊑* E' → w ⊑ D' ⊙ E')
(tup[ i ] d) ⊑ D' = d ⊑ Nth i D'
left d ⊑ D' = d ⊑ Lefts D'
right d ⊑ D' = d ⊑ Rights D'
v ⊑ D' = Lift (lsuc lzero) (v ∈ D')
[] ⊑* E' = pTrue
(u ∷ U) ⊑* E' = u ⊑ E' × U ⊑* E'

⊑-mono : ∀ v {D₁ D₂} → D₁ ⊆ D₂ → v ⊑ D₁ → v ⊑ D₂
⊑-mono ν D⊆ (lift ⟨ u , ⟨ t , p ⟩ ⟩) = lift ⟨ u , ⟨ t , D⊆ _ p ⟩ ⟩
⊑-mono (U ↦ w) D⊆ ⟨ lift ⟨ u , ⟨ t , p ⟩ ⟩ , f ⟩ =
  ⟨ lift ⟨ u , ⟨ t , D⊆ _ p ⟩ ⟩ , (λ E' cE U⊑ → ⊑-mono w (⊙-mono-l D⊆) (f E' cE U⊑)) ⟩
⊑-mono (tup[ i ] d) D⊆ = ⊑-mono d (λ d → D⊆ (tup[ i ] d))
⊑-mono (left d) D⊆ = ⊑-mono d (λ d → D⊆ (left d))
⊑-mono (right d) D⊆ = ⊑-mono d (λ d → D⊆ (right d))
⊑-mono (const k) D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ω D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ⦅ u , v ⦆ D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ⟨⟩ D⊆ (lift v∈) = lift (D⊆ _ v∈)

⊑-ne : ∀ v {D'} → v ⊑ D' → nonempty D'
⊑-ne ν (lift ⟨ u , ⟨ t , p ⟩ ⟩) = ⟨ _ , p ⟩
⊑-ne (U ↦ w) ⟨ lift ⟨ u , ⟨ t , p ⟩ ⟩ , _ ⟩ = ⟨ _ , p ⟩
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

{- The fundamental lemma ------------------------------------------------------}

record Envs {Γ Δ} (r : Ren Γ Δ) (ρ ρ' : Env Value) : Set₁ where
  constructor envs
  field
    NE' : nonempty-env ρ'
    ρ'~ : Con-env ρ'
    ρ⊑ : ∀ {A} (x : Γ ∋ A) v → v ∈ ρ (idx x) → v ⊑ ρ' (idx (r x))

ext-envs : ∀ {Γ Δ B} {r : Ren Γ Δ} {ρ ρ' X X'} → Envs r ρ ρ' → nonempty X' → Con X' → (∀ v → v ∈ X → v ⊑ X')
  → Envs (ext {B = B} r) (X • ρ) (X' • ρ')
ext-envs (envs NE' ρ'~ ρ⊑) ne c h = envs (extend-nonempty-env NE' ne) (Con-• c ρ'~) (λ { Z → h ; (S x) → ρ⊑ x })

preserve : ∀ {Γ Δ A} (M : Tm Γ A) {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ' → ∀ v → v ∈ ⟦ M ⟧ ρ → v ⊑ ⟦ delay r M ⟧' ρ'
preserve-nth : ∀ {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → ∀ i v → v ∈ nthD (⟦ Ms ⟧s ρ) i → v ⊑ nthD (⟦ delays r Ms ⟧s' ρ') i
preserve-𝒯 : ∀ {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → ∀ v → v ∈ 𝒯 (length Δ') (⟦ Ms ⟧s ρ) → v ⊑ 𝒯 (length Δ') (⟦ delays r Ms ⟧s' ρ')

preserve (` x) E = Envs.ρ⊑ E x
preserve (app L N) {r} E v ⟨ U , ⟨ U↦v∈ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ =
  proj₂ (preserve L E (U ↦ v) U↦v∈) _ (S4.con (delay r N) (Envs.ρ'~ E)) (⊑*-intro U U⊆ (preserve N E))
preserve (lit B k) E v v∈ = data-⊑ v (flat-data (ℬ-flat v v∈)) v∈
preserve (prim p L M) {r} {ρ' = ρ'} E _ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
  data-⊑ (out (δ p n m)) {⟦ delay r (prim p L M) ⟧' ρ'} (out-data (δ p n m))
    ⟨ n , ⟨ m , ⟨ lower (preserve L E _ n∈) , ⟨ lower (preserve M E _ m∈) , refl ⟩ ⟩ ⟩ ⟩
preserve (tuple Ms) = preserve-𝒯 Ms
preserve (get i M) E v v∈ = preserve M E (tup[ pos i ] v) v∈
preserve (inl M) E (left v) v∈ = preserve M E v v∈
preserve (inr M) E (right v) v∈ = preserve M E v v∈
preserve (case L M N) {r} {ρ} {ρ'} E v (inj₁ ⟨ u , ⟨ U , ⟨ U⊆ , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
  ⊑-mono v (𝒞-left {⟦ delay r L ⟧' ρ'} {λ X → ⟦ delay (ext r) M ⟧' (X • ρ')} {λ X → ⟦ delay (ext r) N ⟧' (X • ρ')}
              (fin₁ (S4.ok (delay (ext r) M)) NE' ne) cS)
    (preserve M (ext-envs E ne cS u⊑) v v∈)
  where
  open Envs E
  cS = Untag-con leftT (λ c → c) (S4.con (delay r L) ρ'~)
  u⊑ : ∀ d → d ∈ mem (u ∷ U) → d ⊑ Lefts (⟦ delay r L ⟧' ρ')
  u⊑ d d∈ = preserve L E (left d) (U⊆ d d∈)
  ne = ⊑-ne u (u⊑ u (here refl))
preserve (case L M N) {r} {ρ} {ρ'} E v (inj₂ ⟨ u , ⟨ U , ⟨ U⊆ , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
  ⊑-mono v (𝒞-right {⟦ delay r L ⟧' ρ'} {λ X → ⟦ delay (ext r) M ⟧' (X • ρ')} {λ X → ⟦ delay (ext r) N ⟧' (X • ρ')}
              (fin₁ (S4.ok (delay (ext r) N)) NE' ne) cS)
    (preserve N (ext-envs E ne cS u⊑) v v∈)
  where
  open Envs E
  cS = Untag-con rightT (λ c → c) (S4.con (delay r L) ρ'~)
  u⊑ : ∀ d → d ∈ mem (u ∷ U) → d ⊑ Rights (⟦ delay r L ⟧' ρ')
  u⊑ d d∈ = preserve L E (right d) (U⊆ d d∈)
  ne = ⊑-ne u (u⊑ u (here refl))
preserve (let′ M N) {r} {ρ} {ρ'} E v ⟨ U , ⟨ ⟨ v∈ , _ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  ⊑-mono v (proj₂ (Λ-β (mono₁ (S4.ok (delay (ext r) N)) ρ') (fin₁ (S4.ok (delay (ext r) N)) NE' ne) cM))
    (preserve N (ext-envs E ne cM u⊑) v v∈)
  where
  open Envs E
  cM = S4.con (delay r M) ρ'~
  u⊑ : ∀ d → d ∈ mem U → d ⊑ ⟦ delay r M ⟧' ρ'
  u⊑ d d∈ = preserve M E d (U⊆ d d∈)
  ne = let ⟨ u , u∈ ⟩ = ne-mem neU (λ d d∈ → d∈) in ⊑-ne u (u⊑ u u∈)
preserve (fold M) E = preserve M E
preserve (unfold M) E = preserve M E
preserve (clos {Δ} N Ms) {r} {ρ} {ρ'} E v ⟨ FV , ⟨ ⟨ v∈ , _ ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ = G v v∈
  where
  open Envs E
  n = length Δ
  F' = λ X Y → ⟦ delay (λ x → x) N ⟧' (Y • X • λ _ → ⌈ ω ⌉)
  T' = 𝒯 n (⟦ delays r Ms ⟧s' ρ')
  cT' = S4.con (T.tuple (delays r Ms)) ρ'~
  P' = ⟦ delay r (clos N Ms) ⟧' ρ'
  fv⊑ : ∀ fv → fv ∈ mem FV → fv ⊑ T'
  fv⊑ fv fv∈ = preserve-𝒯 Ms E fv (FV⊆ fv fv∈)
  NE-T' = let ⟨ fv , fv∈ ⟩ = ne-mem neFV (λ d d∈ → d∈) in ⊑-ne fv (fv⊑ fv fv∈)
  PV : PairV P'
  PV = ⟨ ν , ⟨ proj₁ NE-T' , ⟨ tt , proj₂ NE-T' ⟩ ⟩ ⟩
  G : ∀ v → v ∈ Λ ⟨ (λ Y → ⟦ N ⟧ (Y • mem FV • (λ _ → ⌈ ω ⌉))) , ptt ⟩ → v ⊑ P'
  G ν _ = lift PV
  G (U ↦ w) ⟨ w∈ , ⟨ neU , _ ⟩ ⟩ = ⟨ lift PV , call ⟩
    where
    call : ∀ E' → Con E' → U ⊑* E' → w ⊑ P' ⊙ E'
    call E' cE' U⊑ = ⊑-mono w β (preserve N {r = λ x → x} Eb w w∈)
      where
      NE-E' = let ⟨ u , u∈ ⟩ = ne-mem neU (λ d d∈ → d∈) in ⊑-ne u (⊑*-elim U⊑ u u∈)
      Eb : Envs (λ x → x) (mem U • mem FV • λ _ → ⌈ ω ⌉) (E' • T' • λ _ → ⌈ ω ⌉)
      Eb = envs (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) NE-T') NE-E')
                (Con-• cE' (Con-• cT' (λ _ → Con-⌈⌉ ω)))
                (λ { Z → ⊑*-elim U⊑ ; (S Z) → fv⊑ })
      β : F' T' E' ⊆ P' ⊙ E'
      β x x∈ = ⋆⋆-mono {Λ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩} {car ⟨ P' , ptt ⟩} {T'} {cdr ⟨ P' , ptt ⟩} (λ c c∈ → ⟨ proj₁ NE-T' , ⟨ c∈ , proj₂ NE-T' ⟩ ⟩) (λ y y∈ → ⟨ ν , ⟨ tt , y∈ ⟩ ⟩) (λ d z → z) x
        (ΛΛ-β {F = F'} cT' cE' (fin₂ (S4.ok (delay (λ x → x) N)) NE-T' NE-E') x x∈)

preserve-nth (M ∷ Ms) E zero = preserve M E
preserve-nth (M ∷ Ms) E (suc i) = preserve-nth Ms E i

preserve-𝒯 [] E ⟨⟩ tt = lift tt
preserve-𝒯 {Δ' = _ ∷ _} Ms E (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
  ⊑-mono d (λ d' d'∈ → ⟨ refl , ⟨ d'∈ , ne' ⟩ ⟩) (preserve-nth Ms E i d d∈)
  where
  ne' = λ j → ⊑-ne (proj₁ (ne j)) (preserve-nth Ms E j _ (proj₂ (ne j)))

{- The end theorem (forward half) ------------------------------------------------}

Envs₀ : ∀ (r : Ren [] []) → Envs r ρ₀ ρ₀
Envs₀ r = envs (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ ())

preserve-const : ∀ {A} (M : Tm [] A) {B} (c : base-rep B) → const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay-program M ⟧' ρ₀
preserve-const M c c∈ = lower (preserve M (Envs₀ _) (const c) c∈)

preserve-nonempty : ∀ {A} (M : Tm [] A) → nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ delay-program M ⟧' ρ₀)
preserve-nonempty M ⟨ v , v∈ ⟩ = ⊑-ne v (preserve M (Envs₀ _) v v∈)
