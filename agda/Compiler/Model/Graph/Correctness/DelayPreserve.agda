{-

  Forward (preserve) direction of the correctness of the delay pass
  (Clos3 → Clos4), by a logical relation between single source values
  and target sets, defined by structural recursion on the value:

    v ⊑ D'   "the target set D' exhibits the source value v"

  A source function entry U ↦ w is exhibited by D' when D', applied to
  its own environment and to any E' that exhibits the arguments U,
  exhibits the result w. The other clauses follow the projections of
  the target operators, so that the cases for get, inl and inr are
  immediate. No fuel or finite lists of observations are needed, unlike
  the backward direction (DelayReflectFinite): there the observed side is
  the target, where a call takes its code from car C and its free
  variables from cdr C separately, so a single target value cannot be
  related on its own.

  The end theorem at the bottom combines both directions.

-}

open import NewSyntaxUtil
open import SetsAsPredicates
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos3
import Compiler.Lang.Clos4 as L4
open import Compiler.Model.Graph.Sem.Clos3Iswim as S3
import Compiler.Model.Graph.Sem.Clos4Iswim as S4
open S4 using () renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧₊ to ⟦_⟧₊')
open import Compiler.Compile.Delay using (delay; del-map-args)
open import NewEnv using (nonempty-env)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon
  using (Env; _⊙_; Nth; Lefts; Rights; Init; ρ₀; ⊙-mono-l; ne-mem; Flat; ℬ-flat;
         flat-const; flat-ω; flat-⟨⟩)
open import Compiler.Model.Graph.Correctness.DelayApp using (let-app-≃)
import Compiler.Model.Graph.Sem.Clos4IswimContinuous as C4
import Compiler.Model.Graph.Correctness.DelayReflectFinite as Reflect

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

module Compiler.Model.Graph.Correctness.DelayPreserve where

{- The relation -----------------------------------------------------------------}

infix 4 _⊑_ _⊑*_
_⊑_ : Value → 𝒫 Value → Set₁
_⊑*_ : List Value → 𝒫 Value → Set₁
ν ⊑ D' = Lift (lsuc lzero) (nonempty D')
(U ↦ w) ⊑ D' = Lift (lsuc lzero) (nonempty D') × (∀ E' → U ⊑* E' → w ⊑ D' ⊙ E')
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
  ⟨ lift ⟨ d , D⊆ d d∈ ⟩ , (λ E' U⊑ → ⊑-mono w (⊙-mono-l D⊆) (f E' U⊑)) ⟩
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

flat-⊑ : ∀ {v D'} → Flat v → v ∈ D' → v ⊑ D'
flat-⊑ flat-const v∈ = lift v∈
flat-⊑ flat-ω v∈ = lift v∈
flat-⊑ flat-⟨⟩ v∈ = lift v∈

⊑*-intro : ∀ U {D E'} → mem U ⊆ D → (∀ v → v ∈ D → v ⊑ E') → U ⊑* E'
⊑*-intro [] U⊆ f = ptt
⊑*-intro (u ∷ U) U⊆ f = ⟨ f u (U⊆ u (here refl)) , ⊑*-intro U (λ d d∈ → U⊆ d (there d∈)) f ⟩

⊑*-elim : ∀ {U E'} → U ⊑* E' → ∀ u → u ∈ mem U → u ⊑ E'
⊑*-elim ⟨ u⊑ , _ ⟩ u (here refl) = u⊑
⊑*-elim ⟨ _ , U⊑ ⟩ u (there u∈) = ⊑*-elim U⊑ u u∈

{- The beta rule for target closures --------------------------------------------}

{- applied to its own environment T' and to E', a target closure behaves
   like its body (using the continuity of the body) -}
clos-β : ∀ (N' : L4.AST) {T' E'} → nonempty T' → nonempty E'
  → ⟦ N' ⟧' (E' • T' • (λ _ → Init))
    ⊆ (pair ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N' ⟧' (Y • X • (λ _ → Init))) , ptt ⟩) , ptt ⟩
           , ⟨ T' , ptt ⟩ ⟩ ⊙ E')
clos-β N' {T'}{E'} NE-T' NE-E' y y∈ with C4.term-continuous N' _ NE y y∈
  where NE : nonempty-env (E' • T' • (λ _ → Init))
        NE zero = NE-E'
        NE (suc zero) = NE-T'
        NE (suc (suc x)) = ⟨ ω , refl ⟩
... | ⟨ Vs , ⟨ ok , y∈fin ⟩ ⟩ with ne-mem (proj₁ (ok 1)) (proj₂ (ok 1))
... | ⟨ t' , t'∈ ⟩ =
  ⟨ Vs 0 , ⟨ ⟨ Vs 1 , ⟨ ⟨ t' , ⟨ ⟨ ⟨ y∈' , proj₁ (ok 0) ⟩ , proj₁ (ok 1) ⟩ , t'∈ ⟩ ⟩
                     , ⟨ (λ d d∈ → ⟨ ν , ⟨ tt , proj₂ (ok 1) d d∈ ⟩ ⟩) , proj₁ (ok 1) ⟩ ⟩ ⟩
           , ⟨ proj₂ (ok 0) , proj₁ (ok 0) ⟩ ⟩ ⟩
  where
  env⊆ : ∀ z → mem (Vs z) ⊆ (mem (Vs 0) • mem (Vs 1) • (λ _ → Init)) z
  env⊆ zero = λ d d∈ → d∈
  env⊆ (suc zero) = λ d d∈ → d∈
  env⊆ (suc (suc z)) = proj₂ (ok (suc (suc z)))
  y∈' = S4.⟦⟧-monotone {ρ = λ z → mem (Vs z)} N' env⊆ y y∈fin

{- a target case contains its left branch, and its right branch -}
case-l : ∀ (M' : L4.AST) {L' ρ' F} → nonempty-env ρ' → nonempty (Lefts L')
  → ⟦ M' ⟧' (Lefts L' • ρ') ⊆ 𝒞 ⟨ L' , ⟨ (λ X → ⟦ M' ⟧' (X • ρ')) , ⟨ F , ptt ⟩ ⟩ ⟩
case-r : ∀ (N' : L4.AST) {L' ρ' F} → nonempty-env ρ' → nonempty (Rights L')
  → ⟦ N' ⟧' (Rights L' • ρ') ⊆ 𝒞 ⟨ L' , ⟨ F , ⟨ (λ X → ⟦ N' ⟧' (X • ρ')) , ptt ⟩ ⟩ ⟩

{- one finite part of the bound variable suffices -}
cont-0 : ∀ (M' : L4.AST) {X ρ'} → nonempty-env ρ' → nonempty X → ∀ y → y ∈ ⟦ M' ⟧' (X • ρ')
  → Σ[ u ∈ Value ] Σ[ U ∈ List Value ] mem (u ∷ U) ⊆ X × y ∈ ⟦ M' ⟧' (mem (u ∷ U) • ρ')
cont-0 M' {X}{ρ'} NE NE-X y y∈ with C4.term-continuous M' (X • ρ') NE' y y∈
  where NE' : nonempty-env (X • ρ')
        NE' zero = NE-X
        NE' (suc x) = NE x
... | ⟨ Vs , ⟨ ok , y∈fin ⟩ ⟩ with Vs 0 | proj₁ (ok 0) | proj₂ (ok 0)
     | S4.⟦⟧-monotone {ρ = λ z → mem (Vs z)} {ρ′ = mem (Vs 0) • ρ'} M' env⊆ y y∈fin
  where env⊆ : ∀ z → mem (Vs z) ⊆ (mem (Vs 0) • ρ') z
        env⊆ zero = λ d d∈ → d∈
        env⊆ (suc z) = proj₂ (ok (suc z))
... | [] | ne | _ | _ = ⊥-elim (ne refl)
... | u ∷ U | _ | U⊆ | y∈' = ⟨ u , ⟨ U , ⟨ U⊆ , y∈' ⟩ ⟩ ⟩

case-l M' NE ne y y∈ = let ⟨ u , ⟨ U , ⟨ U⊆ , y∈' ⟩ ⟩ ⟩ = cont-0 M' NE ne y y∈
                       in inj₁ ⟨ u , ⟨ U , ⟨ U⊆ , y∈' ⟩ ⟩ ⟩
case-r N' NE ne y y∈ = let ⟨ u , ⟨ U , ⟨ U⊆ , y∈' ⟩ ⟩ ⟩ = cont-0 N' NE ne y y∈
                       in inj₂ ⟨ u , ⟨ U , ⟨ U⊆ , y∈' ⟩ ⟩ ⟩

{- The fundamental lemma ------------------------------------------------------}

preserve : ∀ (M : AST) {ρ ρ'} → nonempty-env ρ' → ρ ⊑ₑ ρ'
  → ∀ v → v ∈ ⟦ M ⟧ ρ → v ⊑ ⟦ delay M ⟧' ρ'
preserve-nth : ∀ {n} (args : Args (replicate n ■)) {ρ ρ'} → nonempty-env ρ' → ρ ⊑ₑ ρ'
  → ∀ i v → v ∈ nthD (⟦ args ⟧₊ ρ) i → v ⊑ nthD (⟦ del-map-args args ⟧₊' ρ') i
preserve-𝒯 : ∀ {n} (args : Args (replicate n ■)) {ρ ρ'} → nonempty-env ρ' → ρ ⊑ₑ ρ'
  → ∀ v → v ∈ 𝒯 n (⟦ args ⟧₊ ρ) → v ⊑ 𝒯 n (⟦ del-map-args args ⟧₊' ρ')

preserve (` x) NE ρ⊑ = ρ⊑ x
preserve (app ⦅ L ,, N ,, Nil ⦆) {ρ}{ρ'} NE ρ⊑ v ⟨ U , ⟨ U↦v∈ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ =
  ⊑-mono v (proj₂ (let-app-≃ (delay L) (delay N) ρ'))
    (proj₂ (preserve L NE ρ⊑ (U ↦ v) U↦v∈) _ (⊑*-intro U U⊆ (preserve N NE ρ⊑)))
preserve (lit B k ⦅ Nil ⦆) NE ρ⊑ v v∈ = flat-⊑ (ℬ-flat v v∈) v∈
preserve (tuple n ⦅ args ⦆) = preserve-𝒯 args
preserve (get i ⦅ M ,, Nil ⦆) NE ρ⊑ v v∈ = preserve M NE ρ⊑ (tup[ i ] v) v∈
preserve (inl-op ⦅ M ,, Nil ⦆) NE ρ⊑ (left v) v∈ = preserve M NE ρ⊑ v v∈
preserve (inr-op ⦅ M ,, Nil ⦆) NE ρ⊑ (right v) v∈ = preserve M NE ρ⊑ v v∈
preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ}{ρ'} NE ρ⊑ v
    (inj₁ ⟨ u , ⟨ U , ⟨ U⊆ , v∈ ⟩ ⟩ ⟩) =
  ⊑-mono v (case-l (delay M) {L' = ⟦ delay L ⟧' ρ'} {F = λ X → ⟦ delay N ⟧' (X • ρ')} NE (⊑-ne u (u⊑ u (here refl))))
    (preserve M NE' ρ⊑' v v∈)
  where
  u⊑ : ∀ d → d ∈ mem (u ∷ U) → d ⊑ Lefts (⟦ delay L ⟧' ρ')
  u⊑ d d∈ = preserve L NE ρ⊑ (left d) (U⊆ d d∈)
  NE' : nonempty-env (Lefts (⟦ delay L ⟧' ρ') • ρ')
  NE' zero = ⊑-ne u (u⊑ u (here refl))
  NE' (suc x) = NE x
  ρ⊑' : (mem (u ∷ U) • ρ) ⊑ₑ (Lefts (⟦ delay L ⟧' ρ') • ρ')
  ρ⊑' zero = u⊑
  ρ⊑' (suc x) = ρ⊑ x
preserve (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ}{ρ'} NE ρ⊑ v
    (inj₂ ⟨ u , ⟨ U , ⟨ U⊆ , v∈ ⟩ ⟩ ⟩) =
  ⊑-mono v (case-r (delay N) {L' = ⟦ delay L ⟧' ρ'} {F = λ X → ⟦ delay M ⟧' (X • ρ')} NE (⊑-ne u (u⊑ u (here refl))))
    (preserve N NE' ρ⊑' v v∈)
  where
  u⊑ : ∀ d → d ∈ mem (u ∷ U) → d ⊑ Rights (⟦ delay L ⟧' ρ')
  u⊑ d d∈ = preserve L NE ρ⊑ (right d) (U⊆ d d∈)
  NE' : nonempty-env (Rights (⟦ delay L ⟧' ρ') • ρ')
  NE' zero = ⊑-ne u (u⊑ u (here refl))
  NE' (suc x) = NE x
  ρ⊑' : (mem (u ∷ U) • ρ) ⊑ₑ (Rights (⟦ delay L ⟧' ρ') • ρ')
  ρ⊑' zero = u⊑
  ρ⊑' (suc x) = ρ⊑ x
preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) {ρ}{ρ'} NE ρ⊑ v
    ⟨ FV , ⟨ ⟨ v∈ , _ ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ = G v v∈
  where
  T' = 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ')
  P' = ⟦ delay (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ⟧' ρ'
  fv⊑ : ∀ fv → fv ∈ mem FV → fv ⊑ T'
  fv⊑ fv fv∈ = preserve-𝒯 fvs NE ρ⊑ fv (FV⊆ fv fv∈)
  NE-T' : nonempty T'
  NE-T' = let ⟨ fv , fv∈ ⟩ = ne-mem neFV (λ d d∈ → d∈) in ⊑-ne fv (fv⊑ fv fv∈)
  NE-P' : nonempty P'
  NE-P' = ⟨ ⦅ ν , proj₁ NE-T' ⦆ , ⟨ tt , proj₂ NE-T' ⟩ ⟩

  G : ∀ v → v ∈ Λ ⟨ (λ Y → ⟦ N ⟧ (Y • mem FV • (λ _ → Init))) , ptt ⟩
    → v ⊑ P'
  G ν _ = lift NE-P'
  G (U ↦ w) ⟨ w∈ , neU ⟩ = ⟨ lift NE-P' , call ⟩
    where
    call : ∀ E' → U ⊑* E' → w ⊑ P' ⊙ E'
    call E' U⊑ = ⊑-mono w (clos-β (delay N) NE-T' NE-E')
                  (preserve N NE-ρt ρs⊑ρt w w∈)
      where
      NE-E' : nonempty E'
      NE-E' = let ⟨ u , u∈ ⟩ = ne-mem neU (λ d d∈ → d∈) in ⊑-ne u (⊑*-elim U⊑ u u∈)
      NE-ρt : nonempty-env (E' • T' • (λ _ → Init))
      NE-ρt zero = NE-E'
      NE-ρt (suc zero) = NE-T'
      NE-ρt (suc (suc x)) = ⟨ ω , refl ⟩
      ρs⊑ρt : (mem U • mem FV • (λ _ → Init)) ⊑ₑ (E' • T' • (λ _ → Init))
      ρs⊑ρt zero = ⊑*-elim U⊑
      ρs⊑ρt (suc zero) = fv⊑
      ρs⊑ρt (suc (suc x)) .ω refl = lift refl

preserve-nth (M ,, args) NE ρ⊑ zero = preserve M NE ρ⊑
preserve-nth (M ,, args) NE ρ⊑ (suc i) = preserve-nth args NE ρ⊑ i

preserve-𝒯 {zero} args NE ρ⊑ ⟨⟩ tt = lift tt
preserve-𝒯 {suc n} args NE ρ⊑ (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
  ⊑-mono d (λ d' d'∈ → ⟨ refl , ⟨ d'∈ , ne' ⟩ ⟩) (preserve-nth args NE ρ⊑ i d d∈)
  where
  ne' = λ j → ⊑-ne (proj₁ (ne j)) (preserve-nth args NE ρ⊑ j _ (proj₂ (ne j)))

{- The end theorem ------------------------------------------------------------}

ρ₀⊑ρ₀ : ρ₀ ⊑ₑ ρ₀
ρ₀⊑ρ₀ x .ω refl = lift refl

preserve-const : ∀ (M : AST) {B} (c : base-rep B)
  → const c ∈ ⟦ M ⟧ ρ₀ → const c ∈ ⟦ delay M ⟧' ρ₀
preserve-const M c c∈ = lower (preserve M (λ _ → ⟨ ω , refl ⟩) ρ₀⊑ρ₀ (const c) c∈)

preserve-nonempty : ∀ (M : AST) → nonempty (⟦ M ⟧ ρ₀) → nonempty (⟦ delay M ⟧' ρ₀)
preserve-nonempty M ⟨ v , v∈ ⟩ = ⊑-ne v (preserve M (λ _ → ⟨ ω , refl ⟩) ρ₀⊑ρ₀ v v∈)

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
