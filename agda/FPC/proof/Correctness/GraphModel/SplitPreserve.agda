{-

  This module proves the forward (preserve) direction of split
  (EnvClosμ → PairClosμ) in the graph model, as for typed split
  (ISWIM/proof/Correctness/Graph/SplitPreserve.agda). The logical
  relation v ⊑ D' (Figure 4 of the paper) relates a single source value
  v to a set D' of target values, and it is defined by recursion on v.
  A source entry U ↦ w is related to D' when D' contains a pair and,
  for every consistent set E' related to the elements of U, the result
  w is related to the call D' ⊙ E', which computes callc. FPC has no
  project construct, so this module needs no counterpart of
  acc-preserve. The constructs fold and unfold mean the identity on
  both sides.

-}

open import proof.Framework.GraphModel.Prelude hiding (ρ₀)
open import FPC.Semantics.GraphModel.Closed using (ρ₀)
open import Framework.Primitives
open import proof.Framework.GraphModel.Ops using (⋆; Λ; 𝒯; nthD; pair; car; cdr;
  𝒞-left; 𝒞-right; Λ-β; ΛΛ-β; ⋆₂-mono)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.Env using (Env; nonempty-env;
  extend-nonempty-env)
open import proof.Semantics.Graph.Prim using (out)
open import FPC.Language.Type using (Ctx; _∋_; Z; S; idx)
open import FPC.Language.EnvClos
import FPC.Language.PairClos as T
import FPC.proof.Semantics.GraphModel.EnvClos as S3
import FPC.proof.Semantics.GraphModel.PairClos as S4
open S3 using (⟦_⟧; ⟦_⟧s)
open S4 using () renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧s to ⟦_⟧s')
open import proof.Framework.GraphModel.TypedOkBase using (fin₁; fin₂)
open import FPC.Framework.AllUtil using (All; []; _∷_; pos)
open import FPC.Compiler.Split using (split; splits; split-program)
open import FPC.proof.Correctness.GraphModel.SplitRel using (_●_; _⊙_; ●-mono)
open import FPC.proof.Semantics.GraphModel.Binders using (body-mono)
open import Language.Prim using (δ; int; bool)
open import Data.Bool using (true; false)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to
  ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using () renaming (⊤ to pTrue; tt to ptt)
open import Level using (Lift; lift; lower) renaming (suc to lsuc; zero to
  lzero)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)

module FPC.proof.Correctness.GraphModel.SplitPreserve where

{- The relation ---------------------------------------------------------------}

⋆⋆-mono : ∀ {C C' Y Y' X X'}
  → C ⊆ C'
  → Y ⊆ Y'
  → X ⊆ X'
  → (C ● Y) ● X ⊆ (C' ● Y') ● X'
⋆⋆-mono {C} {C'} {Y} {Y'} C⊆ Y⊆ = ●-mono {C ● Y} {C' ● Y'} (●-mono C⊆ Y⊆)

⊙-mono-l : ∀ {D₁ D₂ E}
  → D₁ ⊆ D₂
  → (D₁ ⊙ E) ⊆ (D₂ ⊙ E)
⊙-mono-l {D₁} {D₂} D⊆ =
  ⋆⋆-mono {car ⟨ D₁ , ptt ⟩} {car ⟨ D₂ , ptt ⟩} {cdr ⟨ D₁ , ptt ⟩}
  {cdr ⟨ D₂ , ptt ⟩} (λ { u ⟨ v , p ⟩ → ⟨ v , D⊆ _ p ⟩ })
  (λ { v ⟨ u , p ⟩ → ⟨ u , D⊆ _ p ⟩ }) (λ d z → z)

{- PairV D' says that D' contains a pair, as a target closure does. -}
PairV : 𝒫 Value → Set
PairV D' = Σ[ u ∈ Value ] Σ[ t ∈ Value ] ⦅ u , t ⦆ ∈ D'

infix 4 _⊑_ _⊑*_
_⊑_ : Value → 𝒫 Value → Set₁
_⊑*_ : List Value → 𝒫 Value → Set₁
ν ⊑ D' = Lift (lsuc lzero) (PairV D')
(U ↦ w) ⊑ D' =
  Lift (lsuc lzero) (PairV D') × (∀ E' → Con E' → U ⊑* E' → w ⊑ D' ⊙ E')
(tup[ i ] d) ⊑ D' = d ⊑ Nth i D'
left d ⊑ D' = d ⊑ Lefts D'
right d ⊑ D' = d ⊑ Rights D'
v ⊑ D' = Lift (lsuc lzero) (v ∈ D')
[] ⊑* E' = pTrue
(u ∷ U) ⊑* E' = u ⊑ E' × U ⊑* E'

⊑-mono : ∀ v {D₁ D₂}
  → D₁ ⊆ D₂
  → v ⊑ D₁
  → v ⊑ D₂
⊑-mono ν D⊆ (lift ⟨ u , ⟨ t , p ⟩ ⟩) = lift ⟨ u , ⟨ t , D⊆ _ p ⟩ ⟩
⊑-mono (U ↦ w) D⊆ ⟨ lift ⟨ u , ⟨ t , p ⟩ ⟩ , f ⟩ =
  ⟨ lift ⟨ u , ⟨ t , D⊆ _ p ⟩ ⟩
      , (λ E' cE U⊑ → ⊑-mono w (⊙-mono-l D⊆) (f E' cE U⊑)) ⟩
⊑-mono (tup[ i ] d) D⊆ = ⊑-mono d (λ d → D⊆ (tup[ i ] d))
⊑-mono (left d) D⊆ = ⊑-mono d (λ d → D⊆ (left d))
⊑-mono (right d) D⊆ = ⊑-mono d (λ d → D⊆ (right d))
⊑-mono (const k) D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ω D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ⦅ u , v ⦆ D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ⟨⟩ D⊆ (lift v∈) = lift (D⊆ _ v∈)

⊑-ne : ∀ v {D'}
  → v ⊑ D'
  → nonempty D'
⊑-ne ν (lift ⟨ u , ⟨ t , p ⟩ ⟩) = ⟨ _ , p ⟩
⊑-ne (U ↦ w) ⟨ lift ⟨ u , ⟨ t , p ⟩ ⟩ , _ ⟩ = ⟨ _ , p ⟩
⊑-ne (tup[ i ] d) d⊑ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ tup[ i ] d' , d'∈ ⟩
⊑-ne (left d) d⊑ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ left d' , d'∈ ⟩
⊑-ne (right d) d⊑ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ right d' , d'∈ ⟩
⊑-ne (const k) (lift v∈) = ⟨ _ , v∈ ⟩
⊑-ne ω (lift v∈) = ⟨ _ , v∈ ⟩
⊑-ne ⦅ u , v ⦆ (lift v∈) = ⟨ _ , v∈ ⟩
⊑-ne ⟨⟩ (lift v∈) = ⟨ _ , v∈ ⟩

out-⊑ : ∀ o {D'}
  → out o ∈ D'
  → out o ⊑ D'
out-⊑ (int n) v∈ = lift v∈
out-⊑ (bool true) v∈ = lift v∈
out-⊑ (bool false) v∈ = lift v∈

⊑*-intro : ∀ U {D E'}
  → mem U ⊆ D
  → (∀ v → v ∈ D → v ⊑ E')
  → U ⊑* E'
⊑*-intro [] U⊆ f = ptt
⊑*-intro (u ∷ U) U⊆ f =
  ⟨ f u (U⊆ u (here refl)) , ⊑*-intro U (λ d d∈ → U⊆ d (there d∈)) f ⟩

⊑*-elim : ∀ {U E'}
  → U ⊑* E'
  → ∀ u
  → u ∈ mem U
  → u ⊑ E'
⊑*-elim ⟨ u⊑ , _ ⟩ u (here refl) = u⊑
⊑*-elim ⟨ _ , U⊑ ⟩ u (there u∈) = ⊑*-elim U⊑ u u∈

{- The fundamental lemma ------------------------------------------------------}

record Envs (Γ : Ctx) (ρ ρ' : Env Value) : Set₁ where
  constructor envs
  field
    NE' : nonempty-env ρ'
    ρ'~ : Con-env ρ'
    ρ⊑ : ∀ {A} (x : Γ ∋ A) v → v ∈ ρ (idx x) → v ⊑ ρ' (idx x)

ext-envs : ∀ {Γ B} {ρ ρ' X X'}
  → Envs Γ ρ ρ'
  → nonempty X'
  → Con X'
  → (∀ v → v ∈ X → v ⊑ X')
  → Envs (B ∷ Γ) (X • ρ) (X' • ρ')
ext-envs (envs NE' ρ'~ ρ⊑) ne c h =
  envs (extend-nonempty-env NE' ne) (Con-• c ρ'~) (λ { Z → h ; (S x) → ρ⊑ x })

preserve : ∀ {Γ A} (M : Tm Γ A) {ρ ρ'}
  → Envs Γ ρ ρ'
  → ∀ v
  → v ∈ ⟦ M ⟧ ρ
  → v ⊑ ⟦ split M ⟧' ρ'
preserve-nth : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ ρ'}
  → Envs Γ ρ ρ'
  → ∀ i v
  → v ∈ nthD (⟦ Ms ⟧s ρ) i
  → v ⊑ nthD (⟦ splits Ms ⟧s' ρ') i
preserve-𝒯 : ∀ {Γ Δ} (Ms : All (Tm Γ) Δ) {ρ ρ'}
  → Envs Γ ρ ρ'
  → ∀ v
  → v ∈ 𝒯 (length Δ) (⟦ Ms ⟧s ρ)
  → v ⊑ 𝒯 (length Δ) (⟦ splits Ms ⟧s' ρ')
{- preserve-body handles the body B of a binder (case or let). Suppose
   every element of the nonempty list U is related to the consistent set
   X', and the translated body, with X' bound, produces results within
   Y' whenever X' is nonempty. If B, with U bound, produces v, then v is
   related to Y'. -}
preserve-body : ∀ {Γ A C} (B : Tm (A ∷ Γ) C) {ρ ρ' U X' Y'}
  → Envs Γ ρ ρ'
  → U ≢ []
  → Con X'
  → (∀ u → u ∈ mem U → u ⊑ X')
  → (nonempty X' → ⟦ split B ⟧' (X' • ρ') ⊆ Y')
  → ∀ v
  → v ∈ ⟦ B ⟧ (mem U • ρ)
  → v ⊑ Y'

preserve (` x) E = Envs.ρ⊑ E x
preserve (app L N) E v ⟨ U , ⟨ U↦v∈ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ =
  proj₂ (preserve L E (U ↦ v) U↦v∈) _ (S4.con (split N) (Envs.ρ'~ E))
    (⊑*-intro U U⊆ (preserve N E))
preserve (lit B k) E (const k') v∈ = lift v∈
preserve (prim p L M) {ρ' = ρ'} E _ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
  out-⊑ (δ p n m) {⟦ split (prim p L M) ⟧' ρ'}
    ⟨ n
        ,
        ⟨ m
          ,
            ⟨ lower (preserve L E _ n∈)
              , ⟨ lower (preserve M E _ m∈) , refl ⟩ ⟩ ⟩ ⟩
preserve (tuple Ms) = preserve-𝒯 Ms
preserve (get i M) E v v∈ = preserve M E (tup[ pos i ] v) v∈
preserve (inl M) E (left v) v∈ = preserve M E v v∈
preserve (inr M) E (right v) v∈ = preserve M E v v∈
preserve (case L M N) {ρ} {ρ'} E v (inj₁ ⟨ u , ⟨ U , ⟨ U⊆ , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
  preserve-body M E (λ ()) cS (λ d d∈ → preserve L E (left d) (U⊆ d d∈))
    (λ ne →
        𝒞-left {⟦ split L ⟧' ρ'} {λ X → ⟦ split M ⟧' (X • ρ')}
        {λ X → ⟦ split N ⟧' (X • ρ')}
              (fin₁ (S4.ok (split M)) (Envs.NE' E) ne) cS) v v∈
  where cS = Untag-con leftT (λ c → c) (S4.con (split L) (Envs.ρ'~ E))
preserve (case L M N) {ρ} {ρ'} E v (inj₂ ⟨ u , ⟨ U , ⟨ U⊆ , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
  preserve-body N E (λ ()) cS (λ d d∈ → preserve L E (right d) (U⊆ d d∈))
    (λ ne →
        𝒞-right {⟦ split L ⟧' ρ'} {λ X → ⟦ split M ⟧' (X • ρ')}
        {λ X → ⟦ split N ⟧' (X • ρ')}
              (fin₁ (S4.ok (split N)) (Envs.NE' E) ne) cS) v v∈
  where cS = Untag-con rightT (λ c → c) (S4.con (split L) (Envs.ρ'~ E))
preserve (let′ M N) {ρ} {ρ'} E v ⟨ U , ⟨ ⟨ v∈ , _ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ =
  preserve-body N E neU cM (λ d d∈ → preserve M E d (U⊆ d d∈))
    (λ ne →
        proj₂
          (Λ-β (body-mono (S4.ok (split N)) ρ')
            (fin₁ (S4.ok (split N)) (Envs.NE' E) ne) cM)) v v∈
  where cM = S4.con (split M) (Envs.ρ'~ E)
preserve (fold M) E = preserve M E
preserve (unfold M) E = preserve M E
preserve (clos {Δ} N Ms) {ρ} {ρ'} E v ⟨ FV , ⟨ ⟨ v∈ , _ ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ =
  G v v∈
  where
  open Envs E
  n = length Δ
  F' = λ X Y → ⟦ split N ⟧' (Y • X • λ _ → ⌈ ⟨⟩ ⌉)
  T' = 𝒯 n (⟦ splits Ms ⟧s' ρ')
  cT' = S4.con (T.tuple (splits Ms)) ρ'~
  P' = ⟦ split (clos N Ms) ⟧' ρ'
  fv⊑ = λ fv fv∈ → preserve-𝒯 Ms E fv (FV⊆ fv fv∈)
  NE-T' = let ⟨ fv , fv∈ ⟩ = ne-mem neFV (λ d d∈ → d∈) in ⊑-ne fv (fv⊑ fv fv∈)
  G : ∀ v
    → v ∈ Λ ⟨ (λ Y → ⟦ N ⟧ (Y • mem FV • (λ _ → ⌈ ⟨⟩ ⌉))) , ptt ⟩
    → v ⊑ P'
  G ν _ = lift ⟨ ν , ⟨ _ , ⟨ tt , proj₂ NE-T' ⟩ ⟩ ⟩
  G (U ↦ w) ⟨ w∈ , ⟨ neU , _ ⟩ ⟩ =
    ⟨ lift ⟨ ν , ⟨ _ , ⟨ tt , proj₂ NE-T' ⟩ ⟩ ⟩ , call ⟩
    where
    call : ∀ E'
      → Con E'
      → U ⊑* E'
      → w ⊑ P' ⊙ E'
    call E' cE' U⊑ = ⊑-mono w β (preserve N Eb w w∈)
      where
      NE-E' =
        let ⟨ u , u∈ ⟩ = ne-mem neU (λ d d∈ → d∈) in ⊑-ne u (⊑*-elim U⊑ u u∈)
      Eb : Envs _ (mem U • mem FV • λ _ → ⌈ ⟨⟩ ⌉) (E' • T' • λ _ → ⌈ ⟨⟩ ⌉)
      Eb =
        envs
        (extend-nonempty-env
          (extend-nonempty-env (λ _ → ⟨ ⟨⟩ , refl ⟩) NE-T') NE-E')
                (Con-• cE' (Con-• cT' (λ _ → Con-⌈⌉ ⟨⟩)))
                (λ { Z → ⊑*-elim U⊑ ; (S Z) → fv⊑ })
      β : F' T' E' ⊆ P' ⊙ E'
      β x x∈ =
        ⋆⋆-mono {Λ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩} {car ⟨ P' , ptt ⟩} {T'}
        {cdr ⟨ P' , ptt ⟩} (λ c c∈ → ⟨ proj₁ NE-T' , ⟨ c∈ , proj₂ NE-T' ⟩ ⟩)
        (λ y y∈ → ⟨ ν , ⟨ tt , y∈ ⟩ ⟩) (λ d z → z) x
        (ΛΛ-β {F = F'} cT' cE' (fin₂ (S4.ok (split N)) NE-T' NE-E') x x∈)

preserve-nth (M ∷ Ms) E zero = preserve M E
preserve-nth (M ∷ Ms) E (suc i) = preserve-nth Ms E i

preserve-𝒯 [] E ⟨⟩ tt = lift tt
preserve-𝒯 {Δ = _ ∷ _} Ms E (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
  ⊑-mono d (λ d' d'∈ → ⟨ refl , ⟨ d'∈ , ne' ⟩ ⟩) (preserve-nth Ms E i d d∈)
  where
  ne' = λ j → ⊑-ne (proj₁ (ne j)) (preserve-nth Ms E j _ (proj₂ (ne j)))

preserve-body B E neU c U⊑ B⊆ v v∈ =
  ⊑-mono v (B⊆ ne) (preserve B (ext-envs E ne c U⊑) v v∈)
  where ne = let ⟨ u , u∈ ⟩ = ne-mem neU (λ d d∈ → d∈) in ⊑-ne u (U⊑ u u∈)

{- The end theorem (forward half) ---------------------------------------------}

Envs₀ : Envs [] ρ₀ ρ₀
Envs₀ = envs (λ _ → ⟨ ⟨⟩ , refl ⟩) (λ _ → Con-⌈⌉ ⟨⟩) (λ ())

preserve-const : ∀ {A} (M : Tm [] A) {B} (c : base-rep B)
  → const c ∈ ⟦ M ⟧ ρ₀
  → const c ∈ ⟦ split-program M ⟧' ρ₀
preserve-const M c c∈ = lower (preserve M Envs₀ (const c) c∈)

preserve-nonempty : ∀ {A} (M : Tm [] A)
  → nonempty (⟦ M ⟧ ρ₀)
  → nonempty (⟦ split-program M ⟧' ρ₀)
preserve-nonempty M ⟨ v , v∈ ⟩ = ⊑-ne v (preserve M Envs₀ v v∈)
