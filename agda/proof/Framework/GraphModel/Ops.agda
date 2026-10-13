module proof.Framework.GraphModel.Ops where

open import Framework.GraphModel.Ops public

open import Framework.Primitives
open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Syntax.SigUtil
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.DOpSig public using (RR; RRs; RRs-refl; rr-trans; mono⇒≃; mono-≃)
open import proof.Framework.GraphModel.DenotProperties
open import proof.Framework.GraphModel.Domain

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; z≤n; s≤s; _+_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂; ∃; ∃-syntax)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; trans; subst)
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc)
open import Relation.Nullary using (¬_; Dec; yes; no)


{- Monotonicity and congruence of operators --------------------------------------------------}

⋆-mono : monotone (■ ∷ ■ ∷ []) ■ ⋆
⋆-mono ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩ = lift G
  where
  G : ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ ⋆ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  G d ⟨ V , ⟨ wv∈D , ⟨ V<E , neV ⟩ ⟩ ⟩ =
     ⟨ V , ⟨ D⊆ (V ↦ d) wv∈D , ⟨ (λ d z → E⊆ d (V<E d z)) , neV ⟩ ⟩ ⟩

Λ-mono : monotone (ν ■ ∷ []) ■ Λ
Λ-mono ⟨ F , _ ⟩ ⟨ F' , _ ⟩ ⟨ F⊆ , _ ⟩ = lift G
  where 
  G : Λ ⟨ F , ptt ⟩  ⊆ Λ ⟨ F' , ptt ⟩
  G (V ↦ w) ⟨ w∈F₁X , neV ⟩ = 
    ⟨ lower (F⊆ (mem V) (mem V) (λ d z → z)) w w∈F₁X , neV ⟩
  G ν v∈ = tt

{- Λ F ≃ Λ F' when F and F' agree on the finite, nonempty, consistent sets -}
Λ-≃ : ∀ {F F'} → (∀ V → V ≢ [] → V ≈ V → F (mem V) ≃ F' (mem V)) → Λ ⟨ F , ptt ⟩ ≃ Λ ⟨ F' , ptt ⟩
Λ-≃ {F} {F'} eq = ⟨ G (λ V ne c → proj₁ (eq V ne c)) , G (λ V ne c → proj₂ (eq V ne c)) ⟩
  where
  G : ∀ {A B : 𝒫 Value → 𝒫 Value} → (∀ V → V ≢ [] → V ≈ V → A (mem V) ⊆ B (mem V))
    → Λ ⟨ A , ptt ⟩ ⊆ Λ ⟨ B , ptt ⟩
  G A⊆ ν tt = tt
  G A⊆ (V ↦ w) ⟨ w∈ , ne ⟩ = ⟨ A⊆ V (proj₁ ne) (proj₂ ne) w w∈ , ne ⟩

pair-mono : monotone (■ ∷ ■ ∷ []) ■ pair
pair-mono ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩ = lift G
  where
  G : pair ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ pair ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  G ⦅ u , v ⦆ ⟨ u∈D , v∈E ⟩ = ⟨ D⊆ u u∈D , E⊆ v v∈E ⟩

car-mono : monotone (■ ∷ []) ■ car
car-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : car ⟨ D , ptt ⟩ ⊆ car ⟨ D' , ptt ⟩
  G u ⟨ v , uv∈ ⟩ = ⟨ v , D⊆ ⦅ u , v ⦆ uv∈ ⟩

cdr-mono : monotone (■ ∷ []) ■ cdr
cdr-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : cdr ⟨ D , _ ⟩ ⊆ cdr ⟨ D' , _ ⟩
  G v ⟨ u , uv∈ ⟩ = ⟨ u , D⊆ ⦅ u , v ⦆ uv∈ ⟩

inl-mono : monotone (■ ∷ []) ■ inl
inl-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : inl ⟨ D , ptt ⟩ ⊆ inl ⟨ D' , ptt ⟩
  G (left v) v∈ = D⊆ v v∈

inr-mono : monotone (■ ∷ []) ■ inr
inr-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : inr ⟨ D , ptt ⟩ ⊆ inr ⟨ D' , ptt ⟩
  G (right v) v∈ = D⊆ v v∈

𝒞-mono : monotone (■ ∷ ν ■ ∷ ν ■ ∷ []) ■ 𝒞
𝒞-mono ⟨ D , ⟨ FL , ⟨ FR , _ ⟩ ⟩ ⟩ ⟨ D' , ⟨ FL' , ⟨ FR' , _ ⟩ ⟩ ⟩ 
       ⟨ lift D⊆ , ⟨ FL⊆ , ⟨ FR⊆ , _ ⟩ ⟩ ⟩ = lift G
  where 
  G : 𝒞 ⟨ D , ⟨ FL , ⟨ FR , _ ⟩ ⟩ ⟩ ⊆ 𝒞 ⟨ D' , ⟨ FL' , ⟨ FR' , _ ⟩ ⟩ ⟩
  G d (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ d∈ , c ⟩ ⟩ ⟩ ⟩) = 
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d z → D⊆ (left d) (V⊆ d z)) 
         , ⟨ lower (FL⊆ (mem (v ∷ V)) (mem (v ∷ V)) (λ d z → z)) d d∈ , c ⟩ ⟩ ⟩ ⟩
  G d (inj₂ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ d∈ , c ⟩ ⟩ ⟩ ⟩) = 
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d z → D⊆ (right d) (V⊆ d z)) 
         , ⟨ lower (FR⊆ (mem (v ∷ V)) (mem (v ∷ V)) (λ d z → z)) d d∈ , c ⟩ ⟩ ⟩ ⟩

nthD-mono : ∀ {n} (Ds Es : Results (𝒫 Value) (replicate n ■))
  → results-rel-pres _⊆_ (replicate n ■) Ds Es → (i : Fin n) → nthD Ds i ⊆ nthD Es i
nthD-mono {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ lift D⊆ , _ ⟩ zero = D⊆
nthD-mono {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ _ , Ds⊆ ⟩ (suc i) = nthD-mono Ds Es Ds⊆ i

𝒯-mono : ∀ n → monotone (replicate n ■) ■ (𝒯 n)
𝒯-mono zero Ds Es Ds⊆ = lift G
  where
  G : 𝒯 zero Ds ⊆ 𝒯 zero Es
  G ⟨⟩ tt = tt
𝒯-mono (suc n) Ds Es Ds⊆ = lift G
  where
  G : 𝒯 (suc n) Ds ⊆ 𝒯 (suc n) Es
  G (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
    ⟨ refl , ⟨ nthD-mono Ds Es Ds⊆ i d d∈
           , (λ j → ⟨ proj₁ (ne j) , nthD-mono Ds Es Ds⊆ j _ (proj₂ (ne j)) ⟩) ⟩ ⟩
  G (const k) ()
  G (V ↦ w) ()
  G ν ()
  G ω ()
  G ⦅ u , v ⦆ ()
  G (left d) ()
  G (right d) ()

proj-mono : ∀ {n} (i : Fin n) → monotone (■ ∷ []) ■ (proj i)
proj-mono i ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ lift D⊆ , _ ⟩ = lift (λ d → D⊆ (tup[ i ] d))

{- Consistency ----------------------------------------------------------------}

⋆-consis : consistent _~_ (■ ∷ ■ ∷ []) ■ ⋆
⋆-consis ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , _ ⟩ ⟩ = lift G
  where
  G : Every _~_ (⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩) (⋆ ⟨ D' , ⟨ E' , ptt ⟩ ⟩)
  G u w ⟨ V , ⟨ u∈D , ⟨ V<E , neV ⟩ ⟩ ⟩
        ⟨ V' , ⟨ w∈D' , ⟨ V<E' , neV' ⟩ ⟩ ⟩
    = D~ (V ↦ u) (V' ↦ w) u∈D w∈D' (Every⇒≈ V V' (Every-⊆ E~ V<E V<E'))

Λ-consis : consistent _~_ (ν ■ ∷ []) ■ Λ
Λ-consis ⟨ F , _ ⟩ ⟨ F' , _ ⟩ ⟨ F~ , _ ⟩ = lift G
  where
  G : Every _~_ (Λ ⟨ F , ptt ⟩) (Λ ⟨ F' , ptt ⟩)
  G ν (V ↦ w) tt _ = tt
  G ν ν tt _ = tt
  G (V ↦ w) ν w∈F₁X tt = tt
  G (V ↦ w) (V' ↦ w') 
    ⟨ w∈F₁X , neV ⟩ ⟨ w∈F₁X' , neV' ⟩ = λ V≈V' →
    lower (F~ (mem V) (mem V') (≈⇒Every V V' V≈V')) w w' w∈F₁X w∈F₁X'

pair-consis : consistent _~_ (■ ∷ ■ ∷ []) ■ pair
pair-consis ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D~ , ⟨ lift E~ , _ ⟩ ⟩ = lift G
  where
  G : Every _~_ (pair ⟨ D , ⟨ E , ptt ⟩ ⟩) (pair ⟨ D' , ⟨ E' , ptt ⟩ ⟩)
  G ⦅ u , v ⦆ ⦅ u' , v' ⦆ ⟨ u∈ , v∈ ⟩ ⟨ u'∈ , v'∈ ⟩ = ⟨ D~ u u' u∈ u'∈ , E~ v v' v∈ v'∈ ⟩

car-consis : consistent _~_ (■ ∷ []) ■ car
car-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (car ⟨ D , ptt ⟩) (car ⟨ D' , ptt ⟩)
  G u u' ⟨ v , u∈ ⟩ ⟨ v' , u'∈ ⟩ = proj₁ (D~ ⦅ u , v ⦆ ⦅ u' , v' ⦆ u∈ u'∈)

cdr-consis : consistent _~_ (■ ∷ []) ■ cdr
cdr-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (cdr ⟨ D , ptt ⟩) (cdr ⟨ D' , ptt ⟩)
  G v v' ⟨ u , v∈ ⟩ ⟨ u' , v'∈ ⟩ = proj₂ (D~ ⦅ u , v ⦆ ⦅ u' , v' ⦆ v∈ v'∈)

inl-consis : consistent _~_ (■ ∷ []) ■ inl
inl-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (inl ⟨ D , ptt ⟩) (inl ⟨ D' , ptt ⟩)
  G (left u) (left v) U∈ V∈ 
    = D~ u v U∈ V∈

inr-consis : consistent _~_ (■ ∷ []) ■ inr
inr-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (inr ⟨ D , ptt ⟩) (inr ⟨ D' , ptt ⟩)
  G (right u) (right v) U∈ V∈ 
    = D~ u v U∈ V∈



𝒞-consis : consistent _~_ (■ ∷ ν ■ ∷ ν ■ ∷ []) ■ 𝒞
𝒞-consis ⟨ D , ⟨ FL , ⟨ FR , _ ⟩ ⟩ ⟩ ⟨ D' , ⟨ FL' , ⟨ FR' , _ ⟩ ⟩ ⟩ 
       ⟨ lift D~ , ⟨ FL~ , ⟨ FR~ , _ ⟩ ⟩ ⟩ = lift G
  where 
  G : Every _~_ (𝒞 ⟨ D , ⟨ FL , ⟨ FR , ptt ⟩ ⟩ ⟩) (𝒞 ⟨ D' , ⟨ FL' , ⟨ FR' , ptt ⟩ ⟩ ⟩)
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩ ) (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    = lower (FL~ (mem (v ∷ V)) (mem (v' ∷ V')) V≈V') u w u∈ w∈
    where
    V≈V' : ∀ d d' → d ∈ mem (v ∷ V) → d' ∈ mem (v' ∷ V') → d ~ d'
    V≈V' d d' d∈ d'∈ = D~ (left d) (left d') (V⊆ d d∈) (V⊆' d' d'∈)
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩) (inj₂ ⟨ v' , ⟨ V' , ⟨ V⊆' , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) = 
    ⊥-elim (D~ (left v) (right v') (V⊆ v (here refl)) (V⊆' v' (here refl)))
  G u w (inj₂ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩) (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) = 
    ⊥-elim (D~ (right v) (left v') (V⊆ v (here refl)) (V⊆' v' (here refl)))
  G u w (inj₂ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩) (inj₂ ⟨ v' , ⟨ V' , ⟨ V⊆' , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩)
    = lower (FR~ (mem (v ∷ V)) (mem (v' ∷ V')) V≈V') u w u∈ w∈
    where
    V≈V' : ∀ d d' → d ∈ mem (v ∷ V) → d' ∈ mem (v' ∷ V') → d ~ d'
    V≈V' d d' d∈ d'∈ = D~ (right d) (right d') (V⊆ d d∈) (V⊆' d' d'∈)

nthD-consis : ∀ {n} (Ds Es : Results (𝒫 Value) (replicate n ■))
  → results-rel-pres (Every _~_) (replicate n ■) Ds Es
  → (i : Fin n) → Every _~_ (nthD Ds i) (nthD Es i)
nthD-consis {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ lift D~ , _ ⟩ zero = D~
nthD-consis {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ _ , Ds~ ⟩ (suc i) = nthD-consis Ds Es Ds~ i

𝒯-consis : ∀ n → consistent _~_ (replicate n ■) ■ (𝒯 n)
𝒯-consis zero Ds Es Ds~ = lift G
  where
  G : Every _~_ (𝒯 zero Ds) (𝒯 zero Es)
  G ⟨⟩ ⟨⟩ tt tt = tt
𝒯-consis (suc n) Ds Es Ds~ = lift G
  where
  G : Every _~_ (𝒯 (suc n) Ds) (𝒯 (suc n) Es)
  G (tup[ i ] d) (tup[ i' ] d') ⟨ refl , ⟨ d∈ , _ ⟩ ⟩ ⟨ refl , ⟨ d'∈ , _ ⟩ ⟩ with i fin≟ i'
  ... | yes refl = ⟨ refl , inj₂ ⟨ refl , nthD-consis Ds Es Ds~ i d d' d∈ d'∈ ⟩ ⟩
  ... | no neq = ⟨ refl , inj₁ neq ⟩

proj-consis : ∀ {n} (i : Fin n) → consistent _~_ (■ ∷ []) ■ (proj i)
proj-consis i ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ lift D~ , _ ⟩ = lift G
  where
  G : Every _~_ (proj i ⟨ D , ptt ⟩) (proj i ⟨ D' , ptt ⟩)
  G d d' d∈ d'∈ with D~ (tup[ i ] d) (tup[ i ] d') d∈ d'∈
  ... | ⟨ refl , inj₁ neq ⟩ = ⊥-elim (neq refl)
  ... | ⟨ refl , inj₂ ⟨ _ , d~ ⟩ ⟩ = d~

ℬ-consis : ∀ B k → consistent _~_ [] ■ (ℬ B k)
ℬ-consis B k _ _ _ = lift G
  where 
  G : Every _~_ (ℬ B k ptt) (ℬ B k ptt)
  G (const {B'} k) (const {B''} k') ⟨ refl , d∈ ⟩  ⟨ refl , d'∈ ⟩ = ⟨ refl , trans (sym d∈) d'∈ ⟩

{- Composite operators ---------------------------------------------------------}

{- let x = D in F x, which means (λx. F x) D -}
letD : DOp (𝒫 Value) (■ ∷ ν ■ ∷ [])
letD ⟨ D , ⟨ F , _ ⟩ ⟩ = ⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

{- application to two arguments -}
⋆₂ : DOp (𝒫 Value) (■ ∷ ■ ∷ ■ ∷ [])
⋆₂ ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ = ⋆ ⟨ ⋆ ⟨ L , ⟨ M , ptt ⟩ ⟩ , ⟨ N , ptt ⟩ ⟩

{- a closed function of two arguments -}
ΛΛ : DOp (𝒫 Value) (∁ (ν (ν ■)) ∷ [])
ΛΛ ⟨ F , _ ⟩ = Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩

{- a closure: its code applied to the tuple of its free variables -}
closD : ∀ n → DOp (𝒫 Value) (∁ (ν (ν ■)) ∷ replicate n ■)
closD n ⟨ F , Ds ⟩ = ⋆ ⟨ ΛΛ ⟨ F , ptt ⟩ , ⟨ 𝒯 n Ds , ptt ⟩ ⟩

ℬ-mono : ∀ B k → monotone [] ■ (ℬ B k)
ℬ-mono B k _ _ _ = lift (λ d d∈ → d∈)

letD-mono : monotone (■ ∷ ν ■ ∷ []) ■ letD
letD-mono ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D⊆ , ⟨ F⊆ , _ ⟩ ⟩ =
  ⋆-mono ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
         ⟨ Λ-mono ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F⊆ , ptt ⟩ , ⟨ D⊆ , ptt ⟩ ⟩

letD-consis : consistent _~_ (■ ∷ ν ■ ∷ []) ■ letD
letD-consis ⟨ D , ⟨ F , _ ⟩ ⟩ ⟨ D' , ⟨ F' , _ ⟩ ⟩ ⟨ D~ , ⟨ F~ , _ ⟩ ⟩ =
  ⋆-consis ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⟨ Λ ⟨ F' , ptt ⟩ , ⟨ D' , ptt ⟩ ⟩
           ⟨ Λ-consis ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ D~ , ptt ⟩ ⟩

⋆₂-mono : monotone (■ ∷ ■ ∷ ■ ∷ []) ■ ⋆₂
⋆₂-mono ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ ⟨ L' , ⟨ M' , ⟨ N' , _ ⟩ ⟩ ⟩ ⟨ L⊆ , ⟨ M⊆ , ⟨ N⊆ , _ ⟩ ⟩ ⟩ =
  ⋆-mono ⟨ ⋆ ⟨ L , ⟨ M , ptt ⟩ ⟩ , ⟨ N , ptt ⟩ ⟩ ⟨ ⋆ ⟨ L' , ⟨ M' , ptt ⟩ ⟩ , ⟨ N' , ptt ⟩ ⟩
         ⟨ ⋆-mono ⟨ L , ⟨ M , ptt ⟩ ⟩ ⟨ L' , ⟨ M' , ptt ⟩ ⟩ ⟨ L⊆ , ⟨ M⊆ , ptt ⟩ ⟩ , ⟨ N⊆ , ptt ⟩ ⟩

⋆₂-consis : consistent _~_ (■ ∷ ■ ∷ ■ ∷ []) ■ ⋆₂
⋆₂-consis ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ ⟨ L' , ⟨ M' , ⟨ N' , _ ⟩ ⟩ ⟩ ⟨ L~ , ⟨ M~ , ⟨ N~ , _ ⟩ ⟩ ⟩ =
  ⋆-consis ⟨ ⋆ ⟨ L , ⟨ M , ptt ⟩ ⟩ , ⟨ N , ptt ⟩ ⟩ ⟨ ⋆ ⟨ L' , ⟨ M' , ptt ⟩ ⟩ , ⟨ N' , ptt ⟩ ⟩
           ⟨ ⋆-consis ⟨ L , ⟨ M , ptt ⟩ ⟩ ⟨ L' , ⟨ M' , ptt ⟩ ⟩ ⟨ L~ , ⟨ M~ , ptt ⟩ ⟩ , ⟨ N~ , ptt ⟩ ⟩

ΛΛ-mono : monotone (∁ (ν (ν ■)) ∷ []) ■ ΛΛ
ΛΛ-mono ⟨ F , _ ⟩ ⟨ F' , _ ⟩ ⟨ F⊆ , _ ⟩ =
  Λ-mono ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩
    ⟨ (λ X X' X⊆ → Λ-mono ⟨ F X , ptt ⟩ ⟨ F' X' , ptt ⟩ ⟨ F⊆ X X' X⊆ , ptt ⟩) , ptt ⟩

ΛΛ-consis : consistent _~_ (∁ (ν (ν ■)) ∷ []) ■ ΛΛ
ΛΛ-consis ⟨ F , _ ⟩ ⟨ F' , _ ⟩ ⟨ F~ , _ ⟩ =
  Λ-consis ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩
    ⟨ (λ X X' X~ → Λ-consis ⟨ F X , ptt ⟩ ⟨ F' X' , ptt ⟩ ⟨ F~ X X' X~ , ptt ⟩) , ptt ⟩


{- a function of two arguments, consistent in both, is consistent -}
ΛΛ-con : ∀ {F : 𝒫 Value → 𝒫 Value → 𝒫 Value}
  → (∀ X X' Y Y' → Every _~_ X X' → Every _~_ Y Y' → Every _~_ (F X Y) (F X' Y'))
  → Con (ΛΛ ⟨ F , ptt ⟩)
ΛΛ-con {F} F~ =
  lower (ΛΛ-consis ⟨ F , ptt ⟩ ⟨ F , ptt ⟩ ⟨ (λ X X' X~ Y Y' Y~ → lift (F~ X X' Y Y' X~ Y~)) , ptt ⟩)

closD-mono : ∀ n → monotone (∁ (ν (ν ■)) ∷ replicate n ■) ■ (closD n)
closD-mono n ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F⊆ , Ds⊆ ⟩ =
  ⋆-mono ⟨ ΛΛ ⟨ F , ptt ⟩ , ⟨ 𝒯 n Ds , ptt ⟩ ⟩ ⟨ ΛΛ ⟨ F' , ptt ⟩ , ⟨ 𝒯 n Ds' , ptt ⟩ ⟩
    ⟨ ΛΛ-mono ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F⊆ , ptt ⟩ , ⟨ 𝒯-mono n Ds Ds' Ds⊆ , ptt ⟩ ⟩

closD-consis : ∀ n → consistent _~_ (∁ (ν (ν ■)) ∷ replicate n ■) ■ (closD n)
closD-consis n ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ =
  ⋆-consis ⟨ ΛΛ ⟨ F , ptt ⟩ , ⟨ 𝒯 n Ds , ptt ⟩ ⟩ ⟨ ΛΛ ⟨ F' , ptt ⟩ , ⟨ 𝒯 n Ds' , ptt ⟩ ⟩
    ⟨ ΛΛ-consis ⟨ F , ptt ⟩ ⟨ F' , ptt ⟩ ⟨ F~ , ptt ⟩ , ⟨ 𝒯-consis n Ds Ds' Ds~ , ptt ⟩ ⟩

{- Congruences ------------------------------------------------------------------}

nthD-≃ : ∀ {n} (Ds Es : Results (𝒫 Value) (replicate n ■)) → RRs (replicate n ■) Ds Es
  → ∀ i → nthD Ds i ≃ nthD Es i
nthD-≃ {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ D≃ , _ ⟩ zero = lower D≃
nthD-≃ {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ ⟨ _ , Ds≃ ⟩ (suc i) = nthD-≃ Ds Es Ds≃ i

nthD⇒RRs : ∀ {n} (Ds Es : Results (𝒫 Value) (replicate n ■)) → (∀ i → nthD Ds i ≃ nthD Es i)
  → RRs (replicate n ■) Ds Es
nthD⇒RRs {zero} _ _ _ = ptt
nthD⇒RRs {suc n} ⟨ D , Ds ⟩ ⟨ E , Es ⟩ eq = ⟨ lift (eq zero) , nthD⇒RRs Ds Es (λ i → eq (suc i)) ⟩

𝒯-≃ : ∀ n {Ds Es} → (∀ i → nthD Ds i ≃ nthD Es i) → 𝒯 n Ds ≃ 𝒯 n Es
𝒯-≃ n {Ds} {Es} eq = mono-≃ (𝒯-mono n) (nthD⇒RRs Ds Es eq)

⋆-≃ : ∀ {D D' E E'} → D ≃ D' → E ≃ E' → ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩ ≃ ⋆ ⟨ D' , ⟨ E' , ptt ⟩ ⟩
⋆-≃ D≃ E≃ = mono-≃ ⋆-mono ⟨ lift D≃ , ⟨ lift E≃ , ptt ⟩ ⟩

proj-≃ : ∀ {n} (i : Fin n) {D E} → D ≃ E → proj i ⟨ D , ptt ⟩ ≃ proj i ⟨ E , ptt ⟩
proj-≃ i D≃ = mono-≃ (proj-mono i) ⟨ lift D≃ , ptt ⟩

inl-≃ : ∀ {D E} → D ≃ E → inl ⟨ D , ptt ⟩ ≃ inl ⟨ E , ptt ⟩
inl-≃ D≃ = mono-≃ inl-mono ⟨ lift D≃ , ptt ⟩

inr-≃ : ∀ {D E} → D ≃ E → inr ⟨ D , ptt ⟩ ≃ inr ⟨ E , ptt ⟩
inr-≃ D≃ = mono-≃ inr-mono ⟨ lift D≃ , ptt ⟩

{- case analysis, whose branches are compared on nonempty consistent finite sets -}
𝒞-≃ : ∀ {D D' F F' G G'} → D ≃ D'
  → (∀ v V → (v ∷ V) ≈ (v ∷ V) → F (mem (v ∷ V)) ≃ F' (mem (v ∷ V)))
  → (∀ v V → (v ∷ V) ≈ (v ∷ V) → G (mem (v ∷ V)) ≃ G' (mem (v ∷ V)))
  → 𝒞 ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞 ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
𝒞-≃ {F = F} {F'} {G} {G'} D≃ F≃ G≃ =
  ⟨ H {B = F} {F'} {G} {G'} (proj₁ D≃) (λ v V c → proj₁ (F≃ v V c)) (λ v V c → proj₁ (G≃ v V c))
  , H {B = F'} {F} {G'} {G} (proj₂ D≃) (λ v V c → proj₂ (F≃ v V c)) (λ v V c → proj₂ (G≃ v V c)) ⟩
  where
  H : ∀ {A A' B B' C C'} → A ⊆ A' → (∀ v V → (v ∷ V) ≈ (v ∷ V) → B (mem (v ∷ V)) ⊆ B' (mem (v ∷ V)))
    → (∀ v V → (v ∷ V) ≈ (v ∷ V) → C (mem (v ∷ V)) ⊆ C' (mem (v ∷ V)))
    → 𝒞 ⟨ A , ⟨ B , ⟨ C , ptt ⟩ ⟩ ⟩ ⊆ 𝒞 ⟨ A' , ⟨ B' , ⟨ C' , ptt ⟩ ⟩ ⟩
  H A⊆ B⊆ C⊆ w (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ (left d) (all d d∈)) , ⟨ B⊆ v V c w w∈ , c ⟩ ⟩ ⟩ ⟩
  H A⊆ B⊆ C⊆ w (inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ (right d) (all d d∈)) , ⟨ C⊆ v V c w w∈ , c ⟩ ⟩ ⟩ ⟩

letD-≃ : ∀ {D D' F F'} → D ≃ D' → (∀ V → V ≢ [] → V ≈ V → F (mem V) ≃ F' (mem V))
  → letD ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ letD ⟨ D' , ⟨ F' , ptt ⟩ ⟩
letD-≃ {F = F} {F'} D≃ F≃ = ⋆-≃ (Λ-≃ {F} {F'} F≃) D≃

ΛΛ-≃ : ∀ {F F' : 𝒫 Value → 𝒫 Value → 𝒫 Value} → (∀ X Y → F X Y ≃ F' X Y)
  → ΛΛ ⟨ F , ptt ⟩ ≃ ΛΛ ⟨ F' , ptt ⟩
ΛΛ-≃ eq = Λ-≃ (λ V _ _ → Λ-≃ (λ U _ _ → eq (mem V) (mem U)))

{- the same, from equal operands (a binder's on equal arguments) -}
𝒞-RR : ∀ {D F G D' F' G'} → RRs (■ ∷ ν ■ ∷ ν ■ ∷ []) ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
  → 𝒞 ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ 𝒞 ⟨ D' , ⟨ F' , ⟨ G' , ptt ⟩ ⟩ ⟩
𝒞-RR {F = F} {G} {F' = F'} {G'} ⟨ D≃ , ⟨ F≃ , ⟨ G≃ , _ ⟩ ⟩ ⟩ =
  𝒞-≃ {F = F} {F'} {G} {G'} (lower D≃) (λ _ _ _ → lower (F≃ _ _ ≃-refl)) (λ _ _ _ → lower (G≃ _ _ ≃-refl))

letD-RR : ∀ {D F D' F'} → RRs (■ ∷ ν ■ ∷ []) ⟨ D , ⟨ F , ptt ⟩ ⟩ ⟨ D' , ⟨ F' , ptt ⟩ ⟩
  → letD ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ letD ⟨ D' , ⟨ F' , ptt ⟩ ⟩
letD-RR {F = F} {F' = F'} ⟨ D≃ , ⟨ F≃ , _ ⟩ ⟩ = letD-≃ {F = F} {F'} (lower D≃) (λ _ _ _ → lower (F≃ _ _ ≃-refl))

{- β laws --------------------------------------------------------------------------}

Mono₁ : (𝒫 Value → 𝒫 Value) → Set₁
Mono₁ F = ∀ {X Y} → X ⊆ Y → F X ⊆ F Y

{- each element of F X needs only a finite, nonempty part of X -}
Finitary : (𝒫 Value → 𝒫 Value) → 𝒫 Value → Set
Finitary F X = ∀ w → w ∈ F X → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ X × w ∈ F (mem V)

{- (λx. F x) D means F D, for D consistent -}
Λ-β : ∀ {F D} → Mono₁ F → Finitary F D → Con D → letD ⟨ D , ⟨ F , ptt ⟩ ⟩ ≃ F D
Λ-β m fin cD =
  ⟨ (λ { w ⟨ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ → m V⊆ w w∈ })
  , (λ w w∈ → let ⟨ V , ⟨ ne , ⟨ V⊆ , w∈′ ⟩ ⟩ ⟩ = fin w w∈
              in ⟨ V , ⟨ ⟨ w∈′ , ⟨ ne , Con⇒≈ V cD V⊆ ⟩ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩) ⟩

{- a case contains its left branch on the left payloads of the scrutinee D,
   and its right branch on the right ones -}
𝒞-left : ∀ {D F G} → Finitary F (λ d → left d ∈ D) → Con (λ d → left d ∈ D)
  → F (λ d → left d ∈ D) ⊆ 𝒞 ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
𝒞-left fin c w w∈ with fin w w∈
... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
... | ⟨ v ∷ V , ⟨ _ , ⟨ V⊆ , w∈′ ⟩ ⟩ ⟩ = inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ w∈′ , Con⇒≈ (v ∷ V) c V⊆ ⟩ ⟩ ⟩ ⟩

𝒞-right : ∀ {D F G} → Finitary G (λ d → right d ∈ D) → Con (λ d → right d ∈ D)
  → G (λ d → right d ∈ D) ⊆ 𝒞 ⟨ D , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩
𝒞-right fin c w w∈ with fin w w∈
... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
... | ⟨ v ∷ V , ⟨ _ , ⟨ V⊆ , w∈′ ⟩ ⟩ ⟩ = inj₂ ⟨ v , ⟨ V , ⟨ V⊆ , ⟨ w∈′ , Con⇒≈ (v ∷ V) c V⊆ ⟩ ⟩ ⟩ ⟩

𝒞-inl-β : ∀ {D F G} → Mono₁ F → Finitary F D → Con D → 𝒞 ⟨ inl ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ F D
𝒞-inl-β {D} {F} {G} m fin cD =
  ⟨ (λ { w (inj₁ ⟨ v , ⟨ V , ⟨ ls , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) → m ls w w∈
       ; w (inj₂ ⟨ v , ⟨ V , ⟨ rs , _ ⟩ ⟩ ⟩) → ⊥-elim (rs v (here refl)) })
  , 𝒞-left {inl ⟨ D , ptt ⟩} {F} {G} fin cD ⟩

𝒞-inr-β : ∀ {D F G} → Mono₁ G → Finitary G D → Con D → 𝒞 ⟨ inr ⟨ D , ptt ⟩ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ ≃ G D
𝒞-inr-β {D} {F} {G} m fin cD =
  ⟨ (λ { w (inj₁ ⟨ v , ⟨ V , ⟨ ls , _ ⟩ ⟩ ⟩) → ⊥-elim (ls v (here refl))
       ; w (inj₂ ⟨ v , ⟨ V , ⟨ rs , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) → m rs w w∈ })
  , 𝒞-right {inr ⟨ D , ptt ⟩} {F} {G} fin cD ⟩

{- a function of two arguments, applied to T and E, contains its body on T and
   E, when that body needs only finite, nonempty parts of T and E -}
ΛΛ-β : ∀ {F T E} → Con T → Con E
  → (∀ w → w ∈ F T E → Σ[ V ∈ List Value ] Σ[ U ∈ List Value ]
       V ≢ [] × U ≢ [] × mem V ⊆ T × mem U ⊆ E × w ∈ F (mem V) (mem U))
  → F T E ⊆ ⋆ ⟨ ⋆ ⟨ ΛΛ ⟨ F , ptt ⟩ , ⟨ T , ptt ⟩ ⟩ , ⟨ E , ptt ⟩ ⟩
ΛΛ-β cT cE fin w w∈ with fin w w∈
... | ⟨ V , ⟨ U , ⟨ neV , ⟨ neU , ⟨ V⊆ , ⟨ U⊆ , w∈′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  ⟨ U , ⟨ ⟨ V , ⟨ ⟨ ⟨ w∈′ , ⟨ neU , Con⇒≈ U cE U⊆ ⟩ ⟩ , ⟨ neV , Con⇒≈ V cT V⊆ ⟩ ⟩ , ⟨ V⊆ , neV ⟩ ⟩ ⟩
      , ⟨ U⊆ , neU ⟩ ⟩ ⟩

{- finitely many elements of a let come from one finite part of its operand -}
letD-collect : ∀ {D F} → Mono₁ F → ∀ V → mem V ⊆ letD ⟨ D , ⟨ F , ptt ⟩ ⟩
  → Σ[ U ∈ List Value ] mem U ⊆ D × mem V ⊆ F (mem U)
letD-collect m [] _ = ⟨ [] , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩
letD-collect {D} m (w ∷ V) V⊆ with V⊆ w (here refl) | letD-collect m V (λ d d∈ → V⊆ d (there d∈))
... | ⟨ U₀ , ⟨ ⟨ w∈ , _ ⟩ , ⟨ U₀⊆ , _ ⟩ ⟩ ⟩ | ⟨ U , ⟨ U⊆ , V⊆F ⟩ ⟩ =
  ⟨ U₀ ++ U , ⟨ ++⊆ , (λ { _ (here refl) → m (λ d → ∈-++⁺ˡ) _ w∈ ; d (there d∈) → m (λ d → ∈-++⁺ʳ U₀) d (V⊆F d d∈) }) ⟩ ⟩
  where
  ++⊆ : mem (U₀ ++ U) ⊆ D
  ++⊆ d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ i = U₀⊆ d i
  ... | inj₂ i = U⊆ d i
