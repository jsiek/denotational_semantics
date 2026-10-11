module Compiler.Model.Graph.Domain.ISWIM.Ops where

open import Primitives
open import SetsAsPredicates
open import abt.Sig using (Sig; ν; ■) public
open import abt.Var using (Var) public
open import abt.GSubst using (_•_) public
open import NewSigUtil
open import NewDOpSig
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (Any; here; there)
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


{- Denotational Operators -----------------------------------------------------}

{- \st -}
⋆ : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
⋆ ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ w = 
    Σ[ V ∈ List Value ] 
      (V ↦ w ∈ D₁) × (mem V ⊆ D₂) × V ≢ []

ℬ : (B : Base) → base-rep B → DOp (𝒫 Value) []
ℬ B k _ (const {B′} k′) = Σ[ B≡ ∈ B ≡ B′ ] (subst base-rep B≡ k) ≡ k′
ℬ B k _ _ = False

pair : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
{- pairs are strict: each half requires the other component to be nonempty -}
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ⦅ f ∣ = Σ[ v ∈ Value ] f ∈ D₁ × v ∈ D₂
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ∣ v ⦆ = Σ[ f ∈ Value ] f ∈ D₁ × v ∈ D₂
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ _ = False

car : DOp (𝒫 Value) (■ ∷ [])
car ⟨ D , _ ⟩ f = ⦅ f ∣ ∈ D

cdr : DOp (𝒫 Value) (■ ∷ [])
cdr ⟨ D , _ ⟩ v = ∣ v ⦆ ∈ D

nthD : ∀ {n}{ℓ}{A : Set ℓ} → Results A (replicate n ■) → (i : Fin n) → Result A ■
nthD {.(suc _)} ⟨ D , Ds ⟩ zero = D
nthD {.(suc _)} ⟨ D , Ds ⟩ (suc i) = nthD Ds i

𝒯 : ∀ (n : ℕ) → DOp (𝒫 Value) (replicate n ■)
𝒯 zero Ds ⟨⟩ = True
{- tuples are strict: a tuple has a value only when all of its components do -}
𝒯 (suc n) Ds (tup[_]_ {n'} i d) =
  Σ[ n≡ ∈ n' ≡ suc n ] d ∈ (nthD Ds (subst Fin n≡ i)) × (∀ j → nonempty (nthD Ds j))
𝒯 n Ds d = False

proj : ∀ {n} → Fin n → DOp (𝒫 Value) (■ ∷ [])
proj i ⟨ D , _ ⟩ d = (tup[ i ] d) ∈ D

inl : DOp (𝒫 Value) (■ ∷ [])
inl ⟨ D , _ ⟩ (left v) = v ∈ D
inl ⟨ D , _ ⟩ _ = False

inr : DOp (𝒫 Value) (■ ∷ [])
inr ⟨ D , _ ⟩ (right v) = v ∈ D
inr ⟨ D , _ ⟩ _ = False

𝒞 : DOp (𝒫 Value) (■ ∷ ν ■ ∷ ν ■ ∷ [])
𝒞 ⟨ D , ⟨ E , ⟨ F , _ ⟩ ⟩ ⟩ w = Σ[ v ∈ Value ] Σ[ V ∈ List Value ] (∀ d → d ∈ mem (v ∷ V) → left d ∈ D) × w ∈ E (mem (v ∷ V)) 
          ⊎ (Σ[ v ∈ Value ] Σ[ V ∈ List Value ] (∀ d → d ∈ mem (v ∷ V) → right d ∈ D) × w ∈ F (mem (v ∷ V)))

Λ : DOp (𝒫 Value) (ν ■ ∷ [])
Λ ⟨ f , _ ⟩ (V ↦ w) = w ∈ f (mem V) × V ≢ []
Λ ⟨ f , _ ⟩ ν = True
Λ ⟨ f , _ ⟩ d = False


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

pair-mono : monotone (■ ∷ ■ ∷ []) ■ pair
pair-mono ⟨ D , ⟨ E , _ ⟩ ⟩ ⟨ D' , ⟨ E' , _ ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩ = lift G
  where
  G : pair ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ pair ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  G ⦅ f ∣ ⟨ v , ⟨ f∈D , v∈E ⟩ ⟩ = ⟨ v , ⟨ D⊆ f f∈D , E⊆ v v∈E ⟩ ⟩
  G ∣ v ⦆ ⟨ f , ⟨ f∈D , v∈E ⟩ ⟩ = ⟨ f , ⟨ D⊆ f f∈D , E⊆ v v∈E ⟩ ⟩

car-mono : monotone (■ ∷ []) ■ car
car-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : car ⟨ D , ptt ⟩ ⊆ car ⟨ D' , ptt ⟩
  G u u∈ = D⊆ ⦅ u ∣ u∈

cdr-mono : monotone (■ ∷ []) ■ cdr
cdr-mono ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D⊆) , _ ⟩ = lift G
  where
  G : cdr ⟨ D , _ ⟩ ⊆ cdr ⟨ D' , _ ⟩
  G v v∈ = D⊆ ∣ v ⦆ v∈

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
  G d (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , d∈ ⟩ ⟩ ⟩) = 
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d z → D⊆ (left d) (V⊆ d z)) 
         , lower (FL⊆ (mem (v ∷ V)) (mem (v ∷ V)) (λ d z → z)) d d∈ ⟩ ⟩ ⟩
  G d (inj₂ ⟨ v , ⟨ V , ⟨ V⊆ , d∈ ⟩ ⟩ ⟩) = 
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d z → D⊆ (right d) (V⊆ d z)) 
         , lower (FR⊆ (mem (v ∷ V)) (mem (v ∷ V)) (λ d z → z)) d d∈ ⟩ ⟩ ⟩

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
  G ⦅ u ∣ ()
  G ∣ v ⦆ ()
  G (left d) ()
  G (right d) ()

{- D, provided that each of the n sets in Ds is nonempty (for strict closures) -}
guard-n : ∀ n → Results (𝒫 Value) (replicate n ■) → 𝒫 Value → 𝒫 Value
guard-n n Ds D w = (∀ i → nonempty (nthD Ds i)) × w ∈ D

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
  G ⦅ u ∣ ⦅ u' ∣ ⟨ v , ⟨ u∈ , v∈ ⟩ ⟩  ⟨ v' , ⟨ u'∈ , v'∈ ⟩ ⟩ = 
    D~ u u' u∈ u'∈
  G ⦅ u ∣ ∣ v ⦆ u∈ v∈ = tt
  G ∣ v ⦆ ⦅ u ∣ v∈ u∈ = tt
  G ∣ v ⦆ ∣ v' ⦆ ⟨ u , ⟨ u∈ , v∈ ⟩ ⟩ ⟨ u' , ⟨ u'∈ , v'∈ ⟩ ⟩ = E~ v v' v∈ v'∈

car-consis : consistent _~_ (■ ∷ []) ■ car
car-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (car ⟨ D , ptt ⟩) (car ⟨ D' , ptt ⟩)
  G u u' u∈ u'∈ = D~ ⦅ u ∣ ⦅ u' ∣ u∈ u'∈

cdr-consis : consistent _~_ (■ ∷ []) ■ cdr
cdr-consis ⟨ D , _ ⟩ ⟨ D' , _ ⟩ ⟨ (lift D~) , _ ⟩ = lift G
  where
  G : Every _~_ (cdr ⟨ D , ptt ⟩) (cdr ⟨ D' , ptt ⟩)
  G v v' v∈ v'∈ = D~ ∣ v ⦆ ∣ v' ⦆ v∈ v'∈

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
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩ ) (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , w∈ ⟩ ⟩ ⟩)
    = lower (FL~ (mem (v ∷ V)) (mem (v' ∷ V')) V≈V') u w u∈ w∈
    where
    V≈V' : ∀ d d' → d ∈ mem (v ∷ V) → d' ∈ mem (v' ∷ V') → d ~ d'
    V≈V' d d' d∈ d'∈ = D~ (left d) (left d') (V⊆ d d∈) (V⊆' d' d'∈)
  G u w (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩) (inj₂ ⟨ v' , ⟨ V' , ⟨ V⊆' , w∈ ⟩ ⟩ ⟩) = 
    ⊥-elim (D~ (left v) (right v') (V⊆ v (here refl)) (V⊆' v' (here refl)))
  G u w (inj₂ ⟨ v , ⟨ V , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩) (inj₁ ⟨ v' , ⟨ V' , ⟨ V⊆' , w∈ ⟩ ⟩ ⟩) = 
    ⊥-elim (D~ (right v) (left v') (V⊆ v (here refl)) (V⊆' v' (here refl)))
  G u w (inj₂ ⟨ v , ⟨ V , ⟨ V⊆ , u∈ ⟩ ⟩ ⟩) (inj₂ ⟨ v' , ⟨ V' , ⟨ V⊆' , w∈ ⟩ ⟩ ⟩)
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
