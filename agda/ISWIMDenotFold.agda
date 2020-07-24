open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Primitives
open import ISWIM
{- open import Level -}
open import ModelISWIM
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import ScopedTuple hiding (𝒫)
open import Sig
open import Structures
{-open import Syntax using (Shiftable; ShiftId) -}
open import Utilities using (_iff_)
open import Var

open import FoldMapFusion Op sig
open import Fold Op sig
open Structures.WithOpSig Op sig

module ISWIMDenotFold where

𝒫 : Set → Set₁
𝒫 V = V → Set

instance
  Value-is-Shiftable : Shiftable Value
  Value-is-Shiftable = record { var→val = λ x → ⊥ ; ⇑ = λ v → v
                              ; var→val-suc-shift = refl }
  PVal-is-Shiftable : Shiftable (𝒫 Value)
  PVal-is-Shiftable = record { ⇑ = λ z → z ; var→val = λ x v → v ⊑ ⊥
      ; var→val-suc-shift = refl }


{- Check the 𝐹-cong requirement needed for subst preserves denot
   fold. (See Experiment module in LambdaDenot.)  -}

{-
  The 𝐹 operator is like ℱ except that it does not have an environment
  parameter.
-}

𝐹 : (Value → 𝒫 Value) → 𝒫 Value
𝐹 f ⊥ = ⊤
𝐹 f (const k) = Bot
𝐹 f (v ↦ w) = f v w
𝐹 f (u ⊔ v) = 𝐹 f u × 𝐹 f v

𝐹-⊔ : ∀{f : Value → 𝒫 Value}{u v : Value}
  → 𝐹 f u → 𝐹 f v → 𝐹 f (u ⊔ v)
𝐹-⊔ d1 d2 = ⟨ d1 , d2 ⟩  

_≲′_ : 𝒫 Value → 𝒫 Value → Set
D₁ ≲′ D₂ = ∀ (v : Value) → wf v → D₁ v → D₂ v

𝐹-≲′ : ∀{f f′ : Value → 𝒫 Value}
   → (∀{v : Value} → wf v → f v ≲′ f′ v)
   → 𝐹 f ≲′ 𝐹 f′
𝐹-≲′ f≲f′ ⊥ wfv 𝐹fv = tt
𝐹-≲′ f≲f′ (v ↦ w) (wf-fun wfv wfw) 𝐹fv = f≲f′ wfv w wfw 𝐹fv
𝐹-≲′ f≲f′ (u ⊔ v) (wf-⊔ u~v wfu wfv) ⟨ 𝐹fu , 𝐹fv ⟩ =
  ⟨ 𝐹-≲′ f≲f′ u wfu 𝐹fu , 𝐹-≲′ f≲f′ v wfv 𝐹fv ⟩

¬k∈𝐹 : ∀{D : Value → 𝒫 Value} {v : Value}
         {b : Base}{k : base-rep b}
        → const {b} k ∈ v → ¬ 𝐹 D v
¬k∈𝐹 {v = ⊥} () 𝐹v
¬k∈𝐹 {v = const k′} k∈v 𝐹v = 𝐹v
¬k∈𝐹 {v = v₁ ↦ v₂} () 𝐹v
¬k∈𝐹 {v = v₁ ⊔ v₂} (inj₁ x) ⟨ fst₁ , snd₁ ⟩ = ¬k∈𝐹 x fst₁
¬k∈𝐹 {v = v₁ ⊔ v₂} (inj₂ y) ⟨ fst₁ , snd₁ ⟩ = ¬k∈𝐹 y snd₁

𝐹-∈ : ∀{D : Value → 𝒫 Value} {v w : Value}
        → w ∈ v → 𝐹 D v → 𝐹 D w
𝐹-∈ {D} {⊥} {w} refl tt = tt
𝐹-∈ {D} {const k} {w} w∈v ()
𝐹-∈ {D} {v₁ ↦ v₂} {w} refl 𝐹v = 𝐹v
𝐹-∈ {D} {v₁ ⊔ v₂} {w} (inj₁ x) ⟨ 𝐹v₁ , 𝐹v₂ ⟩ = 𝐹-∈ x 𝐹v₁
𝐹-∈ {D} {v₁ ⊔ v₂} {w} (inj₂ y) ⟨ 𝐹v₁ , 𝐹v₂ ⟩ = 𝐹-∈ y 𝐹v₂

𝐹-⊆ : ∀{f : Value → 𝒫 Value} {v w : Value}
        → w ⊆ v → 𝐹 f v → 𝐹 f w
𝐹-⊆ {f} {v} {⊥} w⊆v 𝐹fv = tt
𝐹-⊆ {f} {v} {const k} w⊆v 𝐹fv = ⊥-elim (contradiction 𝐹fv (¬k∈𝐹 (w⊆v refl)))
𝐹-⊆ {f} {v} {w₁ ↦ w₂} w⊆v 𝐹fv = 𝐹-∈ (w⊆v refl) 𝐹fv
𝐹-⊆ {f} {v} {w₁ ⊔ w₂} w⊆v 𝐹fv
    with ⊔⊆-inv w⊆v
... | ⟨ w₁⊆v , w₂⊆v ⟩ = ⟨ 𝐹-⊆ w₁⊆v 𝐹fv , 𝐹-⊆ w₂⊆v 𝐹fv ⟩

{- UNDER CONSTRUCTION -}

{-
postulate
  extensionality : ∀ {ℓ : Level}{A : Set}{B : Set ℓ} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
-}

{- Eqivalence of the 𝒫 Value part of denotations -}

_≃′_ : 𝒫 Value → 𝒫 Value → Set₁
D₁ ≃′ D₂ = ∀ (v : Value) → D₁ v iff D₂ v

instance
  Value-is-Equiv : Equiv Value Value
  Value-is-Equiv = record { _≈_ = _≘_ }

  PVal-is-Equiv : Equiv (𝒫 Value) (𝒫 Value)
  PVal-is-Equiv = record { _≈_ = _≃′_ }

{-
𝐹-cong : ∀ {f g : Bind Value (𝒫 Value) (ν ■)}
       → _⩳_ {b = ν ■} f g   →   𝐹 f ≡ 𝐹 g
𝐹-cong {f}{g} f=g = extensionality {lsuc lzero} G
    where
    G : (v : Value) → 𝐹 f v ≡ 𝐹 g v
    G ⊥ = refl
    G (const k) = refl
    G (v ↦ w) = f=g {v}{v} ⟨ ⊑-refl , ⊑-refl ⟩ w 
    G (u ⊔ v) = cong₂ _×_ (G u) (G v)
-}
{-
  open RelBind {lsuc lzero}{Value}{𝒫 Value}{Value}{𝒫 Value} _≡_ _≡_
-}

infixl 7 _○_
_○_ : (𝒫 Value) → (𝒫 Value) → (𝒫 Value)
_○_ D₁ D₂ w = Σ[ v ∈ Value ] wf v × D₁ (v ↦ w) × D₂ v 

denot-op : (op : Op) → Tuple (sig op) (Bind Value (𝒫 Value))
         → 𝒫 Value
denot-op (lit p k) tt v = ℘ {p} k v
denot-op lam ⟨ f , tt ⟩ = 𝐹 (λ v → lower (f v))
denot-op app ⟨ lift dᶠ , ⟨ lift dₐ , tt ⟩ ⟩ = dᶠ ○ dₐ

instance
  Denot-is-Foldable : Foldable Value (𝒫 Value)
  Denot-is-Foldable = record { ret = λ v w → w ⊑ v; fold-op = denot-op }

𝐸 : Term → Env → 𝒫 Value
𝐸 M ρ = fold ρ M


module _ where
{-
  private
   instance
     ≡⇑-Value-is-Equiv : Equiv Value Value
     ≡⇑-Value-is-Equiv = record { _≈_ = λ v w → v ≘ ⇑ w }
     
     ≡⇑-PVal-Equiv : Equiv (𝒫 Value) (𝒫 Value)
     ≡⇑-PVal-Equiv = record { _≈_ = λ D₁ D₂ → D₁ ≃′ ⇑ D₂ }
-}

  denot-op-shift : {op : Op}{rs↑ rs : Tuple (sig op) (Bind Value (𝒫 Value))}
     → zip (λ{b} → _⩳_{V₁ = Value}{Value}{𝒫 Value}{𝒫 Value}{b}) rs↑ rs
     → denot-op op rs↑ ≃′ denot-op op rs
  denot-op-shift {lam} {⟨ f↑ , tt ⟩} {⟨ f , tt ⟩} ⟨ z , tt ⟩ =
      {!!}
  denot-op-shift {app} {rs↑} {rs} zrs = {!!}
  denot-op-shift {lit p x} {rs↑} {rs} zrs = {!!}

  instance
    Value-is-ShiftId : ShiftId Value
    Value-is-ShiftId = record { shift-id = λ x → {!!} {-refl-} }

    PVal-is-FoldShift : FoldShift Value (𝒫 Value)
    PVal-is-FoldShift = record { shift-ret = λ v → extensionality λ x → refl
           ; op-shift = denot-op-shift }
  
{-
subst-pres-denot : ∀ {ρ ρ′ : Env} {σ : Subst} {M : Term}
   → σ ⨟ ρ ⩰ ρ′
   → 𝐸 (⟪ σ ⟫ M) ρ  ≡ 𝐸 M ρ′
subst-pres-denot {ρ}{ρ′}{σ}{M} σ⨟ρ⩰ρ′ =
  fold-subst-fusion M σ⨟ρ⩰ρ′ {!!}


instance
  Value-is-Relatable : Relatable Value Value
  Value-is-Relatable = record { var→val≈ = λ _ → ⟨ ⊑-⊥ , ⊑-⊥ ⟩
                              ; shift≈ = λ x → x }
                              
  Value-is-Similar : Similar Value Value (𝒫 Value) (𝒫 Value) {{Eq = PVal-is-Equiv}}
  Value-is-Similar = record {
      ret≈ = λ { ⟨ v12 , v21 ⟩ →
                 lift (λ v → ⟨ (λ vv1 → ⊑-trans vv1 v12) ,
                               (λ vv2 → ⊑-trans vv2 v21) ⟩) }
    ; op⩳ = {!!} }

subst-pres-denot : ∀ {ρ ρ′ : Env} {σ : Subst} {M : Term}
   → 𝐸 (⟪ σ ⟫ M) ρ  ≡ 𝐸 M ρ′
subst-pres-denot {ρ}{σ}{M} =
   fold-fold-fusion {Vˢ = Value}{𝒫 Value}{Value}{𝒫 Value}
      {Value}{𝒫 Value} ? M ? ? ? ? ?
-}

{-
op-cong : (op : Op) (rs rs' : Tuple (sig op) (Bind Value (𝒫 Value)))
   → zip _⩳_ rs rs' → denot-op op rs ≡ denot-op op rs'
op-cong lam ⟨ r , tt ⟩ ⟨ r' , tt ⟩ ⟨ eq , tt ⟩ = 𝐹-cong eq
op-cong app ⟨ r , ⟨ rs , tt ⟩ ⟩ ⟨ r' , ⟨ rs' , tt ⟩ ⟩
            ⟨ refl , ⟨ refl , tt ⟩ ⟩ = refl
-}
{-
    open import Preserve Op sig
    SPFE : SubstPreserveFoldEnv DenotFold
    SPFE = record { shiftᶜ = λ d → d ; op-cong = op-cong
             ; shift-ret = λ vᶠ → refl
             ; op-shift = λ op {rs↑}{rs} z → op-cong op rs↑ rs z }
-}
