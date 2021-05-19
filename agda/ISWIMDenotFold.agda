open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic renaming (⊤ to ptop ; tt to ptt)
open import Data.Unit using (⊤; tt)
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
open import WFDenotMod value_struct ordering consistent

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

{--------     Analogous to CurryConst         ---------------------------------}

{-
  The below 𝐹 operator is like ℱ except that it does not have an environment
  parameter.
-}

𝐹 : (Value → 𝒫 Value) → 𝒫 Value
𝐹 f ⊥ = ⊤
𝐹 f (const k) = Bot
𝐹 f (v ↦ w) = f v w
𝐹 f (u ⊔ v) = 𝐹 f u × 𝐹 f v

{--------     Analogous to ModelCurryConst    ---------------------------------}

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

{-
  The following adapts WFDenod by changing the environment parameters
  into Value parameters.
-}
record IdealFun (f : Value → 𝒫 Value) : Set₁ where
  field ⊑-input : ∀{u v}{w} → wf u → wf v → wf w → u ⊑ v → f u w → f v w
        ⊑-closed : ∀{u}{v w} → wf u → wf v → wf w
                 → w ⊑ v → f u v → f u w
        ⊔-closed : ∀{w u v} → wf w → wf u → wf v
                 → f w u → f w v → f w (u ⊔ v)
        ~-closed : ∀{w y u v} → wf w → wf y → wf u → wf v
                 → w ~ y → f w u → f y v → u ~ v

𝐹-dom-cod : ∀ {f : Value → 𝒫 Value}{v w : Value}{fv : AllFun v}
       → IdealFun f → wf v → wf w
       → dom v {fv} ⊑ w → 𝐹 f v → 𝐹 f (dom v {fv} ↦ cod v {fv})
𝐹-dom-cod {v = ⊥} {w} {()} ifd wfv wfw dv⊑w 𝐹v
𝐹-dom-cod {v = const k} {w} {()} ifd wfv wfw dv⊑w 𝐹v
𝐹-dom-cod {v = v₁ ↦ v₂} {w} {fv} ifd wfv wfw dv⊑w 𝐹v = 𝐹v
𝐹-dom-cod {f}{v₁ ⊔ v₂} {w} {⟨ fv₁ , fv₂ ⟩} ifd (wf-⊔ v₁~v₂ wfv₁ wfv₂) wfw
    dv⊑w ⟨ 𝐹v₁ , 𝐹v₂ ⟩ =
  let dv₁⊑w = ⊔⊑R dv⊑w in
  let dv₂⊑w = ⊔⊑L dv⊑w in
  let f-dv₁-cv₁ : f (dom v₁) (cod v₁)
      f-dv₁-cv₁ = 𝐹-dom-cod{v = v₁} ifd wfv₁ wfw dv₁⊑w 𝐹v₁ in
  let f-dv₂-cv₂ : f (dom v₂) (cod v₂)
      f-dv₂-cv₂ = 𝐹-dom-cod{v = v₂} ifd wfv₂ wfw dv₂⊑w 𝐹v₂ in
  let wf-dv₁ = wf-dom{v₁}{w} wfv₁ wfw fv₁ dv₁⊑w in
  let wf-dv₂ = wf-dom{v₂}{w} wfv₂ wfw fv₂ dv₂⊑w  in
  let wf-cv₁ = (wf-cod{v₁}{w} wfv₁ wfw fv₁ dv₁⊑w) in
  let wf-cv₂ = (wf-cod{v₂}{w} wfv₂ wfw fv₂ dv₂⊑w) in
  let dv₁~dv₂ = consistent-⊑ (~-refl{w}{wfw}) dv₁⊑w dv₂⊑w in
  let wf-dv₁⊔dv₂ = wf-⊔ dv₁~dv₂ wf-dv₁ wf-dv₂ in
  let f-dv₁⊔dv₂-cv₁ = IdealFun.⊑-input ifd wf-dv₁ wf-dv₁⊔dv₂ wf-cv₁
                          (⊑-conj-R1 ⊑-refl) f-dv₁-cv₁ in
  let f-dv₁⊔dv₂-cv₂ = IdealFun.⊑-input ifd wf-dv₂ wf-dv₁⊔dv₂ wf-cv₂
                          (⊑-conj-R2 ⊑-refl) f-dv₂-cv₂  in
  IdealFun.⊔-closed ifd wf-dv₁⊔dv₂ wf-cv₁ wf-cv₂ f-dv₁⊔dv₂-cv₁ f-dv₁⊔dv₂-cv₂

𝐹-⊑ : ∀{f : Value → 𝒫 Value}{v w : Value}
       → IdealFun f → wf v → wf w
        → w ⊑ v → 𝐹 f v → 𝐹 f w
𝐹-⊑ d wfv wfw ⊑-⊥ 𝐹fuv = tt
𝐹-⊑ d wfv wfw ⊑-const ()
𝐹-⊑ d wfv (wf-⊔ c xx yy) (⊑-conj-L w⊑v w⊑v₁) 𝐹fuv =
    ⟨ (𝐹-⊑ d wfv xx w⊑v 𝐹fuv) , (𝐹-⊑ d wfv yy w⊑v₁ 𝐹fuv) ⟩
𝐹-⊑ d (wf-⊔ x wfv wfv₁) wfw (⊑-conj-R1 w⊑v) ⟨ fst₁ , snd₁ ⟩ =
    𝐹-⊑ d wfv wfw w⊑v fst₁
𝐹-⊑ d (wf-⊔ x wfv wfv₁) wfw (⊑-conj-R2 w⊑v) ⟨ fst₁ , snd₁ ⟩ =
    𝐹-⊑ d wfv₁ wfw w⊑v snd₁
𝐹-⊑ {f} d wfv (wf-fun wfw₁ wfw₂)
    (⊑-fun {v} {v′} {w₁} {w₂} v′⊆v fv′ dv′⊑w₁ w₂⊑cv′) 𝐹fuv =
    let wfv′ = wf-⊆ v′⊆v wfv in
    let wfdv′ = wf-dom wfv′ wfw₁ fv′ dv′⊑w₁ in
    let wfcv′ = wf-cod wfv′ wfw₁ fv′ dv′⊑w₁ in
    let fv′ = 𝐹-⊆ v′⊆v 𝐹fuv in
    let fdv′cv′ = 𝐹-dom-cod{v = v′} d wfv′ wfw₁ dv′⊑w₁ fv′ in
    let fw₁cv′ = IdealFun.⊑-input d wfdv′ wfw₁ wfcv′ dv′⊑w₁ fdv′cv′ in
    IdealFun.⊑-closed d wfw₁ wfcv′ wfw₂ w₂⊑cv′ fw₁cv′

𝐹-~ : ∀{f : Value → 𝒫 Value} {u v : Value}
    → IdealFun f → wf u → wf v
    → 𝐹 f u → 𝐹 f v → u ~ v
𝐹-~ {f} {⊥} {v} wfd wfu wfv d1 d2 = tt
𝐹-~ {f} {const k} {v} wfd wfu wfv () d2
𝐹-~ {f} {u₁ ↦ u₂} {⊥} wfd  wfu wfv d1 d2 = tt
𝐹-~ {f} {u₁ ↦ u₂} {const x} wfd wfu wfv d1 ()
𝐹-~ {f} {u₁ ↦ u₂} {v₁ ↦ v₂} wfd (wf-fun wfu₁ wfu₂) (wf-fun wfv₁ wfv₂) d1 d2
    with consistent? u₁ v₁
... | no u₁~̸v₁ = inj₂ u₁~̸v₁
... | yes u₁~v₁ = inj₁ ⟨ u₁~v₁ , u₂~v₂ ⟩
      where u₂~v₂ = IdealFun.~-closed wfd wfu₁ wfv₁ wfu₂ wfv₂ u₁~v₁ d1 d2
𝐹-~ {f} {u₁ ↦ u₂} {v₁ ⊔ v₂} wfd 
    (wf-fun wfu₁ wfu₂) (wf-⊔ v₁~v₂ wfv₁ wfv₂) d1 ⟨ fst' , snd' ⟩ =
    ⟨ 𝐹-~ {f}{u₁ ↦ u₂}{v₁} wfd (wf-fun wfu₁ wfu₂) wfv₁ d1 fst' ,
      𝐹-~ {f}{u₁ ↦ u₂}{v₂} wfd (wf-fun wfu₁ wfu₂) wfv₂ d1 snd' ⟩
𝐹-~ {f} {u₁ ⊔ u₂} {v} wfd 
    (wf-⊔ u₁~u₂ wfu₁ wfu₂) wfv ⟨ fst' , snd' ⟩ d2 =
    ⟨ 𝐹-~ {f}{u₁}{v} wfd wfu₁ wfv fst' d2 , 𝐹-~{f}{u₂}{v} wfd wfu₂ wfv snd' d2 ⟩

{- UNDER CONSTRUCTION -}

{-
postulate
  extensionality : ∀ {ℓ : Level}{A : Set}{B : Set ℓ} {f g : A → B}
    → (∀ (x : A) → f x ≡ g x)
      -----------------------
    → f ≡ g
-}

{- Equivalence of the 𝒫 Value part of denotations -}

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
denot-op (lit p k) ptt v = ℘ {p} k v
denot-op lam ⟨ f , ptt ⟩ = 𝐹 (λ v → lower (f v))
denot-op app ⟨ lift dᶠ , ⟨ lift dₐ , ptt ⟩ ⟩ = dᶠ ○ dₐ

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
  denot-op-shift {lam} {⟨ f↑ , ptt ⟩} {⟨ f , ptt ⟩} ⟨ z , ptt ⟩ =
      {!!}
  denot-op-shift {app} {rs↑} {rs} zrs = {!!}
  denot-op-shift {lit p x} {rs↑} {rs} zrs = {!!}

  instance
    Value-is-ShiftId : ShiftId Value
    Value-is-ShiftId = record { shift-id = λ x → ⟨ ⊑-⊥ , ⊑-⊥ ⟩ }

    PVal-is-FoldShift : FoldShift Value (𝒫 Value)
    PVal-is-FoldShift = record { shift-ret = λ v → extensionality λ x → refl
           ; op-shift = denot-op-shift }

  instance
    Value-is-EquivRel : EquivRel Value
    Value-is-EquivRel = record { ≈-refl = λ v → ≘-refl ; ≈-sym = ≘-sym ; ≈-trans = ≘-trans }

    Value-is-Relatable : Relatable Value Value
    Value-is-Relatable = record { var→val≈ = λ x → ⟨ ⊑-⊥ , ⊑-⊥ ⟩ ; shift≈ = λ z → z }

    PVal-is-Relatable : Relatable (𝒫 Value) (𝒫 Value)
    PVal-is-Relatable = record {
        var→val≈ = λ x v → record { to = λ x → x ; from = λ z → z } ;
        shift≈ = λ x v → record { to = Utilities.Iso.to (x v) ; from = Utilities.Iso.from (x v) } }

{-
  𝐹-equiv : ∀(v : Value) → (f₁ : Value → Lift lzero (𝒫 Value)) → (f₂ : Value → Lift lzero (𝒫 Value))
          → (f₁=f₂ : {v₁ v₂ : Value} → v₁ ≘ v₂ → (f₁ v₁) ⩳ (f₂ v₂))
          → 𝐹 (λ v₁ → lower (f₁ v₁)) v → 𝐹 (λ v₁ → lower (f₂ v₁)) v
  𝐹-equiv v f₁ f₂ f₁=f₂ = {!!}
-}

  denot-op-equiv : ∀ {op : Op} {rs₁ rs₂ : Tuple (sig op) (Bind Value (𝒫 Value))}
      → zip (λ {b} → _⩳_{V₁ = Value}{V₂ = Value}{C₁ = 𝒫 Value}{C₂ = 𝒫 Value}{b = b}) rs₁ rs₂
      → denot-op op rs₁ ≃′ denot-op op rs₂
  denot-op-equiv {lam} {⟨ f₁ , _ ⟩} {⟨ f₂ , _ ⟩} ⟨ eq , _ ⟩ v =
      record { to = λ x → {!!} ; from = {!!} }
  denot-op-equiv {app} {⟨ lift x₁ , ⟨ lift x₂ , _ ⟩ ⟩} {⟨ lift y₁ , ⟨ lift y₂ , _ ⟩ ⟩} ⟨ lift x₁≃y₁ , ⟨ lift x₂≃y₂ , _ ⟩ ⟩ v =
      record { to = λ { ⟨ w , ⟨ wfw , ⟨ x1w→v , x2w ⟩ ⟩ ⟩ →
                 ⟨ w , ⟨ wfw , ⟨ Utilities.Iso.to (x₁≃y₁ (w ↦ v)) x1w→v , Utilities.Iso.to (x₂≃y₂ w) x2w ⟩ ⟩ ⟩ } ;
               from = λ { ⟨ w , ⟨ wfw , ⟨ x1w→v , x2w ⟩ ⟩ ⟩ →
                 ⟨ w , ⟨ wfw , ⟨ Utilities.Iso.from (x₁≃y₁ (w ↦ v)) x1w→v , Utilities.Iso.from (x₂≃y₂ w) x2w ⟩ ⟩ ⟩ } }
  denot-op-equiv {lit p x} rs₁=rs₂ = λ v → record { to = λ z → z ; from = λ z → z }

  instance
    V²-PVal²-is-Similar : Similar Value Value (𝒫 Value) (𝒫 Value) {{EqC = PVal-is-Equiv}}
    V²-PVal²-is-Similar = record {
          ret≈ = λ { ⟨ v₁⊑v₂ , v₂⊑v₁ ⟩ v → record { to = λ v⊑v₁ → ⊑-trans v⊑v₁ v₁⊑v₂ ; from = λ v⊑v₂ → ⊑-trans v⊑v₂ v₂⊑v₁ } };
          op⩳ = denot-op-equiv }

{-

No instance of type Similar Value Value (Value → Set) (Value → Set)

subst-pres-denot : ∀ {ρ ρ′ : Env} {σ : Subst} {M : Term}
   → σ ⨟ ρ ⩰ ρ′
   → 𝐸 (⟪ σ ⟫ M) ρ  ≡ 𝐸 M ρ′
subst-pres-denot {ρ}{ρ′}{σ}{M} σ⨟ρ⩰ρ′ =
  let xx = fold-subst-fusion M σ⨟ρ⩰ρ′ {!!}
  in ?
  


-}

{-

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
