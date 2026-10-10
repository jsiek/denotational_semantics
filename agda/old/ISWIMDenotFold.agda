open import Agda.Primitive using (Level; lzero; lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic renaming (⊤ to ptop ; tt to ptt)
open import Data.Unit using (⊤; tt)
open import Primitives
open import ISWIM
open import Level using (Lift; lift; lower)
open import ModelISWIM
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
open import ScopedTuple hiding (𝒫)
open import Sig
open import Structures
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
  PVal-is-Shiftable : Shiftable (𝒫 Value)
  PVal-is-Shiftable = record { ⇑ = λ z → z ; var→val = λ x v → v ⊑ ⊥
      ; var→val-suc-shift = refl }

Val : Set₁
Val = Lift (lsuc lzero) Value

⌊_⌋ : Value → Val
⌊ v ⌋ = lift v

instance
  Val-is-Shiftable : Shiftable Val
  Val-is-Shiftable = record { var→val = λ x → lift ⊥ ; ⇑ = λ v → v 
                            ; var→val-suc-shift = refl }

  Val-is-Equiv : Equiv Val Val
  Val-is-Equiv = record { _≈_ = λ v w → Lift (lsuc lzero) (lower v ≘ lower w) }

  Val-is-EquivRel : EquivRel Val
  Val-is-EquivRel = record {
       ≈-refl = λ { (lift v) → lift (≘-refl) }
     ; ≈-sym = λ { (lift eq) → lift (≘-sym eq) }
     ; ≈-trans = λ { (lift eq1) (lift eq2) → lift (≘-trans eq1 eq2) } }

  Val-is-ShiftId : ShiftId Val
  Val-is-ShiftId = record { shift-id = λ x → lift ⟨ ⊑-⊥ , ⊑-⊥ ⟩ }

  Val-is-Relatable : Relatable Val Val
  Val-is-Relatable = record { var→val≈ = λ x → lift ⟨ ⊑-⊥ , ⊑-⊥ ⟩
                              ; shift≈ = λ z → z }

_≲_ : 𝒫 Value → 𝒫 Value → Set
D₁ ≲ D₂ = ∀ (v : Value) → D₁ v → D₂ v

≲-refl : {D : 𝒫 Value} → D ≲ D
≲-refl {D} v Dv = Dv

≲-trans : {D₁ D₂ D₃ : 𝒫 Value} → D₁ ≲ D₂ → D₂ ≲ D₃ → D₁ ≲ D₃
≲-trans D12 D23 v D₁v = D23 v (D12 v D₁v)

{- Denotational Equality. -}

data _≃_ : 𝒫 Value → 𝒫 Value → Set₁ where
  equal : ∀{D₁ D₂} → D₁ ≲ D₂  →  D₂ ≲ D₁  → D₁ ≃ D₂

to : ∀{D₁ D₂} → D₁ ≃ D₂ → D₁ ≲ D₂
to (equal a b) = a

from : ∀{D₁ D₂} → D₁ ≃ D₂ → D₂ ≲ D₁
from (equal a b) = b

≃-refl : {D : 𝒫 Value} → D ≃ D
≃-refl {D} = equal ≲-refl ≲-refl

≃-sym : {D₁ D₂ : 𝒫 Value} → D₁ ≃ D₂ → D₂ ≃ D₁
≃-sym (equal t f) = equal f t

≃-trans : {D₁ D₂ D₃ : 𝒫 Value} → D₁ ≃ D₂ → D₂ ≃ D₃ → D₁ ≃ D₃
≃-trans (equal d12 d21) (equal d23 d32) =
    equal (≲-trans d12 d23) (≲-trans d32 d21)

instance
  PVal-is-Equiv : Equiv (𝒫 Value) (𝒫 Value)
  PVal-is-Equiv = record { _≈_ = λ D₁ D₂ → (D₁ ≃ D₂) }

  PVal-is-EquivRel : EquivRel (𝒫 Value)
  PVal-is-EquivRel = record { ≈-refl = λ v → ≃-refl
      ; ≈-sym = ≃-sym ; ≈-trans = ≃-trans }


{- Denotational Function Abstraction -}

𝐹 : (Val → 𝒫 Value) → 𝒫 Value
𝐹 f ⊥ = ⊤
𝐹 f (const k) = Bot
𝐹 f (v ↦ w) = f (lift v) w
𝐹 f (u ⊔ v) = 𝐹 f u × 𝐹 f v

𝐹-≲ : ∀{f f′ : Val → 𝒫 Value}
   → (∀{v : Val} → f v ≲ f′ v)
   → 𝐹 f ≲ 𝐹 f′
𝐹-≲ f≲f′ ⊥ 𝐹fv = tt
𝐹-≲ f≲f′ (v ↦ w) 𝐹fv = f≲f′ w 𝐹fv
𝐹-≲ f≲f′ (u ⊔ v) ⟨ 𝐹fu , 𝐹fv ⟩ =
  ⟨ 𝐹-≲ f≲f′ u 𝐹fu , 𝐹-≲ f≲f′ v 𝐹fv ⟩

𝐹-≃ : ∀{f₁ f₂ : Val → 𝒫 Value}
     → (∀{v₁ v₂ : Val} → lower v₁ ≡ lower v₂ → f₁ v₁ ≃ f₂ v₂)
     → 𝐹 f₁ ≃ 𝐹 f₂
𝐹-≃ f₁=f₂ = equal (𝐹-≲ (λ v f₁v₁v → to (f₁=f₂ refl) v f₁v₁v))
                  (𝐹-≲ (λ v f₂v₁v → from (f₁=f₂ refl) v f₂v₁v))

{- Denotational Function Application -} 

infixl 7 _○_
_○_ : (𝒫 Value) → (𝒫 Value) → (𝒫 Value)
_○_ D₁ D₂ w = Σ[ v ∈ Value ] wf v × D₁ (v ↦ w) × D₂ v 

○-≲ : ∀{v₁ v₂ w₁ w₂ : 𝒫 Value}
    → v₁ ≲ w₁  →  v₂ ≲ w₂
    →  (v₁ ○ v₂) ≲ (w₁ ○ w₂)
○-≲ v₁≲w₁ v₂≲w₂ v ⟨ d , ⟨ wfd , ⟨ v₁[d↦v] , v₂d ⟩ ⟩ ⟩ =
    ⟨ d , ⟨ wfd , ⟨ v₁≲w₁ (d ↦ v) v₁[d↦v] , v₂≲w₂ d v₂d  ⟩ ⟩ ⟩

○-≃ : ∀{v₁ v₂ w₁ w₂ : 𝒫 Value}
    → v₁ ≃ w₁  →  v₂ ≃ w₂
    →  (v₁ ○ v₂) ≃ (w₁ ○ w₂)
○-≃ v₁≃w₁ v₂≃w₂  = equal (○-≲ (to v₁≃w₁) (to v₂≃w₂))
                         (○-≲ (from v₁≃w₁) (from v₂≃w₂))

{- Denotations of Terms -}

denot-op : (op : Op) → Tuple (sig op) (Bind Val (𝒫 Value)) → 𝒫 Value
denot-op (lit p k) ptt v = ℘ {p} k v
denot-op lam ⟨ f , ptt ⟩ = 𝐹 f
denot-op app ⟨ dᶠ , ⟨ dₐ , ptt ⟩ ⟩ = dᶠ ○ dₐ

instance
  Denot-is-Foldable : Foldable Val (𝒫 Value)
  Denot-is-Foldable = record {
        ret = λ v w → w ⊑ lower v
      ; fold-op = denot-op }

Env3 : Set₁
Env3 = Var → Val

Denot : Set₁
Denot = Env3 → 𝒫 Value

𝐸 : Term → Denot
𝐸 M ρ = fold ρ M

{- What this definition ammounts to. -}
𝐸-var : ∀{γ x w} →  𝐸 (` x ) γ w ≡ (w ⊑ lower (γ x))
𝐸-var = ?
𝐸-lit : ∀{γ p k} →  𝐸 ($ p k) γ ≡ ℘ {p} k
𝐸-lit = refl
𝐸-λ : ∀{γ N} →  𝐸 (ƛ N) γ ≡ 𝐹 (λ d → 𝐸 N (d • γ))
𝐸-λ = refl
𝐸-· : ∀{γ L M} →  𝐸 (L · M) γ ≡ (𝐸 L γ) ○ (𝐸 M γ)
𝐸-· = refl

denot-op-shift : {op : Op}{rs↑ rs : Tuple (sig op) (Bind Val (𝒫 Value))}
   → zip (λ {b} → _⩳_{b = b}) rs↑ rs
   → denot-op op rs↑ ≃ denot-op op rs
denot-op-shift {lam} ⟨ z , _ ⟩ = 𝐹-≃ ?
denot-op-shift {app} ⟨ eq₁ , ⟨ eq₂ , _  ⟩ ⟩ = ○-≃ eq₁ eq₂
denot-op-shift {lit p x} zrs = equal (λ v z → z) (λ v z → z)

instance
  PVal-is-ShiftId : ShiftId (𝒫 Value)
  PVal-is-ShiftId = record { shift-id = λ x → ≃-refl }

  PVal-is-FoldShift : FoldShift Val (𝒫 Value)
  PVal-is-FoldShift = record { shift-ret = λ v → extensionality λ x → refl
         ; op-shift = denot-op-shift }

  PVal-is-Relatable : Relatable (𝒫 Value) (𝒫 Value)
  PVal-is-Relatable = record { var→val≈ = λ x → ≃-refl ; shift≈ = λ x → x }

denot-op-equiv : ∀ {op : Op} {rs₁ rs₂}
    → zip (λ {b} → _⩳_{b = b}) rs₁ rs₂
    → denot-op op rs₁ ≃ denot-op op rs₂
denot-op-equiv {lam} {⟨ f₁ , _ ⟩} {⟨ f₂ , _ ⟩} ⟨ eq , _ ⟩ = 𝐹-≃ ?
denot-op-equiv {app} ⟨ x₁≃y₁ , ⟨ x₂≃y₂ , _ ⟩ ⟩ = ○-≃ x₁≃y₁ x₂≃y₂
denot-op-equiv {lit p x} rs₁=rs₂ = ≃-refl

instance
  Val²PVal²-is-Similar : Similar Val Val (𝒫 Value) (𝒫 Value)
      {{EqC = PVal-is-Equiv}}
  Val²PVal²-is-Similar = record {
      ret≈ = λ { (lift ⟨ lt , gt ⟩) → equal (λ v vv1 → ⊑-trans vv1 lt)
                                             λ v vv2 → ⊑-trans vv2 gt }
      ; op⩳ = denot-op-equiv }


𝐸-subst : ∀ {ρ ρ′ : Env3} {σ : Subst} {M : Term}
   → σ ⨟ ρ ⩰ ρ′
   → 𝐸 (⟪ σ ⟫ M) ρ  ≃ 𝐸 M ρ′
𝐸-subst {ρ}{ρ′}{σ}{M} σ⨟ρ⩰ρ′ =
  fold-subst-fusion{σ = σ} M σ⨟ρ⩰ρ′ denot-op-equiv

{-

A nice benefit of using 𝒫 Value in the environment is then you get a
nice equality like the following for substitution!

-}

{-
𝐸-substitution : ∀ {ρ : Env3} {M N : Term}
   → 𝐸 (M [ N ]) ρ  ≃ 𝐸 M (𝐸 N ρ • ρ)
𝐸-substitution {ρ}{M}{N} =
    𝐸-subst {ρ}{𝐸 N ρ • ρ}{subst-zero N}{M} G
    where
    G : subst-zero N ⨟ ρ ⩰ (𝐸 N ρ • ρ)
    G zero = {!!} {- ≃-refl -}
    G (suc x) = ≃-refl
-}

_`≲_ : Env3 → Env3 → Set
_`≲_ γ δ = (x : Var) → lower (γ x) ≡ lower (δ x)

≲-extend : ∀{γ δ : Env3}{d : Val}
  → γ `≲ δ
  → (d • γ) `≲ (d • δ)
≲-extend γ≲δ zero = refl
≲-extend γ≲δ (suc x) = γ≲δ x

≲-env : ∀{M : Term}{γ δ}
  → γ `≲ δ
  → 𝐸 M γ ≲ 𝐸 M δ
≲-env {` x} γ≲δ v Dγv = {!!} {- γ≲δ x v Dγv -}
≲-env {$ p k} γ≲δ v Dγv = Dγv
≲-env {ƛ N} γ≲δ ⊥ Dγv = tt
≲-env {ƛ N} γ≲δ (const k) Dγv = Dγv
≲-env {ƛ N}{γ}{δ} γ≲δ (v ↦ w) Dγv =
  𝐹-≲ {λ d → 𝐸 N (d • γ)}{λ d → 𝐸 N (d • δ)} G (v ↦ w) Dγv
  where
  G : ∀{v₁ : Val} → 𝐸 N (v₁ • γ) ≲ 𝐸 N (v₁ • δ)
  G {v₁} v₂ 𝐸[N][v₁•γ]v₂ =
    ≲-env {N}{(v₁ • γ)}{(v₁ • δ)} (≲-extend γ≲δ) v₂ 𝐸[N][v₁•γ]v₂
≲-env {ƛ N} γ≲δ (v ⊔ w) ⟨ Dγv , Dγw ⟩ =
   ⟨ ≲-env {ƛ N} γ≲δ v Dγv , ≲-env {ƛ N} γ≲δ w Dγw ⟩
≲-env {L · M} γ≲δ v ⟨ w , ⟨ wfw , ⟨ E[L]w→v , E[M]w ⟩ ⟩ ⟩ =
  let IH1 = ≲-env {L} γ≲δ (w ↦ v) E[L]w→v in
  let IH2 = ≲-env {M} γ≲δ w E[M]w in
  ⟨ w , ⟨ wfw , ⟨ IH1 , IH2 ⟩ ⟩ ⟩


𝐹-○-≲-aux : ∀{Dₐ : 𝒫 Value}{ℐ : Ideal Dₐ}{N}{γ}{v′ v}
  → Dₐ v′
  → 𝐸 N (⌊ v′ ⌋ • γ) v
  → wf v′
  → 𝐸 N (Dₐ • γ) v
𝐹-○-≲-aux {Dₐ}{ℐ}{N}{γ}{v′}{v} Dₐv′ EN[v′•γ]v wfv′ = 
  ≲-env{N}{⌊ v′ ⌋ • γ}{Dₐ • γ} G v EN[v′•γ]v
  where G : (⌊ v′ ⌋ • γ) `≲ (Dₐ • γ)
        G zero w v′w = Ideal.⊑-closed ℐ wfv′ Dₐv′ v′w
        G (suc x) = ≲-refl

𝐹-○-≲ : ∀ {γ}{N : Term}{Dₐ : 𝒫 Value}{ℐ : Ideal Dₐ}
  → (𝐹 (λ D → 𝐸 N (D • γ)) ○ Dₐ)  ≲  𝐸 N (Dₐ • γ)
𝐹-○-≲ {γ} {N} {Dₐ} {ℐ} ⊥ ⟨ v , ⟨ wfv , ⟨ EN[v•γ]⊥ , Dₐv ⟩ ⟩ ⟩ =
  𝐹-○-≲-aux {Dₐ}{ℐ}{N = N} Dₐv EN[v•γ]⊥ wfv
𝐹-○-≲ {γ} {N} {Dₐ} {ℐ} (const k) ⟨ v′ , ⟨ wfv′ , ⟨ EN[v′•γ]k , Dₐv′ ⟩ ⟩ ⟩ =
  𝐹-○-≲-aux {Dₐ}{ℐ}{N = N} Dₐv′ EN[v′•γ]k wfv′
𝐹-○-≲ {γ} {N} {Dₐ} {ℐ} (v ↦ w) ⟨ v′ , ⟨ wfv′ , ⟨ EN[v′•γ]vw , Dₐv′ ⟩ ⟩ ⟩ =
  𝐹-○-≲-aux {Dₐ}{ℐ}{N = N} Dₐv′ EN[v′•γ]vw wfv′
𝐹-○-≲ {γ} {N} {Dₐ}{ℐ} (v ⊔ w) ⟨ v′ , ⟨ wfv′ , ⟨ EN[v′•γ]vw , Dₐv′ ⟩ ⟩ ⟩ =
  𝐹-○-≲-aux {Dₐ}{ℐ}{N = N} Dₐv′ EN[v′•γ]vw wfv′

{-
: ∀ {γ}{N : Term}{D : 𝒫 Value}{ℐ : Ideal Dₐ}
  → (v : Value)
  → 𝐸 N (D • γ) v
  → Σ[ γ' ∈ Env3 ] 𝐸 N γ′ v
-}

≲-𝐹-○ : ∀ {γ}{N : Term}{Dₐ : 𝒫 Value}{ℐ : Ideal Dₐ}
  → 𝐸 N (Dₐ • γ)  ≲  (𝐹 (λ D → 𝐸 N (D • γ)) ○ Dₐ)
≲-𝐹-○ {γ} {N} {Dₐ} {ℐ} ⊥ EN[Dₐ•γ] = {!!}
{-
    ⟨ ⊥ , ⟨ wf-bot , ⟨ {!!} , (Ideal.⊑-closed ℐ wf-bot {!!} {!!}) ⟩ ⟩ ⟩
-}
≲-𝐹-○ {γ} {N} {Dₐ} {ℐ} (const k) EN[Dₐ•γ] = {!!}
≲-𝐹-○ {γ} {N} {Dₐ} {ℐ} (v ↦ w) EN[Dₐ•γ] = {!!}
≲-𝐹-○ {γ} {N} {Dₐ} {ℐ} (v ⊔ w) EN[Dₐ•γ] = {!!}

𝐹-○ : ∀ {γ}{N : Term}{Dₐ : 𝒫 Value}{ℐ : Ideal Dₐ}
  → (𝐹 (λ D → 𝐸 N (D • γ)) ○ Dₐ)  ≃  𝐸 N (Dₐ • γ)
𝐹-○ {γ}{N}{Dₐ}{ℐ} = equal (𝐹-○-≲{γ}{N}{Dₐ}{ℐ})  (≲-𝐹-○{γ}{N}{Dₐ}{ℐ})  

{-
{-

𝐸-reduce : ∀ {γ : Env3} {M N}
  → M —→ N
    -------------
  → 𝐸 M γ ≃ 𝐸 N γ
𝐸-reduce (ξ₁-rule L→L′) = {!!}
𝐸-reduce (ξ₂-rule VL M→M′) = {!!}
𝐸-reduce {γ} (β-rule {N}{M} VM) = G
  where
  EQ1 : 𝐸 ((ƛ N) · M) γ ≡ 𝐹 (λ D → 𝐸 N (D • γ)) ○ 𝐸 M γ
  EQ1 = refl
  EQ2 : 𝐸 N (𝐸 M γ • γ) ≃ 𝐸 (N [ M ]) γ
  EQ2 = ≃-sym (𝐸-substitution {γ}{N}{M})

  G : 𝐸 ((ƛ N) · M) γ ≃ 𝐸 (N [ M ]) γ
  G = {!!}

{-

𝐹 (λ D → 𝐸 N (D • γ)) ○ 𝐸 M γ   =    𝐸 N (𝐸 M γ • γ)


-}

𝐸-reduce δ-rule = {!!}


{-------------------------------------------------------------------------}


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

instance
  Value-is-Equiv : Equiv Value Value
  Value-is-Equiv = record { _≈_ = _≘_ }
  
  Value-is-EquivRel : EquivRel Value
  Value-is-EquivRel = record { ≈-refl = λ v → ≘-refl ; ≈-sym = ≘-sym ; ≈-trans = ≘-trans }

  Value-is-Shiftable : Shiftable Value
  Value-is-Shiftable = record { var→val = λ x → ⊥ ; ⇑ = λ v → v
                              ; var→val-suc-shift = refl }
                              
  Value-is-Relatable : Relatable Value Value
  Value-is-Relatable = record { var→val≈ = λ x → ⟨ ⊑-⊥ , ⊑-⊥ ⟩
           ; shift≈ = λ z → z }


{-
  private
   instance
     ≡⇑-Value-is-Equiv : Equiv Value Value
     ≡⇑-Value-is-Equiv = record { _≈_ = λ v w → v ≘ ⇑ w }
     
     ≡⇑-PVal-Equiv : Equiv (𝒫 Value) (𝒫 Value)
     ≡⇑-PVal-Equiv = record { _≈_ = λ D₁ D₂ → D₁ ≃ ⇑ D₂ }
-}


{-
    Value-is-ShiftId : ShiftId Value
    Value-is-ShiftId = record { shift-id = λ x → ⟨ ⊑-⊥ , ⊑-⊥ ⟩ }
-}

{--------     Analogous to ModelCurryConst    ---------------------------------}

𝐹-⊔ : ∀{f : 𝒫 Value → 𝒫 Value}{u v : Value}
  → 𝐹 f u → 𝐹 f v → 𝐹 f (u ⊔ v)
𝐹-⊔ d1 d2 = ⟨ d1 , d2 ⟩  

¬k∈𝐹 : ∀{D : 𝒫 Value → 𝒫 Value} {v : Value}
         {b : Base}{k : base-rep b}
        → const {b} k ∈ v → ¬ 𝐹 D v
¬k∈𝐹 {v = ⊥} () 𝐹v
¬k∈𝐹 {v = const k′} k∈v 𝐹v = 𝐹v
¬k∈𝐹 {v = v₁ ↦ v₂} () 𝐹v
¬k∈𝐹 {v = v₁ ⊔ v₂} (inj₁ x) ⟨ fst₁ , snd₁ ⟩ = ¬k∈𝐹 x fst₁
¬k∈𝐹 {v = v₁ ⊔ v₂} (inj₂ y) ⟨ fst₁ , snd₁ ⟩ = ¬k∈𝐹 y snd₁

𝐹-∈ : ∀{D : 𝒫 Value → 𝒫 Value} {v w : Value}
        → w ∈ v → 𝐹 D v → 𝐹 D w
𝐹-∈ {D} {⊥} {w} refl tt = tt
𝐹-∈ {D} {const k} {w} w∈v ()
𝐹-∈ {D} {v₁ ↦ v₂} {w} refl 𝐹v = 𝐹v
𝐹-∈ {D} {v₁ ⊔ v₂} {w} (inj₁ x) ⟨ 𝐹v₁ , 𝐹v₂ ⟩ = 𝐹-∈ x 𝐹v₁
𝐹-∈ {D} {v₁ ⊔ v₂} {w} (inj₂ y) ⟨ 𝐹v₁ , 𝐹v₂ ⟩ = 𝐹-∈ y 𝐹v₂

𝐹-⊆ : ∀{f : 𝒫 Value → 𝒫 Value} {v w : Value}
        → w ⊆ v → 𝐹 f v → 𝐹 f w
𝐹-⊆ {f} {v} {⊥} w⊆v 𝐹fv = tt
𝐹-⊆ {f} {v} {const k} w⊆v 𝐹fv = ⊥-elim (contradiction 𝐹fv (¬k∈𝐹 (w⊆v refl)))
𝐹-⊆ {f} {v} {w₁ ↦ w₂} w⊆v 𝐹fv = 𝐹-∈ (w⊆v refl) 𝐹fv
𝐹-⊆ {f} {v} {w₁ ⊔ w₂} w⊆v 𝐹fv
    with ⊔⊆-inv w⊆v
... | ⟨ w₁⊆v , w₂⊆v ⟩ = ⟨ 𝐹-⊆ w₁⊆v 𝐹fv , 𝐹-⊆ w₂⊆v 𝐹fv ⟩

{-
  The following adapts WFDenot by changing the environment parameters
  into Value parameters.
-}
record IdealFun (f : 𝒫 Value → 𝒫 Value) : Set₁ where
  field ⊑-input : ∀{u v}{w} → wf u → wf v → wf w → u ⊑ v → f ⌊ u ⌋ w → f ⌊ v ⌋ w
        ⊑-closed : ∀{u}{v w} → wf u → wf v → wf w
                 → w ⊑ v → f ⌊ u ⌋ v → f ⌊ u ⌋ w
        ⊔-closed : ∀{w u v} → wf w → wf u → wf v
                 → f ⌊ w ⌋ u → f ⌊ w ⌋ v → f ⌊ w ⌋ (u ⊔ v)
        ~-closed : ∀{w y u v} → wf w → wf y → wf u → wf v
                 → w ~ y → f ⌊ w ⌋ u → f ⌊ y ⌋ v → u ~ v

𝐹-dom-cod : ∀ {f : 𝒫 Value → 𝒫 Value}{v w : Value}{fv : AllFun v}
       → IdealFun f → wf v → wf w
       → dom v {fv} ⊑ w → 𝐹 f v → 𝐹 f (dom v {fv} ↦ cod v {fv})
𝐹-dom-cod {v = ⊥} {w} {()} ifd wfv wfw dv⊑w 𝐹v
𝐹-dom-cod {v = const k} {w} {()} ifd wfv wfw dv⊑w 𝐹v
𝐹-dom-cod {v = v₁ ↦ v₂} {w} {fv} ifd wfv wfw dv⊑w 𝐹v = 𝐹v
𝐹-dom-cod {f}{v₁ ⊔ v₂} {w} {⟨ fv₁ , fv₂ ⟩} ifd (wf-⊔ v₁~v₂ wfv₁ wfv₂) wfw
    dv⊑w ⟨ 𝐹v₁ , 𝐹v₂ ⟩ =
  let dv₁⊑w = ⊔⊑R dv⊑w in
  let dv₂⊑w = ⊔⊑L dv⊑w in
  let f-dv₁-cv₁ : f ⌊ (dom v₁) ⌋ (cod v₁)
      f-dv₁-cv₁ = 𝐹-dom-cod{v = v₁} ifd wfv₁ wfw dv₁⊑w 𝐹v₁ in
  let f-dv₂-cv₂ : f ⌊ (dom v₂) ⌋ (cod v₂)
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

𝐹-⊑ : ∀{f : 𝒫 Value → 𝒫 Value}{v w : Value}
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

𝐹-~ : ∀{f : 𝒫 Value → 𝒫 Value} {u v : Value}
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
-}
-}

{-
-}
