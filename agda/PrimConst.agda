open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; cong; cong₂)
open import Data.Nat using (ℕ; suc ; zero; _+_; _<_; _≤_) renaming (_⊔_ to max)
open import Data.Nat.Properties
  using (n≤0⇒n≡0; ≤-refl; ≤-trans; m≤m⊔n; n≤m⊔n; ≤-step; ⊔-mono-≤;
         +-mono-≤-<; +-mono-<-≤; +-comm; n≤1+n;
         ≤-pred)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (contradiction)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Unit using (⊤; tt)

open import Primitives
open import ValueConst
open import Consistency
open import Values
open import CurryConst

module PrimConst where

℘k→BelowConstk : ∀{B : Base}{k : base-rep B}{v : Value}
    → ℘ {base B} k v
    → BelowConst k v
℘k→BelowConstk {B} {k} {⊥} ℘kv = tt
℘k→BelowConstk {B} {k} {const {B′} k′} ℘kv
    with base-eq? B B′
... | yes eq rewrite eq = ℘kv
... | no neq = ℘kv
℘k→BelowConstk {B} {k} {v ↦ v₁} ℘kv = ℘kv
℘k→BelowConstk {B} {k} {v ⊔ v₁} ℘kv =
  ⟨ (℘k→BelowConstk {B}{k}{v} (proj₁ ℘kv)) ,
    (℘k→BelowConstk {B}{k}{v₁} (proj₂ ℘kv)) ⟩

℘-∈ : ∀{p}{k : rep p}{v w : Value}
   → ℘ {p} k v
   → w ∈ v
     ------------
   → ℘ {p} k w
℘-∈ {p} {k} {⊥} {w} ℘kv refl = tt
℘-∈ {p} {k} {const {b′} k′} {w} ℘kv refl
    with p
... | b ⇒ p′ = ⊥-elim ℘kv
... | base b
    with base-eq? b b′
... | yes refl = ℘kv
... | no neq = ⊥-elim ℘kv
℘-∈ {p} {k} {v₁ ↦ v₂} {w} ℘kv refl
    with p
... | base b = ⊥-elim ℘kv
... | b ⇒ p′ = ℘kv
℘-∈ {p} {k} {v₁ ⊔ v₂} {w} ⟨ fst₁ , snd₁ ⟩ (inj₁ x) = ℘-∈ fst₁ x
℘-∈ {p} {k} {v₁ ⊔ v₂} {w} ⟨ fst₁ , snd₁ ⟩ (inj₂ y) = ℘-∈ snd₁ y

℘-⊆ : ∀{p}{k : rep p}{v w : Value}
   → ℘ {p} k v
   → w ⊆ v
     ------------
   → ℘ {p} k w
℘-⊆ {p} {k} {v} {⊥} ℘kv w⊆v = ℘-∈ ℘kv (w⊆v refl)
℘-⊆ {p} {k} {v} {const k′} ℘kv w⊆v = ℘-∈ ℘kv (w⊆v refl)
℘-⊆ {p} {k} {v} {w₁ ↦ w₂} ℘kv w⊆v = ℘-∈ ℘kv (w⊆v refl)
℘-⊆ {p} {k} {v} {w₁ ⊔ w₂} ℘kv w⊆v
   with ⊔⊆-inv w⊆v
... | ⟨ w₁⊆v , w₂⊆v ⟩ = ⟨ ℘-⊆ ℘kv w₁⊆v  , ℘-⊆ ℘kv w₂⊆v ⟩

℘-⊑ : ∀{P}{k : rep P}{v w : Value}
   → wf w
   → ℘ {P} k v
   → w ⊑ v
     ------------
   → ℘ {P} k w
℘-⊑ {P} {k} {v} {.⊥} wfw ℘kv ⊑-⊥ =
   tt
℘-⊑ {P} {k} {.(const _)} {.(const _)} wfw ℘kv ⊑-const =
   ℘kv
℘-⊑ {P} {k} {v} {w₁ ⊔ w₂} (wf-⊔ w₁~w₂ wfw₁ wfw₂) ℘kv (⊑-conj-L w⊑v w⊑v₁) =
   ⟨ ℘-⊑ wfw₁ ℘kv w⊑v , ℘-⊑ wfw₂ ℘kv w⊑v₁ ⟩
℘-⊑ {P} {k} {.(_ ⊔ _)} {w} wfw ℘kv (⊑-conj-R1 w⊑v) =
   ℘-⊑ wfw (proj₁ ℘kv) w⊑v
℘-⊑ {P} {k} {.(_ ⊔ _)} {w} wfw ℘kv (⊑-conj-R2 w⊑v) =
   ℘-⊑ wfw (proj₂ ℘kv) w⊑v
℘-⊑ {P}{f}{v}{w = w₁ ↦ w₂} (wf-fun wfw₁ wfw₂) ℘kv
    (⊑-fun{u′ = v′} v′⊆v fv′ dv′⊑w₁ w₂⊑cv′)
    with P
... | b ⇒ P′ =
      let pdc = ℘-dom-cod {fv = fv′} (℘-⊆ ℘kv v′⊆v) dv′⊑w₁ wfw₁ in
      let IH = ℘-⊑ wfw₂ (proj₂ (proj₂ pdc)) w₂⊑cv′ in
      ⟨ proj₁ pdc , ⟨ proj₁ (proj₂ pdc) , IH ⟩ ⟩

    where
    ℘-dom-cod : ∀{b : Base}{p : Prim}{f : rep (b ⇒ p)}{v w₁ : Value}
                {fv : AllFun v}
              → ℘ {b ⇒ p} f v → dom v {fv} ⊑ w₁ → wf w₁
              → Σ[ k ∈ base-rep b ] const {b} k ⊑ w₁ × ℘ {p} (f k) (cod v {fv})
    ℘-dom-cod {b} {p} {f} {⊥} {w₁} {()} ℘fv dv⊑w₁ wfw
    ℘-dom-cod {b} {p} {f} {const x} {w₁} {()} ℘fv dv⊑w₁ wfw
    ℘-dom-cod {b} {p} {f} {v₁ ↦ v₂} {w₁} {fv} ⟨ k , ⟨ fst₂ , snd₁ ⟩ ⟩
       dv⊑w₁ wfw =
         ⟨ k , ⟨ ⊑-trans fst₂ dv⊑w₁ , snd₁  ⟩ ⟩
    ℘-dom-cod {b} {p} {f} {v₁ ⊔ v₂} {w₁} {⟨ fst₂ , snd₂ ⟩} ⟨ fst₁ , snd₁ ⟩
       dv⊑w₁ wfw
        with ℘-dom-cod{b}{p}{f}{v₁}{w₁} fst₁ (⊔⊑R dv⊑w₁) wfw
        | ℘-dom-cod{b}{p}{f}{v₂}{w₁} snd₁ (⊔⊑L dv⊑w₁) wfw
    ... | ⟨ k1 , ⟨ k1<w1 , pfk1 ⟩ ⟩ | ⟨ k2 , ⟨ k2<w1 , pfk2 ⟩ ⟩
        with base-eq? b b | consistent-⊑{w₁}{w₁} (~-refl{w₁}{wfw}) k1<w1 k2<w1
    ... | yes refl | refl = ⟨ k1 , ⟨ k2<w1 , ⟨ pfk1 , pfk2 ⟩ ⟩ ⟩
    ... | no neq | k1~k2 = ⊥-elim (neq refl)

℘-⊑ {P}{f}{v}{w = w₁ ↦ w₂} wfw ℘kv (⊑-fun{u′ = v′} v′⊆v fv′ dv′⊑w₁ w₂⊑cv′)
    | base b
    with AllFun∈ fv′
... | ⟨ v₁ , ⟨ v₂ , v₁↦v₂∈v′ ⟩ ⟩ =
      let bk = ℘k→BelowConstk{b}{f}{v} ℘kv in
      let v12∈v = v′⊆v v₁↦v₂∈v′ in
      lemma {v} v12∈v bk
    where
    lemma : ∀{v} → v₁ ↦ v₂ ∈ v → BelowConst f v → Bot
    lemma {⊥} () bkv
    lemma {const k′} () bkv
    lemma {v₁ ↦ v₂} refl ()
    lemma {v₁ ⊔ v₂} (inj₁ x) ⟨ fst₁ , snd₁ ⟩ = lemma x fst₁
    lemma {v₁ ⊔ v₂} (inj₂ y) ⟨ fst₁ , snd₁ ⟩ = lemma y snd₁

℘-⊔ : ∀{P : Prim} {k : rep P} {u v : Value}
    → ℘ {P} k u → ℘ {P} k v → ℘ {P} k (u ⊔ v)
℘-⊔ ℘u ℘v = ⟨ ℘u , ℘v ⟩


℘-~ : ∀{P : Prim } {D : rep P} {u v : Value}
    → ℘ {P} D u → ℘ {P} D v
    → u ~ v
℘-~ {P} {D} {⊥} {v} pu pv = tt
℘-~ {P} {D} {const k} {⊥} pu pv = tt
℘-~ {P} {D} {const {b} k} {const {b′} k′} pu pv
    with P
... | b₁ ⇒ p' = ⊥-elim pu
℘-~ {P} {D} {const {b} k} {const {b′} k′} pu pv
    | base b₁
    with base-eq? b₁ b | pu | base-eq? b₁ b′ | pv
... | yes refl | refl | no neq2 | ()
... | no neq1 | () | _ | _
... | yes refl | refl | yes refl | refl
    with base-eq? b₁ b₁
... | yes refl = refl
... | no neq = neq refl
℘-~ {P} {D} {const {b} k} {v ↦ v₁} pu pv
    with P
... | base b′ = ⊥-elim pv
... | b′ ⇒ p' = ⊥-elim pu
℘-~ {P} {D} {const k} {v₁ ⊔ v₂} pu ⟨ pv₁ , pv₂ ⟩
    with P
... | base b′ = ⟨ ℘-~{u = const k}{v₁} pu pv₁ , ℘-~{u = const k}{v₂} pu pv₂ ⟩
... | b′ ⇒ p' = ⊥-elim pu
℘-~ {P} {f} {u₁ ↦ u₂} {v} pu pv
    with P
... | base b′ = ⊥-elim pu
... | b′ ⇒ p′
    with pu
... | ⟨ k , ⟨ k<u₁ , pfku₂ ⟩ ⟩ = G {v} pv
    where
    G : ∀{v} → ℘ {b′ ⇒ p′} f v → u₁ ↦ u₂ ~ v
    G {⊥} pfv = tt
    G {const k′} ()
    G {v₁ ↦ v₂} ⟨ k′ , ⟨ k′<v₁ , pfk′v₂ ⟩ ⟩
        with consistent? u₁ v₁
    ... | no u₁~̸v₁ = inj₂ u₁~̸v₁
    ... | yes u₁~v₁
        with base-eq? b′ b′ | consistent-⊑ u₁~v₁ k<u₁ k′<v₁
    ... | yes refl | refl = inj₁ ⟨ u₁~v₁ , ℘-~{u = u₂}{v = v₂} pfku₂ pfk′v₂ ⟩
    ... | no neq | k~k′ = inj₂ (λ x → k~k′)
    G {v₁ ⊔ v₂} ⟨ fst₁ , snd₁ ⟩ = ⟨ G {v₁} fst₁ , G {v₂} snd₁ ⟩

℘-~ {P} {D} {u₁ ⊔ u₂} {v} ⟨ pu₁ , pu₂ ⟩ pv =
    ⟨ (℘-~{u = u₁}{v} pu₁ pv) , (℘-~{u = u₂}{v} pu₂ pv) ⟩
