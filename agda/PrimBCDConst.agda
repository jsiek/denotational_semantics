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


open import Variables
open import Primitives
open import ValueBCDConst
open import Structures


module PrimBCDConst where

{- need consistency for this to be true! -Jeremy -}
postulate k⊑v→k′⊑v→k′≡k : ∀{B : Base}{k : base-rep B}{k′ : base-rep B} {v : Value} → const k ⊑ v → const k′ ⊑ v → k′ ≡ k

℘-⊑ : ∀{P}{k : rep P}{v w : Value}
   → ℘ {P} k v
   → w ⊑ v
     ------------
   → ℘ {P} k w
℘-⊑ {P} {k} {v} {.⊥} ℘kv ⊑-⊥ =
   tt
℘-⊑ {P} {k} {.(const _)} {.(const _)} ℘kv ⊑-const =
   ℘kv
℘-⊑ {P} {k} {v} {.(_ ⊔ _)} ℘kv (⊑-conj-L w⊑v w⊑v₁) =
   ⟨ ℘-⊑ ℘kv w⊑v , ℘-⊑ ℘kv w⊑v₁ ⟩
℘-⊑ {P} {k} {.(_ ⊔ _)} {w} ℘kv (⊑-conj-R1 w⊑v) =
   ℘-⊑ (proj₁ ℘kv) w⊑v
℘-⊑ {P} {k} {.(_ ⊔ _)} {w} ℘kv (⊑-conj-R2 w⊑v) =
   ℘-⊑ (proj₂ ℘kv) w⊑v
℘-⊑ {P} {k} {v} {w} ℘kv (⊑-trans w⊑v w⊑v₁) =
   ℘-⊑ (℘-⊑ ℘kv w⊑v₁) w⊑v
℘-⊑ {P} {f} {v ↦ w} {v′ ↦ w′} ℘fv (⊑-fun v⊑v′ w′⊑w)
    with P
... | base B = ℘fv
{-
... | B ⇒ P′ = G
    where G : ∀{k} → v′ ⊑ const k → ℘ {P′} (f k) w′
          G {k} v′⊑k = ℘-⊑ {P′} (℘fv {k} (⊑-trans v⊑v′ v′⊑k)) w′⊑w
-}
... | B ⇒ P′
    with ℘fv
... | ⟨ k , ⟨ k⊑v , ℘fkw ⟩ ⟩ = G
    where G : Σ[ k ∈ base-rep B ] (const k ⊑ v′ × ℘ (f k) w′)
          G = ⟨ k , ⟨ (⊑-trans k⊑v v⊑v′) , (℘-⊑ ℘fkw w′⊑w) ⟩ ⟩


℘-⊑ {P} {f} {(v ↦ w ⊔ v ↦ w′)} {(v ↦ (w ⊔ w′))} ℘fv ⊑-dist
    with P
... | base B = proj₁ ℘fv
{-
... | B ⇒ P′ = G
    where G : ∀{k} → v ⊑ const k → ℘ {P′} (f k) w × ℘ {P′} (f k) w′
          G {k} v⊑k = ⟨ (proj₁ ℘fv v⊑k) , (proj₂ ℘fv v⊑k) ⟩
-}
... | B ⇒ P′
    with ℘fv
... | ⟨ ⟨ k , ⟨ k⊑v , ℘fkw ⟩ ⟩ , ⟨ k′ , ⟨ k′⊑v , ℘fk′w ⟩ ⟩ ⟩ = G
    where G : Σ[ k ∈ base-rep B ] (const k ⊑ v × ℘ (f k) w × ℘ (f k) w′)
          G
              with k⊑v→k′⊑v→k′≡k k⊑v k′⊑v
          ... | eq rewrite eq =
             ⟨ k , ⟨ k⊑v , ⟨ ℘fkw , ℘fk′w ⟩ ⟩ ⟩

℘-⊔ : ∀{P : Prim} {k : rep P} {u v : Value}
    → ℘ {P} k u → ℘ {P} k v → ℘ {P} k (u ⊔ v)
℘-⊔ ℘u ℘v = ⟨ ℘u , ℘v ⟩


