{-

  Tuples of sets of values, for the adequacy proofs of ISWIMμ: the
  denotation of a tuple value from those of its components (𝒯L), with
  monotonicity and consistency. A copy of the part of
  proof/Adequacy/Soundness.agda (the ISWIM adequacy of the typed and
  untyped pipelines) that is about tuples, so that ISWIMμ's
  adequacy does not depend on the typed pipeline's.

-}

module Mu.proof.Adequacy.Tuples where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _~_; Con)
  renaming (const to dconst)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Relation.Nullary using (yes; no)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

{- Tuples of sets ------------------------------------------------------------}

{- d is in component i of a list of n sets -}
At : ∀ {n} → Fin n → List (𝒫 Value) → Value → Set
At {suc n} zero (D ∷ Ds) d = length Ds ≡ n × d ∈ D
At (suc i) (D ∷ Ds) d = At i Ds d
At _ [] d = ⊥

AllNE : List (𝒫 Value) → Set
AllNE [] = ⊤
AllNE (D ∷ Ds) = nonempty D × AllNE Ds

Null : List (𝒫 Value) → Set
Null [] = ⊤
Null (D ∷ Ds) = ⊥

{- the tuple of a list of sets (𝒯, for lists) -}
𝒯L : List (𝒫 Value) → 𝒫 Value
𝒯L Ds ⟨⟩ = Null Ds
𝒯L Ds (tup[ i ] d) = At i Ds d × AllNE Ds
𝒯L Ds _ = ⊥

infix 4 _⊆L_
_⊆L_ : List (𝒫 Value) → List (𝒫 Value) → Set
[] ⊆L [] = ⊤
(D ∷ Ds) ⊆L (E ∷ Es) = D ⊆ E × Ds ⊆L Es
_ ⊆L _ = ⊥

⊆L-refl : ∀ Ds → Ds ⊆L Ds
⊆L-refl [] = tt
⊆L-refl (D ∷ Ds) = ⟨ (λ d z → z) , ⊆L-refl Ds ⟩

At-mono : ∀ {n} (i : Fin n) Ds Es d → Ds ⊆L Es → At i Ds d → At i Es d
At-mono {suc n} zero (D ∷ Ds) (E ∷ Es) d ⟨ D⊆ , Ds⊆ ⟩ ⟨ len , d∈ ⟩ =
  ⟨ len' Ds Es Ds⊆ len , D⊆ d d∈ ⟩
  where
  len' : ∀ {m} Ds Es → Ds ⊆L Es → length Ds ≡ m → length Es ≡ m
  len' [] [] _ refl = refl
  len' (D ∷ Ds) (E ∷ Es) ⟨ _ , s ⟩ refl = cong suc (len' Ds Es s refl)
At-mono (suc i) (D ∷ Ds) (E ∷ Es) d ⟨ _ , Ds⊆ ⟩ a = At-mono i Ds Es d Ds⊆ a

AllNE-mono : ∀ Ds Es → Ds ⊆L Es → AllNE Ds → AllNE Es
AllNE-mono [] [] _ _ = tt
AllNE-mono (D ∷ Ds) (E ∷ Es) ⟨ D⊆ , s ⟩ ⟨ ⟨ d , d∈ ⟩ , ne ⟩ = ⟨ ⟨ d , D⊆ d d∈ ⟩ , AllNE-mono Ds Es s ne ⟩

𝒯L-mono : ∀ Ds Es → Ds ⊆L Es → 𝒯L Ds ⊆ 𝒯L Es
𝒯L-mono [] [] s ⟨⟩ tt = tt
𝒯L-mono Ds Es s (tup[ i ] d) ⟨ a , ne ⟩ = ⟨ At-mono i Ds Es d s a , AllNE-mono Ds Es s ne ⟩


At-length : ∀ {m} (i : Fin m) Ds d → At i Ds d → length Ds ≡ m
At-length {suc m} zero (D ∷ Ds) d ⟨ len , _ ⟩ = cong suc len
At-length (suc i) (D ∷ Ds) d a = cong suc (At-length i Ds d a)

AllCon : List (𝒫 Value) → Set
AllCon [] = ⊤
AllCon (D ∷ Ds) = Con D × AllCon Ds

At-con : ∀ {n} (i : Fin n) Ds {d d'} → AllCon Ds → At i Ds d → At i Ds d' → d ~ d'
At-con {suc n} zero (D ∷ Ds) ⟨ c , _ ⟩ ⟨ _ , d∈ ⟩ ⟨ _ , d'∈ ⟩ = c _ _ d∈ d'∈
At-con (suc i) (D ∷ Ds) ⟨ _ , cs ⟩ a a' = At-con i Ds cs a a'

At-[] : ∀ {n} (i : Fin n) {d} → At i [] d → ⊥
At-[] zero ()
At-[] (suc i) ()

𝒯L-con : ∀ Ds → AllCon Ds → Con (𝒯L Ds)
𝒯L-con Ds cs ⟨⟩ ⟨⟩ _ _ = tt
𝒯L-con Ds cs (tup[ i ] d) (tup[ j ] d') ⟨ a , _ ⟩ ⟨ a' , _ ⟩
    with trans (sym (At-length i Ds d a)) (At-length j Ds d' a')
... | refl with i fin≟ j
... | yes refl = ⟨ refl , inj₂ ⟨ refl , At-con i Ds cs a a' ⟩ ⟩
... | no neq = ⟨ refl , inj₁ neq ⟩
𝒯L-con [] cs ⟨⟩ (tup[ i ] d) _ ⟨ a , _ ⟩ = ⊥-elim (At-[] i a)
𝒯L-con [] cs (tup[ i ] d) ⟨⟩ ⟨ a , _ ⟩ _ = ⊥-elim (At-[] i a)
𝒯L-con (D ∷ Ds) cs ⟨⟩ _ () _
𝒯L-con (D ∷ Ds) cs (tup[ i ] d) ⟨⟩ _ ()
𝒯L-con Ds cs (dconst k) v () _
𝒯L-con Ds cs (V ↦ w) v () _
𝒯L-con Ds cs ν v () _
𝒯L-con Ds cs ω v () _
𝒯L-con Ds cs ⦅ _ , _ ⦆ v () _
𝒯L-con Ds cs (left _) v () _
𝒯L-con Ds cs (right _) v () _
𝒯L-con Ds cs u (dconst k) _ ()
𝒯L-con Ds cs u (V ↦ w) _ ()
𝒯L-con Ds cs u ν _ ()
𝒯L-con Ds cs u ω _ ()
𝒯L-con Ds cs u ⦅ _ , _ ⦆ _ ()
𝒯L-con Ds cs u (left _) _ ()
𝒯L-con Ds cs u (right _) _ ()

