{-

  Operators strict in a list of operands, left to right: each is a
  congruence and is empty when one of its operands is, so binding an
  operand first by a let changes nothing (rco). The counterpart, with
  errors, is in ErrorMonad.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lower) renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

module proof.Framework.GraphModel.Strict where

{- Strict operators ----------------------------------------------------------------}

NEs : ∀ n → Results (𝒫 Value) (replicate n ■) → Set
NEs zero _ = ⊤
NEs (suc n) ⟨ D , Ds ⟩ = nonempty D × NEs n Ds

{- an operator on n operands, a congruence, empty if one operand is -}
record Strict (n : ℕ) : Set₁ where
  field
    op : Results (𝒫 Value) (replicate n ■) → 𝒫 Value
    cong : ∀ {Ds Es} → RRs (replicate n ■) Ds Es → op Ds ≃ op Es
    ne-of : ∀ Ds w → w ∈ op Ds → NEs n Ds
open Strict public

{- the operator with its first operand fixed to D -}
_▷_ : ∀ {n} → 𝒫 Value → Strict (suc n) → Strict n
D ▷ O = record { op = λ Ds → op O ⟨ D , Ds ⟩
               ; cong = λ eq → cong O ⟨ up ≃-refl , eq ⟩
               ; ne-of = λ Ds w w∈ → proj₂ (ne-of O _ w w∈) }

{- The operators -----------------------------------------------------------------}

app-op : Strict 3
app-op = record { op = ⋆₂ ; cong = mono-≃ ⋆₂-mono
  ; ne-of = λ { _ w ⟨ V , ⟨ ⟨ U , ⟨ f∈ , ⟨ U⊆ , U≢[] ⟩ ⟩ ⟩ , ⟨ V⊆ , V≢[] ⟩ ⟩ ⟩ →
      ⟨ ⟨ _ , f∈ ⟩ , ⟨ ne-mem U≢[] U⊆ , ⟨ ne-mem V≢[] V⊆ , tt ⟩ ⟩ ⟩ } }

pair-op′ : Strict 2
pair-op′ = record { op = pair ; cong = mono-≃ pair-mono ; ne-of = S }
  where S : ∀ Ds w → w ∈ pair Ds → NEs 2 Ds
        S _ ⦅ u , v ⦆ ⟨ u∈ , v∈ ⟩ = ⟨ ⟨ u , u∈ ⟩ , ⟨ ⟨ v , v∈ ⟩ , tt ⟩ ⟩

car-op : Strict 1
car-op = record { op = car ; cong = mono-≃ car-mono ; ne-of = λ { _ u ⟨ v , ∈ ⟩ → ⟨ ⟨ _ , ∈ ⟩ , tt ⟩ } }

cdr-op : Strict 1
cdr-op = record { op = cdr ; cong = mono-≃ cdr-mono ; ne-of = λ { _ v ⟨ u , ∈ ⟩ → ⟨ ⟨ _ , ∈ ⟩ , tt ⟩ } }

tuple-op : ∀ n → Strict n
tuple-op n = record { op = 𝒯 n ; cong = mono-≃ (𝒯-mono n) ; ne-of = S n }
  where
  all : ∀ n Ds → (∀ j → nonempty (nthD Ds j)) → NEs n Ds
  all zero Ds ne = tt
  all (suc n) ⟨ D , Ds ⟩ ne = ⟨ ne zero , all n Ds (λ j → ne (suc j)) ⟩
  S : ∀ n Ds w → w ∈ 𝒯 n Ds → NEs n Ds
  S zero Ds w _ = tt
  S (suc n) Ds (tup[ i ] d) ⟨ refl , ⟨ _ , ne ⟩ ⟩ = all (suc n) Ds ne

get-op : ∀ {n} (i : Fin n) → Strict 1
get-op i = record { op = proj i ; cong = mono-≃ (proj-mono i)
                  ; ne-of = λ _ d ∈ → ⟨ ⟨ _ , ∈ ⟩ , tt ⟩ }

inl-op′ : Strict 1
inl-op′ = record { op = inl ; cong = mono-≃ inl-mono ; ne-of = S }
  where S : ∀ Ds w → w ∈ inl Ds → NEs 1 Ds
        S _ (left v) ∈ = ⟨ ⟨ v , ∈ ⟩ , tt ⟩

inr-op′ : Strict 1
inr-op′ = record { op = inr ; cong = mono-≃ inr-mono ; ne-of = S }
  where S : ∀ Ds w → w ∈ inr Ds → NEs 1 Ds
        S _ (right v) ∈ = ⟨ ⟨ v , ∈ ⟩ , tt ⟩

{- case on D, with the branches E and F -}
case-op′ : (E F : 𝒫 Value → 𝒫 Value) → Strict 1
case-op′ E F = record { op = λ { ⟨ D , _ ⟩ → 𝒞 ⟨ D , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩ }
  ; cong = λ eq → 𝒞-≃ {F = E} {E} {F} {F} (lower (proj₁ eq)) (λ _ _ _ → ≃-refl) (λ _ _ _ → ≃-refl)
  ; ne-of = λ { _ w (inj₁ ⟨ v , ⟨ V , ⟨ l∈ , _ ⟩ ⟩ ⟩) → ⟨ ⟨ _ , l∈ v (here refl) ⟩ , tt ⟩
               ; _ w (inj₂ ⟨ v , ⟨ V , ⟨ r∈ , _ ⟩ ⟩ ⟩) → ⟨ ⟨ _ , r∈ v (here refl) ⟩ , tt ⟩ } }
