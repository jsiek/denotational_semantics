open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewPValueCBVAnnot
open import NewClos3
open import NewClos4
open import NewCompiler using (delay)


{-

open import ISWIMClos1
open import ISWIMClos2
  renaming (Term to Term₂; Arg to Arg₂; Args to Args₂; `_ to #_;
      pair to pair₂; fst to fst₂; snd to snd₂; tuple to tuple₂;
      $ to %; _❲_❳ to _❲_❳₂; inl to inl₂; inr to inr₂; case to case₂;
      cons to cons₂; ast to ast₂; nil to nil₂; _⦅_⦆ to _⦅_⦆₂;
      ⟦_⟧ to ⟦_⟧₂; ⟦_⟧ₐ to ⟦_⟧₂ₐ; ⟦_⟧₊ to ⟦_⟧₂₊)

-}


open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Level using (Level; Lift; lift)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.Core using (Rel)


tos : List Value → List Value
to : Value → Value
to (const x) = const x
to (fvs ⊢ V ↦ w) = ⦅ [] ⊢ tos V ↦ to w , ∥ tos fvs ∥ ⦆
to ν = ⦅ ν , ∥ [] ∥ ⦆
to ω = ω
to ⦅ v , v₁ ⦆ = ⦅ to v , to v₁ ⦆
to ∥ xs ∥ = ∥ tos xs ∥
to (left V) = left (tos V)
to (right V) = right (tos V)
tos List.[] = []
tos (d List.∷ ds) = to d List.∷ tos ds

to-set : 𝒫 Value → 𝒫 Value
to-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ to d



