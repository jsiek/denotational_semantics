module proof.Framework.GraphModel.DOpSig where

open import Framework.GraphModel.DOpSig public

open import proof.Framework.abt.ScopedTuple hiding (𝒫)
open import Framework.abt.Sig

open import Data.List using (List ; _∷_ ; [])
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using (⊤)
open import Level using (Level; Lift; lift)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Binary.Core using (Rel)

{- =============== The preservation of a relation by a DFun/DOpSig ================ -}

result-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → (∀ b → Result A b → Result A b → Set (lsuc lzero l⊔ ℓ))
result-rel-pres {ℓ} R ■ a1 a2 = Lift (lsuc lzero l⊔ ℓ) (R a1 a2)
result-rel-pres R (ν b) f1 f2 = ∀ a1 a2 → R a1 a2 → result-rel-pres R b (f1 a1) (f2 a2)
result-rel-pres R (∁ b) = result-rel-pres R b

results-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → (∀ bs → Results A bs → Results A bs → Set (lsuc lzero l⊔ ℓ))
results-rel-pres R [] _ _ = ⊤
results-rel-pres R (b ∷ bs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ = 
  result-rel-pres R b D E × results-rel-pres R bs Ds Es

fun-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero)
  → ∀ bs c → DFun A bs c → DFun A bs c → Set (lsuc lzero l⊔ ℓ)
fun-rel-pres R bs c f g = ∀ Ds Es → results-rel-pres R bs Ds Es → result-rel-pres R c (f Ds) (g Es)

opsig-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero)
  → ∀ {Op} (sig : Op → List Sig) → DOpSig A sig → DOpSig A sig → Set (lsuc lzero l⊔ ℓ)
opsig-rel-pres R sig O₁ O₂ = ∀ op → fun-rel-pres R (sig op) ■ (O₁ op) (O₂ op)
