module proof.Framework.GraphModel.DOpSig where

open import Framework.GraphModel.DOpSig public

open import proof.Framework.abt.ScopedTuple hiding (𝒫)
open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.abt.Sig

open import Data.List using (List ; _∷_ ; []; replicate)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Level using (Level; Lift; lift; lower)
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

{- =============== Equal results, and congruence from monotonicity ================ -}

RR : ∀ {T} b → Result (𝒫 T) b → Result (𝒫 T) b → Set₁
RR = result-rel-pres _≃_

RRs : ∀ {T} bs → Results (𝒫 T) bs → Results (𝒫 T) bs → Set₁
RRs = results-rel-pres _≃_

rr-trans : ∀ {T} b (f g h : Result (𝒫 T) b) → RR b f g → RR b g h → RR b f h
rr-trans ■ f g h p q = lift (≃-trans (lower p) (lower q))
rr-trans (ν b) f g h p q = λ a₁ a₂ r → rr-trans b (f a₁) (g a₂) (h a₂) (p a₁ a₂ r) (q a₂ a₂ ≃-refl)
rr-trans (∁ b) f g h p q = rr-trans b f g h p q

RRs-refl : ∀ {T n} (Ds : Results (𝒫 T) (replicate n ■)) → RRs (replicate n ■) Ds Ds
RRs-refl {n = zero} Ds = ptt
RRs-refl {n = suc n} ⟨ D , Ds ⟩ = ⟨ lift ≃-refl , RRs-refl Ds ⟩

{- first-order operands that are equal are included in each other, both ways -}
RRs⇒⊆ : ∀ {T n} {Ds Es : Results (𝒫 T) (replicate n ■)} → RRs (replicate n ■) Ds Es
  → results-rel-pres _⊆_ (replicate n ■) Ds Es × results-rel-pres _⊆_ (replicate n ■) Es Ds
RRs⇒⊆ {n = zero} _ = ⟨ ptt , ptt ⟩
RRs⇒⊆ {n = suc n} ⟨ lift D≃ , Ds≃ ⟩ =
  ⟨ ⟨ lift (proj₁ D≃) , proj₁ (RRs⇒⊆ Ds≃) ⟩ , ⟨ lift (proj₂ D≃) , proj₂ (RRs⇒⊆ Ds≃) ⟩ ⟩

{- a monotone operator is a congruence -}
mono⇒≃ : ∀ {T bs} {f : DOp (𝒫 T) bs} → fun-rel-pres _⊆_ bs ■ f f → ∀ {Ds Es}
  → results-rel-pres _⊆_ bs Ds Es → results-rel-pres _⊆_ bs Es Ds → f Ds ≃ f Es
mono⇒≃ m D⊆ E⊆ = ⟨ lower (m _ _ D⊆) , lower (m _ _ E⊆) ⟩

mono-≃ : ∀ {T n} {f : DOp (𝒫 T) (replicate n ■)} → fun-rel-pres _⊆_ (replicate n ■) ■ f f
  → ∀ {Ds Es} → RRs (replicate n ■) Ds Es → f Ds ≃ f Es
mono-≃ m eq = mono⇒≃ m (proj₁ (RRs⇒⊆ eq)) (proj₂ (RRs⇒⊆ eq))
