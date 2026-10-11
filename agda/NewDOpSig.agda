module NewDOpSig where

open import Primitives
open import SetsAsPredicates
open import abt.Var
open import abt.GSubst using (_•_)
open import abt.ScopedTuple hiding (𝒫)
open import abt.Sig using (Sig; ν; ■) public
open import abt.Var using (Var) public
open import abt.GSubst using (_•_) public
open import abt.Sig

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; _++_; length; replicate; map)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Properties using (++-conicalˡ)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<_; z≤n; s≤s; _+_)
open import Data.Nat.Properties
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using (⊤) renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Level using (Level; Lift; lift)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.Core using (Rel)


private
  variable
   ℓ : Level
   A : Set ℓ

Results : ∀ {ℓ} → Set ℓ → List Sig → Set ℓ
Results A bs = Tuple bs (Result A)

DFun : ∀ {ℓ} (A : Set ℓ) → List Sig → Sig → Set ℓ
DFun A bs c = Results A bs → Result A c

DOp : ∀ {ℓ} A → List Sig → Set ℓ
DOp A bs = DFun A bs ■

DOpSig : ∀ {Op : Set} {ℓ} A → (sig : Op → List Sig) → Set ℓ
DOpSig A sig = ∀ op → DOp A (sig op)

{- =============== Types for the preservation of a relation on a DFun/Op ================ -}

DFun-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DFun-Rel {ℓ} A = ∀ bs c → DFun A bs c → DFun A bs c → Set (lsuc lzero l⊔ ℓ)

DOp-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DOp-Rel {ℓ} A = ∀ bs → DOp A bs → DOp A bs → Set (lsuc lzero l⊔ ℓ)

DOpSig-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DOpSig-Rel {ℓ} A = ∀ {Op} (sig : Op → List Sig) → DOpSig A sig → DOpSig A sig → Set (lsuc lzero l⊔ ℓ)

result-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → (∀ b → Result A b → Result A b → Set (lsuc lzero l⊔ ℓ))
result-rel-pres {ℓ} R ■ a1 a2 = Lift (lsuc lzero l⊔ ℓ) (R a1 a2)
result-rel-pres R (ν b) f1 f2 = ∀ a1 a2 → R a1 a2 → result-rel-pres R b (f1 a1) (f2 a2)
result-rel-pres R (∁ b) = result-rel-pres R b

results-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → (∀ bs → Results A bs → Results A bs → Set (lsuc lzero l⊔ ℓ))
results-rel-pres R [] _ _ = ⊤
results-rel-pres R (b ∷ bs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ = 
  result-rel-pres R b D E × results-rel-pres R bs Ds Es

fun-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → DFun-Rel A
fun-rel-pres R bs c f g = ∀ Ds Es → results-rel-pres R bs Ds Es → result-rel-pres R c (f Ds) (g Es)

op-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → DOp-Rel A
op-rel-pres R bs = fun-rel-pres R bs ■

opsig-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → DOpSig-Rel A
opsig-rel-pres R sig O₁ O₂ = ∀ op → op-rel-pres R (sig op) (O₁ op) (O₂ op)


