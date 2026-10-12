module Framework.GraphModel.DOpSig where

open import Framework.abt.ScopedTuple hiding (𝒫)
open import Framework.abt.Sig using (Sig; ν; ■) public
open import Framework.abt.Var using (Var) public
open import Framework.abt.GSubst using (_•_) public
open import Framework.abt.Sig

open import Data.List using (List)

Results : ∀ {ℓ} → Set ℓ → List Sig → Set ℓ
Results A bs = Tuple bs (Result A)

DFun : ∀ {ℓ} (A : Set ℓ) → List Sig → Sig → Set ℓ
DFun A bs c = Results A bs → Result A c

DOp : ∀ {ℓ} A → List Sig → Set ℓ
DOp A bs = DFun A bs ■

DOpSig : ∀ {Op : Set} {ℓ} A → (sig : Op → List Sig) → Set ℓ
DOpSig A sig = ∀ op → DOp A (sig op)
