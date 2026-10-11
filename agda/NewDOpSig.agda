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

result-rel-pres' : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set) → (∀ b → Result A b → Result B b → Set (lsuc lzero l⊔ ℓ))
result-rel-pres' {ℓ} R ■ a b = Lift (lsuc lzero l⊔ ℓ) (R a b)
result-rel-pres' R (ν 𝓈) f g = ∀ a b → R a b → result-rel-pres' R 𝓈 (f a) (g b)
result-rel-pres' R (∁ 𝓈) = result-rel-pres' R 𝓈

results-rel-pres' : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set) 
      → (∀ bs → Results A bs → Results B bs → Set (lsuc lzero l⊔ ℓ))
results-rel-pres' R [] _ _ = ⊤
results-rel-pres' R (b ∷ bs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ = 
  result-rel-pres' R b D E × results-rel-pres' R bs Ds Es

result-rel-pres-1 : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set (lsuc lzero)) → (∀ b → Result A b → Result B b → Set (lsuc lzero l⊔ ℓ))
result-rel-pres-1 {ℓ} R ■ a b = Lift (lsuc lzero l⊔ ℓ) (R a b)
result-rel-pres-1 R (ν 𝓈) f g = ∀ a b → R a b → result-rel-pres-1 R 𝓈 (f a) (g b)
result-rel-pres-1 R (∁ 𝓈) = result-rel-pres-1 R 𝓈

results-rel-pres-1 : ∀ {ℓ} {A B : Set ℓ} (R : A → B → Set (lsuc lzero)) 
      → (∀ bs → Results A bs → Results B bs → Set (lsuc lzero l⊔ ℓ))
results-rel-pres-1 R [] _ _ = ⊤
results-rel-pres-1 R (b ∷ bs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ = 
  result-rel-pres-1 R b D E × results-rel-pres-1 R bs Ds Es

fun-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → DFun-Rel A
fun-rel-pres R bs c f g = ∀ Ds Es → results-rel-pres R bs Ds Es → result-rel-pres R c (f Ds) (g Es)

op-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → DOp-Rel A
op-rel-pres R bs = fun-rel-pres R bs ■

opsig-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → DOpSig-Rel A
opsig-rel-pres R sig O₁ O₂ = ∀ op → op-rel-pres R (sig op) (O₁ op) (O₂ op)


{- =============== Types for the preservation of a predicate on a DFun/Op ================ -}

DFun-Pred : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DFun-Pred {ℓ} A = ∀ bs c → DFun A bs c → Set (lsuc lzero l⊔ ℓ)

Op-Pred : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
Op-Pred {ℓ} A = ∀ bs → DOp A bs → Set (lsuc lzero l⊔ ℓ)

DOpSig-Pred : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DOpSig-Pred {ℓ} A = ∀ {Op} (sig : Op → List Sig) → DOpSig A sig → Set (lsuc lzero l⊔ ℓ)

result-pred-pres : ∀ {ℓ} {A : Set ℓ} (P : A → Set) → (∀ b → Result A b → Set (lsuc lzero l⊔ ℓ))
result-pred-pres {ℓ} P ■ a = Lift (lsuc lzero l⊔ ℓ) (P a)
result-pred-pres P (ν b) f = ∀ a → P a → result-pred-pres P b (f a)
result-pred-pres P (∁ b) = result-pred-pres P b

results-pred-pres : ∀ {ℓ} {A : Set ℓ} (P : A → Set) → (∀ bs → Results A bs → Set (lsuc lzero l⊔ ℓ))
results-pred-pres P [] _ = ⊤
results-pred-pres P (b ∷ bs) ⟨ D , Ds ⟩ = 
  result-pred-pres P b D × results-pred-pres P bs Ds

fun-pred-pres : ∀ {ℓ}{A : Set ℓ} → (P : A → Set) → DFun-Pred A
fun-pred-pres {ℓ} P bs c F = ∀ Ds → results-pred-pres P bs Ds → result-pred-pres P c (F Ds)

op-pred-pres : ∀ {ℓ}{A : Set ℓ} → (P : A → Set) → Op-Pred A
op-pred-pres P bs = fun-pred-pres P bs ■

{- ============================= Combinators ============================= -}

DApp1 : ∀ {ℓ} {A : Set ℓ} b bs c
  → DFun A (b ∷ bs) c → Result A b → DFun A bs c
DApp1 b bs c F a Ds = F ⟨ a , Ds ⟩

DComp1 : ∀ {ℓ} {A : Set ℓ} b c cs d
  → DFun A (b ∷ []) c → DFun A (c ∷ cs) d
  → DFun A (b ∷ cs) d
DComp1 b c cs d f g ⟨ D , Ds ⟩ = g ⟨ f ⟨ D , ptt ⟩ , Ds ⟩

Dfold : ∀ {ℓ}{A : Set ℓ} b c n → DFun A (b ∷ c ∷ []) c
    → Result A c
    → DFun A (replicate n b) c
Dfold b c zero f a (ptt) = a
Dfold b c (suc n) f a ⟨ D , Ds ⟩ = f ⟨ D , ⟨ Dfold b c n f a Ds , ptt ⟩ ⟩

Dfold-pres : ∀ {ℓ}{A : Set ℓ} R b c n
  → (f1 f2 : DFun A (b ∷ c ∷ []) c)
  → (a1 a2 : Result A c)
  → fun-rel-pres R (b ∷ c ∷ []) c f1 f2
  → result-rel-pres R c a1 a2
  → fun-rel-pres R (replicate n b) c (Dfold b c n f1 a1) (Dfold b c n f2 a2)
Dfold-pres R b c zero f1 f2 a1 a2 f~ a~ _ _ _ = a~
Dfold-pres R b c (suc n) f1 f2 a1 a2 f~ a~ ⟨ D1 , Ds1 ⟩ ⟨ D2 , Ds2 ⟩ ⟨ D~ , Ds~ ⟩ = 
  f~ ⟨ D1 , ⟨ Dfold b c n f1 a1 Ds1 , ptt ⟩ ⟩ ⟨ D2 , ⟨ Dfold b c n f2 a2 Ds2 , ptt ⟩ ⟩ 
     ⟨ D~ , ⟨ Dfold-pres R b c n f1 f2 a1 a2 f~ a~ Ds1 Ds2 Ds~ , ptt ⟩ ⟩
