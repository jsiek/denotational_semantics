
module Results (Value : Set) where

open import Primitives
open import Utilities using (extensionality)
open import SetsAsPredicates
open import Var
open import Substitution using (_•_)
open import ScopedTuple hiding (𝒫)
open import Syntax using (Sig; ext; ν; ■; Var; _•_; ↑; id; _⨟_) public
open import Sig

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

{- from Sig we have "Result A b", 
   which is a type structured using A and a Sig, b  -}
{- from ScopedTuple we have "Tuple bs A", 
   which is a type structured using (A : Sig → Set) and a List Sig, bs
   where A is a type family depended on a Sig, b -}
{- so we can use "Tuple bs (Result A)" to get a structured collection of Results -}

Results : ∀ {ℓ} → Set ℓ → List Sig → Set ℓ
Results A bs = Tuple bs (Result A)

DenotOp : ∀ {ℓ} (A : Set ℓ) (bs : List Sig) → Set ℓ
DenotOp A bs = Results A bs → A

DenotFun : ∀ {ℓ} (A : Set ℓ) (bs : List Sig) (b : Sig) → Set ℓ
DenotFun A bs b = Results A bs → Result A b

DenotOps : ∀ {ℓ} {Op : Set} → (sig : Op → List Sig) → (A : Set ℓ) → Set ℓ
DenotOps sig A = ∀ op → DenotOp A (sig op)


{- Here is an example concrete version of monotonicity with these abstractions -}
{-
  mono : ∀ {A} → 𝒫 A → 𝒫 A → Set
  mono = _⊆_

  mono-result : ∀ {A : Set} b → Result (𝒫 A) b → Result (𝒫 A) b → Set₁
  mono-result ■ D E = Lift (lsuc lzero) (mono D E)
  mono-result (ν b) F G = ∀ X Y → mono X Y → mono-result b (F X) (G Y)
  mono-result (∁ b) D E = mono-result b D E

  mono-results : ∀ {A : Set} bs → Results (𝒫 A) bs → Results (𝒫 A) bs → Set₁
  mono-results [] Ds Es = ⊤
  mono-results (x ∷ bs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ = mono-result x D E × mono-results bs Ds Es

  mono-op : ∀ {A : Set} bs → DenotOp (𝒫 A) bs → Set₁
  mono-op bs 𝒻 = ∀ Ds Es → mono-results bs Ds Es → mono (𝒻 Ds) (𝒻 Es)

  mono-denotops : ∀ {A : Set} {Op} sig → DenotFun {Op = Op} sig (𝒫 A) → Set₁
  mono-denotops sig 𝕆 = ∀ op → mono-op (sig op) (𝕆 op)
-}

Result-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
Result-Rel {ℓ} A = ∀ b → Result A b → Result A b → Set (lsuc lzero l⊔ ℓ)

Results-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
Results-Rel {ℓ} A = ∀ bs → Results A bs → Results A bs → Set (lsuc lzero l⊔ ℓ)

Op-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
Op-Rel {ℓ} A = ∀ bs → DenotOp A bs → Set (lsuc lzero l⊔ ℓ)

Fun-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
Fun-Rel {ℓ} A = ∀ bs c → DenotFun A bs c → Set (lsuc lzero l⊔ ℓ)

DenotOps-Rel : ∀ {ℓ} (A : Set ℓ) → Set (lsuc (lsuc lzero) l⊔ lsuc ℓ)
DenotOps-Rel {ℓ} A = ∀ {Op} sig → DenotOps {Op = Op} sig A → Set (lsuc lzero l⊔ ℓ)

result-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → Result-Rel A
result-rel-pres {ℓ} R ■ a1 a2 = Lift (lsuc lzero l⊔ ℓ) (R a1 a2)
result-rel-pres R (ν b) f1 f2 = ∀ a1 a2 → R a1 a2 → result-rel-pres R b (f1 a1) (f2 a2)
result-rel-pres R (∁ b) = result-rel-pres R b

results-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → Results-Rel A
results-rel-pres R [] _ _ = ⊤
results-rel-pres R (b ∷ bs) ⟨ D , Ds ⟩ ⟨ E , Es ⟩ = 
  result-rel-pres R b D E × results-rel-pres R bs Ds Es

op-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → Op-Rel A
op-rel-pres R bs 𝒻 = ∀ Ds Es → results-rel-pres R bs Ds Es → R (𝒻 Ds) (𝒻 Es)

fun-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → Fun-Rel A
fun-rel-pres R bs c 𝒻 = ∀ Ds Es → results-rel-pres R bs Ds Es → result-rel-pres R c (𝒻 Ds) (𝒻 Es)

ops-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → DenotOps-Rel A
ops-rel-pres R sig 𝕆 = ∀ op → op-rel-pres R (sig op) (𝕆 op)


{-  ======  DenotOps as denotational functions  ==========  -}
{- we want to be able to compose denotational functions and 
   inherit properties after composition... so let's make them functions -}


DApp : ∀ {ℓ} {A : Set ℓ} b bs c
   → DenotFun A (b ∷ bs) c → Result A b → DenotFun A bs c
DApp b bs c F a Bs = F ⟨ a , Bs ⟩

DApp-pres : ∀ {ℓ}{A : Set ℓ} R b bs c
  → (𝒻 : DenotFun A (b ∷ bs) c)
  → fun-rel-pres R (b ∷ bs) c 𝒻
  → ∀ a 
  → result-rel-pres R b a a
  → fun-rel-pres R bs c (DApp b bs c 𝒻 a)
DApp-pres R b bs c 𝒻 𝒻-pres a a-pres Ds Es H = 𝒻-pres ⟨ a , Ds ⟩ ⟨ a , Es ⟩ ⟨ a-pres , H ⟩

DApp-pres' : ∀ {ℓ}{A : Set ℓ} R b bs c
   → (𝒻 : DenotFun A (b ∷ bs) c) → (a1 a2 : Result A b )
   → fun-rel-pres R (b ∷ bs) c 𝒻 
   → result-rel-pres R b a1 a2
   → ∀ Bs1 Bs2
   → results-rel-pres R bs Bs1 Bs2 
   → result-rel-pres R c (DApp b bs c 𝒻 a1 Bs1) (DApp b bs c 𝒻 a2 Bs2)
DApp-pres' R b bs c 𝒻 a1 a2 𝒻-pres a1Ra2 Bs1 Bs2 Bs-pres = 
  𝒻-pres ⟨ a1 , Bs1 ⟩ ⟨ a2 , Bs2 ⟩  ⟨ a1Ra2 , Bs-pres ⟩ 


Results-append : ∀ {bs cs} → Results A bs → Results A cs → Results A (bs ++ cs)
Results-append {bs = []} (lift lower) Cs = Cs
Results-append {bs = x ∷ bs} ⟨ B , Bs ⟩ Cs = ⟨ B , Results-append Bs Cs ⟩

Results-unappend : ∀ bs {cs} → Results A (bs ++ cs) → Results A bs × Results A cs
Results-unappend [] Bs++Cs = ⟨ lift tt , Bs++Cs ⟩
Results-unappend (b ∷ bs) ⟨ B , Bs++Cs ⟩ with Results-unappend bs Bs++Cs
... | ⟨ Bs , Cs ⟩ = ⟨ ⟨ B , Bs ⟩ , Cs ⟩

Results-rel-pres-unappend : ∀ bs {cs} (R : A → A → Set) Bs++Cs1 Bs++Cs2
   → results-rel-pres R (bs ++ cs) Bs++Cs1 Bs++Cs2
   → results-rel-pres R bs (proj₁ (Results-unappend bs Bs++Cs1)) 
                           (proj₁ (Results-unappend bs Bs++Cs2))
   × results-rel-pres R cs (proj₂ (Results-unappend bs Bs++Cs1))
                           (proj₂ (Results-unappend bs Bs++Cs2))
Results-rel-pres-unappend [] R Bs++Cs1 Bs++Cs2 Bs++Cs-pres = 
  ⟨ lift tt , Bs++Cs-pres ⟩
Results-rel-pres-unappend (x ∷ bs) R ⟨ B1 , Bs++Cs1 ⟩ ⟨ B2 , Bs++Cs2 ⟩ ⟨ B-pres , Bs++Cs-pres ⟩ = 
  ⟨ ⟨ B-pres , proj₁ (Results-rel-pres-unappend bs R Bs++Cs1 Bs++Cs2 Bs++Cs-pres) ⟩ 
  , proj₂ (Results-rel-pres-unappend bs R Bs++Cs1 Bs++Cs2 Bs++Cs-pres) ⟩

DComp : ∀ {ℓ} {A : Set ℓ} bs c cs d 
       → DenotFun A bs c → DenotFun A (c ∷ cs) d
       → DenotFun A (bs ++ cs) d
DComp bs c cs d 𝒻 ℊ Bs++Cs with Results-unappend bs Bs++Cs
... | ⟨ Bs , Cs ⟩ = ℊ ⟨ 𝒻 Bs , Cs ⟩


DComp-pres : ∀ {ℓ}{A : Set ℓ} R bs c cs d
   (𝒻 : DenotFun A bs c) (ℊ : DenotFun A (c ∷ cs) d)
    → fun-rel-pres R bs c 𝒻 → fun-rel-pres R (c ∷ cs) d ℊ
    → fun-rel-pres R (bs ++ cs) d (DComp bs c cs d 𝒻 ℊ)
DComp-pres R bs c cs d 𝒻 ℊ 𝒻-pres ℊ-pres Bs++Cs1 Bs++Cs2 H 
  with Results-rel-pres-unappend bs R Bs++Cs1 Bs++Cs2 H
... | ⟨ Bs-pres , Cs-pres ⟩
  with Results-unappend bs Bs++Cs1 | Results-unappend bs Bs++Cs2
... | ⟨ Bs1 , Cs1 ⟩ | ⟨ Bs2 , Cs2 ⟩ =
  ℊ-pres ⟨ 𝒻 Bs1 , Cs1 ⟩ ⟨ 𝒻 Bs2 , Cs2 ⟩ ⟨ 𝒻-pres Bs1 Bs2 Bs-pres , Cs-pres ⟩



{-   =========== Preserved Properties ================ -}

monotonicity : ∀ {A : Set} → 𝒫 A → 𝒫 A → Set
monotonicity = _⊆_

monotone : ∀ {A : Set} bs b → DenotFun (𝒫 A) bs b → Set₁
monotone = fun-rel-pres _⊆_

𝕆-monotone : ∀ {A : Set} {Op} sig → DenotOps {Op = Op} sig (𝒫 A) → Set₁
𝕆-monotone = ops-rel-pres _⊆_


Every : ∀ {A : Set} (R : Rel A lzero) → 𝒫 A → 𝒫 A → Set
Every R A B = ∀ a b → a ∈ A → b ∈ B → R a b

{- this can be used similarly... 
  for a denotational function: fun-rel-pres (Every R)
  for a DenotOps : ops-rel-pres (Every R) 
-}

{- for example, this can be used to define consistency, based on some 
   consistent : Value → Value → Set -}

fun-consistent : ∀ {A : Set} (consistent : A → A → Set) bs b → DenotFun (𝒫 A) bs b → Set₁
fun-consistent consistent = fun-rel-pres (Every consistent)

𝕆-consistent : ∀ {A : Set} (consistent : A → A → Set) {Op} sig → DenotOps {Op = Op} sig (𝒫 A) → Set₁
𝕆-consistent consistent = ops-rel-pres (Every consistent)


{- Continuity appears to be a different beast... relying on info about the environment -}
{- But I wonder if a part of it can be factored into a propert about
  just the denotational operators -}



{- Results are actually an ugly packaging for simpler functions -}
{- =============== Unpeeling Results, Funs, Ops ==================== -}

UnTuple : ∀ {ℓ} (A : Set ℓ) → List Sig → Sig → Set ℓ
UnTuple A [] c = Result A c
UnTuple A (b ∷ bs) c = Result A b → UnTuple A bs c

untuple : ∀ {bs c} → DenotFun A bs c → UnTuple A bs c
untuple {bs = []} 𝒻 = 𝒻 (lift tt)
untuple {bs = (b ∷ bs)} 𝒻 = λ z → untuple (λ z₁ → 𝒻 ⟨ z , z₁ ⟩)

retuple : ∀ {bs c} → UnTuple A bs c → DenotFun A bs c
retuple {bs = []} 𝒻 = λ _ → 𝒻
retuple {bs = (b ∷ bs)} 𝒻 = λ z → retuple (𝒻 (proj₁ z)) (proj₂ z)

{- wondering if all of this should be defined using UnTuple versions
   instead of tuple versions -}


