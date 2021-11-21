
module NewDOpSig where

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


DFun : ∀ {ℓ} (A : Set ℓ) → List Sig → Sig → Set ℓ
DFun A [] c = Result A c
DFun A (b ∷ bs) c = Result A b → DFun A bs c

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

fun-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → DFun-Rel A
fun-rel-pres {ℓ} R [] c 𝒻 ℊ = result-rel-pres R c 𝒻 ℊ
fun-rel-pres R (b ∷ bs) c 𝒻 ℊ = ∀ D E → result-rel-pres R b D E → fun-rel-pres R bs c (𝒻 D) (ℊ E)

op-rel-pres : ∀ {ℓ}{A : Set ℓ} → (R : Rel A lzero) → Op-Rel A
op-rel-pres R bs = fun-rel-pres R bs ■

opsig-rel-pres : ∀ {ℓ} {A : Set ℓ} (R : Rel A lzero) → DOpSig-Rel A
opsig-rel-pres R sig 𝕆₁ 𝕆₂ = ∀ op → op-rel-pres R (sig op) (𝕆₁ op) (𝕆₂ op)


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

fun-pred-pres : ∀ {ℓ}{A : Set ℓ} → (P : A → Set) → DFun-Pred A
fun-pred-pres {ℓ} P [] c 𝒻 = result-pred-pres P c 𝒻
fun-pred-pres P (b ∷ bs) c 𝒻 = ∀ D → result-pred-pres P b D → fun-pred-pres P bs c (𝒻 D)

op-pred-pres : ∀ {ℓ}{A : Set ℓ} → (P : A → Set) → Op-Pred A
op-pred-pres P bs = fun-pred-pres P bs ■

opsig-pred-pres : ∀ {ℓ} {A : Set ℓ} (P : A → Set) → DOpSig-Pred A
opsig-pred-pres P sig 𝕆 = ∀ op → op-pred-pres P (sig op) (𝕆 op)



{- ============================= Combinators ============================= -}

DApp : ∀ {ℓ} {A : Set ℓ} b bs c
  → DFun A (b ∷ bs) c → Result A b → DFun A bs c
DApp b bs c F a = F a


DComp1 : ∀ {ℓ} {A : Set ℓ} b c cs d
  → DFun A (b ∷ []) c → DFun A (c ∷ cs) d
  → DFun A (b ∷ cs) d
DComp1 b c cs d 𝒻 ℊ = λ z → ℊ (𝒻 z)

DComp : ∀ {ℓ} {A : Set ℓ} bs c cs d
  → DFun A bs c → DFun A (c ∷ cs) d
  → DFun A (bs ++ cs) d
DComp [] c cs d 𝒻 ℊ = ℊ 𝒻
DComp (x ∷ bs) c cs d 𝒻 ℊ = λ z → DComp bs c cs d (𝒻 z) ℊ

DApp-pres : ∀ {ℓ}{A : Set ℓ} R b bs c
   → (𝒻1 𝒻2 : DFun A (b ∷ bs) c) → (a1 a2 : Result A b )
   → fun-rel-pres R (b ∷ bs) c 𝒻1 𝒻2
   → result-rel-pres R b a1 a2
   → fun-rel-pres R bs c (DApp b bs c 𝒻1 a1) (DApp b bs c 𝒻2 a2)
DApp-pres R b bs c 𝒻1 𝒻2 a1 a2 𝒻-pres a1Ra2 = 
  𝒻-pres a1 a2 a1Ra2
  
DComp-pres : ∀ {ℓ}{A : Set ℓ} R bs c cs d
   (𝒻1 𝒻2 : DFun A bs c) (ℊ1 ℊ2 : DFun A (c ∷ cs) d)
    → fun-rel-pres R bs c 𝒻1 𝒻2 → fun-rel-pres R (c ∷ cs) d ℊ1 ℊ2
    → fun-rel-pres R (bs ++ cs) d (DComp bs c cs d 𝒻1 ℊ1) (DComp bs c cs d 𝒻2 ℊ2)
DComp-pres R [] c cs d 𝒻1 𝒻2 ℊ1 ℊ2 𝒻-pres ℊ-pres = ℊ-pres 𝒻1 𝒻2 𝒻-pres
DComp-pres R (b ∷ bs) c cs d 𝒻1 𝒻2 ℊ1 ℊ2 𝒻-pres ℊ-pres D E RDE = 
  DComp-pres R bs c cs d (𝒻1 D) (𝒻2 E) ℊ1 ℊ2 (𝒻-pres D E RDE) ℊ-pres

Diter : ∀ {ℓ}{A : Set ℓ} (n : ℕ) bs c → (𝒻₀ : DFun A bs c) 
     → (𝒻 : DFun A bs c → DFun A bs c)
     → DFun A bs c
Diter zero bs c 𝒻₀ 𝒻 = 𝒻₀
Diter (suc n) bs c 𝒻₀ 𝒻 = 𝒻 (Diter n bs c 𝒻₀ 𝒻)

Diter-pres : ∀ {ℓ}{A : Set ℓ} R (n : ℕ) bs c → (𝒻₀ 𝒻₀' : DFun A bs c)
   → (𝒻 𝒻' : DFun A bs c → DFun A bs c)
   → fun-rel-pres R bs c 𝒻₀ 𝒻₀'
   → (∀ ℊ ℊ' → fun-rel-pres R bs c ℊ ℊ' → fun-rel-pres R bs c (𝒻 ℊ) (𝒻' ℊ'))
   → fun-rel-pres R bs c (Diter n bs c 𝒻₀ 𝒻) (Diter n bs c 𝒻₀' 𝒻')
Diter-pres R zero bs c 𝒻₀ 𝒻₀' 𝒻 𝒻' 𝒻₀~ 𝒻~ = 𝒻₀~
Diter-pres R (suc n) bs c 𝒻₀ 𝒻₀' 𝒻 𝒻' 𝒻₀~ 𝒻~ = 
  𝒻~ (Diter n bs c 𝒻₀ 𝒻) (Diter n bs c 𝒻₀' 𝒻') (Diter-pres R n bs c 𝒻₀ 𝒻₀' 𝒻 𝒻' 𝒻₀~ 𝒻~)

DComp-rest : ∀ {ℓ} {A : Set ℓ} bs c d → DFun A bs c → DFun A (c ∷ bs) d
  → DFun A bs d
DComp-rest [] c d 𝒻 ℊ = ℊ 𝒻
DComp-rest (x ∷ bs) c d 𝒻 ℊ D = DComp-rest bs c d (𝒻 D) (λ z → ℊ z D)

DComp-rest-pres : ∀ {ℓ}{A : Set ℓ} R bs c d
  → (𝒻1 𝒻2 : DFun A bs c)
  → (ℊ1 ℊ2 : Result A c → DFun A bs d)
  → fun-rel-pres R bs c 𝒻1 𝒻2
  → fun-rel-pres R (c ∷ bs) d ℊ1 ℊ2
  → fun-rel-pres R bs d (DComp-rest bs c d 𝒻1 ℊ1) (DComp-rest bs c d 𝒻2 ℊ2)
DComp-rest-pres R [] c d 𝒻1 𝒻2 ℊ1 ℊ2 𝒻~ ℊ~ = ℊ~ 𝒻1 𝒻2 𝒻~
DComp-rest-pres R (x ∷ bs) c d 𝒻1 𝒻2 ℊ1 ℊ2 𝒻~ ℊ~ D1 D2 D~ = 
  DComp-rest-pres R bs c d (𝒻1 D1) (𝒻2 D2) (λ z → ℊ1 z D1) (λ z → ℊ2 z D2) 
                  (𝒻~ D1 D2 D~) (λ D E z → ℊ~ D E z D1 D2 D~)

DComp-n-1 : ∀ {ℓ}{A : Set ℓ} bs c d → DFun A bs c → DFun A (c ∷ []) d → DFun A bs d
DComp-n-1 [] c d 𝒻 ℊ = ℊ 𝒻
DComp-n-1 (b ∷ bs) c d 𝒻 ℊ D = DComp-n-1 bs c d (𝒻 D) ℊ

DComp-n-1-pres : ∀ {ℓ}{A : Set ℓ} R bs c d
  → (𝒻1 𝒻2 : DFun A bs c)
  → (ℊ1 ℊ2 : DFun A (c ∷ []) d)
  → fun-rel-pres R bs c 𝒻1 𝒻2
  → fun-rel-pres R (c ∷ []) d ℊ1 ℊ2
  → fun-rel-pres R bs d (DComp-n-1 bs c d 𝒻1 ℊ1) (DComp-n-1 bs c d 𝒻2 ℊ2)
DComp-n-1-pres R [] c d 𝒻1 𝒻2 ℊ1 ℊ2 𝒻~ ℊ~ = ℊ~ 𝒻1 𝒻2 𝒻~
DComp-n-1-pres R (x ∷ bs) c d 𝒻1 𝒻2 ℊ1 ℊ2 𝒻~ ℊ~ D E D~ = 
  DComp-n-1-pres R bs c d (𝒻1 D) (𝒻2 E) ℊ1 ℊ2 (𝒻~ D E D~) ℊ~

Dmap : ∀ {ℓ}{A : Set ℓ} {b}{c}{d}{n} → DFun A (b ∷ []) c 
     → DFun A (replicate n c) d →  DFun A (replicate n b) d
Dmap {n = zero} 𝒻 F = F
Dmap {n = suc n} 𝒻 F D = Dmap {n = n} 𝒻 (F (𝒻 D))

Dfold : ∀ {ℓ}{A : Set ℓ} b c n → DFun A (b ∷ c ∷ []) c
    → Result A c
    → DFun A (replicate n b) c
Dfold b c zero 𝒻 𝒸 = 𝒸
Dfold b c (suc n) 𝒻 𝒸 D = 
  DComp-n-1 (replicate n b) c c (Dfold b c n 𝒻 𝒸) (𝒻 D)

Dfold-pres : ∀ {ℓ}{A : Set ℓ} R b c n
  → (𝒻1 𝒻2 : DFun A (b ∷ c ∷ []) c)
  → (𝒸1 𝒸2 : Result A c)
  → fun-rel-pres R (b ∷ c ∷ []) c 𝒻1 𝒻2
  → result-rel-pres R c 𝒸1 𝒸2
  → fun-rel-pres R (replicate n b) c (Dfold b c n 𝒻1 𝒸1) (Dfold b c n 𝒻2 𝒸2)
Dfold-pres R b c zero 𝒻1 𝒻2 𝒸1 𝒸2 𝒻~ 𝒸~ = 𝒸~
Dfold-pres R b c (suc n) 𝒻1 𝒻2 𝒸1 𝒸2 𝒻~ 𝒸~ D1 D2 D~ = 
  DComp-n-1-pres R (replicate n b) c c 
                 (Dfold b c n 𝒻1 𝒸1) (Dfold b c n 𝒻2 𝒸2) (𝒻1 D1) (𝒻2 D2)
                (Dfold-pres R b c n 𝒻1 𝒻2 𝒸1 𝒸2 𝒻~ 𝒸~) (𝒻~ D1 D2 D~)



{- =============== translating to and from tuples =============== -}

uncurryDFun : ∀ {ℓ} {A : Set ℓ} {bs c} → DFun A bs c → (Tuple bs (Result A) → Result A c)
uncurryDFun {bs = []} 𝒻 _ = 𝒻
uncurryDFun {bs = (b ∷ bs)} 𝒻 ⟨ D , Ds ⟩ = uncurryDFun (𝒻 D) Ds  

curryDFun : ∀ {ℓ} {A : Set ℓ} {bs c} → (Tuple bs (Result A) → Result A c) → DFun A bs c
curryDFun {bs = []} 𝒻 = 𝒻 (lift tt)
curryDFun {bs = (b ∷ bs)} 𝒻 D = curryDFun (λ Ds → 𝒻 ⟨ D , Ds ⟩)






