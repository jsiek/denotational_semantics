{-

  An error monad on 𝒫 Value (Moggi), and the error-propagating operators
  built from it: the semantic algebra of the graph model with
  errors (Semantics/GraphErr/). (Its laws, and the
  monotonicity, consistency and continuity of the operators, are in
  proof/Framework/GraphModel/ErrorMonad.agda.)

  The error is ω (Framework/GraphModel/Domain.agda). A computation is a
  set D: it errs when ω ∈ D, it has the values ⌊ D ⌋ (its elements other
  than ω), and it diverges when it has neither.

  D ≫= F errs when D does, and is F on the values of D when D has one.
  So F never sees ω (binders never bind ω), and nested binds evaluate
  their operands left to right: a later operand is not looked at unless
  the earlier ones have values.

  Each operator is a kernel, the operator of the graph model
  (Framework/GraphModel/Ops.agda), under binds of its first-order
  operands in the machines' order; a kernel that inspects the kind of a
  value adds the error on a value of the wrong kind (checked). The
  binders are the graph model's Λ and 𝒞, restricted (_⇂_) to entries
  and payloads that are values: their bodies only ever see sets without
  ω.

  * Application checks its operator early, before the argument is
    bound, as the machines of ISWIM, Clos2 and Clos3 do:

      ⋆ᵐ D E = D ≫= λ F → checked fun F (E ≫= λ X → ⋆ F X)

  * The late check of Clos4 and Clos5 (code, environment and argument
    first, then the check of the code) is the same kernel, checked
    under all three binds (callᵐ).

-}

module Framework.GraphModel.ErrorMonad where

open import Framework.Primitives using (Base)
open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.abt.Sig using (∁)
open import Framework.GraphModel.Domain
open import Framework.GraphModel.Ops using (⋆; Λ; 𝒯; proj; inl; inr; 𝒞; pair; car; cdr; payloadD)

open import Data.List using (List; _∷_; []; replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

{- The monad -------------------------------------------------------------------}

{- the elements of D with the property P -}
infix 6 _⇂_
_⇂_ : 𝒫 Value → (Value → Set) → 𝒫 Value
(D ⇂ P) d = d ∈ D × P d

{- the values of D -}
⌊_⌋ : 𝒫 Value → 𝒫 Value
⌊ D ⌋ = D ⇂ (_≢ ω)

{- D has a value -}
Conv : 𝒫 Value → Set
Conv D = nonempty ⌊ D ⌋

{- the same, spelled out, for the statements -}
val∈ : 𝒫 Value → Set
val∈ D = Σ[ d ∈ Value ] d ∈ D × d ≢ ω

infixl 5 _≫=_
_≫=_ : 𝒫 Value → (𝒫 Value → 𝒫 Value) → 𝒫 Value
(D ≫= F) w = (w ≡ ω × ω ∈ D) ⊎ (Conv D × w ∈ F ⌊ D ⌋)

{- bind n operands, left to right -}
binds : ∀ n → Results (𝒫 Value) (replicate n ■) → (Results (𝒫 Value) (replicate n ■) → 𝒫 Value)
  → 𝒫 Value
binds zero _ K = K ptt
binds (suc n) ⟨ D , Ds ⟩ K = D ≫= λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)

{- Kinds of values, and the check of a kernel ----------------------------------}

data Kind : Set where
  fun inj prod error : Kind
  tup : ℕ → Kind
  base : Base → Kind

kind : Value → Kind
kind (const {B} k) = base B
kind (V ↦ w) = fun
kind ν = fun
kind ω = error
kind ⦅ u , v ⦆ = prod
kind (tup[_]_ {n} i d) = tup n
kind (left d) = inj
kind (right d) = inj
kind ⟨⟩ = tup 0

{- X has a value that is not of kind k -}
Bad : Kind → 𝒫 Value → Set
Bad k X = Σ[ d ∈ Value ] d ∈ X × kind d ≢ k

{- A, and ω when X has a value of another kind than k -}
checked : Kind → 𝒫 Value → 𝒫 Value → 𝒫 Value
checked k X A w = (w ≡ ω × Bad k X) ⊎ w ∈ A

{- The operators -------------------------------------------------------------------}

{- a finite set without ω: what a binder binds -}
NoErr : List Value → Set
NoErr V = ¬ (ω ∈ mem V)

{- an entry of a function on values, a payload that is a value -}
ValEntry : Value → Set
ValEntry (V ↦ w) = NoErr V
ValEntry _ = ⊤

ValPayload : Value → Set
ValPayload (left v) = v ≢ ω
ValPayload (right v) = v ≢ ω
ValPayload _ = ⊤

{- a function binds only values: the entries of Λ on sets without ω -}
Λᵐ : DOp (𝒫 Value) (ν ■ ∷ [])
Λᵐ Fs = Λ Fs ⇂ ValEntry

⋆ᵐ : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
⋆ᵐ ⟨ D , ⟨ E , _ ⟩ ⟩ = D ≫= λ F → checked fun F (E ≫= λ X → ⋆ ⟨ F , ⟨ X , ptt ⟩ ⟩)

𝒯ᵐ : ∀ n → DOp (𝒫 Value) (replicate n ■)
𝒯ᵐ n Ds = binds n Ds (𝒯 n)

projᵐ : ∀ {n} → Fin n → DOp (𝒫 Value) (■ ∷ [])
projᵐ {n} i ⟨ D , _ ⟩ = D ≫= λ X → checked (tup n) X (proj i ⟨ X , ptt ⟩)

inlᵐ : DOp (𝒫 Value) (■ ∷ [])
inlᵐ ⟨ D , _ ⟩ = D ≫= λ X → inl ⟨ X , ptt ⟩

inrᵐ : DOp (𝒫 Value) (■ ∷ [])
inrᵐ ⟨ D , _ ⟩ = D ≫= λ X → inr ⟨ X , ptt ⟩

{- a case binds only payloads that are values -}
𝒞ᵐ : DOp (𝒫 Value) (■ ∷ ν ■ ∷ ν ■ ∷ [])
𝒞ᵐ ⟨ D , ⟨ F , ⟨ G , _ ⟩ ⟩ ⟩ = D ≫= λ X → checked inj X (𝒞 ⟨ X ⇂ ValPayload , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩)

{- let x = D in F x, which means (λx. F x) D -}
letᵐ : DOp (𝒫 Value) (■ ∷ ν ■ ∷ [])
letᵐ ⟨ D , ⟨ F , _ ⟩ ⟩ = ⋆ᵐ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

{- Closures and pairs (Clos3, Clos4) -----------------------------------------------}

{- a closed function of two arguments on values: the code of a closure -}
ValEntry₂ : Value → Set
ValEntry₂ (V ↦ w) = NoErr V × ValEntry w
ValEntry₂ _ = ⊤

ΛΛᵐ : DOp (𝒫 Value) (∁ (ν (ν ■)) ∷ [])
ΛΛᵐ ⟨ F , _ ⟩ = Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ ⇂ ValEntry₂

{- a Clos3 closure: its code applied to the tuple of its free variables -}
closᵐ : ∀ n → DOp (𝒫 Value) (∁ (ν (ν ■)) ∷ replicate n ■)
closᵐ n ⟨ F , Ds ⟩ = ⋆ᵐ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ 𝒯ᵐ n Ds , ptt ⟩ ⟩

pairᵐ : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
pairᵐ Ds = binds 2 Ds pair

carᵐ : DOp (𝒫 Value) (■ ∷ [])
carᵐ ⟨ D , _ ⟩ = D ≫= λ X → checked prod X (car ⟨ X , ptt ⟩)

cdrᵐ : DOp (𝒫 Value) (■ ∷ [])
cdrᵐ ⟨ D , _ ⟩ = D ≫= λ X → checked prod X (cdr ⟨ X , ptt ⟩)

{- the call of Clos4 and Clos5: code, environment and argument are bound
   left to right, and only then is the code checked (the late check) -}
callᵐ : DOp (𝒫 Value) (■ ∷ ■ ∷ ■ ∷ [])
callᵐ Ds = binds 3 Ds λ { ⟨ F , ⟨ E , ⟨ X , _ ⟩ ⟩ ⟩ → checked fun F (⋆ ⟨ ⋆ ⟨ F , ⟨ E , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩) }

{- Code and machine state (Clos5, Imp, CFG, X86) -----------------------------------}

{- the code of a reference to no definition: a function whose call errs,
   after its operands, as the machines' late check does -}
errcode : 𝒫 Value
errcode = ΛΛᵐ ⟨ (λ X Y → ⌈ ω ⌉) , ptt ⟩

{- E once D has a value; ω if D holds ω: a strict write of D, before E -}
strictᵐ : 𝒫 Value → 𝒫 Value → 𝒫 Value
strictᵐ D E = D ≫= λ _ → E

{- the payload of an injection; an error on a value that is not one -}
payloadᵐ : 𝒫 Value → 𝒫 Value
payloadᵐ D = D ≫= λ X → checked inj X (payloadD (X ⇂ ValPayload))

{- the flag that testinl sets, by the tag of an injection -}
isinlD : 𝒫 Value → 𝒫 Value
isinlD D w = (Σ[ u ∈ Value ] left u ∈ D × w ≡ left ⟨⟩) ⊎ (Σ[ u ∈ Value ] right u ∈ D × w ≡ right ⟨⟩)

isinlᵐ : 𝒫 Value → 𝒫 Value
isinlᵐ D = D ≫= λ X → checked inj X (isinlD X)
