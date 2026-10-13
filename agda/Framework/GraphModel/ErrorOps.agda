{-

  Error-propagating graph-model operators: the semantic algebra of the
  graph model with errors (Semantics/GraphErr/). (Their monotonicity,
  consistency, continuity, congruences and β laws are in
  proof/Framework/GraphModel/ErrorOps.agda and ErrorContinuity.agda.)

  The error is the value ω of the domain (Framework/GraphModel/Domain.agda),
  which is consistent only with itself. A denotation holds ω when the
  program stops with an error (a trapped error), and is empty when it
  diverges; so an operator yields ω

  * when it is applied to a value of the wrong kind (applying a
    non-function, a case on a non-injection, a projection from a
    non-tuple or a tuple of the wrong size), and
  * when one of its operands yields ω, evaluated left to right: an
    earlier operand yields ω, or all earlier operands have values and a
    later one yields ω. An earlier operand that diverges (an empty set)
    gives no error.

  Binders never bind ω: a function (Λᵉ) and a case (𝒞ᵉ) bind only
  finite, nonempty, consistent sets without ω, as call by value binds
  only values.

  Application checks that the operator is a function before it looks at
  the argument (as the machines do): applying a non-function is an error
  even if the argument diverges.

-}

module Framework.GraphModel.ErrorOps where

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig
open import Framework.GraphModel.Domain
open import Framework.GraphModel.OpsBase using (nthD)

open import Data.Empty renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; replicate)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product using (_×_; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_)
open import Data.Unit renaming (⊤ to True)
open import Framework.abt.Sig using (∁)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst)
open import Relation.Nullary using (¬_)

{- Values and errors ------------------------------------------------------------}

{- D has a value: an element other than ω (its operand converges) -}
val∈ : 𝒫 Value → Set
val∈ D = Σ[ d ∈ Value ] d ∈ D × d ≢ ω

{- D has a value that is not of the kind P -}
wrong : (Value → Set) → 𝒫 Value → Set
wrong P D = Σ[ d ∈ Value ] d ∈ D × d ≢ ω × ¬ P d

{- a finite set without ω, which a binder may bind -}
NoErr : List Value → Set
NoErr V = ¬ (ω ∈ mem V)

{- the kinds of values that the operators inspect -}
IsFun : Value → Set
IsFun ν = True
IsFun (V ↦ w) = True
IsFun _ = False

IsInj : Value → Set
IsInj (left d) = True
IsInj (right d) = True
IsInj _ = False

{- a tuple of n components -}
IsTup : ℕ → Value → Set
IsTup n (tup[_]_ {m} i d) = m ≡ n
IsTup n ⟨⟩ = n ≡ 0
IsTup n _ = False

{- n operands, left to right: some operand yields ω, and every operand
   before it has a value -}
errs : ∀ n → Results (𝒫 Value) (replicate n ■) → Set
errs zero _ = False
errs (suc n) ⟨ D , Ds ⟩ = ω ∈ D ⊎ (val∈ D × errs n Ds)

{- every operand has a value -}
vals : ∀ n → Results (𝒫 Value) (replicate n ■) → Set
vals n Ds = ∀ i → val∈ (nthD Ds i)

{- Operators ----------------------------------------------------------------------}

{- application: an entry V ↦ w of the operator whose V the argument
   contains; or an error: in the operator, an operator that is not a
   function, or an error in the argument of a function -}
⋆ᵉ : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
⋆ᵉ ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ w =
    (Σ[ V ∈ List Value ] (V ↦ w ∈ D₁) × (mem V ⊆ D₂) × V ≢ [] × NoErr V)
  ⊎ (w ≡ ω × (ω ∈ D₁ ⊎ wrong IsFun D₁ ⊎ ((Σ[ f ∈ Value ] f ∈ D₁ × IsFun f) × ω ∈ D₂)))

{- a function binds finite, nonempty, consistent sets without ω -}
Λᵉ : DOp (𝒫 Value) (ν ■ ∷ [])
Λᵉ ⟨ f , _ ⟩ (V ↦ w) = w ∈ f (mem V) × V ≢ [] × V ≈ V × NoErr V
Λᵉ ⟨ f , _ ⟩ ν = True
Λᵉ ⟨ f , _ ⟩ _ = False

{- tuples are strict, left to right -}
𝒯ᵉ : ∀ (n : ℕ) → DOp (𝒫 Value) (replicate n ■)
𝒯ᵉ n Ds ω = errs n Ds
𝒯ᵉ zero Ds ⟨⟩ = True
𝒯ᵉ (suc n) Ds (tup[_]_ {n'} i d) =
  Σ[ n≡ ∈ n' ≡ suc n ] d ∈ (nthD Ds (subst Fin n≡ i)) × vals (suc n) Ds
𝒯ᵉ n Ds d = False

{- projection: an error on ω or on a value that is not a tuple of n
   components -}
projᵉ : ∀ {n} → Fin n → DOp (𝒫 Value) (■ ∷ [])
projᵉ {n} i ⟨ D , _ ⟩ d = (tup[ i ] d) ∈ D ⊎ (d ≡ ω × (ω ∈ D ⊎ wrong (IsTup n) D))

inlᵉ : DOp (𝒫 Value) (■ ∷ [])
inlᵉ ⟨ D , _ ⟩ (left v) = v ∈ D × v ≢ ω
inlᵉ ⟨ D , _ ⟩ ω = ω ∈ D
inlᵉ ⟨ D , _ ⟩ _ = False

inrᵉ : DOp (𝒫 Value) (■ ∷ [])
inrᵉ ⟨ D , _ ⟩ (right v) = v ∈ D × v ≢ ω
inrᵉ ⟨ D , _ ⟩ ω = ω ∈ D
inrᵉ ⟨ D , _ ⟩ _ = False

{- case: a branch on the payloads of the scrutinee (finite, nonempty,
   consistent, without ω), or an error: in the scrutinee, or a scrutinee
   that is not an injection -}
𝒞ᵉ : DOp (𝒫 Value) (■ ∷ ν ■ ∷ ν ■ ∷ [])
𝒞ᵉ ⟨ D , ⟨ E , ⟨ F , _ ⟩ ⟩ ⟩ w =
    (Σ[ v ∈ Value ] Σ[ V ∈ List Value ] (∀ d → d ∈ mem (v ∷ V) → left d ∈ D)
       × w ∈ E (mem (v ∷ V)) × (v ∷ V) ≈ (v ∷ V) × NoErr (v ∷ V))
  ⊎ (Σ[ v ∈ Value ] Σ[ V ∈ List Value ] (∀ d → d ∈ mem (v ∷ V) → right d ∈ D)
       × w ∈ F (mem (v ∷ V)) × (v ∷ V) ≈ (v ∷ V) × NoErr (v ∷ V))
  ⊎ (w ≡ ω × (ω ∈ D ⊎ wrong IsInj D))

{- let x = D in F x, which means (λx. F x) D -}
letᵉ : DOp (𝒫 Value) (■ ∷ ν ■ ∷ [])
letᵉ ⟨ D , ⟨ F , _ ⟩ ⟩ = ⋆ᵉ ⟨ Λᵉ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

{- D, once n operands (a closure's free variables) have values; or an
   error in them, left to right -}
guardᵉ-n : ∀ n → Results (𝒫 Value) (replicate n ■) → 𝒫 Value → 𝒫 Value
guardᵉ-n n Ds D w = (w ≡ ω × errs n Ds) ⊎ (vals n Ds × w ∈ D)

{- Closures and pairs (Clos3, Clos4) ---------------------------------------------}

{- a closed function of two arguments: the code of a closure -}
ΛΛᵉ : DOp (𝒫 Value) (∁ (ν (ν ■)) ∷ [])
ΛΛᵉ ⟨ F , _ ⟩ = Λᵉ ⟨ (λ X → Λᵉ ⟨ F X , ptt ⟩) , ptt ⟩

{- a Clos3 closure: its code applied to the tuple of its free variables,
   which are evaluated left to right -}
closᵉ : ∀ n → DOp (𝒫 Value) (∁ (ν (ν ■)) ∷ replicate n ■)
closᵉ n ⟨ F , Ds ⟩ = ⋆ᵉ ⟨ ΛΛᵉ ⟨ F , ptt ⟩ , ⟨ 𝒯ᵉ n Ds , ptt ⟩ ⟩

IsPair : Value → Set
IsPair ⦅ u , v ⦆ = True
IsPair _ = False

{- a pair, left to right -}
pairᵉ : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
pairᵉ ⟨ D , ⟨ E , _ ⟩ ⟩ ⦅ u , v ⦆ = u ∈ D × v ∈ E × u ≢ ω × v ≢ ω
pairᵉ ⟨ D , ⟨ E , _ ⟩ ⟩ ω = errs 2 ⟨ D , ⟨ E , ptt ⟩ ⟩
pairᵉ ⟨ D , ⟨ E , _ ⟩ ⟩ _ = False

{- the components of a pair: an error on ω or on a value that is not a pair -}
carᵉ : DOp (𝒫 Value) (■ ∷ [])
carᵉ ⟨ D , _ ⟩ u = (Σ[ v ∈ Value ] ⦅ u , v ⦆ ∈ D) ⊎ (u ≡ ω × (ω ∈ D ⊎ wrong IsPair D))

cdrᵉ : DOp (𝒫 Value) (■ ∷ [])
cdrᵉ ⟨ D , _ ⟩ v = (Σ[ u ∈ Value ] ⦅ u , v ⦆ ∈ D) ⊎ (v ≡ ω × (ω ∈ D ⊎ wrong IsPair D))

{- the call of Clos4 (and Clos5): the code L, the environment M and the
   argument N are evaluated left to right, and only then is L checked to
   be code (the late check) -}
callᵉ : DOp (𝒫 Value) (■ ∷ ■ ∷ ■ ∷ [])
callᵉ ⟨ L , ⟨ M , ⟨ N , _ ⟩ ⟩ ⟩ w =
    (Σ[ V ∈ List Value ] Σ[ U ∈ List Value ] (V ↦ (U ↦ w)) ∈ L × mem V ⊆ M × mem U ⊆ N
       × V ≢ [] × U ≢ [] × NoErr V × NoErr U)
  ⊎ (w ≡ ω × (errs 3 ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩ ⊎ (wrong IsFun L × val∈ M × val∈ N)))

{- Code and machine state (Clos5, Imp, CFG, X86) -----------------------------}

{- the code of a reference to no definition: a function whose call errs,
   after its operands, as the machines' late check does -}
errcode : 𝒫 Value
errcode = ΛΛᵉ ⟨ (λ X Y → ⌈ ω ⌉) , ptt ⟩

{- E once D has a value; ω if D holds ω: a strict write of D, before E -}
strictᵉ : 𝒫 Value → 𝒫 Value → 𝒫 Value
strictᵉ D E w = (w ≡ ω × ω ∈ D) ⊎ (val∈ D × w ∈ E)

{- the payload of an injection; an error on ω or a non-injection -}
payloadᵉ : 𝒫 Value → 𝒫 Value
payloadᵉ D v = (left v ∈ D × v ≢ ω) ⊎ (right v ∈ D × v ≢ ω) ⊎ (v ≡ ω × (ω ∈ D ⊎ wrong IsInj D))
