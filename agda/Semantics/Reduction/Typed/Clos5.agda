{-

  A reduction semantics for Clos5ᵀ (Language/Typed/Clos5.agda), as for
  Clos4ᵀ (Semantics/Reduction/Typed/Clos4.agda), for a program's table of
  definitions ds: a reference to a definition is a value, and callc
  calls the definition it refers to. A let binds a value of any type.

-}

module Semantics.Reduction.Typed.Clos5 where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)
import Language.Prim as P
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos5 hiding (wk; wks)
open import Framework.Lookup using (_!_)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr; o-error)
open import Semantics.Reduction.Smallstep using (Machine; Red; val; error; to; step-in; reduction)
open import Framework.ReductionVec Obs o-error using (red-∷)

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; does)

{- Renaming and substitution, for a table Σ ----------------------------------}

module _ {Σ : List ℕ} where
  open import Framework.Syntax.Kit {Ctx} {Ty} _∋_ (λ Γ A → A ∷ Γ) (Tm Σ) public

  module _ (𝒦 : Kit) where
    open Kit 𝒦

    exts : ∀ {Γ Δ B} → Sub 𝒦 Γ Δ → Sub 𝒦 (B ∷ Γ) (B ∷ Δ)
    exts σ Z = vr Z
    exts σ (S x) = wk (σ x)

    trav : ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Σ Γ A → Tm Σ Δ A
    travs : ∀ {Γ Δ n} → Sub 𝒦 Γ Δ → Vec (Tm Σ Γ Any) n → Vec (Tm Σ Δ Any) n
    trav σ (` x) = tm (σ x)
    trav σ (fun-ref f) = fun-ref f
    trav σ (pack L M) = pack (trav σ L) (trav σ M)
    trav σ (callc L M) = callc (trav σ L) (trav σ M)
    trav σ (lit B c) = lit B c
    trav σ (tuple Ms) = tuple (travs σ Ms)
    trav σ (get i M) = get i (trav σ M)
    trav σ (inl M) = inl (trav σ M)
    trav σ (inr M) = inr (trav σ M)
    trav σ (case L M N) = case (trav σ L) (trav (exts σ) M) (trav (exts σ) N)
    trav σ (prim p L M) = prim p (trav σ L) (trav σ M)
    trav σ (let′ M N) = let′ (trav σ M) (trav (exts σ) N)
    trav σ (inject G M) = inject G (trav σ M)
    trav σ (project t M) = project t (trav σ M)
    travs σ [] = []
    travs σ (M ∷ Ms) = trav σ M ∷ travs σ Ms

  varK : Kit
  varK = record { K = _∋_ ; vr = λ x → x ; tm = `_ ; wk = S }

  ren : ∀ {Γ Δ A} → (∀ {B} → Γ ∋ B → Δ ∋ B) → Tm Σ Γ A → Tm Σ Δ A
  ren r = trav varK r

  tmK : Kit
  tmK = record { K = Tm Σ ; vr = `_ ; tm = λ M → M ; wk = ren S }

  sub : ∀ {Γ Δ A} → (∀ {B} → Γ ∋ B → Tm Σ Δ B) → Tm Σ Γ A → Tm Σ Δ A
  sub σ = trav tmK σ

  {- a closing substitution: values for the variables, the newest first -}
  infixr 5 _•_
  _•_ : ∀ {Γ Δ A} → Tm Σ Δ A → (∀ {B} → Γ ∋ B → Tm Σ Δ B) → ∀ {B} → (A ∷ Γ) ∋ B → Tm Σ Δ B
  (V • σ) Z = V
  (V • σ) (S x) = σ x

  ∅ : ∀ {Δ B} → [] ∋ B → Tm Σ Δ B
  ∅ ()

  {- substituting a value for variable 0 -}
  _[_] : ∀ {A B} → Tm Σ (A ∷ []) B → Tm Σ [] A → Tm Σ [] B
  N [ V ] = sub (V • ∅) N

{- The reduction ----------------------------------------------------------}

module _ {Σ : List ℕ} where

  obs : ∀ {A} → Tm Σ [] A → Obs
  obss : ∀ {n} → Vec (Tm Σ [] Any) n → List Obs
  obs (pack _ _) = o-fun
  obs (lit B c) = o-const B c
  obs (tuple Ms) = o-tuple (obss Ms)
  obs (inl M) = o-inl (obs M)
  obs (inr M) = o-inr (obs M)
  obs (inject G M) = obs M
  obs _ = o-error
  obss [] = []
  obss (M ∷ Ms) = obs M ∷ obss Ms

  {- the term of a primitive's result: eq gives inl ⟨⟩ for true -}
  out : ∀ {Γ} p → ℤ → ℤ → Tm Σ Γ ⟪ out-flat p ⟫
  out P.sub n m = lit Int (n - m)
  out P.eq n m = if does (n ≟ m) then inl unit else inr unit
    where unit = inject (tup 0) (tuple [])

  {- the redexes, once the operands are values -}
  call : ∀ {A} → All (Code Σ) Σ → Tm Σ [] A → Tm Σ [] Any → Red (Tm Σ [] Any)
  call ds (pack (fun-ref f) E) W = to (sub (W • E • ∅) (ds ! f))
  call ds _ W = error

  get? : ∀ {A n} → Fin n → Tm Σ [] A → A ≡ ⟪ tup n ⟫ → Red (Tm Σ [] Any)
  get? i (tuple Vs) refl = to (lookup Vs i)
  get? i _ _ = error

  case? : ∀ {A} → Tm Σ [] A → Tm Σ (Any ∷ []) Any → Tm Σ (Any ∷ []) Any → Red (Tm Σ [] Any)
  case? (inl V) M N = to (M [ V ])
  case? (inr V) M N = to (N [ V ])
  case? _ M N = error

  prim? : ∀ p {A B} → Tm Σ [] A → Tm Σ [] B → Red (Tm Σ [] ⟪ out-flat p ⟫)
  prim? p (lit Int n) (lit Int m) = to (out p n m)
  prim? p _ _ = error

  {- the only error: a value injected from another flat type -}
  proj-dec : ∀ {G H} → Dec (G ≡ H) → Tm Σ [] ⟪ G ⟫ → Red (Tm Σ [] ⟪ H ⟫)
  proj-dec (yes refl) V = to V
  proj-dec (no _) V = error

  project? : ∀ t {A} → Tm Σ [] A → Red (Tm Σ [] ⟪ flat t ⟫)
  project? t (inject G V) = proj-dec (G ≟F flat t) V
  project? t _ = error

  {- the reduction for a program with the definitions ds -}
  red : All (Code Σ) Σ → ∀ {A} → Tm Σ [] A → Red (Tm Σ [] A)
  reds : All (Code Σ) Σ → ∀ {n} → Vec (Tm Σ [] Any) n → Red (Vec (Tm Σ [] Any) n)
  red ds (` ())
  red ds (fun-ref f) = val
  red ds (pack L M) = step-in (λ L' → pack L' M) (red ds L) (step-in (pack L) (red ds M) val)
  red ds (callc L M) = step-in (λ L' → callc L' M) (red ds L) (step-in (callc L) (red ds M) (call ds L M))
  red ds (lit B c) = val
  red ds (tuple Ms) = step-in tuple (reds ds Ms) val
  red ds (get i M) = step-in (get i) (red ds M) (get? i M refl)
  red ds (inl M) = step-in inl (red ds M) val
  red ds (inr M) = step-in inr (red ds M) val
  red ds (case L M N) = step-in (λ L' → case L' M N) (red ds L) (case? L M N)
  red ds (prim p L M) = step-in (λ L' → prim p L' M) (red ds L) (step-in (prim p L) (red ds M) (prim? p L M))
  red ds (let′ M N) = step-in (λ M' → let′ M' N) (red ds M) (to (N [ M ]))
  red ds (inject G M) = step-in (inject G) (red ds M) val
  red ds (project t M) = step-in (project t) (red ds M) (project? t M)
  reds ds [] = val
  reds ds (M ∷ Ms) = red-∷ M Ms (red ds M) (reds ds Ms)

sem : Program → Machine
sem (program ds M) = reduction obs (red ds) M
