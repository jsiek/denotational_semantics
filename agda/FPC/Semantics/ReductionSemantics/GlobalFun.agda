{-

  A reduction semantics for GlobalFunμ (Mu/Language/GlobalFun.agda), as for
  PairClosμ (Mu/Semantics/ReductionSemantics/PairClos.agda) and Clos5ᵀ
  (Semantics/Reduction/Typed/Clos5.agda), for a program's table of
  definitions ds: a reference to a definition is a value, and callc
  calls the definition it refers to.

-}

module Mu.Semantics.ReductionSemantics.GlobalFun where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)
import Language.Prim as P
open import Mu.Language.Type hiding (_[_])
open import Mu.Language.GlobalFun hiding (wk; wks)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr; o-error)
open import Semantics.Reduction.Smallstep using (Machine; Red; val; error; to; step-in; reduction)
open import Mu.Framework.ReductionAll Obs o-error using (red-∷)

open import Data.Bool using (if_then_else_)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

{- Renaming and substitution, for a table Σ ----------------------------------}

module _ {Σ : List DSig} where
  open import Framework.Syntax.Kit {Ctx} {Type} _∋_ (λ Γ A → A ∷ Γ) (Tm Σ) public

  module _ (𝒦 : Kit) where
    open Kit 𝒦

    exts : ∀ {Γ Δ B} → Sub 𝒦 Γ Δ → Sub 𝒦 (B ∷ Γ) (B ∷ Δ)
    exts σ Z = vr Z
    exts σ (S x) = wk (σ x)

    trav : ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Σ Γ A → Tm Σ Δ A
    travs : ∀ {Γ Δ Δ'} → Sub 𝒦 Γ Δ → All (Tm Σ Γ) Δ' → All (Tm Σ Δ) Δ'
    trav σ (` x) = tm (σ x)
    trav σ (fun-ref f) = fun-ref f
    trav σ (pair L M) = pair (trav σ L) (trav σ M)
    trav σ (callc L M) = callc (trav σ L) (trav σ M)
    trav σ (lit B c) = lit B c
    trav σ (tuple Ms) = tuple (travs σ Ms)
    trav σ (get i M) = get i (trav σ M)
    trav σ (inl M) = inl (trav σ M)
    trav σ (inr M) = inr (trav σ M)
    trav σ (case L M N) = case (trav σ L) (trav (exts σ) M) (trav (exts σ) N)
    trav σ (prim p L M) = prim p (trav σ L) (trav σ M)
    trav σ (let′ M N) = let′ (trav σ M) (trav (exts σ) N)
    trav σ (fold M) = fold (trav σ M)
    trav σ (unfold M) = unfold (trav σ M)
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

module _ {Σ : List DSig} where

  obs : ∀ {A} → Tm Σ [] A → Obs
  obss : ∀ {Δ} → All (Tm Σ []) Δ → List Obs
  obs (fun-ref _) = o-fun
  obs (pair _ _) = o-fun
  obs (lit B c) = o-const B c
  obs (tuple Ms) = o-tuple (obss Ms)
  obs (inl M) = o-inl (obs M)
  obs (inr M) = o-inr (obs M)
  obs (fold M) = obs M
  obs _ = o-error
  obss [] = []
  obss (M ∷ Ms) = obs M ∷ obss Ms

  {- the term of a primitive's result: eq gives inl ⟨⟩ for true -}
  out : ∀ {Γ} p → ℤ → ℤ → Tm Σ Γ (out-ty p)
  out P.sub n m = lit Int (n - m)
  out P.eq n m = if does (n ≟ m) then inl (tuple []) else inr (tuple [])

  {- the redexes, once the operands are values (the code of a pair is
     split by a second function, at a generic type) -}
  call-ref : ∀ {C Δ A B} → All (Code Σ) Σ → Tm Σ [] C → C ≡ code Δ A B → Tm Σ [] (tup Δ) → Tm Σ [] A → Red (Tm Σ [] B)
  call-ref ds (fun-ref f) refl E W = to (sub (W • E • ∅) (lookup ds f))
  call-ref ds _ _ E W = error

  call : ∀ {C A B} → All (Code Σ) Σ → Tm Σ [] C → C ≡ A ⇒ B → Tm Σ [] A → Red (Tm Σ [] B)
  call ds (pair L E) refl W = call-ref ds L refl E W
  call ds _ _ W = error

  get? : ∀ {C Δ A} → Δ ∋ A → Tm Σ [] C → C ≡ tup Δ → Red (Tm Σ [] A)
  get? i (tuple Vs) refl = to (lookup Vs i)
  get? i _ _ = error

  case? : ∀ {C A B D} → Tm Σ [] C → C ≡ A ⊹ B → Tm Σ (A ∷ []) D → Tm Σ (B ∷ []) D → Red (Tm Σ [] D)
  case? (inl V) refl M N = to (M [ V ])
  case? (inr V) refl M N = to (N [ V ])
  case? _ _ M N = error

  prim? : ∀ p {A B} → Tm Σ [] A → Tm Σ [] B → Red (Tm Σ [] (out-ty p))
  prim? p (lit Int n) (lit Int m) = to (out p n m)
  prim? p _ _ = error

  unfold? : ∀ {C A} → Tm Σ [] C → C ≡ μ A → Red (Tm Σ [] (unroll A))
  unfold? (fold V) refl = to V
  unfold? _ _ = error

  {- the reduction for a program with the definitions ds -}
  red : All (Code Σ) Σ → ∀ {A} → Tm Σ [] A → Red (Tm Σ [] A)
  reds : All (Code Σ) Σ → ∀ {Δ} → All (Tm Σ []) Δ → Red (All (Tm Σ []) Δ)
  red ds (` ())
  red ds (fun-ref f) = val
  red ds (pair L M) = step-in (λ L' → pair L' M) (red ds L) (step-in (pair L) (red ds M) val)
  red ds (callc L M) = step-in (λ L' → callc L' M) (red ds L) (step-in (callc L) (red ds M) (call ds L refl M))
  red ds (lit B c) = val
  red ds (tuple Ms) = step-in tuple (reds ds Ms) val
  red ds (get i M) = step-in (get i) (red ds M) (get? i M refl)
  red ds (inl M) = step-in inl (red ds M) val
  red ds (inr M) = step-in inr (red ds M) val
  red ds (case L M N) = step-in (λ L' → case L' M N) (red ds L) (case? L refl M N)
  red ds (prim p L M) = step-in (λ L' → prim p L' M) (red ds L) (step-in (prim p L) (red ds M) (prim? p L M))
  red ds (let′ M N) = step-in (λ M' → let′ M' N) (red ds M) (to (N [ M ]))
  red ds (fold M) = step-in fold (red ds M) val
  red ds (unfold M) = step-in unfold (red ds M) (unfold? M refl)
  reds ds [] = val
  reds ds (M ∷ Ms) = red-∷ M Ms (red ds M) (reds ds Ms)

sem : ∀ {A} → Program A → Machine
sem (program ds M) = reduction obs (red ds) M
