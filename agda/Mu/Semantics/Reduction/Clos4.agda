{-

  A reduction semantics for Clos4μ (Mu/Language/Clos4.agda), as for
  Clos3μ (Mu/Semantics/Reduction/Clos3.agda) and Clos4ᵀ
  (Semantics/Reduction/Typed/Clos4.agda). Code is a value, and so is a
  pack of values; callc L M evaluates L and M, and then calls the code
  of the closure L with its environment and the argument.

-}

module Mu.Semantics.Reduction.Clos4 where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)
import Language.Prim as P
open import Mu.Language.Type hiding (_[_])
open import Mu.Language.Clos4
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr; o-error)
open import Semantics.Reduction.Smallstep using (Machine; Red; val; error; to; step-in; reduction)
open import Mu.Framework.ReductionAll Obs o-error using (red-∷)

open import Data.Bool using (if_then_else_)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

{- Renaming and substitution ----------------------------------------------}

open import Framework.Syntax.Kit {Ctx} {Type} _∋_ (λ Γ A → A ∷ Γ) Tm public

module _ (𝒦 : Kit) where
  open Kit 𝒦

  exts : ∀ {Γ Δ B} → Sub 𝒦 Γ Δ → Sub 𝒦 (B ∷ Γ) (B ∷ Δ)
  exts σ Z = vr Z
  exts σ (S x) = wk (σ x)

  trav : ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A
  travs : ∀ {Γ Δ Δ'} → Sub 𝒦 Γ Δ → All (Tm Γ) Δ' → All (Tm Δ) Δ'
  trav σ (` x) = tm (σ x)
  trav σ (code N) = code N
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
  trav σ (fold M) = fold (trav σ M)
  trav σ (unfold M) = unfold (trav σ M)
  travs σ [] = []
  travs σ (M ∷ Ms) = trav σ M ∷ travs σ Ms

varK : Kit
varK = record { K = _∋_ ; vr = λ x → x ; tm = `_ ; wk = S }

ren : ∀ {Γ Δ A} → (∀ {B} → Γ ∋ B → Δ ∋ B) → Tm Γ A → Tm Δ A
ren r = trav varK r

tmK : Kit
tmK = record { K = Tm ; vr = `_ ; tm = λ M → M ; wk = ren S }

sub : ∀ {Γ Δ A} → (∀ {B} → Γ ∋ B → Tm Δ B) → Tm Γ A → Tm Δ A
sub σ = trav tmK σ

{- a closing substitution: values for the variables, the newest first -}
infixr 5 _•_
_•_ : ∀ {Γ Δ A} → Tm Δ A → (∀ {B} → Γ ∋ B → Tm Δ B) → ∀ {B} → (A ∷ Γ) ∋ B → Tm Δ B
(V • σ) Z = V
(V • σ) (S x) = σ x

∅ : ∀ {Δ B} → [] ∋ B → Tm Δ B
∅ ()

{- substituting a value for variable 0 -}
_[_] : ∀ {A B} → Tm (A ∷ []) B → Tm [] A → Tm [] B
N [ V ] = sub (V • ∅) N

{- The reduction ----------------------------------------------------------}

obs : ∀ {A} → Tm [] A → Obs
obss : ∀ {Δ} → All (Tm []) Δ → List Obs
obs (pack _ _) = o-fun
obs (lit B c) = o-const B c
obs (tuple Ms) = o-tuple (obss Ms)
obs (inl M) = o-inl (obs M)
obs (inr M) = o-inr (obs M)
obs (fold M) = obs M
obs _ = o-error
obss [] = []
obss (M ∷ Ms) = obs M ∷ obss Ms

{- the term of a primitive's result: eq gives inl ⟨⟩ for true -}
out : ∀ {Γ} p → ℤ → ℤ → Tm Γ (out-ty p)
out P.sub n m = lit Int (n - m)
out P.eq n m = if does (n ≟ m) then inl (tuple []) else inr (tuple [])

{- the redexes, once the operands are values -}
{- (the code of a pack is split by a second function, at a generic type) -}
call-code : ∀ {C Δ A B} → Tm [] C → C ≡ code Δ A B → Tm [] (tup Δ) → Tm [] A → Red (Tm [] B)
call-code (code N) refl E W = to (sub (W • E • ∅) N)
call-code _ _ E W = error

call : ∀ {C A B} → Tm [] C → C ≡ A ⇒ B → Tm [] A → Red (Tm [] B)
call (pack L E) refl W = call-code L refl E W
call _ _ W = error

get? : ∀ {C Δ A} → Δ ∋ A → Tm [] C → C ≡ tup Δ → Red (Tm [] A)
get? i (tuple Vs) refl = to (lookup Vs i)
get? i _ _ = error

case? : ∀ {C A B D} → Tm [] C → C ≡ A ⊹ B → Tm (A ∷ []) D → Tm (B ∷ []) D → Red (Tm [] D)
case? (inl V) refl M N = to (M [ V ])
case? (inr V) refl M N = to (N [ V ])
case? _ _ M N = error

prim? : ∀ p {A B} → Tm [] A → Tm [] B → Red (Tm [] (out-ty p))
prim? p (lit Int n) (lit Int m) = to (out p n m)
prim? p _ _ = error

unfold? : ∀ {C A c} → Tm [] C → C ≡ μ A {c} → Red (Tm [] (unroll A {c}))
unfold? (fold V) refl = to V
unfold? _ _ = error

red : ∀ {A} → Tm [] A → Red (Tm [] A)
reds : ∀ {Δ} → All (Tm []) Δ → Red (All (Tm []) Δ)
red (` ())
red (code N) = val
red (pack L M) = step-in (λ L' → pack L' M) (red L) (step-in (pack L) (red M) val)
red (callc L M) = step-in (λ L' → callc L' M) (red L) (step-in (callc L) (red M) (call L refl M))
red (lit B c) = val
red (tuple Ms) = step-in tuple (reds Ms) val
red (get i M) = step-in (get i) (red M) (get? i M refl)
red (inl M) = step-in inl (red M) val
red (inr M) = step-in inr (red M) val
red (case L M N) = step-in (λ L' → case L' M N) (red L) (case? L refl M N)
red (prim p L M) = step-in (λ L' → prim p L' M) (red L) (step-in (prim p L) (red M) (prim? p L M))
red (let′ M N) = step-in (λ M' → let′ M' N) (red M) (to (N [ M ]))
red (fold M) = step-in fold (red M) val
red (unfold M) = step-in unfold (red M) (unfold? M refl)
reds [] = val
reds (M ∷ Ms) = red-∷ M Ms (red M) (reds Ms)

sem : ∀ {A} → Tm [] A → Machine
sem M = reduction obs red M
