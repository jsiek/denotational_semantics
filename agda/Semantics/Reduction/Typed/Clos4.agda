{-

  A reduction semantics for Clos4ᵀ (Language/Typed/Clos4.agda), as for
  Clos3ᵀ (Semantics/Reduction/Typed/Clos3.agda). Code is a value, and
  so is a pack of values; callc L M evaluates L and M, and then calls
  the code of the closure L with its environment and the argument.

-}

module Semantics.Reduction.Typed.Clos4 where

open import Framework.Primitives using (Int)
open import Language.Prim using (Prim)
import Language.Prim as P
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos4
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr; o-error)
open import Semantics.Reduction.Smallstep using (Machine; Red; val; error; to; step-in; reduction)
open import Framework.ReductionVec Obs o-error using (red-∷)

open import Data.Bool using (if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; _-_; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; does)

{- Renaming and substitution ----------------------------------------------}

open import Framework.Syntax.Kit {Ctx} {Ty} _∋_ (λ Γ A → A ∷ Γ) Tm public

module _ (𝒦 : Kit) where
  open Kit 𝒦

  exts : ∀ {Γ Δ B} → Sub 𝒦 Γ Δ → Sub 𝒦 (B ∷ Γ) (B ∷ Δ)
  exts σ Z = vr Z
  exts σ (S x) = wk (σ x)

  trav : ∀ {Γ Δ A} → Sub 𝒦 Γ Δ → Tm Γ A → Tm Δ A
  travs : ∀ {Γ Δ n} → Sub 𝒦 Γ Δ → Vec (Tm Γ Any) n → Vec (Tm Δ Any) n
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
  trav σ (inject G M) = inject G (trav σ M)
  trav σ (project t M) = project t (trav σ M)
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
obss : ∀ {n} → Vec (Tm [] Any) n → List Obs
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
out : ∀ {k} p → ℤ → ℤ → Tm k ⟪ out-flat p ⟫
out P.sub n m = lit Int (n - m)
out P.eq n m = if does (n ≟ m) then inl unit else inr unit
  where unit = inject (tup 0) (tuple [])

{- the redexes, once the operands are values (on terms of any type, so
   that the other shapes need no unification of types) -}
call : ∀ {A} → Tm [] A → Tm [] Any → Red (Tm [] Any)
call (pack (code N) E) W = to (sub (W • E • ∅) N)
call _ W = error

get? : ∀ {A n} → Fin n → Tm [] A → A ≡ ⟪ tup n ⟫ → Red (Tm [] Any)
get? i (tuple Vs) refl = to (lookup Vs i)
get? i _ _ = error

case? : ∀ {A} → Tm [] A → Tm (Any ∷ []) Any → Tm (Any ∷ []) Any → Red (Tm [] Any)
case? (inl V) M N = to (M [ V ])
case? (inr V) M N = to (N [ V ])
case? _ M N = error

prim? : ∀ p {A B} → Tm [] A → Tm [] B → Red (Tm [] ⟪ out-flat p ⟫)
prim? p (lit Int n) (lit Int m) = to (out p n m)
prim? p _ _ = error

{- the only error: a value injected from another flat type -}
proj-dec : ∀ {G H} → Dec (G ≡ H) → Tm [] ⟪ G ⟫ → Red (Tm [] ⟪ H ⟫)
proj-dec (yes refl) V = to V
proj-dec (no _) V = error

project? : ∀ t {A} → Tm [] A → Red (Tm [] ⟪ flat t ⟫)
project? t (inject G V) = proj-dec (G ≟F flat t) V
project? t _ = error

red : ∀ {A} → Tm [] A → Red (Tm [] A)
reds : ∀ {n} → Vec (Tm [] Any) n → Red (Vec (Tm [] Any) n)
red (` ())
red (code N) = val
red (pack L M) = step-in (λ L' → pack L' M) (red L) (step-in (pack L) (red M) val)
red (callc L M) = step-in (λ L' → callc L' M) (red L) (step-in (callc L) (red M) (call L M))
red (lit B c) = val
red (tuple Ms) = step-in tuple (reds Ms) val
red (get i M) = step-in (get i) (red M) (get? i M refl)
red (inl M) = step-in inl (red M) val
red (inr M) = step-in inr (red M) val
red (case L M N) = step-in (λ L' → case L' M N) (red L) (case? L M N)
red (prim p L M) = step-in (λ L' → prim p L' M) (red L) (step-in (prim p L) (red M) (prim? p L M))
red (let′ M N) = step-in (λ M' → let′ M' N) (red M) (to (N [ M ]))
red (inject G M) = step-in (inject G) (red M) val
red (project t M) = step-in (project t) (red M) (project? t M)
reds [] = val
reds (M ∷ Ms) = red-∷ M Ms (red M) (reds Ms)

sem : Tm [] Any → Machine
sem M = reduction obs red M
