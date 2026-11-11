{-

  This module proves the backward half of the correctness of split
  (EnvClosμ → PairClosμ) in Scott domains. The relation Refl d d' is the
  relation of SplitRel.agda that approximates the target value d'. So
  if the target program produces a value, then the source program
  produces a related value.

  As in SplitPreserve.agda, this module handles the two constructs
  where the languages differ. For a closure (Refl-clos), a call of the
  target pair, seen in an approximation of depth m + 2, shows its
  result at depth m (callₛ). That result lies below the approximation
  of depth m of the call of the pair itself (callₛ-below), and the
  relation is downward closed. For a call (Refl-call), the
  approximation of depth n of the result is the sup of the
  approximations of the calls on approximations of the code, the
  environment, and the argument (Rf-approx). Each of those lies below
  the approximation of a call at a greater depth, and the clause for
  pairs relates that call.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (transport₂; ap₂)

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (_+_)
open import Naturals.Order
open import Notation.Order

module FPC.proof.Correctness.ScottDomains.SplitReflect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; pair to
  pairᵈ)
open import proof.Framework.Scott.Stages pt fe pe
open import proof.Framework.Scott.StageCall pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe
open import FPC.proof.Correctness.ScottDomains.SplitRel pt fe pe

Refl : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Refl d d' = Rel reflect d' d

{- Closures -------------------------------------------------------------------}

{- Suppose the tuples t and t' of free variables are related, and the
   bodies B and B' give related results on related environments and
   related arguments. Then the source closure and the target pair are
   related by Refl. -}
Refl-clos : (B B' : Den Env) {t t' : ⟨ 𝔻 ⟩}
  → Refl t t'
  →
    (∀ {X X' Y Y'} → Refl X X' → Refl Y Y'
      → Refl (B · env₂ X Y) (B' · env₂ X' Y'))
  → Refl (appᵈ · codeᶜ B · t) (pairᵈ · codeᶜ B' · t')
Refl-clos B B' {t} {t'} ht hB =
  Rel-from-defined λ q →
    let qt' = pr₂ (pair-defined← (codeᶜ B') t' q)
        qt = Rel-defined ht qt'
    in transport₂ (Rel reflect)
         (guard-defined 2 (pick₂ (codeᶜ B') t')
             (λ { zero → Λ-defined G' ; (suc zero) → qt' })
             (inj pr · pick₂ (codeᶜ B') t') ⁻¹)
         (code₂-env BE t qt ⁻¹)
         (Rel-inj (pick₂ (codeᶜ B') t') (strict · s) s-pr calls)
 where
  BE = ∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B
  G' = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B')) Λ
  s = curry₁ 𝔻 𝔻 𝔻 BE · t
  {- If a and a' are related, then calling the target closure on a' is
     related to calling the source closure on a. -}
  body : ∀ {a a'}
    → Refl a a'
    → Refl (strict · s · a) (appᵈ · (appᵈ · codeᶜ B' · t') · a')
  body {a} {a'} ha =
    transport (λ - → Rel reflect - (strict · s · a)) (codeᶜ-β B' t' a' ⁻¹)
    (Rel-seq-l (Rel-seq ha (hB ht ha)))
  {- The clause for the target pair (Call) holds at every depth. -}
  calls : (n : ℕ)
    → Call n (approx n pr (pick₂ (codeᶜ B') t')) (strict · s)
  calls zero = ⋆
  calls (succ zero) = ⋆
  calls (succ (succ m)) v a r =
    R-mono reflect m (π∞ m · (appᵈ · (appᵈ · codeᶜ B' · t') · (ε∞ m · v)))
      (callₛ m (approx (succ (succ m)) pr (pick₂ (codeᶜ B') t')) v)
      (strict · (strict · s) · a) (callₛ-below m (pick₂ (codeᶜ B') t') v)
      (transport
          (R reflect m (π∞ m · (appᵈ · (appᵈ · codeᶜ B' · t') · (ε∞ m · v))))
          (seq-idem a (s · a) ⁻¹)
         (stage (body (Rel-ε m r)) m))

{- Calls ----------------------------------------------------------------------}

{- Suppose F maps 𝔻 into stage n. If F · e j x is related to d for
   every j, then F · x is related to d, because F · x is the sup of the
   F · e j x (approx-∐) and the relation is closed under directed sups
   (R-sup). -}
Rf-approx : (n : ℕ) (d : ⟨ 𝔻 ⟩) (F : DCPO[ 𝔻 , 𝓓 n ]) (x : ⟨ 𝔻 ⟩)
  → ((j : ℕ) → R reflect n (F · e j x) d)
  → R reflect n (F · x) d
Rf-approx n d F x h =
  transport (λ - → R reflect n - d) (approx-∐ (𝓓 n) F x ⁻¹)
    (R-sup reflect n d (λ j → F · e j x)
        (image-is-directed' 𝔻 (𝓓 n) F {ℕ} {λ k → e k x} (e-directed x)) h)

private
 ≤+' : (a b : ℕ)
   → b ≤ (a + b)
 ≤+' zero b = ≤-refl b
 ≤+' (succ a) b = ≤-trans b (a + b) (succ (a + b)) (≤+' a b) (≤-succ (a + b))

{- If l and l' are related and a and a' are related, then calling the
   pair l' on a' is related to applying the function value l to a. -}
Refl-call : {l l' a a' : ⟨ 𝔻 ⟩}
  → Refl l l'
  → Refl a a'
  → Refl (appᵈ · l · a) (appᵈ · (appᵈ · (car · l') · (cdr · l')) · a')
Refl-call {l} {l'} {a} {a'} hl ha =
  Rel-from-defined λ q →
    Rel-inv hl
      (component-defined zero l'
        (app-defined (car · l') (cdr · l')
          (app-defined (appᵈ · (car · l') · (cdr · l')) a' q)))
      (λ u v →
          Rel reflect (appᵈ · (appᵈ · (car · u) · (cdr · u)) · a')
          (appᵈ · v · a))
      (λ {t} {t'} x y e m → transport₂ (Rel reflect)
                              (ap₂ (λ c d → appᵈ · (appᵈ · c · d) · a')
                                  (case-inj 𝔻⊥ (component-br zero) t x)
                                   (case-inj 𝔻⊥ (component-br (suc zero)) t x)
                                     ⁻¹)
                              (ap (_· a) (case-inj (𝔻 ⟹𝔻) app-br t' y) ⁻¹)
                              (call-ok x y e m))
 where
  {- The maps in-arg, in-env, and in-code approximate one operand of a
     call at a time, namely the argument, the environment, and the
     code. -}
  in-arg : (n : ℕ) (f : ⟨ 𝔻 ⟩) → DCPO[ 𝔻 , 𝓓 n ]
  in-arg n f = ∘₁ 𝔻 𝔻 (𝓓 n) (appᵈ · f) (π∞ n)
  in-env : (n : ℕ) (c a : ⟨ 𝔻 ⟩) → DCPO[ 𝔻 , 𝓓 n ]
  in-env n c a = ∘₁ 𝔻 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 𝔻 (appᵈ · c) (app-at a)) (π∞ n)
  in-code : (n : ℕ) (y a : ⟨ 𝔻 ⟩) → DCPO[ 𝔻 , 𝓓 n ]
  in-code n y a = ∘₁ 𝔻 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 𝔻 (app-at y) (app-at a)) (π∞ n)

  call-fun : (cd : Fin 2 → ⟨ 𝔻 ⟩) (s : DCPO[ 𝔻 , 𝔻 ])
    → ((n : ℕ) → Call n (approx n pr cd) s)
    → Rel reflect (call cd a') (strict · s · a)
  call-fun cd s m = rel λ n →
    Rf-approx n (strict · s · a) (in-arg n (appᵈ · c · env)) a' λ j →
    Rf-approx n (strict · s · a) (in-env n c (e j a')) env λ i →
    Rf-approx n (strict · s · a) (in-code n (e i env) (e j a')) c λ l →
      core n l i j
   where
    c = cd zero
    env = cd (suc zero)
    core : (n l i j : ℕ)
      → R reflect n (π∞ n · (appᵈ · (appᵈ · e l c · e i env) · e j a'))
        (strict · s · a)
    core n l i j =
      R-mono reflect n (π∞ n · G)
        (π∞ n · (appᵈ · (appᵈ · e l c · e i env) · e j a')) (strict · s · a)
        (monotone-if-continuous 𝔻 (𝓓 n) (π∞ n) _ _
           (app-mono _ _ _ _
              (app-mono _ _ _ _
                  (e-mono c l (succ (succ K))
                    (≤-trans l K (succ (succ K)) l≤
                      (≤-trans K (succ K) (succ (succ K)) (≤-succ K)
                        (≤-succ (succ K)))))
                                (e-mono env i (succ K)
                                    (≤-trans i K (succ K) i≤ (≤-succ K))))
              (e-mono a' j K j≤)))
        (transport (λ - → R reflect n - (strict · s · a)) (πs-π∞ k' n G)
           (R-πs reflect k' n (π∞ K · G) (strict · s · a)
              (transport
                  (λ - →
                    R reflect K
                    (π∞ K ·
                      (appᵈ · (appᵈ · e (succ (succ K)) c · (ε∞ (succ K) · -)) ·
                        e K a')) (strict · s · a))
                 (π-π∞ (succ K) env)
                 (m (succ (succ K)) (π∞ K · a') a (stage ha K)))))
     where
      k' = (l + i) + j
      K = k' + n
      G = appᵈ · (appᵈ · e (succ (succ K)) c · e (succ K) env) · e K a'
      l≤ : l ≤ K
      l≤ =
        ≤-trans l (l + i) K (≤+ l i)
        (≤-trans (l + i) k' K (≤+ (l + i) j) (≤+ k' n))
      i≤ : i ≤ K
      i≤ =
        ≤-trans i (l + i) K (≤+' l i)
        (≤-trans (l + i) k' K (≤+ (l + i) j) (≤+ k' n))
      j≤ : j ≤ K
      j≤ = ≤-trans j k' K (≤+' (l + i) j) (≤+ k' n)

  {- If the called target value is not a pair, then its code and its
     environment are ⊥𝔻. So the call is ⊥𝔻, which is related to every
     source value. -}
  ⊥-call : ∀ {w}
    → Rel reflect (appᵈ · (appᵈ · ⊥𝔻 · ⊥𝔻) · a') w
  ⊥-call =
    transport (λ - → Rel reflect - _)
    ((ap (λ - → appᵈ · - · a') (app-⊥ ⊥𝔻) ∙ app-⊥ a') ⁻¹) Rel-⊥

  call-ok : ∀ {t t'} (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩)
    → (e : Same reflect t t')
    → ((n : ℕ) → M reflect n e (approx n t x) y)
    → Rel reflect
      (appᵈ ·
        (appᵈ · (component-br zero t · x) · (component-br (suc zero) t · x)) ·
          a') (app-br t' · y · a)
  call-ok cd s s-pr m = call-fun cd s m
  call-ok x y s-con m = ⊥-call
  call-ok x y s-tup m = ⊥-call
  call-ok x y s-left m = ⊥-call
  call-ok x y s-right m = ⊥-call
