{-

  Correctness of delay (EnvClosμ → PairClosμ) in Scott domains, the forward
  half: what a source program produces, the compiled one produces too
  (Pres, the relation of DelayRel.agda that approximates the source).

  What is left from DelayRel.agda are the two constructs where the
  languages differ. A EnvClosμ closure is its code applied to the tuple of
  its free variables, a function value; its translation is the pair of
  the translated code and the tuple (Pres-clos). An application of a
  function value is related to a call of a pair (Pres-call): the
  approximation of depth n of the result is the sup of the
  approximations of the applications to the approximations of the
  argument (approx-∐), and each of those is related, by the relation of
  the closures at a greater depth.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (transport₂; ap₂)

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (_+_)

module Mu.proof.Correctness.ScottDomains.DelayPreserve
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Stages pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe
open import Mu.proof.Correctness.ScottDomains.DelayRel pt fe pe

Pres : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Pres = Rel preserve

{- Closures: related when the tuples are and the bodies are on related
   arguments -}
Pres-clos : (B B' : Den Env) {t t' : ⟨ 𝔻 ⟩} → Pres t t'
  → (∀ {X X' Y Y'} → Pres X X' → Pres Y Y' → Pres (B · env₂ X Y) (B' · env₂ X' Y'))
  → Pres (appᵈ · codeᶜ B · t) (pairᵈ · codeᶜ B' · t')
Pres-clos B B' {t} {t'} ht hB =
  Rel-from-defined λ q →
    let qt = seq-defined-l t _ (transport defined (app-Λ G t) q)
        qt' = Rel-defined ht qt
    in transport₂ Pres (code₂-env BE t qt ⁻¹)
                       (guard-defined 2 (pick₂ (codeᶜ B') t') (λ { zero → Λ-defined G' ; (suc zero) → qt' })
                          (inj pr · pick₂ (codeᶜ B') t') ⁻¹)
         (Rel-inj (strict · (curry₁ 𝔻 𝔻 𝔻 BE · t)) (pick₂ (codeᶜ B') t') s-fun
           (λ n v a r → transport (R preserve n (π∞ n · (strict · (curry₁ 𝔻 𝔻 𝔻 BE · t) · (ε∞ n · v))))
                          ((codeᶜ-β B' t' a ∙ seq-defined t' (seq · a · (B' · env₂ t' a)) qt') ⁻¹)
                          (stage (Rel-seq (Rel-ε n r) (hB ht (Rel-ε n r))) n)))
 where
  BE = ∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B
  G = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 BE) Λ
  G' = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B')) Λ

{- Calls: an application of a function value, and a call of a pair -}
Pres-call : {l l' a a' : ⟨ 𝔻 ⟩} → Pres l l' → Pres a a'
  → Pres (appᵈ · l · a) (appᵈ · (appᵈ · (car · l') · (cdr · l')) · a')
Pres-call {l} {l'} {a} {a'} hl ha =
  Rel-from-defined λ q →
    Rel-cases hl (app-defined l a q) (λ u v → Pres (appᵈ · u · a) (appᵈ · (appᵈ · (car · v) · (cdr · v)) · a'))
      (λ {t} {t'} x y e m → transport₂ Pres (ap (_· a) (case-inj (𝔻 ⟹𝔻) app-br t x) ⁻¹)
                                            (ap₂ (λ c d → appᵈ · (appᵈ · c · d) · a') (case-inj 𝔻⊥ (component-br zero) t' y)
                                                 (case-inj 𝔻⊥ (component-br (suc zero)) t' y) ⁻¹)
                              (call-ok x y e m))
 where
  call-fun : (s : DCPO[ 𝔻 , 𝔻 ]) (cd : Fin 2 → ⟨ 𝔻 ⟩) → ((n : ℕ) → M preserve n s-fun (approx n fun s) cd)
    → Pres (s · a) (call cd a')
  call-fun s cd m = rel λ n →
    transport (λ - → R preserve n - (call cd a')) (approx-∐ (𝓓 n) (∘₁ 𝔻 𝔻 (𝓓 n) s (π∞ n)) a ⁻¹)
      (R-sup preserve n (call cd a') (λ k → π∞ n · (s · e k a))
         (image-is-directed' 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 (𝓓 n) s (π∞ n)) {ℕ} {λ k → e k a} (e-directed a))
         (λ k → R-mono preserve n (π∞ n · (s · e (k + n) a)) (π∞ n · (s · e k a)) (call cd a')
                  (monotone-if-continuous 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 (𝓓 n) s (π∞ n)) (e k a) (e (k + n) a)
                     (e-mono a k (k + n) (≤+ k n)))
                  (transport (λ - → R preserve n - (call cd a')) (πs-π∞ k n (s · e (k + n) a))
                     (R-πs preserve k n (π∞ (k + n) · (s · e (k + n) a)) (call cd a')
                        (m (k + n) (π∞ (k + n) · a) a' (stage ha (k + n)))))))

  call-ok : ∀ {t t'} (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩) (e : Same preserve t t')
    → ((n : ℕ) → M preserve n e (approx n t x) y)
    → Pres (app-br t · x · a) (appᵈ · (appᵈ · (component-br zero t' · y) · (component-br (suc zero) t' · y)) · a')
  call-ok s cd s-fun m =
    Rel-from-defined λ q →
      transport (λ - → Pres - (call cd a')) (seq-defined a (s · a) (seq-defined-l a (s · a) q) ⁻¹) (call-fun s cd m)
  call-ok x y s-con m = Rel-⊥
  call-ok x y s-tup m = Rel-⊥
  call-ok x y s-left m = Rel-⊥
  call-ok x y s-right m = Rel-⊥
