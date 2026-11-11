{-

  This module proves the forward half of the correctness of split
  (EnvClosμ → PairClosμ) in Scott domains. The relation Pres is the
  relation of SplitRel.agda that approximates the meaning of the source
  program. So if the meaning of the source program is defined, then the
  meaning of the target program is defined and related to it.

  SplitRel.agda handles every construct except the two where the languages
  differ, and this module handles those two. An EnvClosμ closure is its
  code applied to the tuple of its free variables, which gives a function.
  Its translation is the pair of the translated code and the tuple
  (Pres-clos). An application of a function is related to a call of a pair
  (Pres-call). The approximation of depth n of the application is the sup
  of the approximations of depth n of the function applied to the
  approximations e k a of the argument (approx-∐). The relation of the
  closures at the greater depth k + n relates each of those to the call.

-}

open import MLTT.Spartan hiding (inl; inr; cases; _+_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (transport₂; ap₂)

open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (_+_)

module FPC.proof.Correctness.ScottDomains.SplitPreserve
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Functor pt fe pe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; pair to
  pairᵈ)
open import proof.Framework.Scott.Stages pt fe pe
open import proof.Framework.Scott.Values pt fe pe
open import proof.Framework.Scott.Semantics pt fe pe
open import FPC.proof.Correctness.ScottDomains.SplitRel pt fe pe

Pres : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
Pres = Rel preserve

{- A closure means different things in the two languages. In EnvClosμ, it
   means its code applied to the tuple t of its free variables, which
   gives a function that awaits the argument. In PairClosμ, it means the
   pair of its code and the tuple t', with no application. Suppose t and
   t' are related, and the bodies B and B' give related results on related
   environments X, X' and related arguments Y, Y' (env₂ X Y is the
   environment that binds both). Then the application of the source code
   to t is related to the pair of the target code and t'. -}
Pres-clos : (B B' : Den Env) {t t' : ⟨ 𝔻 ⟩}
  → Pres t t'
  → (∀ {X X' Y Y'} → Pres X X' → Pres Y Y'
       → Pres (B · env₂ X Y) (B' · env₂ X' Y'))
  → Pres (appᵈ · codeᶜ B · t) (pairᵈ · codeᶜ B' · t')
Pres-clos B B' {t} {t'} ht hB =
  Rel-from-defined λ q →
    let qt = seq-defined-l t _ (transport defined (app-Λ G t) q)
        qt' = Rel-defined ht qt
    in transport₂ Pres (code₂-env BE t qt ⁻¹)
                       (guard-defined 2 (pick₂ (codeᶜ B') t')
                           (λ { zero → Λ-defined G' ; (suc zero) → qt' })
                          (inj pr · pick₂ (codeᶜ B') t') ⁻¹)
         (Rel-inj (strict · (curry₁ 𝔻 𝔻 𝔻 BE · t)) (pick₂ (codeᶜ B') t') s-fun
           (λ n v a r →
               transport
               (R preserve n
                 (π∞ n · (strict · (curry₁ 𝔻 𝔻 𝔻 BE · t) · (ε∞ n · v))))
                          ((codeᶜ-β B' t' a
                              ∙ seq-defined t' (seq · a · (B' · env₂ t' a)) qt')
                              ⁻¹)
                          (stage (Rel-seq (Rel-ε n r) (hB ht (Rel-ε n r))) n)))
 where
  BE = ∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B
  G = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 BE) Λ
  G' = ∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ B')) Λ

{- In EnvClosμ, an application applies the meaning l of its operator,
   which is expected to be a function, to the meaning a of its argument.
   In PairClosμ, the translated application is a call. The meaning l' of
   the translated operator is expected to be a pair of code and
   environment, and the call applies the code car · l' to the environment
   cdr · l' and then to the argument a'. If l and l' are related and a and
   a' are related, then the application of l to a is related to the call
   of l' on a'. -}
Pres-call : {l l' a a' : ⟨ 𝔻 ⟩}
  → Pres l l'
  → Pres a a'
  → Pres (appᵈ · l · a) (appᵈ · (appᵈ · (car · l') · (cdr · l')) · a')
Pres-call {l} {l'} {a} {a'} hl ha =
  Rel-from-defined λ q →
    Rel-inv hl (app-defined l a q)
      (λ u v → Pres (appᵈ · u · a) (appᵈ · (appᵈ · (car · v) · (cdr · v)) · a'))
      (λ {t} {t'} x y e m →
          transport₂ Pres
            (ap (_· a) (case-inj (𝔻 ⟹𝔻) app-br t x) ⁻¹)
            (ap₂ (λ c d → appᵈ · (appᵈ · c · d) · a')
               (case-inj 𝔻⊥ (component-br zero) t' y)
               (case-inj 𝔻⊥ (component-br (suc zero)) t' y) ⁻¹)
            (call-ok x y e m))
 where
  call-fun : (s : DCPO[ 𝔻 , 𝔻 ]) (cd : Fin 2 → ⟨ 𝔻 ⟩)
    → ((n : ℕ) → M preserve n s-fun (approx n fun s) cd)
    → Pres (s · a) (call cd a')
  call-fun s cd m = rel λ n →
    transport (λ - → R preserve n - (call cd a'))
      (approx-∐ (𝓓 n) (∘₁ 𝔻 𝔻 (𝓓 n) s (π∞ n)) a ⁻¹)
      (R-sup preserve n (call cd a') (λ k → π∞ n · (s · e k a))
         (image-is-directed' 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 (𝓓 n) s (π∞ n)) {ℕ} {λ k → e k a}
             (e-directed a))
         (λ k →
             R-mono preserve n (π∞ n · (s · e (k + n) a)) (π∞ n · (s · e k a))
             (call cd a')
                  (monotone-if-continuous 𝔻 (𝓓 n) (∘₁ 𝔻 𝔻 (𝓓 n) s (π∞ n))
                      (e k a) (e (k + n) a)
                     (e-mono a k (k + n) (≤+ k n)))
                  (transport (λ - → R preserve n - (call cd a'))
                      (πs-π∞ k n (s · e (k + n) a))
                     (R-πs preserve k n (π∞ (k + n) · (s · e (k + n) a))
                         (call cd a')
                        (m (k + n) (π∞ (k + n) · a) a' (stage ha (k + n)))))))

  call-ok : ∀ {t t'} (x : ⟨ obj (Payload t) 𝔻 ⟩) (y : ⟨ obj (Payload t') 𝔻 ⟩)
    → (e : Same preserve t t')
    → ((n : ℕ) → M preserve n e (approx n t x) y)
    → Pres (app-br t · x · a)
      (appᵈ ·
        (appᵈ · (component-br zero t' · y) · (component-br (suc zero) t' · y)) ·
        a')
  call-ok s cd s-fun m =
    Rel-from-defined λ q →
      transport (λ - → Pres - (call cd a'))
        (seq-defined a (s · a) (seq-defined-l a (s · a) q) ⁻¹) (call-fun s cd m)
  call-ok x y s-con m = Rel-⊥
  call-ok x y s-tup m = Rel-⊥
  call-ok x y s-left m = Rel-⊥
  call-ok x y s-right m = Rel-⊥
