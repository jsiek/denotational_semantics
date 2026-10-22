{-

  Scott domains: lemmas about the meanings built with the combinators of
  Framework/Scott/Semantics.agda: a let and a case of an injection
  reduce (β), the code of a closure applied to an environment and an
  argument runs its body, and the values a meaning is made of are
  defined (init, the environment of a closed program).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂)

open import Data.Fin using (Fin; zero; suc)
open import Framework.abt.GSubst using (_•_)

module proof.Framework.Scott.Semantics
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe
open import Framework.Scott.Semantics pt fe pe public

init-defined : defined init
init-defined = unit-defined

{- every position of an environment is defined -}
defined-env : ⟨ Env ⟩ → 𝓤₀ ̇
defined-env ρ = (x : ℕ) → defined (ρ x)

ρ₀ : ⟨ Env ⟩
ρ₀ = λ _ → init

ρ₀-defined : defined-env ρ₀
ρ₀-defined _ = init-defined

•-defined : (d : ⟨ 𝔻 ⟩) (ρ : ⟨ Env ⟩) → defined d → defined-env ρ → defined-env (d • ρ)
•-defined d ρ p h zero = p
•-defined d ρ p h (succ x) = h x

{- let x = M in N -}
letᶜ-β : (M N : Den Env) (ρ : ⟨ Env ⟩) → letᶜ M N · ρ ＝ seq · (M · ρ) · (N · ((M · ρ) • ρ))
letᶜ-β M N ρ = app-Λ (abs N · ρ) (M · ρ)

{- a function, applied -}
lamᶜ-β : (N : Den Env) (ρ : ⟨ Env ⟩) (d : ⟨ 𝔻 ⟩) → app · (lamᶜ N · ρ) · d ＝ seq · d · (N · (d • ρ))
lamᶜ-β N ρ d = app-Λ (abs N · ρ) d

{- the code of a closure, applied to an environment and an argument -}
code₂-β : (B : DCPO[ 𝔻 ×₁ 𝔻 , 𝔻 ]) (X Y : ⟨ 𝔻 ⟩)
  → app · (app · code₂ B · X) · Y ＝ seq · X · (seq · Y · (B · (X , Y)))
code₂-β B X Y =
 ap (λ - → app · - · Y) (app-Λ (∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 B) Λ) X)
 ∙ app-seq X (Λ · (curry₁ 𝔻 𝔻 𝔻 B · X)) Y
 ∙ ap (seq · X ·_) (app-Λ (curry₁ 𝔻 𝔻 𝔻 B · X) Y)

codeᶜ-β : (N : Den Env) (X Y : ⟨ 𝔻 ⟩) → app · (app · codeᶜ N · X) · Y ＝ seq · X · (seq · Y · (N · env₂ X Y))
codeᶜ-β N = code₂-β (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ N)

{- the code of a closure, applied to its environment -}
code₂-env : (B : DCPO[ 𝔻 ×₁ 𝔻 , 𝔻 ]) (X : ⟨ 𝔻 ⟩) → defined X → app · code₂ B · X ＝ Λ · (curry₁ 𝔻 𝔻 𝔻 B · X)
code₂-env B X p = app-Λ-defined (∘₁ 𝔻 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝔻 𝔻 𝔻 B) Λ) X p

{- a case on an injection -}
caseᶜ-inl : (L M N : Den Env) (ρ : ⟨ Env ⟩) (d : ⟨ 𝔻 ⟩) → L · ρ ＝ inl · d → defined d
  → caseᶜ L M N · ρ ＝ M · (d • ρ)
caseᶜ-inl L M N ρ d e p =
 ap (λ - → cases · - · (strict · (abs M · ρ) , strict · (abs N · ρ))) e
 ∙ cases-inl d p (strict · (abs M · ρ)) (strict · (abs N · ρ))
 ∙ strict-defined (abs M · ρ) d p

caseᶜ-inr : (L M N : Den Env) (ρ : ⟨ Env ⟩) (d : ⟨ 𝔻 ⟩) → L · ρ ＝ inr · d → defined d
  → caseᶜ L M N · ρ ＝ N · (d • ρ)
caseᶜ-inr L M N ρ d e p =
 ap (λ - → cases · - · (strict · (abs M · ρ) , strict · (abs N · ρ))) e
 ∙ cases-inr d p (strict · (abs M · ρ)) (strict · (abs N · ρ))
 ∙ strict-defined (abs N · ρ) d p

{- congruences for the binders: the bodies need agree only on defined
   values -}
lamᶜ-cong : (N N' : Den Env) (ρ ρ' : ⟨ Env ⟩) → ((d : ⟨ 𝔻 ⟩) → defined d → N · (d • ρ) ＝ N' · (d • ρ'))
  → lamᶜ N · ρ ＝ lamᶜ N' · ρ'
lamᶜ-cong N N' ρ ρ' h = Λ-cong (abs N · ρ) (abs N' · ρ') h

letᶜ-cong : (M M' N N' : Den Env) (ρ ρ' : ⟨ Env ⟩) → M · ρ ＝ M' · ρ'
  → ((d : ⟨ 𝔻 ⟩) → defined d → N · (d • ρ) ＝ N' · (d • ρ'))
  → letᶜ M N · ρ ＝ letᶜ M' N' · ρ'
letᶜ-cong M M' N N' ρ ρ' eM h = ap₂ (λ a b → app · a · b) (lamᶜ-cong N N' ρ ρ' h) eM

caseᶜ-cong : (L L' M M' N N' : Den Env) (ρ ρ' : ⟨ Env ⟩) → L · ρ ＝ L' · ρ'
  → ((d : ⟨ 𝔻 ⟩) → defined d → M · (d • ρ) ＝ M' · (d • ρ'))
  → ((d : ⟨ 𝔻 ⟩) → defined d → N · (d • ρ) ＝ N' · (d • ρ'))
  → caseᶜ L M N · ρ ＝ caseᶜ L' M' N' · ρ'
caseᶜ-cong L L' M M' N N' ρ ρ' eL hM hN =
 ap₂ (λ a b → cases · a · b) eL
   (ap₂ _,_ (strict-cong (abs M · ρ) (abs M' · ρ') hM) (strict-cong (abs N · ρ) (abs N' · ρ') hN))
