module Delay where

open import Data.List using (List; []; _∷_; _++_; length; replicate)

open import Primitives
open import ISWIMAnnot
open import ClosLang
open import Sig
open import GraphModel
open import ModelISWIM

delay : ISWIMAnn → Clos
delay-arg : ∀{b} → Arg b → Argᵪ b
delay-args : ∀{bs} → Args bs → Argsᵪ bs

delay (` x) = % x
delay (ƛ n (cons N fvs)) =
  〔 fun ⦑ consᵪ (delay-arg N) nilᵪ ⦒ , tuple n ⦑ delay-args fvs ⦒  〕
delay (L · M) =
  ((delay L ❲ 0 ❳) ▫ (delay L ❲ 1 ❳)) ▫ delay M
delay (papp p k ⦅ args ⦆) = papp p k ⦑ delay-args args ⦒

delay-arg {■} (ast M) = astᵪ (delay M)
delay-arg {ν b} (bind arg) = bindᵪ (delay-arg {b} arg)
delay-arg {∁ b} (clear arg) = clearᵪ (delay-arg {b} arg)

delay-args {[]} nil = nilᵪ
delay-args {b ∷ bs} (cons arg args) = consᵪ (delay-arg arg) (delay-args args)

data _≈_ : (𝒫 Value) → (𝒫 Value) → Set where
   ≈-refl : ∀ D → D ≈ D

≈-env : (Var → 𝒫 Value) → (Var → 𝒫 Value) → Set
≈-env ρ ρ′ = ∀ x → ρ x ≈ ρ′ x

delay-correct : ∀ {M : ISWIMAnn} {ρ ρ′ : Var → 𝒫 Value}
  → ≈-env ρ ρ′
  → (ℐ⟦ M ⟧ ρ) ≈ (𝒞⟦ delay M ⟧ ρ′)
delay-correct {` x}{ρ}{ρ′} ρ≈ρ′ = ρ≈ρ′ x
delay-correct {ƛ n N}{ρ}{ρ′} ρ≈ρ′ = {!!}
delay-correct {L · M}{ρ}{ρ′} ρ≈ρ′ = {!!}
{-

IH:
   (ℐ⟦ L ⟧ ρ) ≈ (𝒞⟦ delay L ⟧ ρ′)
   (ℐ⟦ M ⟧ ρ) ≈ (𝒞⟦ delay M ⟧ ρ′)

Goal: ℐ⟦ L · M ⟧ ρ ≈
      𝒞⟦ ((delay L ❲ 0 ❳) ▫ (delay L ❲ 1 ❳)) ▫ delay M ⟧ ρ′

  ℐ⟦ L · M ⟧ ρ
≡ 𝐹 (ℐ⟦ L ⟧ ρ) (ℐ⟦ M ⟧ ρ)




-}
delay-correct {papp p k ⦅ args ⦆}{ρ}{ρ′} ρ≈ρ′ = {!!}
