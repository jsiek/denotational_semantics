{-

  The semantics of Impμ (Mu/Language/Imp.agda) in Scott domains, in
  continuation-passing style, as in the graph model
  (Mu/Semantics/GraphModel/Imp.agda). The frame σ gives each slot a meaning;
  a continuation κ (a continuous map, in K = 𝔻 ⟹ 𝔻) takes the value of
  the expression. An expression means a continuous map of the frame and
  the continuation. Atoms and simple expressions (𝒜, 𝒮, shared with
  CFGμ) are the operators of GlobalFunμ on atoms; fold and unfold are the
  identity.

  x := e₁; e₂ runs e₁ with the continuation that is strict in its value
  D like let in GlobalFunμ: app (Λ F) D, where F X runs e₂ with X in the
  next slot and then κ; case is a case, each branch running with κ. The
  code of a definition runs its body in a frame with its argument and
  environment, with the continuation that returns the value.

-}

open import MLTT.Spartan using (𝓤₀; 𝓤₁; _̇)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Mu.Language.Type
open import Mu.Language.Imp
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; length)

module Mu.Semantics.ScottDomains.Imp
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (Env; ext; const; proj; car; cdr; Λ; strict) renaming (pair to pairᵈ)
  renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ)
open import Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.ScottDomains.Ops pt fe pe

𝒜 : ∀ {Σ Δ A} → Atm Σ Δ A → Table Σ → Den Env
𝒜 (var x) T = at _ 𝔻 (idx x)
𝒜 (lit B c) T = litᶜ (const B c)
𝒜 (ref f) T = litᶜ (T f)

𝒜s : ∀ {Σ Δ Δs} → All (Atm Σ Δ) Δs → Table Σ → Dens (length Δs)
𝒜s [] T = nil
𝒜s (a ∷ as) T = cons (𝒜 a T) (𝒜s as T)

𝒮 : ∀ {Σ Δ A} → Simple Σ Δ A → Table Σ → Den Env
𝒮 (atm a) T = 𝒜 a T
𝒮 (pair a b) T = op₂ pairᵈ (𝒜 a T) (𝒜 b T)
𝒮 (callc f a) T = op₂ appᵈ (op₂ appᵈ (op₁ car (𝒜 f T)) (op₁ cdr (𝒜 f T))) (𝒜 a T)
𝒮 (tuple as) T = tupleᶜ (𝒜s as T)
𝒮 (get i a) T = op₁ (proj (pos i)) (𝒜 a T)
𝒮 (inl a) T = op₁ inlᵈ (𝒜 a T)
𝒮 (inr a) T = op₁ inrᵈ (𝒜 a T)
𝒮 (prim p a b) T = op₂ (primD p) (𝒜 a T) (𝒜 b T)
𝒮 (fold a) T = 𝒜 a T
𝒮 (unfold a) T = 𝒜 a T

{- Continuations -----------------------------------------------------------------}

K : DCPO₁
K = 𝔻 ⟹₁ 𝔻

{- the meaning of an expression: a continuous map of the frame and the
   continuation -}
DenK : 𝓤₁ ̇
DenK = DCPO[ Env , K ⟹₁ 𝔻 ]

{- uncurried: (σ , κ) ↦ e σ κ -}
uncurryK : DenK → DCPO[ Env ×₁ K , 𝔻 ]
uncurryK e = ∘₁ (Env ×₁ K) ((K ⟹₁ 𝔻) ×₁ K) 𝔻
               (pair₁ (Env ×₁ K) (K ⟹₁ 𝔻) K (∘₁ (Env ×₁ K) Env (K ⟹₁ 𝔻) (fst₁ Env K) e) (snd₁ Env K))
               (eval₁ K 𝔻)

{- (σ , κ) ↦ λ X. e (X • σ) κ, a branch under one binder -}
underK : DenK → DCPO[ Env ×₁ K , 𝔻 ⟹₁ 𝔻 ]
underK e = curry₁ (Env ×₁ K) 𝔻 𝔻
             (∘₁ ((Env ×₁ K) ×₁ 𝔻) (Env ×₁ K) 𝔻
                (pair₁ ((Env ×₁ K) ×₁ 𝔻) Env K
                   (∘₁ ((Env ×₁ K) ×₁ 𝔻) (Env ×₁ 𝔻) Env
                      (pair₁ ((Env ×₁ K) ×₁ 𝔻) Env 𝔻
                         (∘₁ ((Env ×₁ K) ×₁ 𝔻) (Env ×₁ K) Env (fst₁ (Env ×₁ K) 𝔻) (fst₁ Env K))
                         (snd₁ (Env ×₁ K) 𝔻))
                      ext)
                   (∘₁ ((Env ×₁ K) ×₁ 𝔻) (Env ×₁ K) K (fst₁ (Env ×₁ K) 𝔻) (snd₁ Env K)))
                (uncurryK e))

⟦_⟧ᴷ : ∀ {Σ Δ A} → Exp Σ Δ A → Table Σ → DenK
⟦ simple s ⟧ᴷ T =
  curry₁ Env K 𝔻 (∘₁ (Env ×₁ K) (K ×₁ 𝔻) 𝔻
    (pair₁ (Env ×₁ K) K 𝔻 (snd₁ Env K) (∘₁ (Env ×₁ K) Env 𝔻 (fst₁ Env K) (𝒮 s T)))
    (eval₁ 𝔻 𝔻))
⟦ assign e₁ e₂ ⟧ᴷ T =
  curry₁ Env K 𝔻 (∘₁ (Env ×₁ K) ((K ⟹₁ 𝔻) ×₁ K) 𝔻
    (pair₁ (Env ×₁ K) (K ⟹₁ 𝔻) K (∘₁ (Env ×₁ K) Env (K ⟹₁ 𝔻) (fst₁ Env K) (⟦ e₁ ⟧ᴷ T))
       (∘₁ (Env ×₁ K) (𝔻 ⟹₁ 𝔻) K (underK (⟦ e₂ ⟧ᴷ T)) (∘₁ (𝔻 ⟹₁ 𝔻) 𝔻 (𝔻 ⟹₁ 𝔻) Λ appᵈ)))
    (eval₁ K 𝔻))
⟦ case a e₁ e₂ ⟧ᴷ T =
  curry₁ Env K 𝔻 (Over.casesᶜ (Env ×₁ K) (∘₁ (Env ×₁ K) Env 𝔻 (fst₁ Env K) (𝒜 a T))
                    (underK (⟦ e₁ ⟧ᴷ T)) (underK (⟦ e₂ ⟧ᴷ T)))

{- the identity continuation -}
idK : ⟨ K ⟩
idK = id₁ 𝔻

{- the function whose body is e, given the table T -}
code′ : ∀ {Σ} → Table Σ → ∀ {s} → Exp Σ (Args s) (DSig.cod s) → ⟨ 𝔻 ⟩
code′ T e = codeᶜ (∘₁ Env (K ⟹₁ 𝔻) 𝔻 (⟦ e ⟧ᴷ T) (at-point₁ K 𝔻 idK))

table : ∀ {Σ} → All (λ s → Exp Σ (Args s) (DSig.cod s)) Σ → Table Σ
table = tables code′

{- the meaning of a whole program: the value of main -}
⟦_⟧ₚ : ∀ {A} → Program A → ⟨ 𝔻 ⟩
⟦ program ds e ⟧ₚ = ⟦ e ⟧ᴷ (table ds) · (λ _ → init) · idK
