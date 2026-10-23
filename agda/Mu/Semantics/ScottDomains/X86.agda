{-

  The semantics of X86μ (Mu/Language/X86.agda) in Scott domains, as in
  the graph model (Mu/Semantics/GraphModel/X86.agda). What runs next (a
  continuation, Kont) is a continuous map of the machine state: the
  frame, the registers and the flag (𝕊). The frame is the environment,
  as in CFGμ: slot x is position idx x, and writing slot k forgets the
  slots after it (drop). A label means its block, under the meanings of
  the older blocks; a block starts with its frame, the registers unset
  and no flag.

  * A slot write binds its value as CFGμ's seq does: app (Λ F) D, F X
    running the rest with X in the slot. A register write is a
    substitution, and so is the flag's (cmpq).
  * Only callq can diverge (⊥), so only it writes its result strictly
    (seq C E, E provided that C is defined): it applies the code to
    %rdi and %rsi (as CFGμ's call) and puts the result in %rax.
  * An unset register, and an unset flag, hold init: typed code never
    reads them. After a call %rdi, %rsi and the flag are unset.
  * fold and unfold (↑, ↓) are the identity; case is a case on the
    slot, as CFGμ's case.
  * The code of a definition is Λ X. Λ Y. its body, with X in %rdi and Y
    in %rsi, in an empty frame; definitions are given meaning as in
    GlobalFunμ (tables).

-}

open import MLTT.Spartan using (𝓤₀; 𝓤₁; _̇; _,_; pr₁; pr₂)
open import UF.FunExt using (Fun-Ext)
open import UF.PropTrunc using (propositional-truncations-exist)
open import UF.Subsingletons using (propext)

open import Language.Prim using (sub; eq)
open import Mu.Language.Type
open import Mu.Language.X86
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Data.List using (List; length)
open import Framework.Membership using (_⊑_)

module Mu.Semantics.ScottDomains.X86
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import Framework.Scott.Domain pt fe pe using (𝔻)
open import Framework.Scott.Ops pt fe pe using (Env; ext; proj; car; cdr; seq; Λ)
  renaming (app to appᵈ; pair to pairᵈ; inl to inlᵈ; inr to inrᵈ)
open import Framework.Scott.Semantics pt fe pe hiding (litᶜ; op₁; op₂; Dens; nil; cons; tupleᶜ; casesᶜ; _∷ᶠ_)
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.ScottDomains.Ops pt fe pe
open import Mu.Semantics.ScottDomains.Imp pt fe pe using (𝒜)
open import Mu.Semantics.ScottDomains.CFG pt fe pe using (Meanings; drop)

{- the registers, and the machine state: frame, registers and flag -}
RegsD : DCPO₁
RegsD = Pow Reg 𝔻

𝕊 : DCPO₁
𝕊 = Env ×₁ (RegsD ×₁ 𝔻)

{- what runs next -}
Kont : 𝓤₁ ̇
Kont = Den 𝕊

open Over 𝕊

frameᶜ : DCPO[ 𝕊 , Env ]
frameᶜ = fst₁ Env (RegsD ×₁ 𝔻)

regsᶜ : DCPO[ 𝕊 , RegsD ]
regsᶜ = ∘₁ 𝕊 (RegsD ×₁ 𝔻) RegsD (snd₁ Env (RegsD ×₁ 𝔻)) (fst₁ RegsD 𝔻)

flagᶜ : Den 𝕊
flagᶜ = ∘₁ 𝕊 (RegsD ×₁ 𝔻) 𝔻 (snd₁ Env (RegsD ×₁ 𝔻)) (snd₁ RegsD 𝔻)

{- R [ r ≔ D ] -}
_[_≔_] : ⟨ RegsD ⟩ → Reg → ⟨ 𝔻 ⟩ → ⟨ RegsD ⟩
(R [ rax ≔ D ]) rax = D
(R [ rdi ≔ D ]) rdi = D
(R [ rsi ≔ D ]) rsi = D
(R [ rax ≔ D ]) rdi = R rdi
(R [ rax ≔ D ]) rsi = R rsi
(R [ rdi ≔ D ]) rax = R rax
(R [ rdi ≔ D ]) rsi = R rsi
(R [ rsi ≔ D ]) rax = R rax
(R [ rsi ≔ D ]) rdi = R rdi

updᶜ : Reg → DCPO[ RegsD ×₁ 𝔻 , RegsD ]
updᶜ r = f r , to-Pow-continuous Reg 𝔻 (RegsD ×₁ 𝔻) (f r) (c r)
 where
  f : Reg → ⟨ RegsD ×₁ 𝔻 ⟩ → Reg → ⟨ 𝔻 ⟩
  f r (R , D) = R [ r ≔ D ]
  old : (r' : Reg) → is-continuous (RegsD ×₁ 𝔻) 𝔻 (λ p → pr₁ p r')
  old r' = pr₂ (∘₁ (RegsD ×₁ 𝔻) RegsD 𝔻 (fst₁ RegsD 𝔻) (at Reg 𝔻 r'))
  new : is-continuous (RegsD ×₁ 𝔻) 𝔻 pr₂
  new = pr₂ (snd₁ RegsD 𝔻)
  c : (r r' : Reg) → is-continuous (RegsD ×₁ 𝔻) 𝔻 (λ p → f r p r')
  c rax rax = new
  c rdi rdi = new
  c rsi rsi = new
  c rax rdi = old rdi
  c rax rsi = old rsi
  c rdi rax = old rax
  c rdi rsi = old rsi
  c rsi rax = old rax
  c rsi rdi = old rdi

{- the state with register r set to D, and with the flag set to D -}
setR : Reg → Den 𝕊 → DCPO[ 𝕊 , 𝕊 ]
setR r D = pair₁ 𝕊 Env (RegsD ×₁ 𝔻) frameᶜ
             (pair₁ 𝕊 RegsD 𝔻 (∘₁ 𝕊 (RegsD ×₁ 𝔻) RegsD (pair₁ 𝕊 RegsD 𝔻 regsᶜ D) (updᶜ r)) flagᶜ)

setF : Den 𝕊 → DCPO[ 𝕊 , 𝕊 ]
setF D = pair₁ 𝕊 Env (RegsD ×₁ 𝔻) frameᶜ (pair₁ 𝕊 RegsD 𝔻 regsᶜ D)

{- the registers after a call that returns C, and at the start of a
   definition of environment X and argument Y -}
called-regs : ⟨ 𝔻 ⟩ → ⟨ RegsD ⟩
called-regs C rax = C
called-regs C rdi = init
called-regs C rsi = init

called-regsᶜ : DCPO[ 𝔻 , RegsD ]
called-regsᶜ = called-regs , to-Pow-continuous Reg 𝔻 𝔻 called-regs c
 where
  c : (r : Reg) → is-continuous 𝔻 𝔻 (λ C → called-regs C r)
  c rax = id-is-continuous 𝔻
  c rdi = constant-functions-are-continuous 𝔻 𝔻 {init}
  c rsi = constant-functions-are-continuous 𝔻 𝔻 {init}

args : ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ RegsD ⟩
args X Y rax = init
args X Y rdi = X
args X Y rsi = Y

argsᶜ : DCPO[ 𝔻 ×₁ 𝔻 , RegsD ]
argsᶜ = f , to-Pow-continuous Reg 𝔻 (𝔻 ×₁ 𝔻) f c
 where
  f : ⟨ 𝔻 ×₁ 𝔻 ⟩ → Reg → ⟨ 𝔻 ⟩
  f (X , Y) = args X Y
  c : (r : Reg) → is-continuous (𝔻 ×₁ 𝔻) 𝔻 (λ p → f p r)
  c rax = constant-functions-are-continuous (𝔻 ×₁ 𝔻) 𝔻 {init}
  c rdi = pr₂ (fst₁ 𝔻 𝔻)
  c rsi = pr₂ (snd₁ 𝔻 𝔻)

module _ {Σ : List DSig} (T : Table Σ) where

  𝒪 : ∀ {ψ τ} → Arg Σ ψ τ → Den 𝕊
  𝒪 (atom a) = ∘₁ 𝕊 Env 𝔻 frameᶜ (𝒜 a T)
  𝒪 (reg r _) = ∘₁ 𝕊 RegsD 𝔻 regsᶜ (at Reg 𝔻 r)
  𝒪 (a ↑) = 𝒪 a
  𝒪 (a ↓) = 𝒪 a

  𝒪s : ∀ {ψ Δ} → All (λ A → Arg Σ ψ (ty A)) Δ → Dens (length Δ)
  𝒪s [] = nil
  𝒪s (a ∷ as) = cons (𝒪 a) (𝒪s as)

  object : ∀ {ψ A} → Obj Σ ψ A → Den 𝕊
  object (pair c e) = op₂ pairᵈ (𝒪 c) (𝒪 e)
  object (tuple as) = tupleᶜ (𝒪s as)
  object (inl a) = op₁ inlᵈ (𝒪 a)
  object (inr a) = op₁ inrᵈ (𝒪 a)

  {- ((σ , R , F) , X) ↦ (X • drop p σ , R , F) -}
  next : ∀ {Δ' Δ : Ctx} → Δ' ⊑ Δ → DCPO[ 𝕊 ×₁ 𝔻 , 𝕊 ]
  next p = pair₁ (𝕊 ×₁ 𝔻) Env (RegsD ×₁ 𝔻)
             (∘₁ (𝕊 ×₁ 𝔻) (Env ×₁ 𝔻) Env
                (pair₁ (𝕊 ×₁ 𝔻) Env 𝔻 (∘₁ (𝕊 ×₁ 𝔻) Env Env (∘₁ (𝕊 ×₁ 𝔻) 𝕊 Env (fst₁ 𝕊 𝔻) frameᶜ) (drop p))
                   (snd₁ 𝕊 𝔻))
                ext)
             (∘₁ (𝕊 ×₁ 𝔻) 𝕊 (RegsD ×₁ 𝔻) (fst₁ 𝕊 𝔻) (snd₁ Env (RegsD ×₁ 𝔻)))

  {- d := D, then κ -}
  put : ∀ {n ψ τ ψ'} → Dst n ψ τ ψ' → Den 𝕊 → Kont → Kont
  put (reg r) D κ = ∘₁ 𝕊 𝕊 𝔻 (setR r D) κ
  put (slot p _) D κ = op₂ appᵈ (∘₁ 𝕊 (𝔻 ⟹₁ 𝔻) 𝔻 (curry₁ 𝕊 𝔻 𝔻 (∘₁ (𝕊 ×₁ 𝔻) 𝕊 𝔻 (next p) κ)) Λ) D

  ⟦_⟧ⁱ : ∀ {n ψ ψ'} → Instr Σ n ψ ψ' → Kont → Kont
  ⟦ movq a d ⟧ⁱ κ = put d (𝒪 a) κ
  ⟦ subq a r _ ⟧ⁱ κ = ∘₁ 𝕊 𝕊 𝔻 (setR r (op₂ (primD sub) (∘₁ 𝕊 RegsD 𝔻 regsᶜ (at Reg 𝔻 r)) (𝒪 a))) κ
  ⟦ cmpq a₂ a₁ ⟧ⁱ κ = ∘₁ 𝕊 𝕊 𝔻 (setF (op₂ (primD eq) (𝒪 a₁) (𝒪 a₂))) κ
  ⟦ sete d ⟧ⁱ κ = put d flagᶜ κ
  ⟦ alloc o d ⟧ⁱ κ = put d (object o) κ
  ⟦ load i a d ⟧ⁱ κ = put d (op₁ (proj (pos i)) (𝒪 a)) κ
  ⟦ loadfst x r ⟧ⁱ κ = ∘₁ 𝕊 𝕊 𝔻 (setR r (op₁ car (∘₁ 𝕊 Env 𝔻 frameᶜ (at _ 𝔻 (idx x))))) κ
  ⟦ loadsnd {x = opened x} r ⟧ⁱ κ = ∘₁ 𝕊 𝕊 𝔻 (setR r (op₁ cdr (∘₁ 𝕊 Env 𝔻 frameᶜ (at _ 𝔻 (idx x))))) κ
  ⟦ callq a _ _ ⟧ⁱ κ = op₂ seq (callᶜ a) (∘₁ 𝕊 𝕊 𝔻 (afterᶜ (callᶜ a)) κ)
   where
    {- the result of the call -}
    callᶜ : ∀ {ψ A B} → Arg Σ ψ (codeα A B) → Den 𝕊
    callᶜ a = op₂ appᵈ (op₂ appᵈ (𝒪 a) (∘₁ 𝕊 RegsD 𝔻 regsᶜ (at Reg 𝔻 rdi))) (∘₁ 𝕊 RegsD 𝔻 regsᶜ (at Reg 𝔻 rsi))
    {- the state after a call that returns C -}
    afterᶜ : Den 𝕊 → DCPO[ 𝕊 , 𝕊 ]
    afterᶜ C = pair₁ 𝕊 Env (RegsD ×₁ 𝔻) frameᶜ (pair₁ 𝕊 RegsD 𝔻 (∘₁ 𝕊 𝔻 RegsD C called-regsᶜ) (litᶜ init))

  ⟦_⟧ˢ : ∀ {n R' Bs ψ} → Seq Σ n R' Bs ψ → Meanings Bs → Kont
  ⟦ i ∷ k ⟧ˢ B = ⟦ i ⟧ⁱ (⟦ k ⟧ˢ B)
  ⟦ retq _ ⟧ˢ B = ∘₁ 𝕊 RegsD 𝔻 regsᶜ (at Reg 𝔻 rax)
  ⟦ jmp l ⟧ˢ B = ∘₁ 𝕊 Env 𝔻 frameᶜ (B l)
  ⟦ case x p _ l₁ l₂ ⟧ˢ B =
    casesᶜ (∘₁ 𝕊 Env 𝔻 frameᶜ (at _ 𝔻 (idx x)))
      (∘₁ 𝕊 Env (𝔻 ⟹₁ 𝔻) frameᶜ (∘₁ Env Env (𝔻 ⟹₁ 𝔻) (drop p) (abs (B l₁))))
      (∘₁ 𝕊 Env (𝔻 ⟹₁ 𝔻) frameᶜ (∘₁ Env Env (𝔻 ⟹₁ 𝔻) (drop p) (abs (B l₂))))

  {- a block starts with its frame, the registers unset and no flag -}
  startᶜ : DCPO[ Env , 𝕊 ]
  startᶜ = pair₁ Env Env (RegsD ×₁ 𝔻) (id₁ Env)
             (const₁ Env (RegsD ×₁ 𝔻) ((λ _ → init) , init))

  {- each block, from its frame, with the meanings of the older ones -}
  blocks : ∀ {n R' Bs} → Blocks Σ n R' Bs → Meanings Bs
  blocks (bs ▷ k) Z = ∘₁ Env 𝕊 𝔻 startᶜ (⟦ k ⟧ˢ (blocks bs))
  blocks (bs ▷ k) (S l) = blocks bs l

  run : ∀ {R' ψ} → Body Σ R' ψ → Kont
  run (body n bs k) = ⟦ k ⟧ˢ (blocks bs)

{- the code of a definition: its body with %rdi and %rsi set, in an
   empty frame -}
codeₜ : ∀ {Σ} → Table Σ → ∀ {s} → Body Σ (DSig.cod s) (called s) → ⟨ 𝔻 ⟩
codeₜ T b = code₂ (∘₁ (𝔻 ×₁ 𝔻) 𝕊 𝔻
                     (pair₁ (𝔻 ×₁ 𝔻) Env (RegsD ×₁ 𝔻) (const₁ (𝔻 ×₁ 𝔻) Env (λ _ → init))
                        (pair₁ (𝔻 ×₁ 𝔻) RegsD 𝔻 argsᶜ (const₁ (𝔻 ×₁ 𝔻) 𝔻 init)))
                     (run T b))

{- the meaning of a whole program: the value of main -}
⟦_⟧ₜ : ∀ {A} → Program A → ⟨ 𝔻 ⟩
⟦ program ds b ⟧ₜ = run (tables codeₜ ds) b · ((λ _ → init) , ((λ _ → init) , init))
