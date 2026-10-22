{-

  Correctness of select instructions (CFGμ → X86μ,
  Mu/Compiler/Select.agda) in Scott domains
  (Mu/Semantics/Scott/{CFG,X86}.agda), as in the graph model
  (Mu/proof/Correctness/Graph/SelectCorrect.agda), with equality of
  values in place of equality of sets.

  The X86μ frame is the CFGμ frame, a slot write binds as CFGμ's seq
  does, and a register write is a substitution, so the code selected
  for a simple expression means it, definitionally, up to the tables
  (sel-＝): callq applies the code and environment that load fst and
  load snd read from the closure's slot, as CFGμ's call does, and callq
  writes strictly, which changes nothing before a return or a bind
  (then-seq: seq d d = d, and app (Λ K) d is strict in d). X86μ's case
  is CFGμ's. What is left is the start of a definition, which binds
  %rdi and %rsi to slots 0 and 1, where CFGμ has them in its frame: the
  environment and the argument of a function value are defined, so
  these binds are β-reductions (movq-slot, start₁₋₃; the graph model's
  fin-β and monotonicity are not needed).

  Checking speed shapes the proof: Agda compares two meanings that are
  equal but not syntactically so by reducing both, which is very slow
  for nested applications. So the result of callq and the function
  values of the start are found by Agda (Σ-types proved by refl, at the
  top level rather than in where blocks), the start of a definition is
  opaque (db, related to the X86μ code by an equation on syntax), and
  the meanings compared are named (runAt, kAt) or taken from one module
  (𝒜, 𝒮 from BackEndLemmas).

-}

open import MLTT.Spartan hiding (inl; inr; cases)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Language.Prim using (sub; eq)
open import Framework.Membership using (_⊑_; here⊑)
open import Mu.Language.Type
import Mu.Language.Imp as I
import Mu.Language.CFG as C
open C using (DSig; Args; Tail; return; goto; _▷_)
open import Mu.Language.X86 using () renaming (Body to X86Body)
import Mu.Language.X86 as X86b
open import Mu.Language.X86 using (Seq; Atm; var; rax; rdi; rsi; St; st; rt; called; _[_↦_]; ℤty; returned; Arg; atom; reg; ty; retq; _∷_; _↑; _↓;
  movq; slot; pair; tuple; inl; inr)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to All-map)
open import Mu.Compiler.Select using (Out; ret; to; after; dst; sel; tail; atms; depth; depth-≥; blocks-depth; def-body; select)
  renaming (blocks to sel-blocks)
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; _≤_; _<_; s≤s; z≤n) renaming (_⊔_ to _⊔ₙ_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Bool using (Bool; false; true)
import Relation.Binary.PropositionalEquality as Eq

module Mu.proof.Correctness.Scott.SelectCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.Scott.Ops pt fe pe
import Mu.Semantics.Scott.CFG pt fe pe as CS
open CS using (⟦_⟧ᵗ; Meanings; drop)
import Mu.Semantics.Scott.X86 pt fe pe as X86
open X86 using (𝕊; RegsD; _[_≔_])
open import Mu.proof.Semantics.Scott.BackEndLemmas pt fe pe using (seq-self; seq-seq; code₂-cong; tables-cons; 𝒮-＝; 𝒜; 𝒜s; 𝒮)

module O𝕊 = Over 𝕊

{- d := D, then K, in CFGμ -}
then : ∀ {n Δ A Δ''} → Out n Δ A Δ'' → DCPO[ 𝔻 , 𝔻 ] → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
then ret K D = D
then (to p _) K D = appᵈ · (Λ · K) · D

{- a strict write changes nothing before a return or a bind -}
then-seq : ∀ {n Δ A Δ''} (o : Out n Δ A Δ'') (K : DCPO[ 𝔻 , 𝔻 ]) (D : ⟨ 𝔻 ⟩) → seq · D · then o K D ＝ then o K D
then-seq ret K D = seq-self D
then-seq (to p _) K D = ap (seq · D ·_) (app-Λ K D) ∙ seq-seq D (K · D) ∙ (app-Λ K D) ⁻¹

{- X86μ code started with the environment X and argument Y in %rdi and
   %rsi, and k run from the frame Y • X; named, so that Agda compares
   them by their arguments -}
runAt : ∀ {Σ R' ψ} → Table Σ → X86Body Σ R' ψ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
runAt T' b X Y = X86.run T' b · ((λ _ → init) , (X86.args X Y , init))

kAt : ∀ {Σ n R' Bs ψ} → Table Σ → Seq Σ n R' Bs ψ → X86b.Blocks Σ n R' Bs → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
kAt T' k bs' X Y = X86.⟦_⟧ˢ T' k (X86.blocks T' bs') · (env₂ X Y , (X86.args X Y , init))

{- the code of a definition, given what its body means -}
codeₜ-cong : ∀ {Σ} (T T' : Table Σ) {s} (b₀ : C.Body Σ (DSig.cod s) (Args s)) (b : X86Body Σ (DSig.cod s) (called s))
  → ((X Y : ⟨ 𝔻 ⟩) → defined X → defined Y → CS.run b₀ T · env₂ X Y ＝ runAt T' b X Y)
  → CS.code′ T b₀ ＝ X86.codeₜ T' b
codeₜ-cong T T' b₀ b h =
  code₂-cong (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻 env₂ᶜ (CS.run b₀ T))
    (∘₁ (𝔻 ×₁ 𝔻) 𝕊 𝔻
       (pair₁ (𝔻 ×₁ 𝔻) Env (RegsD ×₁ 𝔻) (const₁ (𝔻 ×₁ 𝔻) Env (λ _ → init))
          (pair₁ (𝔻 ×₁ 𝔻) RegsD 𝔻 X86.argsᶜ (const₁ (𝔻 ×₁ 𝔻) 𝔻 init)))
       (X86.run T' b))
    h

{- the start of the code of a definition: %rdi and %rsi to slots 1 and 0, then k -}
startSeq : ∀ {Σ n Bs} (s : DSig) (k : Seq Σ n (DSig.cod s) Bs (st (St.rs (called s)) (Args s) nothing false))
  .(l₁ : 0 < n) .(l₂ : 1 < n) → Seq Σ n (DSig.cod s) Bs (called s)
startSeq s k l₁ l₂ = movq (reg rdi Eq.refl) (slot here⊑ l₁) ∷ movq (reg rsi Eq.refl) (slot here⊑ l₂) ∷ k

{- the start of a definition, opaque (Agda unfolds it, to no end, when
   it compares the meanings of code that mentions it) -}
opaque
  db : ∀ {Σ s} → C.Body Σ (DSig.cod s) (Args s) → X86Body Σ (DSig.cod s) (called s)
  db = def-body

opaque
  unfolding db

  {- (on syntax: only the irrelevant proofs differ) -}
  db-body : ∀ {Σ s Bs} (bs : C.Blocks Σ (DSig.cod s) Bs) (t : Tail Σ (DSig.cod s) Bs (Args s))
    → db {s = s} (C.body bs t)
      Eq.≡ X86b.body (blocks-depth bs ⊔ₙ depth t) (sel-blocks bs (m≤m⊔n (blocks-depth bs) (depth t)))
             (startSeq s (tail t (m≤n⊔m (blocks-depth bs) (depth t)) {St.rs (called s)} {nothing} {false})
                (≤-trans (s≤s z≤n) (≤-trans (depth-≥ t) (m≤n⊔m (blocks-depth bs) (depth t))))
                (≤-trans (depth-≥ t) (m≤n⊔m (blocks-depth bs) (depth t))))
  db-body bs t = Eq.refl

  map-db : ∀ {Σ ss} (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) ss) → All-map db ds Eq.≡ All-map def-body ds
  map-db ds = Eq.refl

≡→＝ : ∀ {A : Set} {x y : A} → x Eq.≡ y → x ＝ y
≡→＝ Eq.refl = refl

{- for tables T (of CFGμ) and T' (of X86μ) that agree -}
module _ {Σ : List DSig} (T T' : Table Σ) (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) where

  𝒪s-atms : ∀ {Δ Δs Γ O F} (as : All (Atm Σ Δ) Δs) (ρ : ⟨ Env ⟩) (r : ⟨ RegsD ×₁ 𝔻 ⟩)
    → 𝒜s as T' · ρ ＝ X86.𝒪s T' (atms {Γ = Γ} {O} {F} as) · (ρ , r)
  𝒪s-atms [] ρ r = dfunext fe (λ ())
  𝒪s-atms (a ∷ as) ρ r = dfunext fe λ { zero → refl ; (suc i) → happly (𝒪s-atms as ρ r) i }

  {- a write of a defined value to a slot is a β -}
  movq-slot : ∀ {n R' Bs Γ Δ Δ' O F A} (a : Arg Σ (st Γ Δ O F) (ty A)) (p : Δ' ⊑ Δ) .(le : length Δ' < n)
    (k : Seq Σ n R' Bs (st Γ (A ∷ Δ') nothing F)) (B' : Meanings Bs) (s : ⟨ 𝕊 ⟩) → defined (X86.𝒪 T' a · s)
    → X86.⟦_⟧ˢ T' (movq a (slot p le) ∷ k) B' · s ＝ X86.⟦_⟧ˢ T' k B' · (X86.next T' p · (s , X86.𝒪 T' a · s))
  movq-slot a p le k B' s d =
    app-Λ-defined (curry₁ 𝕊 𝔻 𝔻 (∘₁ (𝕊 ×₁ 𝔻) 𝕊 𝔻 (X86.next T' p) (X86.⟦_⟧ˢ T' k B')) · s) (X86.𝒪 T' a · s) d

  run-body : ∀ {n R' Bs ψ} (bs' : X86b.Blocks Σ n R' Bs) (k : Seq Σ n R' Bs ψ) (s₀ : ⟨ 𝕊 ⟩)
    → X86.run T' (X86b.body n bs' k) · s₀ ＝ X86.⟦_⟧ˢ T' k (X86.blocks T' bs') · s₀
  run-body bs' k s₀ = refl

  {- the start of a definition binds %rdi and %rsi to slots 1 and 0:
     two applications of function values (Agda finds them) -}
  start₁ : ∀ {n Bs} (s : DSig) (bs' : X86b.Blocks Σ n (DSig.cod s) Bs)
    (k : Seq Σ n (DSig.cod s) Bs (st (St.rs (called s)) (Args s) nothing false))
    .(l₁ : 0 < n) .(l₂ : 1 < n) (X Y : ⟨ 𝔻 ⟩)
    → Σ G ꞉ DCPO[ 𝔻 , 𝔻 ] , runAt T' (X86b.body n bs' (startSeq s k l₁ l₂)) X Y ＝ appᵈ · (Λ · G) · X
  start₁ s bs' k l₁ l₂ X Y = _ , refl

  start₂ : ∀ {n Bs} (s : DSig) (bs' : X86b.Blocks Σ n (DSig.cod s) Bs)
    (k : Seq Σ n (DSig.cod s) Bs (st (St.rs (called s)) (Args s) nothing false))
    .(l₁ : 0 < n) .(l₂ : 1 < n) (X Y : ⟨ 𝔻 ⟩)
    → Σ G ꞉ DCPO[ 𝔻 , 𝔻 ] , pr₁ (start₁ s bs' k l₁ l₂ X Y) · X ＝ appᵈ · (Λ · G) · Y
  start₂ s bs' k l₁ l₂ X Y = _ , refl

  start₃ : ∀ {n Bs} (s : DSig) (bs' : X86b.Blocks Σ n (DSig.cod s) Bs)
    (k : Seq Σ n (DSig.cod s) Bs (st (St.rs (called s)) (Args s) nothing false))
    .(l₁ : 0 < n) .(l₂ : 1 < n) (X Y : ⟨ 𝔻 ⟩)
    → pr₁ (start₂ s bs' k l₁ l₂ X Y) · Y ＝ kAt T' k bs' X Y
  start₃ s bs' k l₁ l₂ X Y = refl

  run-start : ∀ {n Bs} (s : DSig) (bs' : X86b.Blocks Σ n (DSig.cod s) Bs)
    (k : Seq Σ n (DSig.cod s) Bs (st (St.rs (called s)) (Args s) nothing false))
    .(l₁ : 0 < n) .(l₂ : 1 < n) (X Y : ⟨ 𝔻 ⟩) → defined X → defined Y
    → runAt T' (X86b.body n bs' (startSeq s k l₁ l₂)) X Y ＝ kAt T' k bs' X Y
  run-start s bs' k l₁ l₂ X Y dX dY =
    pr₂ (start₁ s bs' k l₁ l₂ X Y)
    ∙ app-Λ-defined (pr₁ (start₁ s bs' k l₁ l₂ X Y)) X dX
    ∙ pr₂ (start₂ s bs' k l₁ l₂ X Y)
    ∙ app-Λ-defined (pr₁ (start₂ s bs' k l₁ l₂ X Y)) Y dY
    ∙ start₃ s bs' k l₁ l₂ X Y

  {- ... for a body that is that start (an equation on syntax) -}
  run-start′ : ∀ {n Bs} (s : DSig) (b' : X86Body Σ (DSig.cod s) (called s)) (bs' : X86b.Blocks Σ n (DSig.cod s) Bs)
    (k : Seq Σ n (DSig.cod s) Bs (st (St.rs (called s)) (Args s) nothing false))
    .(l₁ : 0 < n) .(l₂ : 1 < n) → b' Eq.≡ X86b.body n bs' (startSeq s k l₁ l₂)
    → (X Y : ⟨ 𝔻 ⟩) → defined X → defined Y → runAt T' b' X Y ＝ kAt T' k bs' X Y
  run-start′ s .(X86b.body _ bs' (startSeq s k l₁ l₂)) bs' k l₁ l₂ Eq.refl = run-start s bs' k l₁ l₂

  module _ {n R' Bs} (B' : Meanings Bs) where

    {- what k means, after the value of s is in o -}
    Fits : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') → DCPO[ 𝔻 , 𝔻 ] → (∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)) → ⟨ Env ⟩ → 𝓤₁ ̇
    Fits ret K k ρ = ∀ {Γ O F} ρ' R F' → R rax ＝ X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' · (ρ' , (R , F'))
    Fits (to p _) K k ρ = ∀ {Γ O F} X → defined X → ∀ R F'
      → K · X ＝ X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' · (X • (drop p · ρ) , (R , F'))

    put-＝ : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') (K : DCPO[ 𝔻 , 𝔻 ]) (k : ∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F))
      (ρ : ⟨ Env ⟩) (D : ⟨ 𝔻 ⟩) (D' : Den 𝕊) {Γ O F} (R : ⟨ RegsD ⟩) (F' : ⟨ 𝔻 ⟩)
      → Fits o K k ρ → D ＝ D' · (ρ , (R , F'))
      → then o K D ＝ X86.put T' (dst o {Γ} {O} {F}) D' (X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B') · (ρ , (R , F'))
    put-＝ ret K k ρ D D' R F' f e = e ∙ f ρ (R [ rax ≔ D' · (ρ , (R , F')) ]) F'
    put-＝ (to p _) K k ρ D D' {Γ} {O} {F} R F' f e =
      ap (appᵈ · (Λ · K) ·_) e
      ∙ ap (λ G → appᵈ · G · (D' · (ρ , (R , F')))) (Λ-cong K G (λ X d → f {Γ} {O} {F} X d R F'))
     where
      G : DCPO[ 𝔻 , 𝔻 ]
      G = curry₁ 𝕊 𝔻 𝔻 (∘₁ (𝕊 ×₁ 𝔻) 𝕊 𝔻 (X86.next T' p) (X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B')) · (ρ , (R , F'))

    {- the code selected for a call: Agda finds the result C of callq and
       the state after it (in a module, not a where block, so that its
       metas are solved once and for all) -}
    module Callc {Δ A' B Δ''} (x : Δ ∋ A' ⇒ B) (a : I.Atm Σ Δ A') (o : Out n Δ B Δ'')
                 (k : ∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)) (ρ : ⟨ Env ⟩)
                 {Γ : X86b.Regs} {O : Maybe (X86b.Open Δ)} {F : Bool} (R : ⟨ RegsD ⟩) (F' : ⟨ 𝔻 ⟩) where

      k₅ : Seq Σ n R' Bs (returned Δ B)
      k₅ = movq (reg rax Eq.refl) (dst o {rt (just (ty B)) nothing nothing} {nothing} {false})
           ∷ k {rt (just (ty B)) nothing nothing} {nothing} {false}

      g : Σ C ꞉ ⟨ 𝔻 ⟩ , Σ st' ꞉ ⟨ 𝕊 ⟩ , X86.⟦_⟧ˢ T' (sel (I.callc (var x) a) o k {Γ} {O} {F}) B' · (ρ , (R , F'))
                                         ＝ seq · C · (X86.⟦_⟧ˢ T' k₅ B' · st')
      g = _ , _ , refl

      {- C is what CFGμ's call computes (by computation; slow-ish) -}
      eC : 𝒮 (I.callc (var x) a) T' · ρ ＝ pr₁ g
      eC = refl

      {- the state after the call -}
      after-call : X86.put T' (dst o {rt (just (ty B)) nothing nothing} {nothing} {false}) (X86.𝒪 T' {returned Δ B} (reg rax Eq.refl))
                     (X86.⟦_⟧ˢ T' (k {rt (just (ty B)) nothing nothing} {nothing} {false}) B')
                     · (ρ , (X86.called-regs (pr₁ g) , init))
                   ＝ X86.⟦_⟧ˢ T' k₅ B' · pr₁ (pr₂ g)
      after-call = refl

      chain : (K : DCPO[ 𝔻 , 𝔻 ]) → Fits o K k ρ
        → then o K (𝒮 (I.callc (var x) a) T · ρ) ＝ X86.⟦_⟧ˢ T' (sel (I.callc (var x) a) o k {Γ} {O} {F}) B' · (ρ , (R , F'))
      chain K f =
        ap (then o K) (𝒮-＝ T T' TT (I.callc (var x) a) ρ ∙ eC)
        ∙ (then-seq o K (pr₁ g)) ⁻¹
        ∙ ap (seq · pr₁ g ·_) (put-＝ o K k ρ (pr₁ g) (X86.𝒪 T' {returned Δ B} (reg rax Eq.refl))
                                 {rt (just (ty B)) nothing nothing} {nothing} {false} (X86.called-regs (pr₁ g)) init f refl
                               ∙ after-call)
        ∙ (pr₂ (pr₂ g)) ⁻¹

    {- the code selected for s into o, then k -}
    sel-＝ : ∀ {Δ A Δ''} (s : I.Simple Σ Δ A) (o : Out n Δ A Δ'') (K : DCPO[ 𝔻 , 𝔻 ])
      (k : ∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)) (ρ : ⟨ Env ⟩) {Γ O F} (R : ⟨ RegsD ⟩) (F' : ⟨ 𝔻 ⟩)
      → Fits o K k ρ → then o K (𝒮 s T · ρ) ＝ X86.⟦_⟧ˢ T' (sel s o k {Γ} {O} {F}) B' · (ρ , (R , F'))
    sel-＝ s@(I.atm a) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) (X86.𝒪 T' {st Γ _ O F} (atom a)) R F' f (𝒮-＝ T T' TT s ρ)
    sel-＝ s@(I.pack c e) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) (X86.object T' {st Γ _ O F} (pair (atom c) (atom e))) R F' f (𝒮-＝ T T' TT s ρ)
    sel-＝ s@(I.callc (var x) a) o K k ρ {Γ} {O} {F} R F' f = Callc.chain x a o k ρ {Γ} {O} {F} R F' K f
    sel-＝ s@(I.tuple {Δs} as) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) (X86.object T' {st Γ _ O F} (tuple (atms as))) R F' f
        (𝒮-＝ T T' TT s ρ ∙ ap (tupleᵈ (length Δs) ·_) (𝒪s-atms {Γ = Γ} {O} {F} as ρ (R , F')))
    sel-＝ s@(I.get j a) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) (O𝕊.op₁ (proj (pos j)) (X86.𝒪 T' {st Γ _ O F} (atom a))) R F' f (𝒮-＝ T T' TT s ρ)
    sel-＝ s@(I.inl {B = B} a) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) (X86.object T' {st Γ _ O F} (inl {B = B} (atom a))) R F' f (𝒮-＝ T T' TT s ρ)
    sel-＝ s@(I.inr {A = A} a) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) (X86.object T' {st Γ _ O F} (inr {A = A} (atom a))) R F' f (𝒮-＝ T T' TT s ρ)
    sel-＝ s@(I.prim sub a b) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) (X86.𝒪 T' {st Γ' _ O F} (reg rax Eq.refl)) {Γ'} {O} {F}
        ((R [ rax ≔ 𝒜 a T' · ρ ]) [ rax ≔ 𝒮 s T' · ρ ]) F' f (𝒮-＝ T T' TT s ρ)
     where Γ' = _[_↦_] (_[_↦_] Γ rax (just ℤty)) rax (just ℤty)
    sel-＝ s@(I.prim eq a b) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) X86.flagᶜ {Γ} {O} {true} R (𝒮 s T' · ρ) f (𝒮-＝ T T' TT s ρ)
    sel-＝ s@(I.fold {A = A₀} a) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) (X86.𝒪 T' {st Γ _ O F} (_↑ {A = A₀} (atom a))) R F' f (𝒮-＝ T T' TT s ρ)
    sel-＝ s@(I.unfold {A = A₀} a) o K k ρ {Γ} {O} {F} R F' f =
      put-＝ o K k ρ (𝒮 s T · ρ) (X86.𝒪 T' {st Γ _ O F} (_↓ {A = A₀} (atom a))) R F' f (𝒮-＝ T T' TT s ρ)

  {- the blocks B (of CFGμ) and B' (of X86μ) agree -}
  BR : ∀ {Bs} → Meanings Bs → Meanings Bs → 𝓤₁ ̇
  BR {Bs} B B' = ∀ {Δ} (l : Bs ∋ Δ) ρ → B l · ρ ＝ B' l · ρ

  tail-＝ : ∀ {n R' Bs Δ} (t : Tail Σ R' Bs Δ) .(le : depth t ≤ n) (B B' : Meanings Bs) → BR B B' → ∀ ρ
    → ∀ {Γ O F} R F' → ⟦ t ⟧ᵗ T B · ρ ＝ X86.⟦_⟧ˢ T' (tail t le {Γ} {O} {F}) B' · (ρ , (R , F'))
  tail-＝ (return s) le B B' br ρ R F' = sel-＝ B' s ret (id₁ 𝔻) (retq Eq.refl) ρ R F' (λ ρ' R F' → refl)
  tail-＝ (C.seq p s t) le B B' br ρ R F' =
    sel-＝ B' s (to p _) (abs (⟦ t ⟧ᵗ T B) · (drop p · ρ)) (tail t _) ρ R F'
      (λ X _ R F → tail-＝ t _ B B' br (X • (drop p · ρ)) R F)
  tail-＝ (goto l) le B B' br ρ R F' = br l ρ
  tail-＝ (C.case (var x) p l₁ l₂) le B B' br ρ R F' =
    ap (λ y → cases · ρ (idx x) · y)
      (ap₂ _,_ (ap (strict ·_) (to-continuous-function-＝ 𝔻 𝔻 {abs (B l₁) · (drop p · ρ)} {abs (B' l₁) · (drop p · ρ)}
                                  (λ X → br l₁ (X • (drop p · ρ)))))
               (ap (strict ·_) (to-continuous-function-＝ 𝔻 𝔻 {abs (B l₂) · (drop p · ρ)} {abs (B' l₂) · (drop p · ρ)}
                                  (λ X → br l₂ (X • (drop p · ρ))))))

  blocks-＝ : ∀ {n R' Bs} (bs : C.Blocks Σ R' Bs) .(le : blocks-depth bs ≤ n)
    → BR (CS.blocks bs T) (X86.blocks T' (sel-blocks bs le))
  blocks-＝ (bs ▷ t) le Z ρ =
    tail-＝ t _ (CS.blocks bs T) (X86.blocks T' (sel-blocks bs _)) (blocks-＝ bs _) ρ (λ _ → init) init
  blocks-＝ (bs ▷ t) le (S l) = blocks-＝ bs _ l

  {- the code of a definition: its start binds %rdi and %rsi to slots 0 and 1
     (the states are written as the semantics builds them, so that Agda
     need not unfold the instructions to compare them) -}
  code-＝ : ∀ {s} (b : C.Body Σ (DSig.cod s) (Args s)) → CS.code′ T b ＝ X86.codeₜ T' (db {s = s} b)
  code-＝ {s} b@(C.body bs t) =
    codeₜ-cong T T' {s} b (db {s = s} b) λ X Y dX dY →
      tail-＝ t (m≤n⊔m (blocks-depth bs) (depth t)) (CS.blocks bs T) (X86.blocks T' (sel-blocks bs (m≤m⊔n (blocks-depth bs) (depth t))))
        (blocks-＝ bs (m≤m⊔n (blocks-depth bs) (depth t))) (env₂ X Y) {St.rs (called s)} {nothing} {false} (X86.args X Y) init
      ∙ (run-start′ s (db {s = s} b) (sel-blocks bs (m≤m⊔n (blocks-depth bs) (depth t)))
           (tail t (m≤n⊔m (blocks-depth bs) (depth t)) {St.rs (called s)} {nothing} {false})
           (≤-trans (s≤s z≤n) (≤-trans (depth-≥ t) (m≤n⊔m (blocks-depth bs) (depth t))))
           (≤-trans (depth-≥ t) (m≤n⊔m (blocks-depth bs) (depth t))) (db-body {s = s} bs t) X Y dX dY) ⁻¹

{- the tables of definitions agree -}
table-＝ : ∀ {Σ ss} (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) ss) {s} (f : Σ ∋ s)
  → tables CS.code′ ds f ＝ tables X86.codeₜ (All-map db ds) f
table-＝ [] f = refl
table-＝ (d ∷ ds) f =
  tables-cons CS.code′ X86.codeₜ d ds (db d) (All-map db ds) f
    (code-＝ (tables CS.code′ ds) (tables X86.codeₜ (All-map db ds)) (table-＝ ds) d)
    (table-＝ ds f)

select-correct : ∀ {A} (P : C.Program A) → CS.⟦ P ⟧ₚ ＝ X86.⟦ select P ⟧ₜ
select-correct (C.program ds (C.body bs t)) =
  tail-＝ T T' TT t _ (CS.blocks bs T) (X86.blocks T' (sel-blocks bs _)) (blocks-＝ T T' TT bs _)
    ρ₀ (λ _ → init) init
 where
  T = CS.table ds
  T' = tables X86.codeₜ (All-map def-body ds)
  TT : ∀ {s} (f : _ ∋ s) → T f ＝ T' f
  TT f = table-＝ ds f ∙ ap (λ ds' → tables X86.codeₜ ds' f) (≡→＝ (map-db ds))
