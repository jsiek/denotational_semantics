{-

  Correctness of select instructions (CFGμ → X86μ,
  FPC/Compiler/Select.agda) in Scott domains
  (FPC/Semantics/ScottDomains/{CFG,X86}.agda), as in the graph model
  (FPC/proof/Correctness/GraphModel/SelectCorrect.agda), with equality of
  values in place of equality of sets.

  The X86μ frame is the CFGμ frame, a slot write binds as CFGμ's seq
  does, and a register write is a substitution, so the code selected
  for a simple expression means it, definitionally, up to the tables
  (sel-＝): callq applies the code and environment that load fst and
  load snd read from the closure's slot, as CFGμ's call does, and callq
  writes strictly, which changes nothing before a return or a bind
  (then-seq: seq d d = d, and app (Λ K) d is strict in d). X86μ's case
  is CFGμ's. What is left is the start of a definition, which writes
  %rdi and %rsi to the slots of its environment and argument, where
  CFGμ's frame holds them (frame₂): the environment and the argument of
  a function value are defined, so these writes are β-reductions
  (Start; the graph model's fin-β and monotonicity are not needed).

  Checking speed shapes the start of a definition only: Agda compares
  two meanings that are equal but not syntactically so by reducing
  both, which is very slow for the code of a definition. So the start is
  opaque (db, related to the X86μ code by an equation on syntax), its
  function values are found by Agda (Σ-types proved by refl, g₁ and g₂),
  and the meanings compared are named (runAt, kAt).

-}

open import MLTT.Spartan hiding (inl; inr; cases; Type)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂; happly)

open import Language.Prim using (sub; eq)
open import Framework.Membership using (_⊑_; here⊑; ⊑-∋)
open import FPC.Language.Type
import FPC.Language.Imp as I
open I using (Inits; none; _⊕_; ⊆-refl)
import FPC.Language.CFG as C
open C using (DSig; Args; Tail; return; goto; _▷_)
open import FPC.Language.X86 using () renaming (Body to X86Body)
import FPC.Language.X86 as X86b
open import FPC.Language.X86 using (Seq; Atm; var; rax; rdi; rsi; St; st;
  called; reg; retq; _∷_; movq; slot)
open import FPC.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to
  All-map)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (nothing)
open import Data.Bool using (false)
import Relation.Binary.PropositionalEquality as Eq
open import FPC.Compiler.Select using (Out; ret; to; after; dst; sel; tail;
  atms; def-body; select) renaming (blocks to sel-blocks)

module FPC.proof.Correctness.ScottDomains.SelectCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to
  inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import FPC.Semantics.ScottDomains.Ops pt fe pe
import FPC.Semantics.ScottDomains.CFG pt fe pe as CS
open CS using (⟦_⟧ᵗ; Meanings)
import FPC.Semantics.ScottDomains.X86 pt fe pe as X86
open X86 using (𝕊; RegsD; _[_≔_])
open import FPC.proof.Semantics.ScottDomains.BackEndLemmas pt fe pe using
  (seq-self; seq-seq; code₂-cong; tables-cons; 𝒮-＝; 𝒜s; 𝒮)

{- d := D, then K, in CFGμ -}
then : ∀ {Δ} {I J : Inits Δ} {A} → Out I A J → DCPO[ 𝔻 , 𝔻 ] → ⟨ 𝔻 ⟩
  → ⟨ 𝔻 ⟩
then ret K D = D
then (to x _) K D = appᵈ · (Λ · K) · D

{- a strict write changes nothing before a return or a bind -}
then-seq : ∀ {Δ} {I J : Inits Δ} {A} (o : Out I A J) (K : DCPO[ 𝔻 , 𝔻 ])
  (D : ⟨ 𝔻 ⟩)
  → seq · D · then o K D ＝ then o K D
then-seq ret K D = seq-self D
then-seq (to x _) K D =
  ap (seq · D ·_) (app-Λ K D) ∙ seq-seq D (K · D) ∙ (app-Λ K D) ⁻¹

{- the slots of the environment and the argument of a definition -}
envˢ : ∀ {Δ : Ctx} {A B} → (A ∷ B ∷ []) ⊑ Δ → Δ ∋ B
envˢ p = ⊑-∋ p (S Z)

argˢ : ∀ {Δ : Ctx} {A B} → (A ∷ B ∷ []) ⊑ Δ → Δ ∋ A
argˢ p = ⊑-∋ p Z

{- the frame at the start of a definition with parameters p -}
frameₚ : ∀ {Δ : Ctx} {A B} → (A ∷ B ∷ []) ⊑ Δ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ Env ⟩
frameₚ p = frame₂ (idx (envˢ p)) (idx (argˢ p))

{- X86μ code started with the environment X and argument Y in %rdi and
   %rsi, and k run from the frame σ; named, so that Agda compares them
   by their arguments -}
runAt : ∀ {Σ R' ψ} → Table Σ → X86Body Σ R' ψ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
runAt T' b X Y = X86.run T' b · ((λ _ → init) , (X86.args X Y , init))

kAt : ∀ {Σ Δ R' Bs ψ} → Table Σ → Seq Σ Δ R' Bs ψ → X86b.Blocks Σ Δ R' Bs
  → ⟨ Env ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩ → ⟨ 𝔻 ⟩
kAt T' k bs' σ X Y =
  X86.⟦_⟧ˢ T' k (X86.blocks T' bs') · (σ , (X86.args X Y , init))

{- the code of a definition, given what its body means -}
codeₜ-cong : ∀ {Σ} (T T' : Table Σ) {s} (b₀ : C.Body Σ (DSig.cod s) (Args s))
  (b : X86Body Σ (DSig.cod s) (called s))
  → (  (X Y : ⟨ 𝔻 ⟩)
     → defined X
     → defined Y
     → CS.run b₀ T · frameₚ (C.Body.params b₀) X Y ＝ runAt T' b X Y)
  → CS.code′ T b₀ ＝ X86.codeₜ T' b
codeₜ-cong T T' b₀ b h =
  code₂-cong
    (∘₁ (𝔻 ×₁ 𝔻) Env 𝔻
       (frame₂ᶜ (idx (envˢ (C.Body.params b₀))) (idx (argˢ (C.Body.params b₀))))
       (CS.run b₀ T))
    (∘₁ (𝔻 ×₁ 𝔻) 𝕊 𝔻
       (pair₁ (𝔻 ×₁ 𝔻) Env (RegsD ×₁ 𝔻) (const₁ (𝔻 ×₁ 𝔻) Env (λ _ → init))
          (pair₁ (𝔻 ×₁ 𝔻) RegsD 𝔻 X86.argsᶜ (const₁ (𝔻 ×₁ 𝔻) 𝔻 init)))
       (X86.run T' b))
    h

{- the start of the code of a definition: %rdi and %rsi to the slots of
   the environment and the argument, then k -}
startSeq : ∀ {Σ Δ Bs} (s : DSig) (p : Args s ⊑ Δ)
  (k : Seq Σ Δ (DSig.cod s) Bs
         (st (St.rs (called s Δ)) (none Δ ⊕ envˢ p ⊕ argˢ p) nothing false))
  → Seq Σ Δ (DSig.cod s) Bs (called s Δ)
startSeq {Δ = Δ} s p k =
  movq (reg rdi Eq.refl) (slot (envˢ p) (⊆-refl {I = none Δ ⊕ envˢ p}))
  ∷ movq (reg rsi Eq.refl)
      (slot (argˢ p) (⊆-refl {I = none Δ ⊕ envˢ p ⊕ argˢ p}))
  ∷ k

{- the start of a definition, opaque (Agda unfolds it, to no end, when
   it compares the meanings of code that mentions it) -}
opaque
  db : ∀ {Σ s} → C.Body Σ (DSig.cod s) (Args s)
    → X86Body Σ (DSig.cod s) (called s)
  db = def-body

opaque
  unfolding db

  {- (on syntax: only the irrelevant proofs differ) -}
  db-body : ∀ {Σ s Δ Bs} (p : Args s ⊑ Δ) (bs : C.Blocks Σ (DSig.cod s) Δ Bs)
    (t : Tail Σ (DSig.cod s) Δ Bs (I.initial p))
    → db {s = s} (C.body Δ p bs t)
      Eq.≡ X86b.body {ψ = called s} Δ (sel-blocks bs)
             (startSeq s p (tail t {St.rs (called s Δ)} {nothing} {false}))
  db-body p bs t = Eq.refl

  map-db : ∀ {Σ ss} (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) ss)
    → All-map db ds Eq.≡ All-map def-body ds
  map-db ds = Eq.refl

≡→＝ : ∀ {A : Set} {x y : A}
  → x Eq.≡ y
  → x ＝ y
≡→＝ Eq.refl = refl

{- for tables T (of CFGμ) and T' (of X86μ) that agree -}
module _ {Σ : List DSig} {T T' : Table Σ}
  (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) where

  𝒪s-atms : ∀ {Δ Δs Γ} {I : Inits Δ} {O F} (as : All (Atm Σ Δ I) Δs)
    (ρ : ⟨ Env ⟩) (r : ⟨ RegsD ×₁ 𝔻 ⟩)
    → 𝒜s as T' · ρ ＝ X86.𝒪s T' (atms {Γ = Γ} {O = O} {F = F} as) · (ρ , r)
  𝒪s-atms [] ρ r = dfunext fe (λ ())
  𝒪s-atms (a ∷ as) ρ r =
    dfunext fe λ { zero → refl ; (suc i) → happly (𝒪s-atms as ρ r) i }

  {- the start of a definition writes %rdi and %rsi to the slots of the
     environment and the argument: two applications of function values,
     which Agda finds (g₁, g₂) -}
  module Start {Δ Bs} (s : DSig) (p : Args s ⊑ Δ)
               (bs' : X86b.Blocks Σ Δ (DSig.cod s) Bs)
               (k : Seq Σ Δ (DSig.cod s) Bs
                      (st (St.rs (called s Δ)) (none Δ ⊕ envˢ p ⊕ argˢ p)
                         nothing false))
               (X Y : ⟨ 𝔻 ⟩) where
    {- the code after the first write -}
    k₁ : Seq Σ Δ (DSig.cod s) Bs
           (st (St.rs (called s Δ)) (none Δ ⊕ envˢ p) nothing false)
    k₁ =
      movq (reg rsi Eq.refl)
        (slot (argˢ p) (⊆-refl {I = none Δ ⊕ envˢ p ⊕ argˢ p})) ∷ k

    g₁ : Σ G ꞉ DCPO[ 𝔻 , 𝔻 ]
      , runAt T' (X86b.body {ψ = called s} Δ bs' (startSeq s p k)) X Y
        ＝ appᵈ · (Λ · G) · X
    g₁ =
      curry₁ 𝕊 𝔻 𝔻
        (∘₁ (𝕊 ×₁ 𝔻) 𝕊 𝔻 (X86.next T' (envˢ p))
           (X86.⟦_⟧ˢ T' k₁ (X86.blocks T' bs')))
      · ((λ _ → init) , (X86.args X Y , init))
      , refl

    g₂ : Σ G ꞉ DCPO[ 𝔻 , 𝔻 ] , pr₁ g₁ · X ＝ appᵈ · (Λ · G) · Y
    g₂ =
      curry₁ 𝕊 𝔻 𝔻
        (∘₁ (𝕊 ×₁ 𝔻) 𝕊 𝔻 (X86.next T' (argˢ p))
           (X86.⟦_⟧ˢ T' k (X86.blocks T' bs')))
      · (write (idx (envˢ p)) (λ _ → init) X , (X86.args X Y , init))
      , refl

    run-start : defined X
      → defined Y
      → runAt T' (X86b.body {ψ = called s} Δ bs' (startSeq s p k)) X Y
        ＝ kAt T' k bs' (frameₚ p X Y) X Y
    run-start dX dY =
      pr₂ g₁ ∙ app-Λ-defined (pr₁ g₁) X dX ∙ pr₂ g₂
      ∙ app-Λ-defined (pr₁ g₂) Y dY

  {- ... for a body that is that start (an equation on syntax) -}
  run-start′ : ∀ {Δ Bs} (s : DSig) (p : Args s ⊑ Δ)
    (b' : X86Body Σ (DSig.cod s) (called s))
    (bs' : X86b.Blocks Σ Δ (DSig.cod s) Bs)
    (k : Seq Σ Δ (DSig.cod s) Bs
           (st (St.rs (called s Δ)) (none Δ ⊕ envˢ p ⊕ argˢ p) nothing false))
    → b' Eq.≡ X86b.body {ψ = called s} Δ bs' (startSeq s p k)
    → (X Y : ⟨ 𝔻 ⟩)
    → defined X
    → defined Y
    → runAt T' b' X Y ＝ kAt T' k bs' (frameₚ p X Y) X Y
  run-start′ s p .(X86b.body {ψ = called s} _ bs' (startSeq s p k)) bs' k
    Eq.refl X Y =
    Start.run-start s p bs' k X Y

  module _ {Δ R' Bs} (B' : Meanings {Δ} Bs) where

    {- what k means, after the value of s is in o -}
    Fits : ∀ {I J : Inits Δ} {A} (o : Out I A J) → DCPO[ 𝔻 , 𝔻 ]
      → (∀ {Γ O F} → Seq Σ Δ R' Bs (after o Γ O F)) → ⟨ Env ⟩ → 𝓤₁ ̇
    Fits ret K k ρ =
      ∀ {Γ O F} ρ' R F'
      → R rax ＝ X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' · (ρ' , (R , F'))
    Fits (to x _) K k ρ = ∀ {Γ O F} X → defined X → ∀ R F'
      → K · X
        ＝ X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' · (write (idx x) ρ X , (R , F'))

    put-＝ : ∀ {I J : Inits Δ} {A} (o : Out I A J) {K}
      {k : ∀ {Γ O F} → Seq Σ Δ R' Bs (after o Γ O F)} {ρ D} {D' : Den 𝕊}
      {Γ O F R F'}
      → Fits o K k ρ
      → D ＝ D' · (ρ , (R , F'))
      → then o K D
        ＝ X86.put T' (dst o {Γ} {O} {F}) D' (X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B') ·
        (ρ , (R , F'))
    put-＝ ret {R = R} {F'} f e = e ∙ f _ _ F'
    put-＝ (to x _) {K} {k} {ρ} {D} {D'} {Γ} {O} {F} {R} {F'} f e =
      ap (appᵈ · (Λ · K) ·_) e
      ∙ ap (λ G → appᵈ · G · (D' · (ρ , (R , F'))))
        (Λ-cong K G (λ X d → f {Γ} {O} {F} X d R F'))
     where
      G =
        curry₁ 𝕊 𝔻 𝔻
        (∘₁ (𝕊 ×₁ 𝔻) 𝕊 𝔻 (X86.next T' x) (X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B')) ·
        (ρ , (R , F'))

    {- the code selected for s into o, then k -}
    sel-＝ : ∀ {I J : Inits Δ} {A} (s : I.Simple Σ Δ I A) (o : Out I A J) {K}
      {k : ∀ {Γ O F} → Seq Σ Δ R' Bs (after o Γ O F)} {ρ Γ O F R F'}
      → Fits o K k ρ
      → then o K (𝒮 s T · ρ)
        ＝ X86.⟦_⟧ˢ T' (sel s o k {Γ} {O} {F}) B' · (ρ , (R , F'))
    sel-＝ s@(I.atm a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.pair c e) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.callc (var x _) a) o {K} {k} {ρ} f =
      ap (then o K) (𝒮-＝ TT s ρ) ∙ then-seq o K (𝒮 s T' · ρ) ⁻¹
        ∙ ap (seq · (𝒮 s T' · ρ) ·_) (put-＝ o f refl)
    sel-＝ s@(I.tuple {Δs} as) o {ρ = ρ} {Γ} {O} {F} {R} {F'} f =
      put-＝ o f
        (𝒮-＝ TT s ρ
          ∙ ap (tupleᵈ (length Δs) ·_) (𝒪s-atms {Γ = Γ} {O = O} {F = F} as ρ
                (R , F')))
    sel-＝ s@(I.get j a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.inl a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.inr a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.prim sub a b) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.prim eq a b) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.fold a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.unfold a) o f = put-＝ o f (𝒮-＝ TT s _)

  {- the blocks B (of CFGμ) and B' (of X86μ) agree -}
  BR : ∀ {Δ} {Bs : List (Inits Δ)} → Meanings Bs → Meanings Bs → 𝓤₁ ̇
  BR {Δ} {Bs} B B' = ∀ {I} (l : Bs ∋ I) ρ → B l · ρ ＝ B' l · ρ

  tail-＝ : ∀ {Δ R' Bs} {I : Inits Δ} (t : Tail Σ R' Δ Bs I)
    → {B B' : Meanings Bs}
    → BR B B'
    → ∀ ρ → ∀ {Γ O F} R F'
    → ⟦ t ⟧ᵗ T B · ρ ＝ X86.⟦_⟧ˢ T' (tail t {Γ} {O} {F}) B' · (ρ , (R , F'))
  tail-＝ (return s) {B' = B'} br ρ R F' =
    sel-＝ B' s ret {K = id₁ 𝔻} {k = retq Eq.refl} (λ ρ' R F' → refl)
  tail-＝ (C.seq x s p t) {B} {B'} br ρ R F' =
    sel-＝ B' s (to x p) {K = absAt (idx x) (⟦ t ⟧ᵗ T B) · ρ} {k = tail t}
      (λ X _ R F → tail-＝ t br (write (idx x) ρ X) R F)
  tail-＝ (goto l) br ρ R F' = br l ρ
  tail-＝ (C.case (var x _) y z l₁ l₂) {B} {B'} br ρ R F' =
    ap (λ v → cases · ρ (idx x) · v)
      (ap₂ _,_
          (strict-cong (absAt (idx y) (B l₁) · ρ) (absAt (idx y) (B' l₁) · ρ)
            (λ X _ → br l₁ (write (idx y) ρ X)))
          (strict-cong (absAt (idx z) (B l₂) · ρ) (absAt (idx z) (B' l₂) · ρ)
            (λ X _ → br l₂ (write (idx z) ρ X))))

  blocks-＝ : ∀ {Δ R' Bs} (bs : C.Blocks Σ R' Δ Bs)
    → BR (CS.blocks bs T) (X86.blocks T' (sel-blocks bs))
  blocks-＝ (bs ▷ t) Z ρ =
    tail-＝ t (blocks-＝ bs) ρ (λ _ → init) init
  blocks-＝ (bs ▷ t) (S l) = blocks-＝ bs l

  {- the code of a definition: its start writes %rdi and %rsi to the
     slots of the environment and the argument (the states are written
     as the semantics builds them, so that Agda need not unfold the
     instructions to compare them) -}
  code-＝ : ∀ {s} (b : C.Body Σ (DSig.cod s) (Args s))
    → CS.code′ T b ＝ X86.codeₜ T' (db {s = s} b)
  code-＝ {s} b@(C.body Δ p bs t) =
    codeₜ-cong T T' {s} b (db {s = s} b) λ X Y dX dY →
      tail-＝ t (blocks-＝ bs) (frameₚ p X Y) {St.rs (called s Δ)} {nothing}
        {false} (X86.args X Y) init
      ∙ run-start′ s p (db {s = s} b) _ _ (db-body {s = s} p bs t) X Y dX dY ⁻¹

{- the tables of definitions agree -}
table-＝ : ∀ {Σ ss} (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) ss)
  {s} (f : Σ ∋ s)
  → tables CS.code′ ds f ＝ tables X86.codeₜ (All-map db ds) f
table-＝ [] f = refl
table-＝ (d ∷ ds) f =
  tables-cons CS.code′ X86.codeₜ d ds (db d) (All-map db ds) f
    (code-＝ (table-＝ ds) d)
    (table-＝ ds f)

select-correct : ∀ {A} (P : C.Program A) → CS.⟦ P ⟧ₚ ＝ X86.⟦ select P ⟧ₜ
select-correct (C.program ds (C.body Δ p bs t)) =
  tail-＝ TT t (blocks-＝ TT bs) ρ₀ (λ _ → init) init
 where
  T = CS.table ds
  T' = tables X86.codeₜ (All-map def-body ds)
  TT : ∀ {s} (f : _ ∋ s) → T f ＝ T' f
  TT f = table-＝ ds f ∙ ap (λ ds' → tables X86.codeₜ ds' f) (≡→＝ (map-db ds))
