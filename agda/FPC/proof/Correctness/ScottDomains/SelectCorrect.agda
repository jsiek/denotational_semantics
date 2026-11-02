{-

  Correctness of select instructions (CFGμ → X86μ,
  Mu/Compiler/Select.agda) in Scott domains
  (Mu/Semantics/ScottDomains/{CFG,X86}.agda), as in the graph model
  (Mu/proof/Correctness/GraphModel/SelectCorrect.agda), with equality of
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
  these binds are β-reductions (Start; the graph model's fin-β and
  monotonicity are not needed).

  Checking speed shapes the start of a definition only: Agda compares
  two meanings that are equal but not syntactically so by reducing
  both, which is very slow for the code of a definition. So the start is
  opaque (db, related to the X86μ code by an equation on syntax), its
  function values are found by Agda (Σ-types proved by refl, g₁ and g₂),
  and the meanings compared are named (runAt, kAt). (With def-body in
  place of db, or with app-Λ-defined _ in place of g₁ and g₂, the module
  does not check in 7 minutes.)

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
open import Mu.Language.X86 using (Seq; Atm; var; rax; rdi; rsi; St; st; called; reg; retq; _∷_; movq; slot)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos) renaming (map to All-map)
open import Mu.Compiler.Select using (Out; ret; to; after; dst; sel; tail; atms; depth; depth-≥; blocks-depth; def-body; select)
  renaming (blocks to sel-blocks)
open import Framework.abt.GSubst using (_•_)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (zero; suc)
open import Data.Nat using (_≤_; _<_; s≤s; z≤n) renaming (_⊔_ to _⊔ₙ_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.Maybe using (nothing)
open import Data.Bool using (false)
import Relation.Binary.PropositionalEquality as Eq

module Mu.proof.Correctness.ScottDomains.SelectCorrect
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe
open import proof.Framework.Scott.Ops pt fe pe renaming (app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Semantics pt fe pe
open import Semantics.Scott.Prim pt fe pe using (primD)
open import Mu.Semantics.ScottDomains.Ops pt fe pe
import Mu.Semantics.ScottDomains.CFG pt fe pe as CS
open CS using (⟦_⟧ᵗ; Meanings; drop)
import Mu.Semantics.ScottDomains.X86 pt fe pe as X86
open X86 using (𝕊; RegsD; _[_≔_])
open import Mu.proof.Semantics.ScottDomains.BackEndLemmas pt fe pe using (seq-self; seq-seq; code₂-cong; tables-cons; 𝒮-＝; 𝒜s; 𝒮)

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
module _ {Σ : List DSig} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ＝ T' f) where

  𝒪s-atms : ∀ {Δ Δs Γ O F} (as : All (Atm Σ Δ) Δs) (ρ : ⟨ Env ⟩) (r : ⟨ RegsD ×₁ 𝔻 ⟩)
    → 𝒜s as T' · ρ ＝ X86.𝒪s T' (atms {Γ = Γ} {O} {F} as) · (ρ , r)
  𝒪s-atms [] ρ r = dfunext fe (λ ())
  𝒪s-atms (a ∷ as) ρ r = dfunext fe λ { zero → refl ; (suc i) → happly (𝒪s-atms as ρ r) i }

  {- the start of a definition binds %rdi and %rsi to slots 1 and 0:
     two applications of function values, which Agda finds (g₁, g₂) -}
  module Start {n Bs} (s : DSig) (bs' : X86b.Blocks Σ n (DSig.cod s) Bs)
               (k : Seq Σ n (DSig.cod s) Bs (st (St.rs (called s)) (Args s) nothing false))
               .(l₁ : 0 < n) .(l₂ : 1 < n) (X Y : ⟨ 𝔻 ⟩) where
    g₁ : Σ G ꞉ DCPO[ 𝔻 , 𝔻 ] , runAt T' (X86b.body n bs' (startSeq s k l₁ l₂)) X Y ＝ appᵈ · (Λ · G) · X
    g₁ = _ , refl

    g₂ : Σ G ꞉ DCPO[ 𝔻 , 𝔻 ] , pr₁ g₁ · X ＝ appᵈ · (Λ · G) · Y
    g₂ = _ , refl

    run-start : defined X → defined Y → runAt T' (X86b.body n bs' (startSeq s k l₁ l₂)) X Y ＝ kAt T' k bs' X Y
    run-start dX dY = pr₂ g₁ ∙ app-Λ-defined (pr₁ g₁) X dX ∙ pr₂ g₂ ∙ app-Λ-defined (pr₁ g₂) Y dY

  {- ... for a body that is that start (an equation on syntax) -}
  run-start′ : ∀ {n Bs} (s : DSig) (b' : X86Body Σ (DSig.cod s) (called s)) (bs' : X86b.Blocks Σ n (DSig.cod s) Bs)
    (k : Seq Σ n (DSig.cod s) Bs (st (St.rs (called s)) (Args s) nothing false))
    .(l₁ : 0 < n) .(l₂ : 1 < n) → b' Eq.≡ X86b.body n bs' (startSeq s k l₁ l₂)
    → (X Y : ⟨ 𝔻 ⟩) → defined X → defined Y → runAt T' b' X Y ＝ kAt T' k bs' X Y
  run-start′ s .(X86b.body _ bs' (startSeq s k l₁ l₂)) bs' k l₁ l₂ Eq.refl X Y = Start.run-start s bs' k l₁ l₂ X Y

  module _ {n R' Bs} (B' : Meanings Bs) where

    {- what k means, after the value of s is in o -}
    Fits : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') → DCPO[ 𝔻 , 𝔻 ] → (∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)) → ⟨ Env ⟩ → 𝓤₁ ̇
    Fits ret K k ρ = ∀ {Γ O F} ρ' R F' → R rax ＝ X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' · (ρ' , (R , F'))
    Fits (to p _) K k ρ = ∀ {Γ O F} X → defined X → ∀ R F'
      → K · X ＝ X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' · (X • (drop p · ρ) , (R , F'))

    put-＝ : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') {K} {k : ∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)} {ρ D} {D' : Den 𝕊} {Γ O F R F'}
      → Fits o K k ρ → D ＝ D' · (ρ , (R , F'))
      → then o K D ＝ X86.put T' (dst o {Γ} {O} {F}) D' (X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B') · (ρ , (R , F'))
    put-＝ ret {R = R} {F'} f e = e ∙ f _ _ F'
    put-＝ (to p _) {K} {k} {ρ} {D} {D'} {Γ} {O} {F} {R} {F'} f e =
      ap (appᵈ · (Λ · K) ·_) e
      ∙ ap (λ G → appᵈ · G · (D' · (ρ , (R , F')))) (Λ-cong K G (λ X d → f {Γ} {O} {F} X d R F'))
     where
      G = curry₁ 𝕊 𝔻 𝔻 (∘₁ (𝕊 ×₁ 𝔻) 𝕊 𝔻 (X86.next T' p) (X86.⟦_⟧ˢ T' (k {Γ} {O} {F}) B')) · (ρ , (R , F'))

    {- the code selected for s into o, then k -}
    sel-＝ : ∀ {Δ A Δ''} (s : I.Simple Σ Δ A) (o : Out n Δ A Δ'') {K} {k : ∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)} {ρ Γ O F R F'}
      → Fits o K k ρ → then o K (𝒮 s T · ρ) ＝ X86.⟦_⟧ˢ T' (sel s o k {Γ} {O} {F}) B' · (ρ , (R , F'))
    sel-＝ s@(I.atm a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.pair c e) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.callc (var x) a) o {K} {k} {ρ} f =
      ap (then o K) (𝒮-＝ TT s ρ) ∙ then-seq o K (𝒮 s T' · ρ) ⁻¹ ∙ ap (seq · (𝒮 s T' · ρ) ·_) (put-＝ o f refl)
    sel-＝ s@(I.tuple {Δs} as) o {ρ = ρ} {Γ} {O} {F} {R} {F'} f =
      put-＝ o f (𝒮-＝ TT s ρ ∙ ap (tupleᵈ (length Δs) ·_) (𝒪s-atms {Γ = Γ} {O} {F} as ρ (R , F')))
    sel-＝ s@(I.get j a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.inl a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.inr a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.prim sub a b) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.prim eq a b) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.fold a) o f = put-＝ o f (𝒮-＝ TT s _)
    sel-＝ s@(I.unfold a) o f = put-＝ o f (𝒮-＝ TT s _)

  {- the blocks B (of CFGμ) and B' (of X86μ) agree -}
  BR : ∀ {Bs} → Meanings Bs → Meanings Bs → 𝓤₁ ̇
  BR {Bs} B B' = ∀ {Δ} (l : Bs ∋ Δ) ρ → B l · ρ ＝ B' l · ρ

  tail-＝ : ∀ {n R' Bs Δ} (t : Tail Σ R' Bs Δ) .(le : depth t ≤ n) {B B' : Meanings Bs} → BR B B' → ∀ ρ
    → ∀ {Γ O F} R F' → ⟦ t ⟧ᵗ T B · ρ ＝ X86.⟦_⟧ˢ T' (tail t le {Γ} {O} {F}) B' · (ρ , (R , F'))
  tail-＝ (return s) le {B' = B'} br ρ R F' = sel-＝ B' s ret {K = id₁ 𝔻} {k = retq Eq.refl} (λ ρ' R F' → refl)
  tail-＝ (C.seq p s t) le {B} {B'} br ρ R F' =
    sel-＝ B' s (to p _) {K = abs (⟦ t ⟧ᵗ T B) · (drop p · ρ)} {k = tail t _}
      (λ X _ R F → tail-＝ t _ br (X • (drop p · ρ)) R F)
  tail-＝ (goto l) le br ρ R F' = br l ρ
  tail-＝ (C.case (var x) p l₁ l₂) le {B} {B'} br ρ R F' =
    ap (λ y → cases · ρ (idx x) · y)
      (ap₂ _,_ (strict-cong (abs (B l₁) · (drop p · ρ)) (abs (B' l₁) · (drop p · ρ)) (λ X _ → br l₁ (X • (drop p · ρ))))
               (strict-cong (abs (B l₂) · (drop p · ρ)) (abs (B' l₂) · (drop p · ρ)) (λ X _ → br l₂ (X • (drop p · ρ)))))

  blocks-＝ : ∀ {n R' Bs} (bs : C.Blocks Σ R' Bs) .(le : blocks-depth bs ≤ n)
    → BR (CS.blocks bs T) (X86.blocks T' (sel-blocks bs le))
  blocks-＝ (bs ▷ t) le Z ρ =
    tail-＝ t _ (blocks-＝ bs _) ρ (λ _ → init) init
  blocks-＝ (bs ▷ t) le (S l) = blocks-＝ bs _ l

  {- the code of a definition: its start binds %rdi and %rsi to slots 0 and 1
     (the states are written as the semantics builds them, so that Agda
     need not unfold the instructions to compare them) -}
  code-＝ : ∀ {s} (b : C.Body Σ (DSig.cod s) (Args s)) → CS.code′ T b ＝ X86.codeₜ T' (db {s = s} b)
  code-＝ {s} b@(C.body bs t) =
    codeₜ-cong T T' {s} b (db {s = s} b) λ X Y dX dY →
      tail-＝ t _ (blocks-＝ bs _) (env₂ X Y) {St.rs (called s)} {nothing} {false} (X86.args X Y) init
      ∙ run-start′ s (db {s = s} b) _ _ _ _ (db-body {s = s} bs t) X Y dX dY ⁻¹

{- the tables of definitions agree -}
table-＝ : ∀ {Σ ss} (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) ss) {s} (f : Σ ∋ s)
  → tables CS.code′ ds f ＝ tables X86.codeₜ (All-map db ds) f
table-＝ [] f = refl
table-＝ (d ∷ ds) f =
  tables-cons CS.code′ X86.codeₜ d ds (db d) (All-map db ds) f
    (code-＝ (table-＝ ds) d)
    (table-＝ ds f)

select-correct : ∀ {A} (P : C.Program A) → CS.⟦ P ⟧ₚ ＝ X86.⟦ select P ⟧ₜ
select-correct (C.program ds (C.body bs t)) =
  tail-＝ TT t _ (blocks-＝ TT bs _) ρ₀ (λ _ → init) init
 where
  T = CS.table ds
  T' = tables X86.codeₜ (All-map def-body ds)
  TT : ∀ {s} (f : _ ∋ s) → T f ＝ T' f
  TT f = table-＝ ds f ∙ ap (λ ds' → tables X86.codeₜ ds' f) (≡→＝ (map-db ds))
