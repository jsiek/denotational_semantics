{-

  Select instructions (CFGμ → X86μ, Mu/Compiler/Select.agda) is correct
  in the graph model, as for the typed pass
  (proof/Correctness/Graph/SelectCorrect.agda): the X86μ program
  (Mu/Semantics/Graph/X86.agda) means exactly what the CFGμ program does
  (≃, Mu/Semantics/Graph/CFG.agda), for every CFGμ program.

  The X86μ frame is the CFGμ frame, a slot write binds as CFGμ's seq
  does, and a register write is a substitution, so the code selected
  for a simple expression means it, definitionally, up to the tables
  (sel-≃): callq applies the code and environment that load fst and
  load snd read from the closure's slot, as CFGμ's call does, and callq
  writes strictly, which changes nothing before a return or a bind
  (strict-put). X86μ's case is CFGμ's (a pseudo-instruction, where
  X86ᵀ has testinl, the payload and je, which the typed proof shows
  agree with CFGᵀ's case on a slot that never holds both an inl and an
  inr). What is left is the start of a definition, which binds %rdi and
  %rsi to slots 0 and 1, where CFGμ has them in its frame: Λ binds
  finite sets, so this is a β (fin-β), by the monotonicity of CFGμ's
  tails (tail-mono).

-}

module Mu.proof.Correctness.Graph.SelectCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops using (⋆; Λ; 𝒞; 𝒯; strict; Mono₁; Λ-≃; ⋆-≃; Λ-β; 𝒞-≃)
open import proof.Framework.GraphModel.Laws using (strict-≃; ⋆-ne)
open import Mu.Semantics.Graph.Ops using (Table; tables; init)
open import Mu.proof.Semantics.Graph.CFG using (⟦_⟧ᵗ; Meanings; drop; 𝒮; 𝒮-≃; tail-mono; blocks-mono)
  renaming (code′ to codeᶜ; ⟦_⟧ₚ to ⟦_⟧ᶜ)
import Mu.proof.Semantics.Graph.CFG as GC
open import Mu.Semantics.Graph.Imp using (𝒜s)
import Mu.Semantics.Graph.X86 as X
open import Mu.Language.Type
import Mu.Language.Imp as I
import Mu.Language.CFG as C
open C using (DSig; Args; Tail; return; seq; goto; case; _▷_)
open import Mu.Language.X86 using (Seq; Atm; var; rax; St; called)
open import Mu.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)
open import Data.Bool using (false)
open import Data.Maybe using (nothing)
open import Mu.Compiler.Select using (Out; ret; to; after; dst; sel; tail; atms; depth; blocks-depth; def-body; select)
  renaming (blocks to sel-blocks)
open import Language.Prim using (sub; eq)

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (zero; suc; _≤_; _≟_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (yes; no)

{- a bind of a finite set of values is a β -}
fin-β : ∀ {G V} → Mono₁ G → V ≢ [] → V ≈ V → G (mem V) ≃ ⋆ ⟨ Λ ⟨ G , ptt ⟩ , ⟨ mem V , ptt ⟩ ⟩
fin-β {V = V} m ne c = ≃-sym (Λ-β m (λ w w∈ → ⟨ V , ⟨ ne , ⟨ (λ _ z → z) , w∈ ⟩ ⟩ ⟩) (≈⇒Con c))

{- The pass -------------------------------------------------------------------------------}

{- d := D, then K, in CFGμ -}
then : ∀ {n Δ A Δ''} → Out n Δ A Δ'' → (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
then ret K D = D
then (to p _) K D = ⋆ ⟨ Λ ⟨ K , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

then-ne : ∀ {n Δ A Δ''} (o : Out n Δ A Δ'') {K D w} → w ∈ then o K D → nonempty D
then-ne ret w∈ = ⟨ _ , w∈ ⟩
then-ne (to p _) {K} {D} w∈ = proj₂ (⋆-ne {Λ ⟨ K , ptt ⟩} {D} ⟨ _ , w∈ ⟩)

{- for tables T (of CFGμ) and T' (of X86μ) that agree -}
module _ {Σ : List DSig} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ≃ T' f) where

  𝒪s-atms : ∀ {Δ Δs Γ O F} (as : All (Atm Σ Δ) Δs) ρ R → 𝒜s as T' ρ ≡ X.𝒪s T' (atms {Γ = Γ} {O} {F} as) ρ R
  𝒪s-atms [] ρ R = refl
  𝒪s-atms (a ∷ as) ρ R = cong (λ r → ⟨ GC.𝒜 a T' ρ , r ⟩) (𝒪s-atms as ρ R)

  module _ {n R' Bs} (B' : Meanings Bs) where

    {- what k means, after the value of s is in o -}
    Fits : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') → (𝒫 Value → 𝒫 Value) → (∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)) → Env Value → Set₁
    Fits ret K k ρ = ∀ {Γ O F} ρ' R F' → R rax ≃ X.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' ρ' R F'
    Fits (to p _) K k ρ = ∀ {Γ O F} V → V ≈ V → ∀ R F' → K (mem V) ≃ X.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' (mem V • drop p ρ) R F'

    put-≃ : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') {K} {k : ∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)} {ρ D D' Γ O F R F'}
      → Fits o K k ρ → D ≃ D' → then o K D ≃ X.put T' (dst o {Γ} {O} {F}) D' (X.⟦_⟧ˢ T' (k {Γ} {O} {F}) B') ρ R F'
    put-≃ ret f D≃ = ≃-trans D≃ (f _ _ _)
    put-≃ (to p _) {K} {k} {ρ} {Γ = Γ} {O} {F} {R} {F'} f D≃ =
      ⋆-≃ (Λ-≃ {K} {λ X → X.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' (X • drop p ρ) R F'} (λ V _ c → f {Γ} {O} {F} V c R F')) D≃

    {- a strict write, before a return or a bind -}
    strict-put : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') {K} {k : ∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)} {ρ D D' Γ O F R F'}
      → Fits o K k ρ → D ≃ D' → then o K D ≃ strict D' (X.put T' (dst o {Γ} {O} {F}) D' (X.⟦_⟧ˢ T' (k {Γ} {O} {F}) B') ρ R F')
    strict-put o {K} {k} f D≃ =
      ≃-sym (strict-≃ (≃-sym (put-≃ o {K} {k} f D≃)) (λ w w∈ → then-ne o (proj₂ (put-≃ o {K} {k} f ≃-refl) w w∈)))

    {- the code selected for s into o, then k -}
    sel-≃ : ∀ {Δ A Δ''} (s : I.Simple Σ Δ A) (o : Out n Δ A Δ'') {K} {k : ∀ {Γ O F} → Seq Σ n R' Bs (after o Γ O F)} {ρ Γ O F R F'}
      → Fits o K k ρ → then o K (𝒮 s T ρ) ≃ X.⟦_⟧ˢ T' (sel s o k {Γ} {O} {F}) B' ρ R F'
    sel-≃ s@(I.atm a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.pack c e) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.callc (var x) a) o f = strict-put o f (𝒮-≃ TT s _)
    sel-≃ s@(I.tuple {Δs} as) o {ρ = ρ} {Γ} {O} {F} {R} f =
      put-≃ o f (≃-trans (𝒮-≃ TT s ρ) (≃-reflexive (cong (𝒯 (length Δs)) (𝒪s-atms {Γ = Γ} {O} {F} as ρ R))))
    sel-≃ s@(I.get j a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.inl a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.inr a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.prim sub a b) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.prim eq a b) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.fold a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.unfold a) o f = put-≃ o f (𝒮-≃ TT s _)

  {- the blocks B (of CFGμ) and B' (of X86μ) agree -}
  BR : ∀ {Bs} → Meanings Bs → Meanings Bs → Set₁
  BR {Bs} B B' = ∀ {Δ} (l : Bs ∋ Δ) ρ → B l ρ ≃ B' l ρ

  tail-≃ : ∀ {n R' Bs Δ} (t : Tail Σ R' Bs Δ) .(le : depth t ≤ n) {B B' : Meanings Bs} → BR B B' → ∀ ρ
    → ∀ {Γ O F} R F' → ⟦ t ⟧ᵗ T B ρ ≃ X.⟦_⟧ˢ T' (tail t le {Γ} {O} {F}) B' ρ R F'
  tail-≃ (return s) le {B' = B'} br ρ R F' = sel-≃ B' s ret {K = λ X → X} (λ _ _ _ → ≃-refl)
  tail-≃ (seq p s t) le {B} {B'} br ρ R F' =
    sel-≃ B' s (to p _) {K = λ X → ⟦ t ⟧ᵗ T B (X • drop p ρ)} (λ V c R F → tail-≃ t _ br _ R F)
  tail-≃ (goto l) le br ρ R F' = br l ρ
  tail-≃ (case (var x) p l₁ l₂) le {B} {B'} br ρ R F' =
    𝒞-≃ {D = ρ (idx x)} {ρ (idx x)} {F = λ X → B l₁ (X • drop p ρ)} {λ X → B' l₁ (X • drop p ρ)} {λ X → B l₂ (X • drop p ρ)} {λ X → B' l₂ (X • drop p ρ)}
      ≃-refl (λ _ _ _ → br l₁ _) (λ _ _ _ → br l₂ _)

  blocks-≃ : ∀ {n R' Bs} (bs : C.Blocks Σ R' Bs) .(le : blocks-depth bs ≤ n) → BR (GC.blocks bs T) (X.blocks T' (sel-blocks bs le))
  blocks-≃ (bs ▷ t) le Z ρ = tail-≃ t _ (blocks-≃ bs _) ρ _ _
  blocks-≃ (bs ▷ t) le (S l) = blocks-≃ bs _ l

  {- the code of a definition: its start binds %rdi and %rsi to slots 0 and 1 -}
  code-≃ : ∀ {s} (b : C.Body Σ (DSig.cod s) (Args s)) → codeᶜ T b ≃ X.codeₜ T' (def-body b)
  code-≃ {s} (C.body bs t) = Λ-≃ λ V neV cV → Λ-≃ λ W neW cW →
    ≃-trans (fin-β {λ X' → E (mem W • X' • ι)} (λ X⊆ → mono X⊆ (λ _ z → z)) neV cV)
      (≃-trans (⋆-≃ (Λ-≃ {λ X' → E (mem W • X' • ι)} {λ X' → L (λ Y' → E (Y' • X' • ι)) (mem W)}
                       λ V' _ _ → fin-β {λ Y' → E (Y' • mem V' • ι)} (mono (λ _ z → z)) neW cW) ≃-refl)
        (⋆-≃ (Λ-≃ {λ X' → L (λ Y' → E (Y' • X' • ι)) (mem W)} {λ X' → L (λ Y' → x86 (mem V) (mem W) (Y' • X' • ι)) (mem W)}
                   λ V' _ cV' → ⋆-≃ (Λ-≃ {λ Y' → E (Y' • mem V' • ι)} {λ Y' → x86 (mem V) (mem W) (Y' • mem V' • ι)}
                     λ W' _ cW' → tail-≃ t _ (blocks-≃ bs _) (mem W' • mem V' • ι) _ _) ≃-refl)
                 ≃-refl))
    where
    ι : Env Value
    ι = λ _ → init
    E = ⟦ t ⟧ᵗ T (GC.blocks bs T)
    x86 : 𝒫 Value → 𝒫 Value → Env Value → 𝒫 Value
    x86 X Y ρ = X.⟦_⟧ˢ T' (tail t (m≤n⊔m (blocks-depth bs) _) {St.rs (called s)} {nothing} {false})
                  (X.blocks T' (sel-blocks bs (m≤m⊔n _ (depth t)))) ρ (X.args X Y) init
    L : (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
    L F D = ⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
    mono : ∀ {X X' Y Y'} → X ⊆ X' → Y ⊆ Y' → E (Y • X • ι) ⊆ E (Y' • X' • ι)
    mono X⊆ Y⊆ = tail-mono t (blocks-mono bs) λ { zero → Y⊆ ; (suc zero) → X⊆ ; (suc (suc j)) → λ _ z → z }

{- the tables of definitions agree -}
table-≃ : ∀ {Σ ss} (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) ss) {s} (f : Σ ∋ s)
  → tables codeᶜ ds f ≃ tables X.codeₜ (All-map def-body ds) f
table-≃ [] f = ≃-refl
table-≃ {ss = _ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = code-≃ (table-≃ ds) d
... | no _ = table-≃ ds f

select-correct : ∀ {A} (P : C.Program A) → ⟦ P ⟧ᶜ ≃ X.⟦ select P ⟧ₜ
select-correct (C.program ds (C.body bs t)) = tail-≃ (table-≃ ds) t _ (blocks-≃ (table-≃ ds) bs _) _ _ _
