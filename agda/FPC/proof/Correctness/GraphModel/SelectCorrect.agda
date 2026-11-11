{-

  Select instructions (CFGμ → X86μ, FPC/Compiler/Select.agda) is correct
  in the graph model, as for the typed pass
  (ISWIM/proof/Correctness/Graph/SelectCorrect.agda): the X86μ program
  (FPC/Semantics/GraphModel/X86.agda) means exactly what the CFGμ program does
  (≃, FPC/Semantics/GraphModel/CFG.agda), for every CFGμ program.

  The X86μ frame is the CFGμ frame, a slot write binds as CFGμ's seq
  does (it updates the frame in place), and a register write is a
  substitution, so the code selected for a simple expression means it,
  definitionally, up to the tables (sel-≃): callq applies the code and
  environment that load fst and load snd read from the closure's slot,
  as CFGμ's call does, and callq writes strictly, which changes nothing
  before a return or a bind (strict-put). X86μ's case is CFGμ's (a
  pseudo-instruction, where X86ᵀ has testinl, the payload and je, which
  the typed proof shows agree with CFGᵀ's case on a slot that never
  holds both an inl and an inr). What is left is the start of a
  definition, which writes %rdi and %rsi to the slots of its environment
  and argument, where CFGμ has them in its start frame: Λ binds finite
  sets, so this is a β (fin-β), by the monotonicity of CFGμ's tails
  (tail-mono).

-}

module FPC.proof.Correctness.GraphModel.SelectCorrect where

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.Ops using (⋆; Λ; 𝒞; 𝒯; strict; Mono₁;
  Λ-≃; ⋆-≃; Λ-β; 𝒞-≃)
open import proof.Framework.GraphModel.Laws using (strict-≃; ⋆-ne)
open import FPC.Semantics.GraphModel.Ops using (Table; tables; init; _[_≔_];
  start)
open import FPC.proof.Semantics.GraphModel.CFG using (⟦_⟧ᵗ; Meanings; 𝒮; 𝒮-≃;
  tail-mono; blocks-mono; ≔-mono) renaming (code′ to codeᶜ; ⟦_⟧ₚ to ⟦_⟧ᶜ)
import FPC.proof.Semantics.GraphModel.CFG as GC
open import FPC.Semantics.GraphModel.Imp using (𝒜s)
import FPC.Semantics.GraphModel.X86 as X
open import FPC.Language.Type
import FPC.Language.Imp as I
import FPC.Language.CFG as C
open C using (DSig; Args; Tail; return; seq; goto; case; _▷_)
open import FPC.Language.X86 using (Seq; Atm; var; rax; St; called; Inits)
open import FPC.proof.Semantics.GraphModel.Binders using (let-≃; case-≃)
open import FPC.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)
open import Data.Bool using (false)
open import Data.Maybe using (nothing)
open import FPC.Compiler.Select using (Out; ret; to; after; dst; sel; tail;
  atms; def-body; select) renaming (blocks to sel-blocks)
open import Language.Prim using (sub; eq)
open import Framework.Membership using (⊑-∋)

open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (zero; suc; _≟_)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (yes; no)

{- a bind of a finite set of values is a β -}
fin-β : ∀ {G V}
  → Mono₁ G
  → V ≢ []
  → V ≈ V
  → G (mem V) ≃ ⋆ ⟨ Λ ⟨ G , ptt ⟩ , ⟨ mem V , ptt ⟩ ⟩
fin-β {V = V} m ne c =
  ≃-sym (Λ-β m (λ w w∈ → ⟨ V , ⟨ ne , ⟨ (λ _ z → z) , w∈ ⟩ ⟩ ⟩) (≈⇒Con c))


{- The pass -------------------------------------------------------------------}

{- d := D, then K, in CFGμ -}
then : ∀ {Δ} {I J : Inits Δ} {A} → Out I A J → (𝒫 Value → 𝒫 Value) → 𝒫 Value
  → 𝒫 Value
then ret K D = D
then (to x _) K D = ⋆ ⟨ Λ ⟨ K , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

then-ne : ∀ {Δ} {I J : Inits Δ} {A} (o : Out I A J) {K D w}
  → w ∈ then o K D
  → nonempty D
then-ne ret w∈ = ⟨ _ , w∈ ⟩
then-ne (to x _) {K} {D} w∈ = proj₂ (⋆-ne {Λ ⟨ K , ptt ⟩} {D} ⟨ _ , w∈ ⟩)

{- for tables T (of CFGμ) and T' (of X86μ) that agree -}
module _ {Σ : List DSig} {T T' : Table Σ}
  (TT : ∀ {s} (f : Σ ∋ s) → T f ≃ T' f) where

  𝒪s-atms : ∀ {Δ I Δs Γ O F} (as : All (Atm Σ Δ I) Δs) ρ R
    → 𝒜s as T' ρ ≡ X.𝒪s T' (atms {Γ = Γ} {O = O} {F = F} as) ρ R
  𝒪s-atms [] ρ R = refl
  𝒪s-atms (a ∷ as) ρ R = cong (λ r → ⟨ GC.𝒜 a T' ρ , r ⟩) (𝒪s-atms as ρ R)

  module _ {Δ R' Bs} (B' : Meanings {Δ} Bs) where

    {- what k means, after the value of s is in o -}
    Fits : ∀ {I J : Inits Δ} {A} (o : Out I A J) → (𝒫 Value → 𝒫 Value)
      → (∀ {Γ O F} → Seq Σ Δ R' Bs (after o Γ O F)) → Env Value → Set₁
    Fits ret K k ρ =
      ∀ {Γ O F} ρ' R F' → R rax ≃ X.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' ρ' R F'
    Fits (to x _) K k ρ =
      ∀ {Γ O F} X → Con X → ∀ R F'
      → K X ≃ X.⟦_⟧ˢ T' (k {Γ} {O} {F}) B' (ρ [ idx x ≔ X ]) R F'

    put-≃ : ∀ {I J : Inits Δ} {A} (o : Out I A J) {K}
      {k : ∀ {Γ O F} → Seq Σ Δ R' Bs (after o Γ O F)} {ρ D D' Γ O F R F'}
      → Fits o K k ρ
      → D ≃ D'
      → then o K D
        ≃ X.put T' (dst o {Γ} {O} {F}) D' (X.⟦_⟧ˢ T' (k {Γ} {O} {F}) B') ρ R F'
    put-≃ ret f D≃ = ≃-trans D≃ (f _ _ _)
    put-≃ (to x _) {Γ = Γ} {O} {F} {R} {F'} f D≃ =
      let-≃ D≃ λ X _ cX → f {Γ} {O} {F} X cX R F'

    {- a strict write, before a return or a bind -}
    strict-put : ∀ {I J : Inits Δ} {A} (o : Out I A J) {K}
      {k : ∀ {Γ O F} → Seq Σ Δ R' Bs (after o Γ O F)} {ρ D D' Γ O F R F'}
      → Fits o K k ρ
      → D ≃ D'
      → then o K D
        ≃ strict D'
        (X.put T' (dst o {Γ} {O} {F}) D' (X.⟦_⟧ˢ T' (k {Γ} {O} {F}) B') ρ R F')
    strict-put o {K} {k} f D≃ =
      ≃-sym
        (strict-≃ (≃-sym (put-≃ o {K} {k} f D≃))
          (λ w w∈ → then-ne o (proj₂ (put-≃ o {K} {k} f ≃-refl) w w∈)))

    {- the code selected for s into o, then k -}
    sel-≃ : ∀ {I J : Inits Δ} {A} (s : I.Simple Σ Δ I A) (o : Out I A J) {K}
      {k : ∀ {Γ O F} → Seq Σ Δ R' Bs (after o Γ O F)} {ρ Γ O F R F'}
      → Fits o K k ρ
      → then o K (𝒮 s T ρ) ≃ X.⟦_⟧ˢ T' (sel s o k {Γ} {O} {F}) B' ρ R F'
    sel-≃ s@(I.atm a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.pair c e) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.callc (var x i) a) o f = strict-put o f (𝒮-≃ TT s _)
    sel-≃ s@(I.tuple {Δs} as) o {ρ = ρ} {Γ} {O} {F} {R} f =
      put-≃ o f
        (≃-trans (𝒮-≃ TT s ρ)
          (≃-reflexive
            (cong (𝒯 (length Δs)) (𝒪s-atms {Γ = Γ} {O = O} {F = F} as ρ R))))
    sel-≃ s@(I.get j a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.inl a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.inr a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.prim sub a b) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.prim eq a b) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.fold a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.unfold a) o f = put-≃ o f (𝒮-≃ TT s _)

  {- the blocks B (of CFGμ) and B' (of X86μ) agree -}
  BR : ∀ {Δ} {Bs : List (Inits Δ)} → Meanings Bs → Meanings Bs → Set₁
  BR {Bs = Bs} B B' = ∀ {I} (l : Bs ∋ I) ρ → B l ρ ≃ B' l ρ

  tail-≃ : ∀ {Δ R' Bs I} (t : Tail Σ R' Δ Bs I)
    → {B B' : Meanings Bs}
    → BR B B'
    → ∀ ρ → ∀ {Γ O F} R F'
    → ⟦ t ⟧ᵗ T B ρ ≃ X.⟦_⟧ˢ T' (tail t {Γ} {O} {F}) B' ρ R F'
  tail-≃ (return s) {B' = B'} br ρ R F' =
    sel-≃ B' s ret {K = λ X → X} (λ _ _ _ → ≃-refl)
  tail-≃ (seq x s p t) {B} {B'} br ρ R F' =
    sel-≃ B' s (to x p) {K = λ X → ⟦ t ⟧ᵗ T B (ρ [ idx x ≔ X ])}
      (λ X c R F → tail-≃ t br _ R F)
  tail-≃ (goto l) br ρ R F' = br l ρ
  tail-≃ (case (var x i) y z l₁ l₂) br ρ R F' =
    case-≃ (≃-refl {D = ρ (idx x)}) (λ X _ _ → br l₁ (ρ [ idx y ≔ X ]))
      (λ X _ _ → br l₂ (ρ [ idx z ≔ X ]))

  blocks-≃ : ∀ {Δ R' Bs} (bs : C.Blocks Σ R' Δ Bs)
    → BR (GC.blocks bs T) (X.blocks T' (sel-blocks bs))
  blocks-≃ (bs ▷ t) Z ρ = tail-≃ t (blocks-≃ bs) ρ _ _
  blocks-≃ (bs ▷ t) (S l) = blocks-≃ bs l

  {- the code of a definition: its start writes %rdi and %rsi to the
     slots of its environment and argument -}
  code-≃ : ∀ {s} (b : C.Body Σ (DSig.cod s) (Args s))
    → codeᶜ T b ≃ X.codeₜ T' (def-body b)
  code-≃ {s} (C.body Δ p bs t) = Λ-≃ λ V neV cV → Λ-≃ λ W neW cW →
    ≃-trans
      (fin-β {λ X' → E (ι [ e ≔ X' ] [ a ≔ mem W ])}
        (λ X⊆ → mono X⊆ (λ _ z → z)) neV cV)
      (≃-trans
          (let-≃ ≃-refl λ X' _ _ →
            fin-β {λ Y' → E (ι [ e ≔ X' ] [ a ≔ Y' ])} (mono (λ _ z → z))
              neW cW)
        (let-≃ ≃-refl λ X' _ _ →
            let-≃ {F' = λ Y' → x86 (mem V) (mem W) (ι [ e ≔ X' ] [ a ≔ Y' ])}
            (≃-refl {D = mem W}) λ Y' _ _ →
          tail-≃ t (blocks-≃ bs) (ι [ e ≔ X' ] [ a ≔ Y' ]) _ _))
    where
    ι : Env Value
    ι = λ _ → init
    e = idx (⊑-∋ p (S Z))
    a = idx (⊑-∋ p Z)
    E = ⟦ t ⟧ᵗ T (GC.blocks bs T)
    x86 : 𝒫 Value → 𝒫 Value → Env Value → 𝒫 Value
    x86 X Y ρ =
      X.⟦_⟧ˢ T' (tail t {St.rs (called s Δ)} {nothing} {false})
        (X.blocks T' (sel-blocks bs)) ρ (X.args X Y) init
    mono : ∀ {X X' Y Y'}
      → X ⊆ X'
      → Y ⊆ Y'
      → E (ι [ e ≔ X ] [ a ≔ Y ]) ⊆ E (ι [ e ≔ X' ] [ a ≔ Y' ])
    mono X⊆ Y⊆ =
      tail-mono t (blocks-mono bs)
        (≔-mono a (≔-mono e (λ _ _ z → z) X⊆) Y⊆)

{- the tables of definitions agree -}
table-≃ : ∀ {Σ ss} (ds : All (λ s → C.Body Σ (DSig.cod s) (Args s)) ss)
  {s} (f : Σ ∋ s)
  → tables codeᶜ ds f ≃ tables X.codeₜ (All-map def-body ds) f
table-≃ [] f = ≃-refl
table-≃ {ss = _ ∷ ss} (d ∷ ds) f with lvl f ≟ length ss
... | yes _ = code-≃ (table-≃ ds) d
... | no _ = table-≃ ds f

select-correct : ∀ {A} (P : C.Program A) → ⟦ P ⟧ᶜ ≃ X.⟦ select P ⟧ₜ
select-correct (C.program ds (C.body Δ p bs t)) =
  tail-≃ (table-≃ ds) t (blocks-≃ (table-≃ ds) bs) _ _ _
