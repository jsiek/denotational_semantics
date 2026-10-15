{-

  Select instructions (CFGᵀ → X86ᵀ, Compiler/Select.agda) is correct in
  the graph model with errors: the X86ᵀ program means exactly what the
  CFGᵀ program does (≃), for every CFGᵀ program; the compiler to X86ᵀ,
  Same, is in CompilerCorrect.agda.

  The X86ᵀ frame is the CFGᵀ environment, and both check nothing but
  project, so the code selected for a statement means the statement:
  most instructions mean the operator of the simple expression they
  compute, definitionally (sel-≃). Three things are left.
  * callc: callq applies the code to the environment of a closure, read
    by load fst and load snd from its slot; CFGᵀ binds the closure and
    the argument first, which changes nothing on a slot, a set of values
    (callc-≃).
  * case: testinl, the payload into the slot and je take apart what the
    case of CFGᵀ does at once; they agree on a slot that never holds
    both an inl and an inr (Tagged, case-coreᵗ).
  * The start of a definition binds %rdi and %rsi to slots 0 and 1,
    where CFGᵀ has them in its environment: a let of a finite set of
    values, β (let-fin-β), by the monotonicity of CFGᵀ's semantics.
  callq and chk write their results strictly, as CFGᵀ's let binds them
  (strict-then).

-}

module proof.Correctness.GraphErr.SelectCorrect where

open import proof.Framework.GraphModel.ErrorPrelude
open import proof.Framework.GraphModel.OpsBase using (Mono₁; Finitary)
open import proof.Framework.GraphModel.Ops using (⋆; car; cdr; payloadD; Λ; 𝒞)
open import proof.Semantics.GraphErr.Typed.Clos2 using (caseᵗ-≃)
open import proof.Semantics.GraphErr.Typed.Clos5 using (tm-≃; tbl-map; tbl-con; map-id; tbl)
open import proof.Semantics.GraphErr.Typed.Imp using (letᵗ-≃)
open import proof.Semantics.GraphErr.Typed.CFG using (run-ok; codeᶜ-con)
open import Semantics.GraphErr.Typed.Ops using (init; caseᵗ)
open import Semantics.GraphErr.Typed.Imp using (Table; 𝒮; 𝒜; letᵗ; ⌞_⌟)
import Semantics.GraphErr.Typed.CFG as GC
open GC using (BEnv; drop)
import Semantics.GraphErr.Typed.X86 as GX
open GX using (RegsD; _[_≔_]; args)
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧s[_])
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Mon as M
import Language.Typed.Imp as I
import Language.Typed.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
open import Language.Typed.X86
open import Compiler.Select
open import Language.Prim using (sub; eq)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming (map to All-map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Bool using (Bool; false)
open import Data.Maybe using (Maybe; nothing)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)
open import Relation.Nullary using (¬_)

{- Sets of values ----------------------------------------------------------------}

{- a slot holds a set of values, never both an inl and an inr -}
Tagged : 𝒫 Value → Set
Tagged D = ∀ {u v} → left u ∈ D → right v ∈ D → ⊥

Atom : 𝒫 Value → Set
Atom D = Tagged D × Val D

atom-≈ : ∀ {V} → V ≢ [] → V ≈ V → NoErr V → Atom (mem V)
atom-≈ {V} ne c n = ⟨ (λ l r → ≈⇒Every V V c _ _ l r) , noerr-val V ne n ⟩

{- the binders of the code of a definition, on finite sets of values -}
ΛΛᵐ-⊆ : ∀ {F F' : 𝒫 Value → 𝒫 Value → 𝒫 Value}
  → (∀ V W → V ≢ [] → V ≈ V → NoErr V → W ≢ [] → W ≈ W → NoErr W → F (mem V) (mem W) ⊆ F' (mem V) (mem W))
  → ΛΛᵐ ⟨ F , ptt ⟩ ⊆ ΛΛᵐ ⟨ F' , ptt ⟩
ΛΛᵐ-⊆ h ν r = r
ΛΛᵐ-⊆ {F} {F'} h (V ↦ e) ⟨ ⟨ e∈ , ⟨ ne , c ⟩ ⟩ , ⟨ nV , ve ⟩ ⟩ = ⟨ ⟨ inner e e∈ ve , ⟨ ne , c ⟩ ⟩ , ⟨ nV , ve ⟩ ⟩
  where
  inner : ∀ e → e ∈ Λ ⟨ F (mem V) , ptt ⟩ → ValEntry e → e ∈ Λ ⟨ F' (mem V) , ptt ⟩
  inner ν r _ = r
  inner (W ↦ w) ⟨ w∈ , ⟨ neW , cW ⟩ ⟩ nW = ⟨ h V W ne c nV neW cW nW w w∈ , ⟨ neW , cW ⟩ ⟩
  inner (const k) () _
  inner ω () _
  inner ⦅ u , v ⦆ () _
  inner (tup[ i ] d) () _
  inner (left d) () _
  inner (right d) () _
  inner ⟨⟩ () _

{- G (mem V) is let x = mem V in G x -}
let-fin-β : ∀ {G V} → Mono₁ G → V ≢ [] → V ≈ V → NoErr V → G (mem V) ≃ letᵗ (mem V) G
let-fin-β {G} {V} m ne c nv =
  ≃-trans (≃-sym (letᵐ-β m (λ w w∈ → ⟨ V , ⟨ ne , ⟨ (λ d d∈ → d∈) , w∈ ⟩ ⟩ ⟩) (≈⇒Con c) (noerr-val V ne nv))) (letᵐ-unfold {mem V} {G})

{- a strict write, before a bind of the same set -}
strict-≫= : ∀ {D G} → strictᵐ D (D ≫= G) ≃ (D ≫= G)
strict-≫= = ⟨ (λ { w (inj₁ ⟨ refl , ω∈ ⟩) → inj₁ ⟨ refl , ω∈ ⟩ ; w (inj₂ ⟨ _ , w∈ ⟩) → w∈ })
            , (λ { w (inj₁ ⟨ refl , ω∈ ⟩) → inj₁ ⟨ refl , ω∈ ⟩ ; w (inj₂ ⟨ c , w∈ ⟩) → inj₂ ⟨ c , inj₂ ⟨ c , w∈ ⟩ ⟩ }) ⟩

{- callc: the code of a closure applied to its environment and an argument -}
H : 𝒫 Value → 𝒫 Value → 𝒫 Value
H P X = ⋆ ⟨ ⋆ ⟨ car ⟨ P , ptt ⟩ , ⟨ cdr ⟨ P , ptt ⟩ , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩

H-mono : ∀ {P P' X X'} → P ⊆ P' → X ⊆ X' → H P X ⊆ H P' X'
H-mono P⊆ X⊆ w ⟨ V , ⟨ ⟨ U , ⟨ ⟨ v , pv ⟩ , ⟨ U⊆ , U≢ ⟩ ⟩ ⟩ , ⟨ V⊆ , V≢ ⟩ ⟩ ⟩ =
  ⟨ V , ⟨ ⟨ U , ⟨ ⟨ v , P⊆ _ pv ⟩ , ⟨ (λ d d∈ → ⟨ proj₁ (U⊆ d d∈) , P⊆ _ (proj₂ (U⊆ d d∈)) ⟩) , U≢ ⟩ ⟩ ⟩
      , ⟨ (λ d d∈ → X⊆ d (V⊆ d d∈)) , V≢ ⟩ ⟩ ⟩

callc-≃ : ∀ {P A} → Val P → Val A → (P ≫= λ P' → A ≫= λ X → H P' X) ≃ H P A
callc-≃ {P} {A} vP vA =
  ≃-trans (≫=-val-β {P} {λ P' → A ≫= λ X → H P' X} vP)
    (≃-trans (≫=-val-β {A} {H ⌊ P ⌋} vA)
      ⟨ H-mono (⌊⌋-⊆ {P}) (⌊⌋-⊆ {A}) , H-mono (⌊⌋-clean {P} (proj₁ vP)) (⌊⌋-clean {A} (proj₁ vA)) ⟩)

{- case: test, bind the payload, and branch on the flag -}
case-coreᵗ : ∀ {A : 𝒫 Value} {F₁ F₂ : 𝒫 Value → 𝒫 Value} → Atom A
  → caseᵗ A F₁ F₂
    ≃ letᵗ (A ≫= λ X → payloadD (X ⇂ ValPayload)) (λ X → caseᵗ (A ≫= isinlD) (λ _ → F₁ X) (λ _ → F₂ X))
case-coreᵗ {A} {F₁} {F₂} ⟨ tg , ⟨ cl , ne ⟩ ⟩ = ⟨ bwd , fwd ⟩
  where
  P = A ≫= λ X → payloadD (X ⇂ ValPayload)
  I = A ≫= isinlD
  cA : Conv A
  cA = Val⇒Conv ⟨ cl , ne ⟩
  noω : ¬ (ω ∈ A)
  noω ω∈ = cl ω ω∈ refl

  lefts : ∀ {a} V → left a ∈ A → mem V ⊆ ⌊ P ⌋ → ∀ d → d ∈ mem V → (⌊ A ⌋ ⇂ ValPayload) (left d)
  lefts V la V⊆ d d∈ with V⊆ d d∈
  ... | ⟨ inj₁ ⟨ refl , _ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  ... | ⟨ inj₂ ⟨ _ , inj₁ l ⟩ , _ ⟩ = l
  ... | ⟨ inj₂ ⟨ _ , inj₂ ⟨ ⟨ r , _ ⟩ , _ ⟩ ⟩ , _ ⟩ = ⊥-elim (tg la r)
  rights : ∀ {a} V → right a ∈ A → mem V ⊆ ⌊ P ⌋ → ∀ d → d ∈ mem V → (⌊ A ⌋ ⇂ ValPayload) (right d)
  rights V ra V⊆ d d∈ with V⊆ d d∈
  ... | ⟨ inj₁ ⟨ refl , _ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
  ... | ⟨ inj₂ ⟨ _ , inj₁ ⟨ ⟨ l , _ ⟩ , _ ⟩ ⟩ , _ ⟩ = ⊥-elim (tg l ra)
  ... | ⟨ inj₂ ⟨ _ , inj₂ r ⟩ , _ ⟩ = r

  branch : ∀ V → V ≢ [] → V ≈ V → mem V ⊆ ⌊ P ⌋
    → caseᵗ I (λ _ → F₁ (mem V)) (λ _ → F₂ (mem V)) ⊆ caseᵗ A F₁ F₂
  branch V V≢ c V⊆ w (inj₁ ⟨ refl , inj₁ ⟨ _ , ω∈ ⟩ ⟩) = ⊥-elim (noω ω∈)
  branch V V≢ c V⊆ w (inj₁ ⟨ refl , inj₂ ⟨ _ , inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩ ⟩ ⟩)
  branch V V≢ c V⊆ w (inj₁ ⟨ refl , inj₂ ⟨ _ , inj₂ ⟨ _ , ⟨ _ , () ⟩ ⟩ ⟩ ⟩)
  branch [] V≢ c V⊆ w (inj₂ _) = ⊥-elim (V≢ refl)
  branch (v ∷ V) V≢ c V⊆ w (inj₂ ⟨ _ , inj₁ ⟨ u , ⟨ U , ⟨ ls , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩ ⟩) with ls u (here refl)
  ... | ⟨ ⟨ inj₂ ⟨ _ , inj₁ ⟨ a , ⟨ la , refl ⟩ ⟩ ⟩ , _ ⟩ , _ ⟩ =
    inj₂ ⟨ cA , inj₁ ⟨ v , ⟨ V , ⟨ lefts (v ∷ V) (proj₁ la) V⊆ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩ ⟩
  ... | ⟨ ⟨ inj₂ ⟨ _ , inj₂ ⟨ _ , ⟨ _ , () ⟩ ⟩ ⟩ , _ ⟩ , _ ⟩
  ... | ⟨ ⟨ inj₁ ⟨ () , _ ⟩ , _ ⟩ , _ ⟩
  branch (v ∷ V) V≢ c V⊆ w (inj₂ ⟨ _ , inj₂ ⟨ u , ⟨ U , ⟨ rs , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩ ⟩) with rs u (here refl)
  ... | ⟨ ⟨ inj₂ ⟨ _ , inj₂ ⟨ a , ⟨ ra , refl ⟩ ⟩ ⟩ , _ ⟩ , _ ⟩ =
    inj₂ ⟨ cA , inj₂ ⟨ v , ⟨ V , ⟨ rights (v ∷ V) (proj₁ ra) V⊆ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩ ⟩
  ... | ⟨ ⟨ inj₂ ⟨ _ , inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩ ⟩ , _ ⟩ , _ ⟩
  ... | ⟨ ⟨ inj₁ ⟨ () , _ ⟩ , _ ⟩ , _ ⟩

  fwd : letᵗ P (λ X → caseᵗ I (λ _ → F₁ X) (λ _ → F₂ X)) ⊆ caseᵗ A F₁ F₂
  fwd w (inj₁ ⟨ refl , inj₁ ⟨ _ , ω∈ ⟩ ⟩) = ⊥-elim (noω ω∈)
  fwd w (inj₁ ⟨ refl , inj₂ ⟨ _ , inj₁ ⟨ _ , ω≢ ⟩ ⟩ ⟩) = ⊥-elim (ω≢ refl)
  fwd w (inj₁ ⟨ refl , inj₂ ⟨ _ , inj₂ ⟨ _ , ω≢ ⟩ ⟩ ⟩) = ⊥-elim (ω≢ refl)
  fwd w (inj₂ ⟨ _ , ⟨ V , ⟨ ⟨ ⟨ w∈ , ⟨ V≢ , c ⟩ ⟩ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ ⟩) = branch V V≢ c V⊆ w w∈

  bwd : caseᵗ A F₁ F₂ ⊆ letᵗ P (λ X → caseᵗ I (λ _ → F₁ X) (λ _ → F₂ X))
  bwd w (inj₁ ⟨ _ , ω∈ ⟩) = ⊥-elim (noω ω∈)
  bwd w (inj₂ ⟨ _ , inj₁ ⟨ v , ⟨ V , ⟨ ls , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ ⟨ v , pv (here refl) ⟩ , ⟨ v ∷ V , ⟨ ⟨ ⟨ g , ⟨ (λ ()) , c ⟩ ⟩ , nV ⟩ , ⟨ (λ d d∈ → pv d∈) , (λ ()) ⟩ ⟩ ⟩ ⟩
    where
    pv : ∀ {d} → d ∈ mem (v ∷ V) → d ∈ ⌊ P ⌋
    pv d∈ = ⟨ inj₂ ⟨ cA , inj₁ (ls _ d∈) ⟩ , proj₂ (ls _ d∈) ⟩
    nV : NoErr (v ∷ V)
    nV ω∈ = proj₂ (ls ω ω∈) refl
    tag : left ⟨⟩ ∈ I
    tag = inj₂ ⟨ cA , inj₁ ⟨ v , ⟨ proj₁ (ls v (here refl)) , refl ⟩ ⟩ ⟩
    g : w ∈ caseᵗ I (λ _ → F₁ (mem (v ∷ V))) (λ _ → F₂ (mem (v ∷ V)))
    g = inj₂ ⟨ ⟨ left ⟨⟩ , ⟨ tag , (λ ()) ⟩ ⟩
             , inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ tag , (λ ()) ⟩ , (λ ()) ⟩ }) , ⟨ w∈ , ≈-single ⟩ ⟩ ⟩ ⟩ ⟩
  bwd w (inj₂ ⟨ _ , inj₂ ⟨ v , ⟨ V , ⟨ rs , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ ⟨ v , pv (here refl) ⟩ , ⟨ v ∷ V , ⟨ ⟨ ⟨ g , ⟨ (λ ()) , c ⟩ ⟩ , nV ⟩ , ⟨ (λ d d∈ → pv d∈) , (λ ()) ⟩ ⟩ ⟩ ⟩
    where
    pv : ∀ {d} → d ∈ mem (v ∷ V) → d ∈ ⌊ P ⌋
    pv d∈ = ⟨ inj₂ ⟨ cA , inj₂ (rs _ d∈) ⟩ , proj₂ (rs _ d∈) ⟩
    nV : NoErr (v ∷ V)
    nV ω∈ = proj₂ (rs ω ω∈) refl
    tag : right ⟨⟩ ∈ I
    tag = inj₂ ⟨ cA , inj₂ ⟨ v , ⟨ proj₁ (rs v (here refl)) , refl ⟩ ⟩ ⟩
    g : w ∈ caseᵗ I (λ _ → F₁ (mem (v ∷ V))) (λ _ → F₂ (mem (v ∷ V)))
    g = inj₂ ⟨ ⟨ right ⟨⟩ , ⟨ tag , (λ ()) ⟩ ⟩
             , inj₂ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ tag , (λ ()) ⟩ , (λ ()) ⟩ }) , ⟨ w∈ , ≈-single ⟩ ⟩ ⟩ ⟩ ⟩

{- Frames ---------------------------------------------------------------------}

drop-idx : ∀ {Δ' Δ A} (p : Δ' ⊑ Δ) (ρ : Env Value) (y : Δ' ∋ A) → drop p ρ (idx y) ≡ ρ (idx (⊑-∋ p y))
drop-idx here⊑ ρ y = refl
drop-idx (there⊑ p) ρ y = drop-idx p (λ i → ρ (suc i)) y

{- each slot of the frame holds a set of values, never both an inl and an inr -}
Inv : Ctx → Env Value → Set
Inv Δ ρ = ∀ {A} (x : Δ ∋ A) → Atom (ρ (idx x))

inv-• : ∀ {Δ' Δ A ρ X} (p : Δ' ⊑ Δ) → Inv Δ ρ → Atom X → Inv (A ∷ Δ') (X • drop p ρ)
inv-• p i aX Z = aX
inv-• {ρ = ρ} p i aX (S y) = subst Atom (sym (drop-idx p ρ y)) (i (⊑-∋ p y))

{- The pass -------------------------------------------------------------------}

{- d := D, then K -}
then : ∀ {n Δ A Δ''} → Out n Δ A Δ'' → (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
then ret K D = D
then (to p _) K D = letᵗ D K

then-≃ : ∀ {n Δ A Δ''} (o : Out n Δ A Δ'') {K D D'} → D ≃ D' → then o K D ≃ then o K D'
then-≃ ret D≃ = D≃
then-≃ (to p _) {K} D≃ = letᵗ-≃ {F = K} {K} D≃ (λ _ _ _ _ → ≃-refl)

strict-then : ∀ {n Δ A Δ''} (o : Out n Δ A Δ'') {K C} → strictᵐ C (then o K C) ≃ then o K C
strict-then ret = strictᵐ-self ≃-refl
strict-then (to p _) {K} {C} = strict-≫= {C} {λ X → ⋆ ⟨ Λᵐ ⟨ K , ptt ⟩ , ⟨ X , ptt ⟩ ⟩}

{- for tables T (of CFGᵀ) and T' (of X86ᵀ) that agree -}
module _ {Σ : List ℕ} {T T' : Table} (TT : ∀ k → T k ≃ T' k) where

  𝒮-≃ : ∀ {Δ A} (s : I.Simple Σ Δ A) ρ → 𝒮 s T ρ ≃ 𝒮 s T' ρ
  𝒮-≃ s ρ = tm-≃ TT M.⌜ ⌞ s ⌟ ⌝ (λ _ → ≃-refl)

  𝒪s-atms : ∀ {Δ m Γ O F} (as : Vec (Atm Σ Δ Any) m) ρ R → ⟦ M.⌜ as ⌝ᵛ ⟧s[ T' ] ρ ≡ GX.𝒪s T' (atms {Γ = Γ} {O} {F} as) ρ R
  𝒪s-atms [] ρ R = refl
  𝒪s-atms (a ∷ as) ρ R = cong (λ r → ⟨ 𝒜 a T' ρ , r ⟩) (𝒪s-atms as ρ R)

  module _ {n Bs} (B : BEnv Bs) where

    {- K means what k does, after the value of s is in o -}
    Fits : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') → (𝒫 Value → 𝒫 Value) → (∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)) → Env Value → Set₁
    Fits ret K k ρ = ∀ {Γ O F} ρ' R F' → R rax ≃ GX.⟦_⟧ˢ T' (k {Γ} {O} {F}) B ρ' R F'
    Fits (to p _) K k ρ = ∀ {Γ O F} X → Atom X → ∀ R F' → K X ≃ GX.⟦_⟧ˢ T' (k {Γ} {O} {F}) B (X • drop p ρ) R F'

    put-≃ : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') {K : 𝒫 Value → 𝒫 Value} {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {ρ : Env Value} {D D' : 𝒫 Value} {Γ : Regs} {O : Maybe (Δ ∋ ⟪ fun ⟫)} {F : Bool} {R : RegsD} {F' : 𝒫 Value} → Fits o K k ρ → D ≃ D'
      → then o K D ≃ GX.put {Σ} T' (dst o {Γ} {O} {F}) D' (GX.⟦_⟧ˢ T' (k {Γ} {O} {F}) B) ρ R F'
    put-≃ ret {K} {k} {ρ} {D} {D'} {Γ} {O} {F} {R} {F'} f D≃ = ≃-trans D≃ (f {Γ} {O} {F} ρ (R [ rax ≔ D' ]) F')
    put-≃ (to p _) {K} {k} {ρ} {Γ = Γ} {O} {F} {R} {F'} f D≃ =
      letᵗ-≃ {F = K} {λ X → GX.⟦_⟧ˢ T' (k {Γ} {O} {F}) B (X • drop p ρ) R F'} D≃
        (λ V ne c nv → f {Γ} {O} {F} (mem V) (atom-≈ ne c nv) R F')

    putˢ-≃ : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') {K : 𝒫 Value → 𝒫 Value} {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {ρ : Env Value} {D D' : 𝒫 Value} {Γ : Regs} {O : Maybe (Δ ∋ ⟪ fun ⟫)} {F : Bool} {R : RegsD} {F' : 𝒫 Value} → Fits o K k ρ → D ≃ D'
      → then o K D ≃ GX.putˢ {Σ} T' (dst o {Γ} {O} {F}) D' (GX.⟦_⟧ˢ T' (k {Γ} {O} {F}) B) ρ R F'
    putˢ-≃ ret {K} {k} {ρ} {D} {D'} {Γ} {O} {F} {R} {F'} f D≃ =
      ≃-trans (≃-sym (strictᵐ-self {D} {D} ≃-refl)) (strictᵐ-≃ {D} {D'} {D} {E} D≃ (put-≃ ret {K} {k = λ {Γ₀} {O₀} {F₀} → k {Γ₀} {O₀} {F₀}} {ρ} {D} {D'} {Γ} {O} {F} {R} {F'} f D≃))
      where E = GX.⟦_⟧ˢ T' (k {Γ} {O} {F}) B ρ (R [ rax ≔ D' ]) F'
    putˢ-≃ (to p lt) {K} {k} {ρ} {D} {D'} {Γ} {O} {F} {R} {F'} f D≃ = put-≃ (to p lt) {K} {λ {Γ₀} {O₀} {F₀} → k {Γ₀} {O₀} {F₀}} {ρ} {D} {D'} {Γ} {O} {F} {R} {F'} f D≃

    {- the code selected for s into o, then k -}
    sel-≃ : ∀ {Δ A Δ''} (s : I.Simple Σ Δ A) (o : Out n Δ A Δ'') {K} {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {ρ Γ O F R F'} → Fits o K k ρ → Inv Δ ρ
      → then o K (𝒮 s T' ρ) ≃ GX.⟦_⟧ˢ T' (sel s o k {Γ} {O} {F}) B ρ R F'
    sel-≃ (I.atm a) o f i = put-≃ o f ≃-refl
    sel-≃ (I.pack c e) o f i = put-≃ o f ≃-refl
    sel-≃ (I.callc (var x) (var y)) o {K} {k} {ρ} f i =
      ≃-trans (then-≃ o (callc-≃ (proj₂ (i x)) (proj₂ (i y))))
        (≃-trans (≃-sym (strict-then o {K} {C})) (strictᵐ-≃ {C} {C} ≃-refl (put-≃ o {K} {k} {ρ} {C} {C} f ≃-refl)))
      where C = H (ρ (idx x)) (ρ (idx y))
    sel-≃ (I.tuple {n = m} as) o {ρ = ρ} {Γ} {O} {F} {R} f i = put-≃ o f (≃-reflexive (cong (𝒯ᵐ m) (𝒪s-atms {Γ = Γ} {O} {F} as ρ R)))
    sel-≃ (I.get j a) o f i = put-≃ o f ≃-refl
    sel-≃ (I.inl a) o f i = put-≃ o f ≃-refl
    sel-≃ (I.inr a) o f i = put-≃ o f ≃-refl
    sel-≃ (I.prim sub a b) o f i = put-≃ o f ≃-refl
    sel-≃ (I.prim eq a b) o f i = put-≃ o f ≃-refl
    sel-≃ (I.inject G a) o f i = put-≃ o f ≃-refl
    sel-≃ (I.project t (var x)) o f i = putˢ-≃ o f ≃-refl

  {- the blocks B (of CFGᵀ) and B' (of X86ᵀ) agree -}
  BR : ∀ {Bs} → BEnv Bs → BEnv Bs → Set₁
  BR {Bs} B B' = ∀ {Δ} (l : Bs ∋ Δ) ρ → Inv Δ ρ → B l ρ ≃ B' l ρ

  tail-≃ : ∀ {n Bs Δ} (t : Tail Σ Bs Δ) .(le : depth t ≤ n) {B B' : BEnv Bs} → BR B B' → ∀ ρ → Inv Δ ρ
    → ∀ {Γ O F} R F' → GC.⟦ t ⟧ᵗ T B ρ ≃ GX.⟦_⟧ˢ T' (tail t le {Γ} {O} {F}) B' ρ R F'
  tail-≃ (return s) le {B' = B'} br ρ i R F' = ≃-trans (𝒮-≃ s ρ) (sel-≃ B' s ret {K = λ X → X} (λ _ R _ → ≃-refl) i)
  tail-≃ (seq p s t) le {B} {B'} br ρ i R F' =
    ≃-trans (letᵗ-≃ {F = K} {K} (𝒮-≃ s ρ) (λ _ _ _ _ → ≃-refl))
      (sel-≃ B' s (to p _) {K = K} (λ X aX R F → tail-≃ t _ br (X • drop p ρ) (inv-• p i aX) R F) i)
    where K = λ X → GC.⟦ t ⟧ᵗ T B (X • drop p ρ)
  tail-≃ (goto l) le br ρ i R F' = br l ρ i
  tail-≃ (case (var x) p l₁ l₂) le {B} {B'} br ρ i R F' =
    ≃-trans (caseᵗ-≃ {F = F₁} {F₁'} {F₂} {F₂'} ≃-refl (λ V ne c nv → br l₁ _ (inv-• p i (atom-≈ ne c nv)))
                                                    (λ V ne c nv → br l₂ _ (inv-• p i (atom-≈ ne c nv))))
      (case-coreᵗ {F₁ = F₁'} {F₂'} (i x))
    where F₁ = λ X → B l₁ (X • drop p ρ)
          F₂ = λ X → B l₂ (X • drop p ρ)
          F₁' = λ X → B' l₁ (X • drop p ρ)
          F₂' = λ X → B' l₂ (X • drop p ρ)

  blocks-≃ : ∀ {n Bs} (bs : C.Blocks Σ Bs) .(le : blocks-depth bs ≤ n) → BR (GC.blocks bs T) (GX.blocks T' (blocks bs le))
  blocks-≃ (bs ▷ t) le Z ρ i = tail-≃ t _ (blocks-≃ bs _) ρ i _ _
  blocks-≃ (bs ▷ t) le (S l) = blocks-≃ bs _ l

  {- the code of a definition: its start binds %rdi and %rsi to slots 0 and 1 -}
  code-≃ : (∀ k → Con (T k)) → ∀ {m} (b : C.Body Σ (Any ∷ ⟪ tup m ⟫ ∷ [])) → GC.codeᶜ T b ≃ GX.codeₜ T' (def-body b)
  code-≃ TC {m} b@(C.body bs t) = ⟨ ΛΛᵐ-⊆ (λ V W a₁ a₂ a₃ a₄ a₅ a₆ → proj₁ (body≃ V W a₁ a₂ a₃ a₄ a₅ a₆))
                               , ΛΛᵐ-⊆ (λ V W a₁ a₂ a₃ a₄ a₅ a₆ → proj₂ (body≃ V W a₁ a₂ a₃ a₄ a₅ a₆)) ⟩
    where
    E = GC.run b T
    mE = proj₁ (run-ok TC b)
    body≃ : ∀ V W → V ≢ [] → V ≈ V → NoErr V → W ≢ [] → W ≈ W → NoErr W
      → E (mem W • mem V • λ _ → init) ≃ GX.run T' (def-body b) (λ _ → init) (args (mem V) (mem W)) init
    body≃ V W neV cV nV neW cW nW =
      ≃-trans (let-fin-β {G = λ X' → E (Y • X' • ι)}
                 (λ X⊆ → mE (λ { zero → λ _ z → z ; (suc zero) → X⊆ ; (suc (suc i)) → λ _ z → z })) neV cV nV)
        (≃-trans (letᵗ-≃ {F = λ X' → E (Y • X' • ι)} {λ X' → letᵗ Y (λ Y' → E (Y' • X' • ι))} ≃-refl (λ V' _ _ _ →
                   let-fin-β {G = λ Y' → E (Y' • mem V' • ι)} (λ Y⊆ → mE (λ { zero → Y⊆ ; (suc i) → λ _ z → z })) neW cW nW))
          (letᵗ-≃ {F = λ X' → letᵗ Y (λ Y' → E (Y' • X' • ι))} {λ X' → letᵗ Y (λ Y' → x86 (Y' • X' • ι))} ≃-refl
             λ V' neV' cV' nV' → letᵗ-≃ {F = λ Y' → E (Y' • mem V' • ι)} {λ Y' → x86 (Y' • mem V' • ι)} ≃-refl
               λ W' neW' cW' nW' → tail-≃ t le₂ (blocks-≃ bs le₁) (mem W' • mem V' • ι)
                                     (λ { Z → atom-≈ neW' cW' nW' ; (S Z) → atom-≈ neV' cV' nV' }) (args X Y) init))
      where
      X = mem V
      Y = mem W
      ι : Env Value
      ι = λ _ → init
      le₁ = m≤m⊔n (blocks-depth bs) (depth t)
      le₂ = m≤n⊔m (blocks-depth bs) (depth t)
      x86 : Env Value → 𝒫 Value
      x86 ρ' = GX.⟦_⟧ˢ T' (tail t le₂ {St.rs (called m)} {nothing} {false}) (GX.blocks T' (blocks bs le₁)) ρ' (args X Y) init

{- the tables of definitions agree -}
table-≃ : ∀ {Σ} (ds : All (λ m → C.Body Σ (Any ∷ ⟪ tup m ⟫ ∷ [])) Σ) k
  → tbl (GC.codeᶜ {Σ}) ds k ≃ tbl (GX.codeₜ {Σ}) (All-map def-body ds) k
table-≃ {Σ} ds k =
  subst (λ ds' → tbl (GC.codeᶜ {Σ}) ds' k ≃ tbl (GX.codeₜ {Σ}) (All-map def-body ds) k) (map-id ds)
    (tbl-map (λ T → ∀ k → Con (T k)) (λ x → x) def-body (λ ds → tbl-con (λ TC d → codeᶜ-con TC d) (All-map (λ x → x) ds))
       (λ TT TC d → code-≃ TT TC d) ds k)

select-correct : ∀ (P : C.Program) → GC.⟦ P ⟧ᶜ ≃ GX.⟦ select P ⟧ₜ
select-correct (C.program ds (C.body bs t)) =
  tail-≃ (table-≃ ds) t _ (blocks-≃ (table-≃ ds) bs _) (λ _ → init) (λ ()) _ _
