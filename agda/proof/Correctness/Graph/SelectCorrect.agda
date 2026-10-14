{-

  Select instructions (CFGᵀ → X86ᵀ, Compiler/Select.agda) is correct in
  the graph model: the X86ᵀ program (Semantics/Graph/Typed/X86.agda)
  means exactly what the CFGᵀ program does (≃,
  Semantics/Graph/Typed/CFG.agda), for every CFGᵀ program; the compiler
  to X86ᵀ, Same, is in CompilerCorrect.agda.

  The X86ᵀ frame is the CFGᵀ frame, a slot write binds as CFGᵀ's seq
  does, and a register write is a substitution, so the code selected
  for a simple expression means it, definitionally, up to the tables
  (sel-≃): callq applies the code and environment that load fst and
  load snd read from the closure's slot, as CFGᵀ's call does, and callq
  and chk write strictly, which changes nothing before a return or a
  bind (strict-put). Two things are left.
  * case: testinl, the payload into the slot and je take apart what the
    case of CFGᵀ does at once; they agree on a slot that never holds
    both an inl and an inr (Tagged, Inv, case-core), as every slot,
    bound by Λ to a consistent finite set, does.
  * The start of a definition binds %rdi and %rsi to slots 0 and 1,
    where CFGᵀ has them in its frame: Λ binds finite sets, so this is a
    β (fin-β), by the monotonicity of CFGᵀ's tails (tail-mono).

-}

module proof.Correctness.Graph.SelectCorrect where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops using (⋆; Λ; 𝒞; 𝒯; payloadD; strict; Mono₁; Λ-≃; ⋆-≃; Λ-β)
open import proof.Framework.GraphModel.Laws using (strict-≃; ⋆-ne)
open import proof.Framework.GraphModel.Env using (Env)
open import proof.Semantics.Graph.Typed.Ops using (Table; tables; init)
open import proof.Semantics.Graph.Typed.CFG using (⟦_⟧ᵗ; Meanings; drop; 𝒮; 𝒮-≃; tail-mono; blocks-mono)
  renaming (code′ to codeᶜ; ⟦_⟧ₚ to ⟦_⟧ᶜ)
import proof.Semantics.Graph.Typed.CFG as GC
open import Semantics.Graph.Typed.Imp using (𝒜s)
import Semantics.Graph.Typed.X86 as X
open X using (isinl)
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Language.Typed.Type hiding (_≟_)
import Language.Typed.Imp as I
import Language.Typed.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
open import Language.Typed.X86 using (Seq; Atm; var; rax; St; called)
open import Data.Bool using (false)
open import Data.Maybe using (nothing)
open import Compiler.Select using (Out; ret; to; after; dst; sel; tail; atms; depth; blocks-depth; def-body; select)
  renaming (blocks to sel-blocks)
open import Language.Prim using (sub; eq)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≟_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)
open import Relation.Nullary using (yes; no)

{- Slots ---------------------------------------------------------------------------------}

{- no slot holds both an inl and an inr -}
Tagged : 𝒫 Value → Set
Tagged D = ∀ {u v} → left u ∈ D → right v ∈ D → ⊥

Inv : Env Value → Set
Inv ρ = ∀ i → Tagged (ρ i)

tagged-≈ : ∀ {V} → V ≈ V → Tagged (mem V)
tagged-≈ {V} c l r = ≈⇒Every V V c _ _ l r

inv-drop : ∀ {Δ' Δ : Ctx} (p : Δ' ⊑ Δ) {ρ} → Inv ρ → Inv (drop p ρ)
inv-drop here⊑ i = i
inv-drop (there⊑ p) i = inv-drop p (λ j → i (suc j))

inv-• : ∀ {Δ' Δ : Ctx} (p : Δ' ⊑ Δ) {ρ V} → Inv ρ → V ≈ V → Inv (mem V • drop p ρ)
inv-• p i c zero = tagged-≈ c
inv-• p i c (suc j) = inv-drop p i j

{- case: test, bind the payload, and branch on the flag -}
case-core : ∀ {A : 𝒫 Value} {F₁ F₂ G₁ G₂ : 𝒫 Value → 𝒫 Value} → Tagged A
  → (∀ V → V ≈ V → F₁ (mem V) ≃ G₁ (mem V)) → (∀ V → V ≈ V → F₂ (mem V) ≃ G₂ (mem V))
  → ⋆ ⟨ Λ ⟨ (λ X → 𝒞 ⟨ isinl A , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩) , ptt ⟩ , ⟨ payloadD A , ptt ⟩ ⟩
    ≃ 𝒞 ⟨ A , ⟨ G₁ , ⟨ G₂ , ptt ⟩ ⟩ ⟩
case-core {A} tg F₁≃ F₂≃ = ⟨ G , H ⟩
  where
  G : _
  G w ⟨ [] , ⟨ ⟨ _ , ⟨ ne , _ ⟩ ⟩ , _ ⟩ ⟩ = ⊥-elim (ne refl)
  G w ⟨ v ∷ V , ⟨ ⟨ inj₁ ⟨ f , ⟨ _ , ⟨ fl , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩ , ⟨ _ , c ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with fl f (here refl)
  ... | inj₁ ⟨ u , ⟨ l∈ , _ ⟩ ⟩ =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → lefts (V⊆ d d∈)) , ⟨ proj₁ (F₁≃ (v ∷ V) c) w w∈ , c ⟩ ⟩ ⟩ ⟩
    where
    lefts : ∀ {d} → payloadD A d → left d ∈ A
    lefts (inj₁ l) = l
    lefts (inj₂ r) = ⊥-elim (tg l∈ r)
  ... | inj₂ ⟨ _ , ⟨ _ , () ⟩ ⟩
  G w ⟨ v ∷ V , ⟨ ⟨ inj₂ ⟨ f , ⟨ _ , ⟨ fr , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩ , ⟨ _ , c ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with fr f (here refl)
  ... | inj₂ ⟨ u , ⟨ r∈ , _ ⟩ ⟩ =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → rights (V⊆ d d∈)) , ⟨ proj₁ (F₂≃ (v ∷ V) c) w w∈ , c ⟩ ⟩ ⟩ ⟩
    where
    rights : ∀ {d} → payloadD A d → right d ∈ A
    rights (inj₁ l) = ⊥-elim (tg l r∈)
    rights (inj₂ r) = r
  ... | inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩
  H : _
  H w (inj₁ ⟨ v , ⟨ V , ⟨ l∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ v ∷ V , ⟨ ⟨ inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → inj₁ ⟨ v , ⟨ l∈ v (here refl) , refl ⟩ ⟩ })
                                      , ⟨ proj₂ (F₁≃ (v ∷ V) c) w w∈ , ⟨ tt ∷ [] , tt ⟩ ⟩ ⟩ ⟩ ⟩
                , ⟨ (λ ()) , c ⟩ ⟩
              , ⟨ (λ d d∈ → inj₁ (l∈ d d∈)) , (λ ()) ⟩ ⟩ ⟩
  H w (inj₂ ⟨ v , ⟨ V , ⟨ r∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ v ∷ V , ⟨ ⟨ inj₂ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → inj₂ ⟨ v , ⟨ r∈ v (here refl) , refl ⟩ ⟩ })
                                      , ⟨ proj₂ (F₂≃ (v ∷ V) c) w w∈ , ⟨ tt ∷ [] , tt ⟩ ⟩ ⟩ ⟩ ⟩
                , ⟨ (λ ()) , c ⟩ ⟩
              , ⟨ (λ d d∈ → inj₂ (r∈ d d∈)) , (λ ()) ⟩ ⟩ ⟩

{- a bind of a finite set of values is a β -}
fin-β : ∀ {G V} → Mono₁ G → V ≢ [] → V ≈ V → ⋆ ⟨ Λ ⟨ G , ptt ⟩ , ⟨ mem V , ptt ⟩ ⟩ ≃ G (mem V)
fin-β {V = V} m ne c = Λ-β m (λ w w∈ → ⟨ V , ⟨ ne , ⟨ (λ _ z → z) , w∈ ⟩ ⟩ ⟩) (≈⇒Con c)

{- The pass -------------------------------------------------------------------------------}

{- d := D, then K, in CFGᵀ -}
then : ∀ {n Δ A Δ''} → Out n Δ A Δ'' → (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
then ret K D = D
then (to p _) K D = ⋆ ⟨ Λ ⟨ K , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

then-ne : ∀ {n Δ A Δ''} (o : Out n Δ A Δ'') {K D w} → w ∈ then o K D → nonempty D
then-ne ret w∈ = ⟨ _ , w∈ ⟩
then-ne (to p _) {K} {D} w∈ = proj₂ (⋆-ne {Λ ⟨ K , ptt ⟩} {D} ⟨ _ , w∈ ⟩)

{- for tables T (of X86ᵀ) and T' (of CFGᵀ) that agree -}
module _ {Σ : List ℕ} {T T' : Table Σ} (TT : ∀ {m} (f : Σ ∋ m) → T f ≃ T' f) where

  𝒪s-atms : ∀ {Δ m Γ O F} (as : Vec (Atm Σ Δ Any) m) ρ R → X.𝒪s T (atms {Γ = Γ} {O} {F} as) ρ R ≡ 𝒜s as T ρ
  𝒪s-atms [] ρ R = refl
  𝒪s-atms (a ∷ as) ρ R = cong (λ r → ⟨ GC.𝒜 a T ρ , r ⟩) (𝒪s-atms as ρ R)

  module _ {n Bs} (B : Meanings Bs) where

    {- what k means, after the value of s is in o -}
    Fits : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') → (∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)) → (𝒫 Value → 𝒫 Value) → Env Value → Set₁
    Fits ret k K ρ = ∀ {Γ O F} ρ' R F' → X.⟦_⟧ˢ T (k {Γ} {O} {F}) B ρ' R F' ≃ R rax
    Fits (to p _) k K ρ = ∀ {Γ O F} V → V ≈ V → ∀ R F' → X.⟦_⟧ˢ T (k {Γ} {O} {F}) B (mem V • drop p ρ) R F' ≃ K (mem V)

    put-≃ : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {K ρ D D' Γ O F R F'}
      → Fits o k K ρ → D ≃ D' → X.put T (dst o {Γ} {O} {F}) D (X.⟦_⟧ˢ T (k {Γ} {O} {F}) B) ρ R F' ≃ then o K D'
    put-≃ ret f D≃ = ≃-trans (f _ _ _) D≃
    put-≃ (to p _) {k} {K} {ρ} {Γ = Γ} {O} {F} {R} {F'} f D≃ =
      ⋆-≃ (Λ-≃ {λ X → X.⟦_⟧ˢ T (k {Γ} {O} {F}) B (X • drop p ρ) R F'} {K} (λ V _ c → f {Γ} {O} {F} V c R F')) D≃

    {- a strict write, before a return or a bind -}
    strict-put : ∀ {Δ A Δ''} (o : Out n Δ A Δ'') {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {K ρ D D' Γ O F R F'}
      → Fits o k K ρ → D ≃ D' → strict D (X.put T (dst o {Γ} {O} {F}) D (X.⟦_⟧ˢ T (k {Γ} {O} {F}) B) ρ R F') ≃ then o K D'
    strict-put o {k} f D≃ = strict-≃ (put-≃ o {k} f D≃) (λ w w∈ → then-ne o (proj₁ (put-≃ o {k} f ≃-refl) w w∈))

    {- the code selected for s into o, then k -}
    sel-≃ : ∀ {Δ A Δ''} (s : I.Simple Σ Δ A) (o : Out n Δ A Δ'') {k : ∀ {Γ O F} → Seq Σ n Bs (after o Γ O F)} {K ρ Γ O F R F'}
      → Fits o k K ρ → X.⟦_⟧ˢ T (sel s o k {Γ} {O} {F}) B ρ R F' ≃ then o K (𝒮 s T' ρ)
    sel-≃ s@(I.atm a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.pack c e) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.callc (var x) a) o f = strict-put o f (𝒮-≃ TT s _)
    sel-≃ s@(I.tuple {n = m} as) o {ρ = ρ} {Γ} {O} {F} {R} f =
      put-≃ o f (≃-trans (≃-reflexive (cong (𝒯 m) (𝒪s-atms {Γ = Γ} {O} {F} as ρ R))) (𝒮-≃ TT s ρ))
    sel-≃ s@(I.get j a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.inl a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.inr a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.prim sub a b) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.prim eq a b) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.inject G a) o f = put-≃ o f (𝒮-≃ TT s _)
    sel-≃ s@(I.project t (var x)) o {k} {ρ = ρ} f = strict-put o {k} f (𝒮-≃ TT s ρ)

  {- the blocks B (of X86ᵀ) and B' (of CFGᵀ) agree -}
  BR : ∀ {Bs} → Meanings Bs → Meanings Bs → Set₁
  BR {Bs} B B' = ∀ {Δ} (l : Bs ∋ Δ) ρ → Inv ρ → B l ρ ≃ B' l ρ

  tail-≃ : ∀ {n Bs Δ} (t : Tail Σ Bs Δ) .(le : depth t ≤ n) {B B' : Meanings Bs} → BR B B' → ∀ ρ → Inv ρ
    → ∀ {Γ O F} R F' → X.⟦_⟧ˢ T (tail t le {Γ} {O} {F}) B ρ R F' ≃ ⟦ t ⟧ᵗ T' B' ρ
  tail-≃ (return s) le {B} br ρ i R F' = sel-≃ B s ret {K = λ X → X} (λ _ _ _ → ≃-refl)
  tail-≃ (seq p s t) le {B} {B'} br ρ i R F' =
    sel-≃ B s (to p _) {K = λ X → ⟦ t ⟧ᵗ T' B' (X • drop p ρ)} (λ V c R F → tail-≃ t _ br _ (inv-• p i c) R F)
  tail-≃ (goto l) le br ρ i R F' = br l ρ i
  tail-≃ (case (var x) p l₁ l₂) le {B} {B'} br ρ i R F' =
    case-core {ρ (idx x)} {λ X → B l₁ (X • drop p ρ)} {λ X → B l₂ (X • drop p ρ)} {λ X → B' l₁ (X • drop p ρ)} {λ X → B' l₂ (X • drop p ρ)} (i (idx x))
      (λ V c → br l₁ _ (inv-• p i c)) (λ V c → br l₂ _ (inv-• p i c))

  blocks-≃ : ∀ {n Bs} (bs : C.Blocks Σ Bs) .(le : blocks-depth bs ≤ n) → BR (X.blocks T (sel-blocks bs le)) (GC.blocks bs T')
  blocks-≃ (bs ▷ t) le Z ρ i = tail-≃ t _ (blocks-≃ bs _) ρ i _ _
  blocks-≃ (bs ▷ t) le (S l) = blocks-≃ bs _ l

  {- the code of a definition: its start binds %rdi and %rsi to slots 0 and 1 -}
  code-≃ : ∀ {m} (b : C.Body Σ (Any ∷ ⟪ tup m ⟫ ∷ [])) → X.codeₜ T (def-body b) ≃ codeᶜ T' b
  code-≃ {m} (C.body bs t) = Λ-≃ λ V neV cV → Λ-≃ λ W neW cW →
    ≃-trans (⋆-≃ (Λ-≃ {λ X' → L (λ Y' → x86 (mem V) (mem W) (Y' • X' • ι)) (mem W)} {λ X' → L (λ Y' → E (Y' • X' • ι)) (mem W)}
                   λ V' _ cV' → ⋆-≃ (Λ-≃ {λ Y' → x86 (mem V) (mem W) (Y' • mem V' • ι)} {λ Y' → E (Y' • mem V' • ι)}
                     λ W' _ cW' → tail-≃ t _ (blocks-≃ bs _) (mem W' • mem V' • ι)
                       (λ { zero → tagged-≈ cW' ; (suc zero) → tagged-≈ cV' ; (suc (suc j)) → λ () }) _ _) ≃-refl)
                 ≃-refl)
      (≃-trans (⋆-≃ (Λ-≃ {λ X' → L (λ Y' → E (Y' • X' • ι)) (mem W)} {λ X' → E (mem W • X' • ι)}
                       λ V' _ _ → fin-β {λ Y' → E (Y' • mem V' • ι)} (mono (λ _ z → z)) neW cW) ≃-refl)
        (fin-β {λ X' → E (mem W • X' • ι)} (λ X⊆ → mono X⊆ (λ _ z → z)) neV cV))
    where
    ι : Env Value
    ι = λ _ → init
    E = ⟦ t ⟧ᵗ T' (GC.blocks bs T')
    x86 : 𝒫 Value → 𝒫 Value → Env Value → 𝒫 Value
    x86 X Y ρ = X.⟦_⟧ˢ T (tail t (m≤n⊔m (blocks-depth bs) _) {St.rs (called m)} {nothing} {false})
                  (X.blocks T (sel-blocks bs (m≤m⊔n _ (depth t)))) ρ (X.args X Y) init
    L : (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
    L F D = ⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
    mono : ∀ {X X' Y Y'} → X ⊆ X' → Y ⊆ Y' → E (Y • X • ι) ⊆ E (Y' • X' • ι)
    mono X⊆ Y⊆ = tail-mono t (blocks-mono bs) λ { zero → Y⊆ ; (suc zero) → X⊆ ; (suc (suc j)) → λ _ z → z }

{- the tables of definitions agree -}
table-≃ : ∀ {Σ ns} (ds : All (λ n → C.Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) ns) {m} (f : Σ ∋ m)
  → tables X.codeₜ (All-map def-body ds) f ≃ tables codeᶜ ds f
table-≃ [] f = ≃-refl
table-≃ {ns = _ ∷ ns} (d ∷ ds) f with lvl f ≟ length ns
... | yes _ = code-≃ (table-≃ ds) d
... | no _ = table-≃ ds f

select-correct : ∀ (P : C.Program) → X.⟦ select P ⟧ₜ ≃ ⟦ P ⟧ᶜ
select-correct (C.program ds (C.body bs t)) = tail-≃ (table-≃ ds) t _ (blocks-≃ (table-≃ ds) bs _) _ (λ _ ()) _ _
