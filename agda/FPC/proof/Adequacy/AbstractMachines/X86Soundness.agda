{-

  Soundness of the X86μ machine (Mu/Semantics/AbstractMachines/X86.agda) with
  respect to the graph model (Mu/Semantics/GraphModel/X86.agda), as for X86ᵀ
  (proof/Adequacy/X86Soundness.agda): what the machine computes is in
  the denotation of the program, for a table that is consistent (cT)
  and contains the code of each definition interpreted with the whole
  table (closed), as the table of a compiled program does
  (X86Compiled.agda): the machine runs a definition with the whole
  table, the semantics with the table of the older ones.

  Each state denotes a set of values (𝒮) that a step can only shrink
  (back), the call stack being its continuation (𝒦), and a location (a
  register or a slot, numbered as in 𝓛) denotes not the whole meaning
  𝒱 v of the value v it holds (GlobalFunValues.agda) but a finite part of it
  (an approximation, Apx), as the semantics binds a slot to a finite set
  and calls code on finite parts of %rdi and %rsi. A step that writes v
  is matched by approximating, before the step, the operands it reads by
  enough of their values to compute the part of v written (Grow, put-⊆),
  one element at a time (grow-each), and by the monotonicity of the
  semantics (seq-mono). A call makes, from the callee's approximation,
  the entries X ↦ (Y ↦ w) of the code that the caller applies (call-⊆).
  case binds the payload of the injection in its slot, as a slot write
  does, and takes the branch of 𝒞 for its side.

  load snd reads the environment of the open closure, which the machine
  keeps apart from its slot: in the states that the machine reaches,
  it is the closure's (Inv, OpR, which back also shows a step keeps).
  Typed code reads no unset register and no unset flag: those hold no
  part (∅). fold and unfold (↑, ↓) are the identity on denotations.

-}

open import Data.List using (List)
open import Mu.Language.X86
open import Mu.Framework.AllUtil using (All; lookup)
open import Framework.Membership using (_∋_)
open import proof.Framework.GraphModel.SetsAsPredicates using (_⊆_)
open import Mu.proof.Semantics.GraphModel.Ops using (ConT; tables)
open import Mu.Semantics.GraphModel.X86 using (codeₜ)

module Mu.proof.Adequacy.AbstractMachines.X86Soundness {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ)
  (cT : ConT (tables codeₜ ds)) (closed : ∀ {s} (f : Σ ∋ s) → codeₜ (tables codeₜ ds) (lookup ds f) ⊆ tables codeₜ ds f) where

open import Language.Prim using (sub; eq)
open import Mu.Language.Type hiding (_[_])
open import Framework.Primitives using (Int)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres)
open import proof.Framework.GraphModel.Domain using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _•_; ■; Con⇒≈)
  renaming (const to dconst)
open import proof.Framework.GraphModel.Ops
  using (⋆; Λ; 𝒞; nthD; ⋆-mono; Λ-mono; pair-mono; 𝒯-mono; inl-mono; inr-mono; car-mono; cdr-mono; 𝒞-mono)
  renaming (car to carD; cdr to cdrD; proj to projD)
open import proof.Framework.GraphModel.Env using (Env; _⊆ₑ_; •-~)
open import proof.Semantics.Graph.Prim using (primD; primD-mono)
open import Mu.proof.Semantics.GraphModel.Ops using (Table; init)
open import Mu.proof.Semantics.GraphModel.CFG using (Meanings; drop; drop-mono; 𝒜-mono)
open import Mu.Semantics.GraphModel.X86 using (⟦_⟧ⁱ; ⟦_⟧ˢ; ⟦_⟧ₜ; 𝒪; 𝒪s; object; called-regs; RegsD; Kont)
  renaming (put to putₛ; _[_≔_] to _[_≔ₛ_]; args to argsₛ; blocks to blocksₛ; run to runₛ)
open import Mu.Semantics.AbstractMachines.X86
open import Semantics.Observation using (Obs; Answer)
open import proof.Semantics.CEK.Smallstep using (Star; Terminates; Next; next; stop)
open import Framework.Lookup using (forget)
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Mu.Framework.AllUtil using ([]; _∷_; pos)
open import Mu.proof.Adequacy.AbstractMachines.X86Common ds
open import Mu.proof.Adequacy.AbstractMachines.GlobalFunValues using (module Den; pair-inv; inl-inv; inr-inv; 𝒯L[]-inv)
open import Mu.proof.Adequacy.Tuples using (At; 𝒯L; At-length)

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using ([]; _∷_; _++_; map; replicate; length)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Relation.Nullary using (does)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

T : Table Σ
T = tables codeₜ ds

T-ν : ∀ {s} (f : Σ ∋ s) → ν ∈ T f
T-ν f = closed f ν tt

open Den T cT T-ν public

⊆r : ∀ {D : 𝒫 Value} → D ⊆ D
⊆r _ z = z

∅⊆ : ∀ {D E : 𝒫 Value} → D ⊆ ∅ → D ⊆ E
∅⊆ h d d∈ = ⊥-elim (h d d∈)

{- Monotonicity of the semantics in the frame, the registers and the flag -----------}

_⊆ᵣ_ : RegsD → RegsD → Set
R ⊆ᵣ R' = ∀ r → R r ⊆ R' r

MonoK : Kont → Set₁
MonoK κ = ∀ {ρ ρ' R R' F F'} → ρ ⊆ₑ ρ' → R ⊆ᵣ R' → F ⊆ F' → κ ρ R F ⊆ κ ρ' R' F'

≔-mono : ∀ r {R R' D D'} → R ⊆ᵣ R' → D ⊆ D' → (R [ r ≔ₛ D ]) ⊆ᵣ (R' [ r ≔ₛ D' ])
≔-mono rax h D⊆ = λ { rax → D⊆ ; rdi → h rdi ; rsi → h rsi }
≔-mono rdi h D⊆ = λ { rax → h rax ; rdi → D⊆ ; rsi → h rsi }
≔-mono rsi h D⊆ = λ { rax → h rax ; rdi → h rdi ; rsi → D⊆ }

primD-⊆ : ∀ p {D D' E E'} → D ⊆ D' → E ⊆ E' → primD p ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ primD p ⟨ D' , ⟨ E' , ptt ⟩ ⟩
primD-⊆ p D⊆ E⊆ = lower (primD-mono p _ _ ⟨ lift D⊆ , ⟨ lift E⊆ , ptt ⟩ ⟩)

projₛ-mono : ∀ {Δ : Ctx} {A} (i : Δ ∋ A) {D D'} → D ⊆ D' → projD (pos i) ⟨ D , ptt ⟩ ⊆ projD (pos i) ⟨ D' , ptt ⟩
projₛ-mono i D⊆ d = D⊆ (tup[ pos i ] d)

module _ {ρ ρ' : Env Value} {R R' : RegsD} (s : ρ ⊆ₑ ρ') (h : R ⊆ᵣ R') where

  𝒪-mono : ∀ {ψ τ} (a : Arg Σ ψ τ) → 𝒪 T a ρ R ⊆ 𝒪 T a ρ' R'
  𝒪-mono (atom a) = 𝒜-mono s a
  𝒪-mono (reg r _) = h r
  𝒪-mono (a ↑) = 𝒪-mono a
  𝒪-mono (a ↓) = 𝒪-mono a

  𝒪s-mono : ∀ {ψ Δ} (as : All (λ A → Arg Σ ψ (ty A)) Δ) → results-rel-pres _⊆_ (replicate (length Δ) ■) (𝒪s T as ρ R) (𝒪s T as ρ' R')
  𝒪s-mono [] = ptt
  𝒪s-mono (a ∷ as) = ⟨ lift (𝒪-mono a) , 𝒪s-mono as ⟩

  object-mono : ∀ {ψ A} (o : Obj Σ ψ A) → object T o ρ R ⊆ object T o ρ' R'
  object-mono (pair c e) = lower (pair-mono _ _ ⟨ lift (𝒪-mono c) , ⟨ lift (𝒪-mono e) , ptt ⟩ ⟩)
  object-mono (tuple as) = lower (𝒯-mono _ _ _ (𝒪s-mono as))
  object-mono (inl a) = lower (inl-mono _ _ ⟨ lift (𝒪-mono a) , ptt ⟩)
  object-mono (inr a) = lower (inr-mono _ _ ⟨ lift (𝒪-mono a) , ptt ⟩)

put-mono : ∀ {n ψ τ ψ'} (d : Dst n ψ τ ψ') {D D' κ ρ ρ' R R' F F'} → D ⊆ D' → MonoK κ → ρ ⊆ₑ ρ' → R ⊆ᵣ R' → F ⊆ F'
  → putₛ T d D κ ρ R F ⊆ putₛ T d D' κ ρ' R' F'
put-mono (reg r) D⊆ mκ s h f = mκ s (≔-mono r h D⊆) f
put-mono (slot p _) D⊆ mκ s h f =
  lower (⋆-mono _ _ ⟨ Λ-mono _ _ ⟨ (λ X Y X⊆ → lift (mκ (•-~ _⊆_ (drop-mono p s) X⊆) h f)) , ptt ⟩ , ⟨ lift D⊆ , ptt ⟩ ⟩)

instr-mono : ∀ {n ψ ψ'} (i : Instr Σ n ψ ψ') {κ} → MonoK κ → MonoK (⟦_⟧ⁱ T i κ)
instr-mono (movq a d) mκ s h f = put-mono d (𝒪-mono s h a) mκ s h f
instr-mono (subq a r _) mκ s h f = mκ s (≔-mono r h (primD-⊆ sub (h r) (𝒪-mono s h a))) f
instr-mono (cmpq a₂ a₁) mκ s h f = mκ s h (primD-⊆ eq (𝒪-mono s h a₁) (𝒪-mono s h a₂))
instr-mono (sete d) mκ s h f = put-mono d f mκ s h f
instr-mono (alloc o d) mκ s h f = put-mono d (object-mono s h o) mκ s h f
instr-mono (load i a d) mκ s h f = put-mono d (projₛ-mono i (𝒪-mono s h a)) mκ s h f
instr-mono (loadfst x r) mκ s h f = mκ s (≔-mono r h (lower (car-mono _ _ ⟨ lift (s (idx x)) , ptt ⟩))) f
instr-mono (loadsnd {x = opened x} r) mκ s h f = mκ s (≔-mono r h (lower (cdr-mono _ _ ⟨ lift (s _) , ptt ⟩))) f
instr-mono (callq a _ _) mκ s h f w ⟨ ⟨ u , u∈ ⟩ , w∈ ⟩ =
  ⟨ ⟨ u , C⊆ u u∈ ⟩ , mκ s (λ { rax → C⊆ ; rdi → ⊆r ; rsi → ⊆r }) ⊆r w w∈ ⟩
  where C⊆ = lower (⋆-mono _ _ ⟨ ⋆-mono _ _ ⟨ lift (𝒪-mono s h a) , ⟨ lift (h rdi) , ptt ⟩ ⟩ , ⟨ lift (h rsi) , ptt ⟩ ⟩)

MonoB : ∀ {Bs : List Ctx} → Meanings Bs → Set₁
MonoB {Bs} B = ∀ {Δ} (l : Bs ∋ Δ) {ρ ρ'} → ρ ⊆ₑ ρ' → B l ρ ⊆ B l ρ'

seq-mono : ∀ {n Rt Bs ψ} (k : Seq Σ n Rt Bs ψ) {B : Meanings Bs} → MonoB B → MonoK (⟦_⟧ˢ T k B)
seq-mono (i ∷ k) mB = instr-mono i (seq-mono k mB)
seq-mono (retq _) mB s h f = h rax
seq-mono (jmp l) mB s h f = mB l s
seq-mono (case x p _ l₁ l₂) mB s h f = lower (𝒞-mono _ _ ⟨ lift (s (idx x))
  , ⟨ (λ X Y X⊆ → lift (mB l₁ (•-~ _⊆_ (drop-mono p s) X⊆))) , ⟨ (λ X Y X⊆ → lift (mB l₂ (•-~ _⊆_ (drop-mono p s) X⊆))) , ptt ⟩ ⟩ ⟩)

blocks-mono : ∀ {n Rt Bs} (bs : Blocks Σ n Rt Bs) → MonoB (blocksₛ T bs)
blocks-mono (bs ▷ k) Z s = seq-mono k (blocks-mono bs) s (λ _ → ⊆r) ⊆r
blocks-mono (bs ▷ k) (S l) = blocks-mono bs l

K : ∀ {n Rt Bs ψ} → Seq Σ n Rt Bs ψ → Blocks Σ n Rt Bs → Kont
K k bs = ⟦_⟧ˢ T k (blocksₛ T bs)

K-mono : ∀ {n Rt Bs ψ} (k : Seq Σ n Rt Bs ψ) bs → MonoK (K k bs)
K-mono k bs = seq-mono k (blocks-mono bs)

{- a jump runs the block, from its frame -}
blocks-at : ∀ {n Rt Bs Δ} (bs : Blocks Σ n Rt Bs) (l : Bs ∋ Δ) {ρ}
  → K (Blk.start (block bs l)) (Blk.blocks (block bs l)) ρ (λ _ → init) init ⊆ blocksₛ T bs l ρ
blocks-at (bs ▷ k) Z = ⊆r
blocks-at (bs ▷ k) (S l) = blocks-at bs l

{- Approximations ---------------------------------------------------------------------}

{- what a register holds -}
𝒱ᵐ : ∀ {η} m → MV Σ η m → 𝒫 Value
𝒱ᵐ (just (ty A)) v = 𝒱 v
𝒱ᵐ (just (codeα A B)) v = 𝒱 v
𝒱ᵐ (just tupα) v = 𝒱 v
𝒱ᵐ nothing v = ∅

𝒱ʳ-ne : ∀ {η} τ (v : RV Σ η τ) → nonempty (𝒱ᵐ (just τ) v)
𝒱ʳ-ne (ty A) v = 𝒱-ne v
𝒱ʳ-ne (codeα A B) v = 𝒱-ne v
𝒱ʳ-ne tupα v = 𝒱-ne v

cast-𝒱 : ∀ {η m τ} (e : m ≡ just τ) {v : MV Σ η m} → 𝒱ᵐ (just τ) (cast e v) ⊆ 𝒱ᵐ m v
cast-𝒱 refl = ⊆r

forget-𝒱 : ∀ {η η'} m {v : MV Σ η m} → 𝒱ᵐ {η'} (forgetα m) (forgetᵥ m v) ⊆ 𝒱ᵐ m v
forget-𝒱 (just (ty A)) = ⊆r
forget-𝒱 (just (codeα A B)) = λ _ ()
forget-𝒱 (just tupα) = λ _ ()
forget-𝒱 nothing = λ _ ()

{- the locations of a machine: %rax, %rdi and %rsi at 0, 1 and 2, slot i at 3 + i -}
ix : Reg → ℕ
ix rax = 0
ix rdi = 1
ix rsi = 2

ix<3 : ∀ r i → suc (suc (suc i)) ≢ ix r
ix<3 rax i ()
ix<3 rdi i ()
ix<3 rsi i ()

𝓛 : ∀ {η Γ Δ} → RegVals Σ η Γ → Frame Σ Δ → ℕ → 𝒫 Value
𝓛 {Γ = Γ} ρ φ 0 = 𝒱ᵐ (Regs.ax Γ) (RegVals.ax ρ)
𝓛 {Γ = Γ} ρ φ 1 = 𝒱ᵐ (Regs.di Γ) (RegVals.di ρ)
𝓛 {Γ = Γ} ρ φ 2 = 𝒱ᵐ (Regs.si Γ) (RegVals.si ρ)
𝓛 ρ φ (suc (suc (suc i))) = 𝓔 φ i

{- after r := v, the other locations are unchanged -}
upd-𝓛 : ∀ r {η Γ Δ τ} {ρ : RegVals Σ η Γ} {φ : Frame Σ Δ} {v : MV Σ η τ}
  → (∀ l → l ≢ ix r → 𝓛 (_[_≔_] {τ = τ} ρ r v) φ l ⊆ 𝓛 ρ φ l) × 𝓛 (_[_≔_] {τ = τ} ρ r v) φ (ix r) ⊆ 𝒱ᵐ τ v
upd-𝓛 rax = ⟨ (λ { 0 ne → ⊥-elim (ne refl) ; 1 _ → ⊆r ; 2 _ → ⊆r ; (suc (suc (suc i))) _ → ⊆r }) , ⊆r ⟩
upd-𝓛 rdi = ⟨ (λ { 0 _ → ⊆r ; 1 ne → ⊥-elim (ne refl) ; 2 _ → ⊆r ; (suc (suc (suc i))) _ → ⊆r }) , ⊆r ⟩
upd-𝓛 rsi = ⟨ (λ { 0 _ → ⊆r ; 1 _ → ⊆r ; 2 ne → ⊥-elim (ne refl) ; (suc (suc (suc i))) _ → ⊆r }) , ⊆r ⟩

wipe-𝓛 : ∀ {η η' Γ Δ} {ρ : RegVals Σ η Γ} {φ : Frame Σ Δ} l → 𝓛 (wipeᵣ {η' = η'} ρ) φ l ⊆ 𝓛 ρ φ l
wipe-𝓛 {Γ = rt a b c} = λ { 0 → forget-𝒱 a ; 1 → forget-𝒱 b ; 2 → forget-𝒱 c ; (suc (suc (suc i))) → ⊆r }

{- a finite part of each location -}
Apx : Set
Apx = ℕ → List Value

σ̂ : Apx → Env Value
σ̂ A i = mem (A (suc (suc (suc i))))

ρ̂ : Apx → RegsD
ρ̂ A r = mem (A (ix r))

AL : ∀ {η ψ} → Apx → Mach Σ η ψ → Set
AL A m = ∀ l → mem (A l) ⊆ 𝓛 (regs m) (frame m) l

Ext : Apx → Apx → Set
Ext A B = ∀ l → mem (A l) ⊆ mem (B l)

σ̂E : ∀ {A B} → Ext A B → σ̂ A ⊆ₑ σ̂ B
σ̂E E i = E (suc (suc (suc i)))

ρ̂E : ∀ {A B} → Ext A B → ρ̂ A ⊆ᵣ ρ̂ B
ρ̂E E r = E (ix r)

one : ∀ {d} {D : 𝒫 Value} → d ∈ D → mem (d ∷ []) ⊆ D
one d∈ _ (here refl) = d∈

{- a nonempty finite part of X -}
ext : ∀ {X : 𝒫 Value} → List Value → nonempty X → List Value
ext W ne = W ++ proj₁ ne ∷ []

ext-⊆ : ∀ {X} W (ne : nonempty X) → mem W ⊆ X → mem (ext W ne) ⊆ X
ext-⊆ W ne W⊆ d d∈ with ∈-++⁻ W d∈
... | inj₁ d∈W = W⊆ d d∈W
... | inj₂ (here refl) = proj₂ ne

ext-ne : ∀ {X} W (ne : nonempty X) → ext W ne ≢ []
ext-ne [] ne ()
ext-ne (_ ∷ W) ne ()

add : Apx → ℕ → List Value → Apx
add A l W l' with l' ≟ l
... | yes _ = A l' ++ W
... | no _ = A l'

clear : Apx → ℕ → Apx
clear A l l' with l' ≟ l
... | yes _ = []
... | no _ = A l'

clear-≢ : ∀ {A l l'} → l' ≢ l → mem (A l') ⊆ mem (clear A l l')
clear-≢ {A} {l} {l'} ne with l' ≟ l
... | yes e = ⊥-elim (ne e)
... | no _ = ⊆r

{- r := D, the other registers growing -}
upd : ∀ r {A' A : Apx} {D} → (∀ l → l ≢ ix r → mem (A' l) ⊆ mem (A l)) → mem (A' (ix r)) ⊆ D → ρ̂ A' ⊆ᵣ (ρ̂ A [ r ≔ₛ D ])
upd rax E h = λ { rax → h ; rdi → E 1 (λ ()) ; rsi → E 2 (λ ()) }
upd rdi E h = λ { rax → E 0 (λ ()) ; rdi → h ; rsi → E 2 (λ ()) }
upd rsi E h = λ { rax → E 0 (λ ()) ; rdi → E 1 (λ ()) ; rsi → h }

{- the slots before a write of slot p, from those after it -}
undrop : ∀ {Δ' Δ : Ctx} → Δ' ⊑ Δ → (ℕ → List Value) → ℕ → List Value
undrop here⊑ f = f
undrop (there⊑ p) f zero = []
undrop (there⊑ p) f (suc i) = undrop p f i

undrop-AL : ∀ {Δ' Δ} (p : Δ' ⊑ Δ) {f} {φ : Frame Σ Δ} → (∀ j → mem (f j) ⊆ 𝓔 (forget p φ) j) → ∀ i → mem (undrop p f i) ⊆ 𝓔 φ i
undrop-AL here⊑ h = h
undrop-AL (there⊑ p) {φ = v ∷ φ} h zero = λ _ ()
undrop-AL (there⊑ p) {φ = v ∷ φ} h (suc i) = undrop-AL p h i

drop-undrop : ∀ {Δ' Δ} (p : Δ' ⊑ Δ) f → (λ j → mem (f j)) ⊆ₑ drop p (λ i → mem (undrop p f i))
drop-undrop here⊑ f j = ⊆r
drop-undrop (there⊑ p) f = drop-undrop p f

und : ∀ {Δ' Δ : Ctx} → Δ' ⊑ Δ → Apx → Apx
und p A' = λ { 0 → A' 0 ; 1 → A' 1 ; 2 → A' 2 ; (suc (suc (suc i))) → undrop p (λ j → A' (suc (suc (suc (suc j))))) i }

und-AL : ∀ {Δ' Δ A η Γ} (p : Δ' ⊑ Δ) {A'} {ρ : RegVals Σ η Γ} {φ : Frame Σ Δ} {v : Val Σ A}
  → (∀ l → mem (A' l) ⊆ 𝓛 ρ (v ∷ forget p φ) l) → ∀ l → mem (und p A' l) ⊆ 𝓛 ρ φ l
und-AL p al' = λ { 0 → al' 0 ; 1 → al' 1 ; 2 → al' 2 ; (suc (suc (suc i))) → undrop-AL p (λ j → al' (suc (suc (suc (suc j))))) i }

{- a jump, from a state with no register and no flag -}
jump : ∀ {n Rt Bs Δ} (bs : Blocks Σ n Rt Bs) (l : Bs ∋ Δ) {A' : Apx} {η'} {φ : Frame Σ Δ}
  → (∀ l' → mem (A' l') ⊆ 𝓛 {η'} {unset} (rv tt tt tt) φ l')
  → K (Blk.start (block bs l)) (Blk.blocks (block bs l)) (σ̂ A') (ρ̂ A') ∅ ⊆ blocksₛ T bs l (σ̂ A')
jump bs l al' u u∈ = blocks-at bs l u
  (K-mono (Blk.start (block bs l)) (Blk.blocks (block bs l)) (λ _ → ⊆r) (λ { rax → ∅⊆ (al' 0) ; rdi → ∅⊆ (al' 1) ; rsi → ∅⊆ (al' 2) }) (λ _ ()) u u∈)

unset-AL : ∀ {A' : Apx} {η η' Γ Δ} {ρ : RegVals Σ η Γ} {φ : Frame Σ Δ}
  → (∀ l → mem (A' l) ⊆ 𝓛 {η'} {unset} (rv tt tt tt) φ l) → ∀ l → mem (A' l) ⊆ 𝓛 ρ φ l
unset-AL al' = λ { 0 → ∅⊆ (al' 0) ; 1 → ∅⊆ (al' 1) ; 2 → ∅⊆ (al' 2) ; (suc (suc (suc i))) → al' _ }

{- Values -}
int∈ : (v : Val Σ (base Int)) → dconst (int v) ∈ 𝒱 v
int∈ (const k) = ⟨ refl , refl ⟩

prim-in : ∀ p {n m D E} → mem (dconst n ∷ []) ⊆ D → mem (dconst m ∷ []) ⊆ E → 𝒱 (δᵀ {Σ} p n m) ⊆ primD p ⟨ D , ⟨ E , ptt ⟩ ⟩
prim-in p {n} {m} n∈ m∈ d d∈ = ⟨ n , ⟨ m , ⟨ n∈ _ (here refl) , ⟨ m∈ _ (here refl) , proj₂ (proj₂ (proj₂ (proj₂ (prim-⊆ p n m d d∈)))) ⟩ ⟩ ⟩ ⟩

unfold-𝒱 : ∀ {A} (v : Val Σ (μ A)) → 𝒱 (unfoldᵥ v) ⊆ 𝒱 v
unfold-𝒱 (fold v) = ⊆r

{- the environment of the open closure is the second component of its slot -}
snd-𝒱 : ∀ {Δ A B} {φ : Frame Σ Δ} {x : Δ ∋ A ⇒ B} {η o z} → OpR φ (just (opened x)) η o
  → z ∈ 𝒱 o → Σ[ c ∈ Value ] ⦅ c , z ⦆ ∈ 𝒱 (lookup φ x)
snd-𝒱 {φ = φ} {x} agree = snd (lookup φ x)
  where snd : ∀ (v : Val Σ _) {z} → z ∈ 𝒱 (env-of v) → Σ[ c ∈ Value ] ⦅ c , z ⦆ ∈ 𝒱 v
        snd (pack c e) z∈ = ⟨ proj₁ (𝒱-ne c) , ⟨ proj₂ (𝒱-ne c) , z∈ ⟩ ⟩

put-inv : ∀ {n ψ τ ψ'} (d : Dst n ψ τ ψ') {η} {m : Mach Σ η ψ} {v} → OpR (frame m) (St.op ψ) η (envα m)
  → OpR (frame (put d v m)) (St.op ψ') η (envα (put d v m))
put-inv (reg r) i = i
put-inv (slot p _) i = none

{- Growing an approximation, from A₀, so that P holds -}
record Grow {η ψ} (m : Mach Σ η ψ) (P : Apx → Set) : Set where
  constructor grow
  field grown : ∀ A₀ → AL A₀ m → Σ[ A ∈ Apx ] AL A m × Ext A₀ A × P A
open Grow

module _ {η ψ} {m : Mach Σ η ψ} where

  grow-at : ∀ l W → mem W ⊆ 𝓛 (regs m) (frame m) l → Grow m (λ A → mem W ⊆ mem (A l))
  grow-at l W W⊆ = grow λ A₀ al → ⟨ add A₀ l W , ⟨ al′ A₀ al , ⟨ ext′ A₀ , here′ A₀ ⟩ ⟩ ⟩
    where
    al′ : ∀ A₀ → AL A₀ m → AL (add A₀ l W) m
    al′ A₀ al l' with l' ≟ l
    ... | yes refl = λ d d∈ → [ al l d , W⊆ d ]′ (∈-++⁻ (A₀ l) d∈)
      where open import Data.Sum using ([_,_]′)
    ... | no _ = al l'
    ext′ : ∀ A₀ → Ext A₀ (add A₀ l W)
    ext′ A₀ l' with l' ≟ l
    ... | yes _ = λ d d∈ → ∈-++⁺ˡ d∈
    ... | no _ = ⊆r
    here′ : ∀ A₀ → mem W ⊆ mem (add A₀ l W l)
    here′ A₀ with l ≟ l
    ... | yes _ = λ d d∈ → ∈-++⁺ʳ (A₀ l) d∈
    ... | no ne = ⊥-elim (ne refl)

  {- P, then Q -}
  both : ∀ {P Q : Apx → Set} → Grow m P → (∀ {A B} → Ext A B → P A → P B) → Grow m Q → Grow m (λ A → P A × Q A)
  both g mP g' = grow λ A₀ al → let ⟨ A₁ , ⟨ al₁ , ⟨ E₁ , p ⟩ ⟩ ⟩ = grown g A₀ al ; ⟨ A₂ , ⟨ al₂ , ⟨ E₂ , q ⟩ ⟩ ⟩ = grown g' A₁ al₁
    in ⟨ A₂ , ⟨ al₂ , ⟨ (λ l d d∈ → E₂ l d (E₁ l d d∈)) , ⟨ mP E₂ p , q ⟩ ⟩ ⟩ ⟩

  _⊳_ : ∀ {P Q : Apx → Set} → Grow m P → (∀ {A} → P A → Q A) → Grow m Q
  g ⊳ f = grow λ A₀ al → let ⟨ A , ⟨ al′ , ⟨ E , p ⟩ ⟩ ⟩ = grown g A₀ al in ⟨ A , ⟨ al′ , ⟨ E , f p ⟩ ⟩ ⟩

  {- a finite part of D, one element at a time -}
  grow-each : ∀ (D : Apx → 𝒫 Value) → (∀ {A B} → Ext A B → D A ⊆ D B) → ∀ V
    → (∀ z → z ∈ mem V → Grow m (λ A → z ∈ D A)) → Grow m (λ A → mem V ⊆ D A)
  grow-each D mD [] h = grow λ A₀ al → ⟨ A₀ , ⟨ al , ⟨ (λ _ → ⊆r) , (λ _ ()) ⟩ ⟩ ⟩
  grow-each D mD (z ∷ V) h = both (h z (here refl)) (λ E → mD E _) (grow-each D mD V (λ z' z'∈ → h z' (there z'∈)))
    ⊳ λ { ⟨ z∈ , V⊆ ⟩ → λ { _ (here refl) → z∈ ; d (there d∈) → V⊆ d d∈ } }

  {- the operand a -}
  grow-arg : ∀ {τ} (a : Arg Σ ψ τ) W → mem W ⊆ 𝒱ᵐ (just τ) (arg a m) → Grow m (λ A → mem W ⊆ 𝒪 T a (σ̂ A) (ρ̂ A))
  grow-arg (atom (var x)) W W⊆ = grow-at _ W (λ d d∈ → 𝓔-lookup (frame m) x d (W⊆ d d∈))
  grow-arg (atom (lit B c)) W W⊆ = grow λ A₀ al → ⟨ A₀ , ⟨ al , ⟨ (λ _ → ⊆r) , W⊆ ⟩ ⟩ ⟩
  grow-arg (atom (ref f)) W W⊆ = grow λ A₀ al → ⟨ A₀ , ⟨ al , ⟨ (λ _ → ⊆r) , W⊆ ⟩ ⟩ ⟩
  grow-arg (reg r e) W W⊆ = grow-at (ix r) W (λ d d∈ → at r d (cast-𝒱 e d (W⊆ d d∈)))
    where
    at : ∀ r → 𝒱ᵐ (St.rs ψ ‹ r ›) (regs m ⦅ r ⦆) ⊆ 𝓛 (regs m) (frame m) (ix r)
    at rax = ⊆r
    at rdi = ⊆r
    at rsi = ⊆r
  grow-arg (a ↑) = grow-arg a
  grow-arg (a ↓) W W⊆ = grow-arg a W (λ d d∈ → unfold-𝒱 (arg a m) d (W⊆ d d∈))

  {- an element of an object -}
  grow-obj : ∀ {A} (o : Obj Σ ψ A) z → z ∈ 𝒱 (obj o m) → Grow m (λ A → z ∈ object T o (σ̂ A) (ρ̂ A))
  grow-obj (pair c e) z z∈ with pair-inv z z∈
  ... | ⟨ u , ⟨ u' , ⟨ refl , ⟨ u∈ , u'∈ ⟩ ⟩ ⟩ ⟩ =
    both (grow-arg c (u ∷ []) λ { _ (here refl) → u∈ }) (λ E h → λ d d∈ → 𝒪-mono (σ̂E E) (ρ̂E E) c d (h d d∈))
         (grow-arg e (u' ∷ []) λ { _ (here refl) → u'∈ })
    ⊳ λ { ⟨ h , h' ⟩ → ⟨ h u (here refl) , h' u' (here refl) ⟩ }
  grow-obj (inl a) z z∈ with inl-inv z z∈
  ... | ⟨ u , ⟨ refl , u∈ ⟩ ⟩ = grow-arg a (u ∷ []) (λ { _ (here refl) → u∈ }) ⊳ λ h → h u (here refl)
  grow-obj (inr a) z z∈ with inr-inv z z∈
  ... | ⟨ u , ⟨ refl , u∈ ⟩ ⟩ = grow-arg a (u ∷ []) (λ { _ (here refl) → u∈ }) ⊳ λ h → h u (here refl)
  grow-obj (tuple []) ⟨⟩ _ = grow λ A₀ al → ⟨ A₀ , ⟨ al , ⟨ (λ _ → ⊆r) , tt ⟩ ⟩ ⟩
  grow-obj (tuple as) (tup[ i ] x) ⟨ a , _ ⟩ with trans (sym (At-length i _ x a)) (len𝒱v (args as m))
  grow-obj (tuple []) (tup[ () ] x) _ | refl
  grow-obj (tuple (b ∷ bs)) (tup[ i ] x) ⟨ a , _ ⟩ | refl =
    both (prime (b ∷ bs)) (λ E ne k → let ⟨ d , d∈ ⟩ = ne k in ⟨ d , nth-mono (σ̂E E) (ρ̂E E) (b ∷ bs) k d d∈ ⟩) (comp (b ∷ bs) i x a)
    ⊳ λ { ⟨ ne , x∈ ⟩ → ⟨ refl , ⟨ x∈ , ne ⟩ ⟩ }
    where
    nth-mono : ∀ {ρ ρ' R R'} → ρ ⊆ₑ ρ' → R ⊆ᵣ R' → ∀ {Δ} (as : All (λ A → Arg Σ ψ (ty A)) Δ) k
      → nthD (𝒪s T as ρ R) k ⊆ nthD (𝒪s T as ρ' R') k
    nth-mono s h (a ∷ as) zero = 𝒪-mono s h a
    nth-mono s h (a ∷ as) (suc k) = nth-mono s h as k
    prime : ∀ {Δ} (as : All (λ A → Arg Σ ψ (ty A)) Δ) → Grow m (λ A → ∀ k → nonempty (nthD (𝒪s T as (σ̂ A) (ρ̂ A)) k))
    prime [] = grow λ A₀ al → ⟨ A₀ , ⟨ al , ⟨ (λ _ → ⊆r) , (λ ()) ⟩ ⟩ ⟩
    prime (a ∷ as) = both (grow-arg a _ (one (proj₂ (𝒱-ne (arg a m))))) (λ E h d d∈ → 𝒪-mono (σ̂E E) (ρ̂E E) a d (h d d∈)) (prime as)
      ⊳ λ { ⟨ h , ne ⟩ → λ { zero → ⟨ _ , h _ (here refl) ⟩ ; (suc k) → ne k } }
    comp : ∀ {Δ} (as : All (λ A → Arg Σ ψ (ty A)) Δ) (i : Fin (length Δ)) x → At i (𝒱v (args as m)) x
      → Grow m (λ A → x ∈ nthD (𝒪s T as (σ̂ A) (ρ̂ A)) i)
    comp (a ∷ as) zero x ⟨ _ , x∈ ⟩ = grow-arg a _ (one x∈) ⊳ λ h → h x (here refl)
    comp (a ∷ as) (suc i) x a′ = comp as i x a′
  grow-obj (tuple as) (dconst k) ()
  grow-obj (tuple as) (V ↦ w) ()
  grow-obj (tuple as) ν ()
  grow-obj (tuple as) ω ()
  grow-obj (tuple as) ⦅ u , v ⦆ ()
  grow-obj (tuple as) (left d) ()
  grow-obj (tuple as) (right d) ()
  grow-obj (tuple (_ ∷ _)) ⟨⟩ ()

  {- an element of a component of a tuple -}
  grow-load : ∀ {Δ B} (i : Δ ∋ B) (a : Arg Σ ψ (ty (tup Δ))) z → z ∈ 𝒱 (lookup (elems (arg a m)) i)
    → Grow m (λ A → z ∈ projD (pos i) ⟨ 𝒪 T a (σ̂ A) (ρ̂ A) , ptt ⟩)
  grow-load i a z z∈ = gw (arg a m) z∈ (grow-arg a)
    where
    gw : ∀ (v : Val Σ (tup _)) → z ∈ 𝒱 (lookup (elems v) i)
      → (∀ W → mem W ⊆ 𝒱 v → Grow m (λ A → mem W ⊆ 𝒪 T a (σ̂ A) (ρ̂ A))) → Grow m (λ A → z ∈ projD (pos i) ⟨ 𝒪 T a (σ̂ A) (ρ̂ A) , ptt ⟩)
    gw (tup ws) z∈ g = g _ (one ⟨ At-lookup i ws z∈ , 𝒱v-ne ws ⟩) ⊳ λ h → h _ (here refl)

{- The denotations of states ------------------------------------------------------------}

𝓕 : ∀ {f} → Flag Σ f → 𝒫 Value
𝓕 {true} b = 𝒱 (bit {Σ} b)
𝓕 {false} _ = ∅

{- the call stack: a caller runs its rest with the result in %rax -}
𝒦 : ∀ {B} → Stack Σ B → 𝒫 Value → 𝒫 Value
𝒦 halt D = D
𝒦 (retK k bs φ σ) D z = Σ[ A ∈ Apx ] Σ[ W ∈ List Value ] σ̂ A ⊆ₑ 𝓔 φ × mem W ⊆ D × W ≢ []
  × z ∈ 𝒦 σ (K k bs (σ̂ A) (called-regs (mem W)) init)

𝒮 : State Σ → 𝒫 Value
𝒮 (run k bs σ η m) z = Σ[ A ∈ Apx ] AL A m × z ∈ 𝒦 σ (K k bs (σ̂ A) (ρ̂ A) (𝓕 (flag m)))

𝒦-mono : ∀ {B} (σ : Stack Σ B) {D E} → D ⊆ E → 𝒦 σ D ⊆ 𝒦 σ E
𝒦-mono halt D⊆ = D⊆
𝒦-mono (retK k bs φ σ) D⊆ z ⟨ A , ⟨ W , ⟨ fr , ⟨ W⊆ , r ⟩ ⟩ ⟩ ⟩ = ⟨ A , ⟨ W , ⟨ fr , ⟨ (λ d d∈ → D⊆ d (W⊆ d d∈)) , r ⟩ ⟩ ⟩ ⟩

{- the open closure agrees with its slot -}
Inv : State Σ → Set
Inv (run {ψ = ψ} k bs σ η m) = OpR (frame m) (St.op ψ) η (envα m)

nn : ∀ {P Q R : Apx → Set} → Σ[ A ∈ Apx ] P A × Q A × R A → Σ[ A ∈ Apx ] P A × R A
nn ⟨ A , ⟨ p , ⟨ _ , r ⟩ ⟩ ⟩ = ⟨ A , ⟨ p , r ⟩ ⟩

{- Writes ------------------------------------------------------------------------------------}

{- r := v, after the other registers are made ρ' -}
reg-⊆ : ∀ {n Rt Bs η η' Γ Γ' Δ O O' F τ} (r : Reg) {k : Seq Σ n Rt Bs (st (Γ' [ r ↦ just τ ]) Δ O' F)} {bs σ}
  {m : Mach Σ η (st Γ Δ O F)} {ρ' : RegVals Σ η' Γ'} {o' : Opened Σ η' O'} {v : RV Σ η' τ} (D : Apx → 𝒫 Value)
  → (∀ l → 𝓛 ρ' (frame m) l ⊆ 𝓛 (regs m) (frame m) l)
  → (∀ W → mem W ⊆ 𝒱ᵐ (just τ) v → Grow m (λ A → mem W ⊆ D A))
  → 𝒮 (run k bs σ η' ⟨ _[_≔_] {τ = just τ} ρ' r v , frame m , o' , flag m ⟩)
    ⊆ λ z → Σ[ A ∈ Apx ] AL A m × nonempty (D A) × z ∈ 𝒦 σ (K k bs (σ̂ A) (ρ̂ A [ r ≔ₛ D A ]) (𝓕 (flag m)))
reg-⊆ {τ = τ} r {k} {bs} {σ} {m = m} {v = v} D h g z ⟨ A' , ⟨ al' , z∈ ⟩ ⟩
    with grown (g (ext (A' (ix r)) (𝒱ʳ-ne τ v)) (ext-⊆ (A' (ix r)) (𝒱ʳ-ne τ v) (λ d d∈ → proj₂ (upd-𝓛 r) d (al' (ix r) d d∈)))) (clear A' (ix r)) al₀
  where
  al₀ : AL (clear A' (ix r)) m
  al₀ l with l ≟ ix r
  ... | yes _ = λ _ ()
  ... | no ne = λ d d∈ → h l d (proj₁ (upd-𝓛 r) l ne d (al' l d d∈))
... | ⟨ A , ⟨ al , ⟨ E , W⊆ ⟩ ⟩ ⟩ =
  ⟨ A , ⟨ al , ⟨ ne-mem (ext-ne _ (𝒱ʳ-ne τ v)) W⊆
  , 𝒦-mono σ (K-mono k bs (λ i → E′ _ (ix<3 r i)) (upd r E′ (λ d d∈ → W⊆ d (∈-++⁺ˡ d∈))) ⊆r) z z∈ ⟩ ⟩ ⟩
  where
  E′ : ∀ l → l ≢ ix r → mem (A' l) ⊆ mem (A l)
  E′ l ne d d∈ = E l d (clear-≢ ne d d∈)

{- d := v -}
put-⊆ : ∀ {n Rt Bs ψ τ ψ'} (d : Dst n ψ τ ψ') {k : Seq Σ n Rt Bs ψ'} {bs σ η} {m : Mach Σ η ψ} {v : RV Σ η τ} (D : Apx → 𝒫 Value)
  → (∀ W → mem W ⊆ 𝒱ᵐ (just τ) v → Grow m (λ A → mem W ⊆ D A))
  → 𝒮 (run k bs σ η (put d v m))
    ⊆ λ z → Σ[ A ∈ Apx ] AL A m × nonempty (D A) × z ∈ 𝒦 σ (putₛ T d (D A) (K k bs) (σ̂ A) (ρ̂ A) (𝓕 (flag m)))
put-⊆ (reg r) {k} {bs} {σ} {m = m} {v} D g = reg-⊆ r {k} {bs} {σ} {m} {regs m} {envα m} {v} D (λ _ → ⊆r) g
put-⊆ (slot {A = A₁} p _) {k} {bs} {σ} {m = m} {v} D g z ⟨ A' , ⟨ al' , z∈ ⟩ ⟩
    with grown (g (ext (A' 3) (𝒱-ne v)) (ext-⊆ (A' 3) (𝒱-ne v) (al' 3))) (und p A') (und-AL p al')
... | ⟨ A , ⟨ al , ⟨ E , W⊆ ⟩ ⟩ ⟩ =
  ⟨ A , ⟨ al , ⟨ ne-mem (ext-ne _ (𝒱-ne v)) W⊆
  , 𝒦-mono σ (λ u u∈ → ⟨ ext (A' 3) (𝒱-ne v) , ⟨ ⟨ K-mono k bs fr (λ { rax → E 0 ; rdi → E 1 ; rsi → E 2 }) ⊆r u u∈
                                            , ⟨ ext-ne _ (𝒱-ne v) , Con⇒≈ _ (𝒱-con v) (ext-⊆ (A' 3) (𝒱-ne v) (al' 3)) ⟩ ⟩
                                          , ⟨ W⊆ , ext-ne _ (𝒱-ne v) ⟩ ⟩ ⟩) z z∈ ⟩ ⟩ ⟩
  where
  fr : σ̂ A' ⊆ₑ (mem (ext (A' 3) (𝒱-ne v)) • drop p (σ̂ A))
  fr zero d d∈ = ∈-++⁺ˡ d∈
  fr (suc j) d d∈ = drop-mono p (σ̂E E) j d (drop-undrop p _ j d d∈)

{- the flag := b -}
flag-⊆ : ∀ {n Rt Bs Γ Δ O F} {k : Seq Σ n Rt Bs (st Γ Δ O true)} {bs σ η} {m : Mach Σ η (st Γ Δ O F)} b (G : Apx → 𝒫 Value)
  → Grow m (λ A → 𝒱 (bit b) ⊆ G A)
  → 𝒮 (run k bs σ η ⟨ regs m , frame m , envα m , b ⟩) ⊆ λ z → Σ[ A ∈ Apx ] AL A m × z ∈ 𝒦 σ (K k bs (σ̂ A) (ρ̂ A) (G A))
flag-⊆ {k = k} {bs} {σ} b G g z ⟨ A' , ⟨ al' , z∈ ⟩ ⟩ with grown g A' al'
... | ⟨ A , ⟨ al , ⟨ E , F⊆ ⟩ ⟩ ⟩ = ⟨ A , ⟨ al , 𝒦-mono σ (K-mono k bs (σ̂E E) (ρ̂E E) F⊆) z z∈ ⟩ ⟩

{- Calls and returns -----------------------------------------------------------------------}

{- callq: the callee's approximation gives the entries X ↦ (Y ↦ w) of the
   code that the caller applies -}
call-⊆ : ∀ {n Rt Bs Γ Δ O F A B} {k : Seq Σ n Rt Bs (returned Δ B)} {bs σ η} {m : Mach Σ η (st Γ Δ O F)} (a : Arg Σ (st Γ Δ O F) (codeα A B)) e₁ e₂
  → 𝒮 (start (arg a m) (cast e₁ (regs m ⦅ rdi ⦆)) (cast e₂ (regs m ⦅ rsi ⦆)) (retK k bs (frame m) σ)) ⊆ 𝒮 (run (callq a e₁ e₂ ∷ k) bs σ η m)
call-⊆ {n} {A = A₁} {B₁} {k = k} {bs} {σ} {η} {m} a e₁ e₂ = gw (arg a m) (grow-arg {m = m} a)
  where
  e = cast e₁ (regs m ⦅ rdi ⦆)
  w = cast e₂ (regs m ⦅ rsi ⦆)
  gw : (c : Val Σ (code η A₁ B₁)) → (∀ W → mem W ⊆ 𝒱 c → Grow m (λ A → mem W ⊆ 𝒪 T a (σ̂ A) (ρ̂ A)))
    → 𝒮 (start c e w (retK k bs (frame m) σ)) ⊆ λ z → Σ[ A ∈ Apx ] AL A m × z ∈ 𝒦 σ (⟦_⟧ⁱ T {n} (callq a e₁ e₂) (K k bs) (σ̂ A) (ρ̂ A) (𝓕 (flag m)))
  gw (code f) g z ⟨ A' , ⟨ al' , ⟨ Ac , ⟨ W , ⟨ fr , ⟨ W⊆ , ⟨ W≢ , z∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
      with grown (both {m = m} (g (map ent W) entries) (λ E h d d∈ → 𝒪-mono (σ̂E E) (ρ̂E E) a d (h d d∈))
             (both {m = m} (grow-at {m = m} 1 X (λ d d∈ → cast-𝒱 e₁ d (ext-⊆ (A' 1) (𝒱-ne e) (al' 1) d d∈))) (λ E h d d∈ → E 1 d (h d d∈))
                   (grow-at {m = m} 2 Y (λ d d∈ → cast-𝒱 e₂ d (ext-⊆ (A' 2) (𝒱-ne w) (al' 2) d d∈))))
             ) A₀ al₀
    where
    X = ext (A' 1) (𝒱-ne e)
    Y = ext (A' 2) (𝒱-ne w)
    ent : Value → Value
    ent w' = X ↦ (Y ↦ w')
    A₀ : Apx
    A₀ = λ { 0 → [] ; 1 → [] ; 2 → [] ; l → Ac l }
    al₀ : AL A₀ m
    al₀ = λ { 0 → λ _ () ; 1 → λ _ () ; 2 → λ _ () ; (suc (suc (suc i))) → fr i }
    entries : mem (map ent W) ⊆ T f
    entries x x∈ with ∈-map⁻ ent x∈
    ... | ⟨ w' , ⟨ w'∈ , refl ⟩ ⟩ = closed f (ent w')
      ⟨ ⟨ K-mono (Body.start (lookup ds f)) (Body.blocks (lookup ds f)) (λ i → al' (suc (suc (suc i))))
            (λ { rax → ∅⊆ (al' 0) ; rdi → λ d d∈ → ∈-++⁺ˡ d∈ ; rsi → λ d d∈ → ∈-++⁺ˡ d∈ }) (λ _ ()) w' (W⊆ w' w'∈)
        , ⟨ ext-ne _ (𝒱-ne w) , Con⇒≈ Y (𝒱-con w) (ext-⊆ (A' 2) (𝒱-ne w) (al' 2)) ⟩ ⟩
      , ⟨ ext-ne _ (𝒱-ne e) , Con⇒≈ X (𝒱-con e) (ext-⊆ (A' 1) (𝒱-ne e) (al' 1)) ⟩ ⟩
  ... | ⟨ A , ⟨ al , ⟨ E , ⟨ F⊆ , ⟨ X⊆ , Y⊆ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ A , ⟨ al , 𝒦-mono σ (λ u u∈ → ⟨ ne-mem W≢ W⊆C , K-mono k bs (σ̂E E) (λ { rax → W⊆C ; rdi → ⊆r ; rsi → ⊆r }) ⊆r u u∈ ⟩) z z∈ ⟩ ⟩
    where
    W⊆C : mem W ⊆ ⋆ ⟨ ⋆ ⟨ 𝒪 T a (σ̂ A) (ρ̂ A) , ⟨ ρ̂ A rdi , ptt ⟩ ⟩ , ⟨ ρ̂ A rsi , ptt ⟩ ⟩
    W⊆C w' w'∈ = ⟨ _ , ⟨ ⟨ _ , ⟨ F⊆ _ (∈-map⁺ _ w'∈) , ⟨ X⊆ , ext-ne _ (𝒱-ne e) ⟩ ⟩ ⟩ , ⟨ Y⊆ , ext-ne _ (𝒱-ne w) ⟩ ⟩ ⟩

{- Steps ----------------------------------------------------------------------------------------}

{- what a step does: a step to s' keeps the open closure in agreement with its
   slot and shrinks the denotation, and a stop with an answer returns v -}
Back : State Σ → Next (State Σ) → Set
Back s (next s') = Inv s' × 𝒮 s' ⊆ 𝒮 s
Back s (stop o) = Answer o → Σ[ B ∈ Type ] Σ[ v ∈ Val Σ B ] o ≡ obs v × 𝒱 v ⊆ 𝒮 s

back : ∀ s → Inv s → Back s (step ds s)
back (run (movq a d ∷ k) bs σ η m) i = ⟨ put-inv d i , (λ z z∈ → nn (put-⊆ d {k = k} {bs} {σ} {η} {m} (λ A → 𝒪 T a (σ̂ A) (ρ̂ A)) (grow-arg {m = m} a) z z∈)) ⟩
back (run (subq a r e ∷ k) bs σ η m) i = ⟨ i , (λ z z∈ →
  nn (put-⊆ (reg r) {k = k} {bs} {σ} {η} {m} (λ A → primD sub ⟨ ρ̂ A r , ⟨ 𝒪 T a (σ̂ A) (ρ̂ A) , ptt ⟩ ⟩)
        (λ W W⊆ → both {m = m} (grow-arg {m = m} (reg r e) _ (one (int∈ (cast e (regs m ⦅ r ⦆))))) (λ E h d d∈ → E (ix r) d (h d d∈)) (grow-arg {m = m} a _ (one (int∈ (arg a m))))
          ⊳ λ { ⟨ h₁ , h₂ ⟩ d d∈ → prim-in sub h₁ h₂ d (W⊆ d d∈) }) z z∈)) ⟩
back (run (cmpq a₂ a₁ ∷ k) bs σ η m) i = ⟨ i ,
  flag-⊆ {k = k} {bs} {σ} {η} {m} (does (int (arg a₁ m) ≟ℤ int (arg a₂ m))) (λ A → primD eq ⟨ 𝒪 T a₁ (σ̂ A) (ρ̂ A) , ⟨ 𝒪 T a₂ (σ̂ A) (ρ̂ A) , ptt ⟩ ⟩)
    (both {m = m} (grow-arg {m = m} a₁ _ (one (int∈ (arg a₁ m)))) (λ E h d d∈ → 𝒪-mono (σ̂E E) (ρ̂E E) a₁ d (h d d∈)) (grow-arg {m = m} a₂ _ (one (int∈ (arg a₂ m))))
      ⊳ λ { ⟨ h₁ , h₂ ⟩ → prim-in eq h₁ h₂ }) ⟩
back (run (sete d ∷ k) bs σ η m) i =
  ⟨ put-inv d i , (λ z z∈ → nn (put-⊆ d {k = k} {bs} {σ} {η} {m} (λ _ → 𝓕 (flag m)) (λ W W⊆ → grow λ A₀ al → ⟨ A₀ , ⟨ al , ⟨ (λ _ → ⊆r) , W⊆ ⟩ ⟩ ⟩) z z∈)) ⟩
back (run (alloc o d ∷ k) bs σ η m) i = ⟨ put-inv d i , (λ z z∈ →
  nn (put-⊆ d {k = k} {bs} {σ} {η} {m} (λ A → object T o (σ̂ A) (ρ̂ A))
        (λ W W⊆ → grow-each {m = m} _ (λ E → object-mono (σ̂E E) (ρ̂E E) o) W (λ z z∈ → grow-obj o z (W⊆ z z∈))) z z∈)) ⟩
back (run (load j a d ∷ k) bs σ η m) i = ⟨ put-inv d i , (λ z z∈ →
  nn (put-⊆ d {k = k} {bs} {σ} {η} {m} (λ A → projD (pos j) ⟨ 𝒪 T a (σ̂ A) (ρ̂ A) , ptt ⟩)
        (λ W W⊆ → grow-each {m = m} _ (λ E → projₛ-mono j (𝒪-mono (σ̂E E) (ρ̂E E) a)) W (λ z z∈ → grow-load j a z (W⊆ z z∈))) z z∈)) ⟩
back (run (loadfst x r ∷ k) bs σ η m) i = ⟨ agree , (λ z z∈ →
  nn (reg-⊆ r {k} {bs} {σ} {m} {wipeᵣ (regs m)} {env-of (lookup (frame m) x)} {code-of (lookup (frame m) x)} (λ A → carD ⟨ σ̂ A (idx x) , ptt ⟩) wipe-𝓛
        (λ W W⊆ → grow-each {m = m} _ (λ E → lower (car-mono _ _ ⟨ lift (σ̂E E (idx x)) , ptt ⟩)) W
          (λ z z∈ → fst (lookup (frame m) x) (grow-arg {m = m} (atom (var x))) (W⊆ z z∈))) z z∈)) ⟩
  where
  fst : ∀ (v : Val Σ _) {z} → (∀ W → mem W ⊆ 𝒱 v → Grow m (λ A → mem W ⊆ σ̂ A (idx x)))
    → z ∈ 𝒱 (code-of v) → Grow m (λ A → z ∈ carD ⟨ σ̂ A (idx x) , ptt ⟩)
  fst (pack c e) g z∈ = g _ (one ⟨ z∈ , proj₂ (𝒱-ne e) ⟩) ⊳ λ h → ⟨ _ , h _ (here refl) ⟩
back (run (loadsnd {x = opened x} r ∷ k) bs σ η m) i = ⟨ i , (λ z z∈ →
  nn (reg-⊆ r {k} {bs} {σ} {m} {regs m} {envα m} {envα m} (λ A → cdrD ⟨ σ̂ A (idx x) , ptt ⟩) (λ _ → ⊆r)
        (λ W W⊆ → grow-each {m = m} _ (λ E → lower (cdr-mono _ _ ⟨ lift (σ̂E E (idx x)) , ptt ⟩)) W
          (λ z z∈ → let ⟨ c , c∈ ⟩ = snd-𝒱 i (W⊆ z z∈) in
            grow-arg {m = m} (atom (var x)) _ (one c∈) ⊳ λ h → ⟨ c , h _ (here refl) ⟩)) z z∈)) ⟩
back s@(run (callq a e₁ e₂ ∷ k) bs σ η m) i = subst (Back s) (sym (enter-start (arg a m))) ⟨ inv (arg a m) , call-⊆ a e₁ e₂ ⟩
  where
  inv : ∀ {η A B} (c : Val Σ (code η A B)) {e w σ'} → Inv (start c e w σ')
  inv (code f) = none
back (run (retq e) bs halt η m) i ans =
  ⟨ _ , ⟨ v , ⟨ refl , (λ z z∈ → ⟨ (λ { 0 → z ∷ [] ; _ → [] }) , ⟨ (λ { 0 → λ { _ (here refl) → cast-𝒱 e _ z∈ } ; (suc l) → λ _ () }) , here refl ⟩ ⟩) ⟩ ⟩ ⟩
  where v = cast e (regs m ⦅ rax ⦆)
back (run (retq e) bs (retK k bs' φ σ) η m) i = ⟨ none , (λ { z ⟨ A' , ⟨ al' , z∈ ⟩ ⟩ →
  ⟨ (λ { 0 → W A' ; _ → [] }) , ⟨ (λ { 0 → λ d d∈ → cast-𝒱 e d (ext-⊆ (A' 0) (𝒱-ne v) (al' 0) d d∈) ; (suc l) → λ _ () })
  , ⟨ A' , ⟨ W A' , ⟨ (λ j → al' (suc (suc (suc j)))) , ⟨ ⊆r , ⟨ ext-ne _ (𝒱-ne v)
  , 𝒦-mono σ (K-mono k bs' (λ _ → ⊆r) (λ { rax d d∈ → ∈-++⁺ˡ d∈ ; rdi → ∅⊆ (al' 1) ; rsi → ∅⊆ (al' 2) }) (λ _ ())) z z∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ }) ⟩
  where
  v = cast e (regs m ⦅ rax ⦆)
  W = λ (A' : Apx) → ext (A' 0) (𝒱-ne v)
back (run (jmp l) bs σ η m) i = ⟨ none , (λ { z ⟨ A' , ⟨ al' , z∈ ⟩ ⟩ → ⟨ A' , ⟨ unset-AL al' , 𝒦-mono σ (jump bs l al') z z∈ ⟩ ⟩ }) ⟩
back s@(run (case x p _ l₁ l₂) bs σ η m) i with lookup (frame m) x in eq
... | inl u = ⟨ none , ⊆′ ⟩
  where
  X : Apx → List Value
  X A' = proj₁ (𝒱-ne u) ∷ A' 3
  ⊆′ : 𝒮 (go ds (block bs l₁) σ η (u ∷ forget p (frame m))) ⊆ 𝒮 s
  ⊆′ z ⟨ A' , ⟨ al' , z∈ ⟩ ⟩ = fin (grown (grow-arg {m = m} (atom (var x)) (map left (X A')) Xin) (und p A') (und-AL p (unset-AL al')))
    where
    X⊆ : mem (X A') ⊆ 𝒱 u
    X⊆ _ (here refl) = proj₂ (𝒱-ne u)
    X⊆ d (there d∈) = al' 3 d d∈
    Xin : mem (map left (X A')) ⊆ 𝒱 (lookup (frame m) x)
    Xin d d∈ with ∈-map⁻ left d∈
    ... | ⟨ d' , ⟨ d'∈ , refl ⟩ ⟩ = subst (λ v → left d' ∈ 𝒱 v) (sym eq) (X⊆ d' d'∈)
    fin : Σ[ A ∈ Apx ] AL A m × Ext (und p A') A × mem (map left (X A')) ⊆ σ̂ A (idx x) → z ∈ 𝒮 s
    fin ⟨ A , ⟨ al , ⟨ E , L⊆ ⟩ ⟩ ⟩ = ⟨ A , ⟨ al , 𝒦-mono σ (λ w w∈ →
      inj₁ ⟨ proj₁ (𝒱-ne u) , ⟨ A' 3 , ⟨ (λ d d∈ → L⊆ (left d) (∈-map⁺ left d∈))
      , ⟨ blocks-mono bs l₁ fr w (jump bs l₁ al' w w∈) , Con⇒≈ (X A') (𝒱-con u) X⊆ ⟩ ⟩ ⟩ ⟩) z z∈ ⟩ ⟩
      where
      fr : σ̂ A' ⊆ₑ (mem (X A') • drop p (σ̂ A))
      fr zero d d∈ = there d∈
      fr (suc j) d d∈ = drop-mono p (σ̂E E) j d (drop-undrop p _ j d d∈)
... | inr u = ⟨ none , ⊆′ ⟩
  where
  X : Apx → List Value
  X A' = proj₁ (𝒱-ne u) ∷ A' 3
  ⊆′ : 𝒮 (go ds (block bs l₂) σ η (u ∷ forget p (frame m))) ⊆ 𝒮 s
  ⊆′ z ⟨ A' , ⟨ al' , z∈ ⟩ ⟩ = fin (grown (grow-arg {m = m} (atom (var x)) (map right (X A')) Xin) (und p A') (und-AL p (unset-AL al')))
    where
    X⊆ : mem (X A') ⊆ 𝒱 u
    X⊆ _ (here refl) = proj₂ (𝒱-ne u)
    X⊆ d (there d∈) = al' 3 d d∈
    Xin : mem (map right (X A')) ⊆ 𝒱 (lookup (frame m) x)
    Xin d d∈ with ∈-map⁻ right d∈
    ... | ⟨ d' , ⟨ d'∈ , refl ⟩ ⟩ = subst (λ v → right d' ∈ 𝒱 v) (sym eq) (X⊆ d' d'∈)
    fin : Σ[ A ∈ Apx ] AL A m × Ext (und p A') A × mem (map right (X A')) ⊆ σ̂ A (idx x) → z ∈ 𝒮 s
    fin ⟨ A , ⟨ al , ⟨ E , L⊆ ⟩ ⟩ ⟩ = ⟨ A , ⟨ al , 𝒦-mono σ (λ w w∈ →
      inj₂ ⟨ proj₁ (𝒱-ne u) , ⟨ A' 3 , ⟨ (λ d d∈ → L⊆ (right d) (∈-map⁺ right d∈))
      , ⟨ blocks-mono bs l₂ fr w (jump bs l₂ al' w w∈) , Con⇒≈ (X A') (𝒱-con u) X⊆ ⟩ ⟩ ⟩ ⟩) z z∈ ⟩ ⟩
      where
      fr : σ̂ A' ⊆ₑ (mem (X A') • drop p (σ̂ A))
      fr zero d d∈ = there d∈
      fr (suc j) d d∈ = drop-mono p (σ̂E E) j d (drop-undrop p _ j d d∈)

↠-⊆ : ∀ {s t} → Inv s → s ↠ t → Inv t × 𝒮 t ⊆ 𝒮 s
↠-⊆ i done = ⟨ i , ⊆r ⟩
↠-⊆ {s} i (stp ∷↠ τ) = let ⟨ i′ , ⊆₁ ⟩ = subst (Back s) stp (back s i) ; ⟨ i″ , ⊆₂ ⟩ = ↠-⊆ i′ τ in ⟨ i″ , (λ z z∈ → ⊆₁ z (⊆₂ z z∈)) ⟩

{- Soundness ------------------------------------------------------------------------------}

{- what the machine stops with, from main, is in the denotation of the program -}
soundness : ∀ {A} (b : Body Σ A (entry [])) {o} → Terminates (sem (program ds b)) o → Answer o
  → Σ[ B ∈ Type ] Σ[ v ∈ Val Σ B ] o ≡ obs v × 𝒱 v ⊆ ⟦ program ds b ⟧ₜ
soundness (body n bs k) ⟨ s , ⟨ τ , fin ⟩ ⟩ ans =
  let ⟨ i , ⊆₁ ⟩ = ↠-⊆ none (star→↠ τ) ; ⟨ B , ⟨ v , ⟨ e , v⊆ ⟩ ⟩ ⟩ = subst (Back s) fin (back s i) ans in
  ⟨ B , ⟨ v , ⟨ e , (λ z z∈ → start⊆ z (⊆₁ z (v⊆ z z∈))) ⟩ ⟩ ⟩
  where
  start⊆ : 𝒮 (run k bs halt [] ⟨ rv tt tt tt , [] , tt , tt ⟩) ⊆ ⟦ program ds (body n bs k) ⟧ₜ
  start⊆ z ⟨ A , ⟨ al , z∈ ⟩ ⟩ =
    K-mono k bs (λ i → al (suc (suc (suc i)))) (λ { rax → ∅⊆ (al 0) ; rdi → ∅⊆ (al 1) ; rsi → ∅⊆ (al 2) }) (λ _ ()) z z∈
