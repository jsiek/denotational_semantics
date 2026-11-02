{-

  Soundness of the X86μ interpreter (Mu/Semantics/ClockedInterpreters/X86.agda)
  with respect to the Scott-domain semantics of X86μ
  (Mu/Semantics/ScottDomains/X86.agda): what the interpreter returns, at
  any clock, means what the program means, and the interpreter never
  errs; for a table that contains the code of each definition
  interpreted with the whole table (closed), as the table of a compiled
  program does (X86Compiled.agda): the interpreter runs a definition
  with the whole table, the semantics with the table of the older ones.

  As for FPC (Soundness.agda), through the meanings of values (𝒱; a
  code pointer means its entry of the table), by induction on the
  clock, the blocks and the sequence, as the interpreter runs. A
  machine state m agrees with a state S of the semantics (Agree): each
  slot, each set register and the set flag of m mean what S holds, and
  the open closure is that of its slot (OpR, X86Common.agda). Typed code
  reads no unset register and no unset flag, so S may hold anything
  there. Each instruction but callq maps S to a state that agrees with
  the next machine state; a slot write and a call are strict, but every
  value means a defined element. fold and unfold (↑, ↓) are the
  identity on meanings.

-}

open import MLTT.Spartan hiding (inl; inr; cases; Type)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import UF.Base using (ap₂)

open import Framework.Primitives using (Base; base-rep; Int)
open import Framework.abt.GSubst using (_•_)
open import Framework.Lookup using (forget)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋)
open import Language.Prim using (sub; eq; bool) renaming (δ to δᴾ)
open import Mu.Language.Type using (Type; Ctx; base; tup; _⊹_; _⇒_; μ; code; _∋_; Z; S; idx)
open import Mu.Language.X86
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup; pos)
open import Mu.Semantics.ClockedInterpreters.GlobalFun using (module Vals)
open import Mu.Semantics.ClockedInterpreters.X86
  using (RV; MV; RegVals; rv; Flag; Mach; regs; frame; clo; flag; _⦅_⦆; _[_≔_]; cast; forgetᵥ; wipeᵣ;
         arg; args; put; obj; equal; bit; size; code-of; env-of; run; jump; call)
  renaming (⟨_,_,_,_⟩ to mach)
open import Mu.proof.Adequacy.X86Common using (OpR; none; agree)
open import Semantics.Interp.Clock using (Result; timeout; error; ret; _>>=_)
open import Semantics.Observation using (o-const)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_) renaming (refl to ≡-refl)

module Mu.proof.Adequacy.ScottDomains.X86Soundness
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : propext 𝓤₀)
       where

open import Framework.Scott.Base pt fe hiding (_>>=_)
open import proof.Framework.Scott.Ops pt fe pe hiding (Val)
  renaming (Env to Envᵈ; app to appᵈ; inl to inlᵈ; inr to inrᵈ; tuple to tupleᵈ; pair to pairᵈ)
open import proof.Framework.Scott.Semantics pt fe pe using (Den; abs; init; init-defined; code₂-β; module Over)
open import Semantics.Scott.Prim pt fe pe using (primD; out)
open import Mu.Semantics.ScottDomains.Ops pt fe pe using (Table; tables)
open import Mu.Semantics.ScottDomains.CFG pt fe pe using (drop)
open import Mu.Semantics.ScottDomains.X86 pt fe pe
  using (RegsD; 𝕊; Kont; regsᶜ; flagᶜ; ⟦_⟧ˢ; codeₜ; ⟦_⟧ₜ; 𝒪; 𝒪s; object; called-regs)
  renaming (put to putₛ; _[_≔_] to _[_≔ₛ_]; args to argsₛ; blocks to blocksₛ; run to runₛ)
open import Mu.proof.Adequacy.ScottDomains.Soundness pt fe pe using (Holds; timeout; ret; bind-holds; inj-tag; con-inj; not-con)
open Over 𝕊 using (op₁; op₂)

module _ {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ) where

 open Vals Σ renaming (Env to Frame; const to cv; δ to δᵥ)

 T : Table Σ
 T = tables codeₜ ds

 {- Meanings of values ------------------------------------------------------------}

 𝒱 : ∀ {A} → Val A → ⟨ 𝔻 ⟩
 𝒱s : ∀ {Δ} → All Val Δ → Fin (length Δ) → ⟨ 𝔻 ⟩
 𝒱 (code f) = T f
 𝒱 (pack c e) = pairᵈ · 𝒱 c · 𝒱 e
 𝒱 (cv {B} k) = const B k
 𝒱 (tup {Δ} ws) = tupleᵈ (length Δ) · 𝒱s ws
 𝒱 (inl v) = inlᵈ · 𝒱 v
 𝒱 (inr v) = inrᵈ · 𝒱 v
 𝒱 (fold v) = 𝒱 v
 𝒱s [] = λ ()
 𝒱s (w ∷ ws) = λ { zero → 𝒱 w ; (suc i) → 𝒱s ws i }

 {- the meaning of the contents of a register of type τ -}
 𝒱ᵣ : ∀ {η} τ → RV Σ η τ → ⟨ 𝔻 ⟩
 𝒱ᵣ (ty A) v = 𝒱 v
 𝒱ᵣ (codeα A B) v = 𝒱 v
 𝒱ᵣ tupα v = 𝒱 v

 𝒱s-lookup : ∀ {Δ A} (ws : All Val Δ) (i : Δ ∋ A) → 𝒱s ws (pos i) ＝ 𝒱 (lookup ws i)
 𝒱s-lookup (w ∷ ws) Z = refl
 𝒱s-lookup (w ∷ ws) (S i) = 𝒱s-lookup ws i

 unfold-𝒱 : ∀ {A} (v : Val (μ A)) → 𝒱 (unfold-v v) ＝ 𝒱 v
 unfold-𝒱 (fold v) = refl

 𝒱-bit : (b : Bool) → 𝒱 (bit {Σ} b) ＝ out (bool b)
 𝒱-bit true = ap (λ - → inlᵈ · (tupleᵈ 0 · -)) (dfunext fe (λ ()))
 𝒱-bit false = ap (λ - → inrᵈ · (tupleᵈ 0 · -)) (dfunext fe (λ ()))

 𝒱-δ : (u w : Val (base Int)) → primD sub · 𝒱 u · 𝒱 w ＝ 𝒱 (δᵥ sub u w)
 𝒱-δ (cv n) (cv m) = primD-const sub n m

 𝒱-equal : (u w : Val (base Int)) → primD eq · 𝒱 u · 𝒱 w ＝ 𝒱 (bit {Σ} (equal u w))
 𝒱-equal (cv n) (cv m) = primD-const eq n m ∙ 𝒱-bit (equal (cv n) (cv m)) ⁻¹

 {- a value of a table whose entries are the code of their definitions -}
 module _ (closed : ∀ {s} (f : Σ ∋ s) → T f ＝ codeₜ T (lookup ds f)) where

  𝒱-defined : ∀ {A} (v : Val A) → defined (𝒱 v)
  𝒱s-defined : ∀ {Δ} (ws : All Val Δ) (i : Fin (length Δ)) → defined (𝒱s ws i)
  𝒱-defined (code f) = transport defined (closed f ⁻¹) (Λ-defined _)
  𝒱-defined (pack c e) = pair-defined (𝒱 c) (𝒱 e) (𝒱-defined c) (𝒱-defined e)
  𝒱-defined (cv {B} k) = const-defined B k
  𝒱-defined (tup {Δ} ws) = tuple-defined (length Δ) (𝒱s ws) (𝒱s-defined ws)
  𝒱-defined (inl v) = inl-defined (𝒱 v) (𝒱-defined v)
  𝒱-defined (inr v) = inr-defined (𝒱 v) (𝒱-defined v)
  𝒱-defined (fold v) = 𝒱-defined v
  𝒱s-defined (w ∷ ws) zero = 𝒱-defined w
  𝒱s-defined (w ∷ ws) (suc i) = 𝒱s-defined ws i

  𝒱ᵣ-defined : ∀ {η} τ (v : RV Σ η τ) → defined (𝒱ᵣ τ v)
  𝒱ᵣ-defined (ty A) v = 𝒱-defined v
  𝒱ᵣ-defined (codeα A B) v = 𝒱-defined v
  𝒱ᵣ-defined tupα v = 𝒱-defined v

  {- Agreement of the machine with a state of the semantics ---------------------------}

  FrameAgree : ∀ {Δ} → ⟨ Envᵈ ⟩ → Frame Δ → 𝓤₁ ̇
  FrameAgree {Δ} σ φ = ∀ {A} (x : Δ ∋ A) → σ (idx x) ＝ 𝒱 (lookup φ x)

  FlagAgree : ∀ {b} → ⟨ 𝔻 ⟩ → Flag Σ b → 𝓤₁ ̇
  FlagAgree {true} F b = F ＝ 𝒱 (bit {Σ} b)
  FlagAgree {false} F _ = 𝟙

  RegsAgree : ∀ {η Γ} → ⟨ RegsD ⟩ → RegVals Σ η Γ → 𝓤₁ ̇
  RegsAgree {Γ = Γ} R ρ = ∀ r {τ} (e : Γ ‹ r › ≡ just τ) → R r ＝ 𝒱ᵣ τ (cast e (ρ ⦅ r ⦆))

  record Agree {η ψ} (S : ⟨ 𝕊 ⟩) (m : Mach Σ η ψ) : 𝓤₁ ̇ where
   constructor agr
   field
    fr : FrameAgree (pr₁ S) (frame m)
    rg : RegsAgree (pr₁ (pr₂ S)) (regs m)
    fl : FlagAgree (pr₂ (pr₂ S)) (flag m)
    op : OpR (frame m) (St.op ψ) η (clo m)
  open Agree

  frame-drop : ∀ {Δ' Δ} (p : Δ' ⊑ Δ) {σ : ⟨ Envᵈ ⟩} {φ : Frame Δ} → FrameAgree σ φ → FrameAgree (drop p · σ) (forget p φ)
  frame-drop here⊑ h x = h x
  frame-drop (there⊑ p) {σ} {v ∷ φ} h x = frame-drop p {σ = λ i → σ (succ i)} (λ y → h (S y)) x

  frame-ext : ∀ {Δ A} {σ : ⟨ Envᵈ ⟩} {φ : Frame Δ} (v : Val A) → FrameAgree σ φ → FrameAgree (𝒱 v • σ) (v ∷ φ)
  frame-ext v h Z = refl
  frame-ext v h (S x) = h x

  regs-upd : ∀ r {η Γ τ} {R : ⟨ RegsD ⟩} {ρ : RegVals Σ η Γ} {D} {v : RV Σ η τ} → RegsAgree R ρ → D ＝ 𝒱ᵣ τ v
    → RegsAgree (R [ r ≔ₛ D ]) (_[_≔_] {τ = just τ} ρ r v)
  regs-upd rax h hD rax ≡-refl = hD
  regs-upd rax h hD rdi e = h rdi e
  regs-upd rax h hD rsi e = h rsi e
  regs-upd rdi h hD rax e = h rax e
  regs-upd rdi h hD rdi ≡-refl = hD
  regs-upd rdi h hD rsi e = h rsi e
  regs-upd rsi h hD rax e = h rax e
  regs-upd rsi h hD rdi e = h rdi e
  regs-upd rsi h hD rsi ≡-refl = hD

  {- an unset register agrees with anything, and wiping unsets registers -}
  private
   forget-agree : ∀ {η η' τ} m {x : MV Σ η m} {D} (e : forgetα m ≡ just τ)
     → (∀ {τ'} (e' : m ≡ just τ') → D ＝ 𝒱ᵣ τ' (cast e' x)) → D ＝ 𝒱ᵣ {η'} τ (cast e (forgetᵥ m x))
   forget-agree (just (ty A)) ≡-refl h = h ≡-refl
   forget-agree (just (codeα A B)) () h
   forget-agree (just tupα) () h
   forget-agree nothing () h

  regs-wipe : ∀ {η η' Γ} {R : ⟨ RegsD ⟩} {ρ : RegVals Σ η Γ} → RegsAgree R ρ → RegsAgree R (wipeᵣ {η' = η'} ρ)
  regs-wipe {Γ = rt a b c} h rax e = forget-agree a e (h rax)
  regs-wipe {Γ = rt a b c} h rdi e = forget-agree b e (h rdi)
  regs-wipe {Γ = rt a b c} h rsi e = forget-agree c e (h rsi)

  {- Operands and objects ---------------------------------------------------------------}

  module _ {η ψ} {S : ⟨ 𝕊 ⟩} {m : Mach Σ η ψ} (A : Agree S m) where

   arg-agree : ∀ {τ} (a : Arg Σ ψ τ) → 𝒪 T a · S ＝ 𝒱ᵣ τ (arg a m)
   arg-agree (atom (var x)) = fr A x
   arg-agree (atom (lit B c)) = refl
   arg-agree (atom (ref f)) = refl
   arg-agree (reg r e) = rg A r e
   arg-agree (a ↑) = arg-agree a
   arg-agree (a ↓) = arg-agree a ∙ unfold-𝒱 (arg a m) ⁻¹

   args-agree : ∀ {Δ} (as : All (λ A → Arg Σ ψ (ty A)) Δ) (i : Fin (length Δ)) → (𝒪s T as · S) i ＝ 𝒱s (args as m) i
   args-agree (a ∷ as) zero = arg-agree a
   args-agree (a ∷ as) (suc i) = args-agree as i

   obj-agree : ∀ {B} (o : Obj Σ ψ B) → object T o · S ＝ 𝒱 (obj o m)
   obj-agree (pair c e) = ap₂ (λ a b → pairᵈ · a · b) (arg-agree c) (arg-agree e)
   obj-agree (tuple {Δ} as) = ap (tupleᵈ (length Δ) ·_) (dfunext fe (args-agree as))
   obj-agree (inl a) = ap (inlᵈ ·_) (arg-agree a)
   obj-agree (inr a) = ap (inrᵈ ·_) (arg-agree a)

  {- a write to d -}
  put-agree : ∀ {n ψ τ ψ'} (d : Dst n ψ τ ψ') {η} {m : Mach Σ η ψ} {v : RV Σ η τ} (S : ⟨ 𝕊 ⟩) (D : Den 𝕊) (κ : Kont)
    → Agree S m → D · S ＝ 𝒱ᵣ τ v → Σ S' ꞉ ⟨ 𝕊 ⟩ , Agree S' (put d v m) × (putₛ T d D κ · S ＝ κ · S')
  put-agree (reg r) 𝔰 D κ (agr fa ra fla oa) hD = _ , agr fa (regs-upd r ra hD) fla oa , refl
  put-agree {τ = τ} (slot p _) {η} {v = v} (σ , RF) D κ (agr fa ra fla oa) hD =
    ((D · (σ , RF)) • (drop p · σ) , RF) , agr fr' ra fla none ,
    (app-Λ _ (D · (σ , RF))
     ∙ seq-defined (D · (σ , RF)) (κ · ((D · (σ , RF)) • (drop p · σ) , RF)) (transport defined (hD ⁻¹) (𝒱ᵣ-defined {η} τ v)))
   where
    fr' : FrameAgree ((D · (σ , RF)) • (drop p · σ)) (v ∷ forget p _)
    fr' Z = hD
    fr' (S x) = frame-drop p fa x

  {- Soundness --------------------------------------------------------------------}

  Sound : ∀ {A} → Result (Val A) → ⟨ 𝔻 ⟩ → 𝓤₁ ̇
  Sound r d = Holds (λ v → 𝒱 v ＝ d) r

  sound-＝ : ∀ {A} {r : Result (Val A)} {d d'} → d ＝ d' → Sound r d → Sound r d'
  sound-＝ refl s = s

  sound-run : ∀ ck {n R Bs ψ} (bs : Blocks Σ n R Bs) η (m : Mach Σ η ψ) (k : Seq Σ n R Bs ψ) (S : ⟨ 𝕊 ⟩)
    → Agree S m → Sound (run ds ck bs η m k) (⟦_⟧ˢ T k (blocksₛ T bs) · S)
  sound-jump : ∀ ck {n R Bs Δ} (bs : Blocks Σ n R Bs) η (l : Bs ∋ Δ) (φ : Frame Δ) (σ : ⟨ Envᵈ ⟩)
    → FrameAgree σ φ → Sound (jump ds ck bs η l φ) (blocksₛ T bs l · σ)
  sound-call : ∀ ck {η A B} (c : Val (code η A B)) (e : Val (tup η)) (w : Val A)
    → Sound (call ds ck c e w) (appᵈ · (appᵈ · 𝒱 c · 𝒱 e) · 𝒱 w)

  {- a write, then k -}
  sound-put : ∀ ck {n R Bs ψ τ ψ'} (bs : Blocks Σ n R Bs) η (d : Dst n ψ τ ψ') (k : Seq Σ n R Bs ψ')
    {m : Mach Σ η ψ} {v : RV Σ η τ} (S : ⟨ 𝕊 ⟩) (D : Den 𝕊) → Agree S m → D · S ＝ 𝒱ᵣ τ v
    → Sound (run ds ck bs η (put d v m) k) (putₛ T d D (⟦_⟧ˢ T k (blocksₛ T bs)) · S)
  sound-put ck bs η d k 𝔰 D A hD =
    let (S' , A' , e) = put-agree d 𝔰 D (⟦_⟧ˢ T k (blocksₛ T bs)) A hD in
    sound-＝ (e ⁻¹) (sound-run ck bs η _ k S' A')

  sound-run ck bs η m (movq a d ∷ k) 𝔰 A = sound-put ck bs η d k 𝔰 (𝒪 T a) A (arg-agree A a)
  sound-run ck bs η m (subq a r e ∷ k) 𝔰 A =
    sound-put ck bs η (reg r) k 𝔰 (op₂ (primD sub) (∘₁ 𝕊 RegsD 𝔻 regsᶜ (at Reg 𝔻 r)) (𝒪 T a)) A
      (ap₂ (λ x y → primD sub · x · y) (rg A r e) (arg-agree A a) ∙ 𝒱-δ (cast e (regs m ⦅ r ⦆)) (arg a m))
  sound-run ck bs η m (cmpq a₂ a₁ ∷ k) (σ , R , F) A =
    sound-run ck bs η _ k _
      (agr (fr A) (rg A) (ap₂ (λ x y → primD eq · x · y) (arg-agree A a₁) (arg-agree A a₂) ∙ 𝒱-equal (arg a₁ m) (arg a₂ m))
           (op A))
  sound-run ck bs η m (sete d ∷ k) 𝔰 A = sound-put ck bs η d k 𝔰 flagᶜ A (fl A)
  sound-run ck bs η m (alloc o d ∷ k) 𝔰 A = sound-put ck bs η d k 𝔰 (object T o) A (obj-agree A o)
  sound-run ck bs η m (load i a d ∷ k) 𝔰 A =
    sound-put ck bs η d k 𝔰 (op₁ (proj (pos i)) (𝒪 T a)) A (ap (proj (pos i) ·_) (arg-agree A a) ∙ nth-𝒱 (arg a m))
   where
    nth-𝒱 : (v : Val (tup _)) → proj (pos i) · 𝒱 v ＝ 𝒱 (nth i v)
    nth-𝒱 (tup ws) = proj-tuple _ (𝒱s ws) (𝒱s-defined ws) (pos i) ∙ 𝒱s-lookup ws i
  sound-run ck bs η m (loadfst x r ∷ k) (σ , R , F) A =
    sound-run ck bs (size v) _ k _ (agr (fr A) (regs-upd r (regs-wipe (rg A)) (ap (car ·_) (fr A x) ∙ car-𝒱 v)) (fl A) agree)
   where
    v = lookup (frame m) x
    car-𝒱 : ∀ {A B} (v : Val (A ⇒ B)) → car · 𝒱 v ＝ 𝒱 (code-of v)
    car-𝒱 (pack c e) = car-pair (𝒱 c) (𝒱 e) (𝒱-defined c) (𝒱-defined e)
  sound-run ck bs η m (loadsnd {x = opened x} r ∷ k) (σ , R , F) A =
    sound-run ck bs η _ k _ (agr (fr A) (regs-upd r (rg A) (snd-𝒱 (op A) (fr A x))) (fl A) (op A))
   where
    snd-𝒱 : ∀ {Δ A B} {φ : Frame Δ} {x : Δ ∋ A ⇒ B} {η'} {o : Val (tup η')} → OpR φ (just (opened x)) η' o
      → σ (idx x) ＝ 𝒱 (lookup φ x) → cdr · σ (idx x) ＝ 𝒱 o
    snd-𝒱 {φ = φ} {x} agree h = ap (cdr ·_) h ∙ cdr-𝒱 (lookup φ x)
     where
      cdr-𝒱 : ∀ {A B} (v : Val (A ⇒ B)) → cdr · 𝒱 v ＝ 𝒱 (env-of v)
      cdr-𝒱 (pack c e) = cdr-pair (𝒱 c) (𝒱 e) (𝒱-defined c) (𝒱-defined e)
  sound-run ck bs η m (callq a e₁ e₂ ∷ k) (σ , R , F) A =
    bind-holds (sound-call ck (arg a m) (cast e₁ (regs m ⦅ rdi ⦆)) (cast e₂ (regs m ⦅ rsi ⦆))) λ v ev →
      sound-＝ (seq-defined C (⟦_⟧ˢ T k (blocksₛ T bs) · (σ , called-regs C , init))
                  (transport defined ((eqC ∙ ev ⁻¹) ⁻¹) (𝒱-defined v)) ⁻¹)
        (sound-run ck bs η _ k (σ , called-regs C , init)
           (agr (fr A) (λ { rax ≡-refl → eqC ∙ ev ⁻¹ ; rdi () ; rsi () }) ⋆ none))
   where
    C : ⟨ 𝔻 ⟩
    C = appᵈ · (appᵈ · (𝒪 T a · (σ , R , F)) · R rdi) · R rsi
    eqC : C ＝ appᵈ · (appᵈ · 𝒱 (arg a m) · 𝒱 (cast e₁ (regs m ⦅ rdi ⦆))) · 𝒱 (cast e₂ (regs m ⦅ rsi ⦆))
    eqC = ap₂ (λ x y → appᵈ · x · y) (ap₂ (λ x y → appᵈ · x · y) (arg-agree A a) (rg A rdi e₁)) (rg A rsi e₂)
  sound-run ck bs η m (retq e) 𝔰 A = ret (rg A rax e ⁻¹)
  sound-run ck bs η m (jmp l) (σ , RF) A = sound-jump ck bs η l (frame m) σ (fr A)
  sound-run ck bs η m (case x p _ l₁ l₂) (σ , RF) A = sel (lookup (frame m) x) (fr A x)
   where
    br : ⟨ Br ⟩
    br = (strict · (abs (blocksₛ T bs l₁) · (drop p · σ)) , strict · (abs (blocksₛ T bs l₂) · (drop p · σ)))
    sel : (v : Val (_ ⊹ _)) → σ (idx x) ＝ 𝒱 v
      → Sound (either v (λ u → jump ds ck bs η l₁ (u ∷ forget p (frame m))) (λ u → jump ds ck bs η l₂ (u ∷ forget p (frame m))))
              (cases · σ (idx x) · br)
    sel (inl u) h =
      sound-＝ ((ap (λ - → cases · - · br) h ∙ cases-inl (𝒱 u) (𝒱-defined u) _ _
                 ∙ strict-defined (abs (blocksₛ T bs l₁) · (drop p · σ)) (𝒱 u) (𝒱-defined u)) ⁻¹)
        (sound-jump ck bs η l₁ (u ∷ forget p (frame m)) _ (frame-ext u (frame-drop p (fr A))))
    sel (inr u) h =
      sound-＝ ((ap (λ - → cases · - · br) h ∙ cases-inr (𝒱 u) (𝒱-defined u) _ _
                 ∙ strict-defined (abs (blocksₛ T bs l₂) · (drop p · σ)) (𝒱 u) (𝒱-defined u)) ⁻¹)
        (sound-jump ck bs η l₂ (u ∷ forget p (frame m)) _ (frame-ext u (frame-drop p (fr A))))

  sound-jump ck (bs ▷ k) η Z φ σ h =
    sound-run ck bs η (mach (rv tt tt tt) φ tt tt) k (σ , (λ _ → init) , init) (agr h (λ { rax () ; rdi () ; rsi () }) ⋆ none)
  sound-jump ck (bs ▷ k) η (S l) φ σ h = sound-jump ck bs η l φ σ h

  sound-call zero c e w = timeout
  sound-call (succ ck) {η} (code f) e w =
    sound-＝ (eqB ⁻¹)
      (sound-run ck (Body.blocks (lookup ds f)) η (mach (rv tt e w) [] tt tt) (Body.start (lookup ds f))
         ((λ _ → init) , argsₛ (𝒱 e) (𝒱 w) , init)
         (agr (λ ()) (λ { rax () ; rdi ≡-refl → refl ; rsi ≡-refl → refl }) ⋆ none))
   where
    eqB : appᵈ · (appᵈ · T f · 𝒱 e) · 𝒱 w
         ＝ ⟦_⟧ˢ T (Body.start (lookup ds f)) (blocksₛ T (Body.blocks (lookup ds f))) · ((λ _ → init) , argsₛ (𝒱 e) (𝒱 w) , init)
    eqB = ap (λ - → appᵈ · (appᵈ · - · 𝒱 e) · 𝒱 w) (closed f)
         ∙ code₂-β _ (𝒱 e) (𝒱 w)
         ∙ seq-defined (𝒱 e) _ (𝒱-defined e)
         ∙ seq-defined (𝒱 w) _ (𝒱-defined w)

  {- main, run from no slot, no register and no flag, means the program -}
  soundness : ∀ {A} (b : Body Σ A (entry [])) ck
    → Sound (run ds ck (Body.blocks b) [] (mach (rv tt tt tt) [] tt tt) (Body.start b)) ⟦ program ds b ⟧ₜ
  soundness b ck =
    sound-run ck (Body.blocks b) [] (mach (rv tt tt tt) [] tt tt) (Body.start b) _
      (agr (λ ()) (λ { rax () ; rdi () ; rsi () }) ⋆ none)

  {- Observations of constants ---------------------------------------------------------}

  {- a value means a constant exactly when it is observed as that constant -}
  𝒱-const : ∀ {A B} {k : base-rep B} (v : Val A) → 𝒱 v ＝ const B k → obs v ≡ o-const B k
  𝒱-const (cv k') e = con-inj (inj-tag _ _ ⋆ ⋆ e)
  𝒱-const (fold v) e = 𝒱-const v e
  𝒱-const (code f) e = 𝟘-elim (not-con fun _ (λ _ _ ()) (closed f ⁻¹ ∙ e))
  𝒱-const (pack c e') e =
    𝟘-elim (not-con pr (pick₂ (𝒱 c) (𝒱 e')) (λ _ _ ())
              (guard-defined 2 (pick₂ (𝒱 c) (𝒱 e')) (λ { zero → 𝒱-defined c ; (suc zero) → 𝒱-defined e' })
                 (inj pr · pick₂ (𝒱 c) (𝒱 e')) ⁻¹ ∙ e))
  𝒱-const (tup {Δ} ws) e =
    𝟘-elim (not-con (tup (length Δ)) (𝒱s ws) (λ _ _ ()) (guard-defined (length Δ) (𝒱s ws) (𝒱s-defined ws) _ ⁻¹ ∙ e))
  𝒱-const (inl v) e = 𝟘-elim (not-con left (𝒱 v) (λ _ _ ()) (seq-defined (𝒱 v) _ (𝒱-defined v) ⁻¹ ∙ e))
  𝒱-const (inr v) e = 𝟘-elim (not-con right (𝒱 v) (λ _ _ ()) (seq-defined (𝒱 v) _ (𝒱-defined v) ⁻¹ ∙ e))

  const-𝒱 : ∀ {A B} {k : base-rep B} (v : Val A) → obs v ≡ o-const B k → 𝒱 v ＝ const B k
  const-𝒱 (cv k) ≡-refl = refl
  const-𝒱 (fold v) e = const-𝒱 v e
  const-𝒱 (code f) ()
  const-𝒱 (pack c e') ()
  const-𝒱 (tup ws) ()
  const-𝒱 (inl v) ()
  const-𝒱 (inr v) ()
