{-

  A clocked interpreter for X86μ (FPC/Language/X86.agda), the output of
  select instructions, with the values of the GlobalFunμ interpreter
  (FPC/Semantics/ClockedInterpreters/GlobalFun.agda), as the one for X86ᵀ
  (ISWIM/Semantics/Interp/Typed/X86.agda): the registers, frame, open closure
  and flag (Mach) have the types of the start of the sequence that runs
  in them; η is α, the types of the open closure's environment, so a
  register of type codeα A B holds code of η, A and B. The frame holds a
  value for each initialized slot, as in CFGμ
  (FPC/Semantics/ClockedInterpreters/CFG.agda); an unset register, an unset flag
  and the open closure (when there is none) hold nothing (⊤); the open closure
  holds its environment.

  The instructions of a sequence run in order, each passing its state
  to the rest, then its jump: retq returns %rax, jmp l runs block l with
  the blocks older than it, and case x y z l₁ l₂ writes the payload of x
  to slot y or z and runs l₁ or l₂. callq runs the start of the
  definition of its code with %rdi and %rsi, and the caller continues
  with the result in %rax.
  Only calls tick the clock, so the interpreter is structurally
  recursive on the clock, the list of blocks and the sequence. Nothing
  errs: a fold (↑) and an unfold (↓) are moves.

-}

module FPC.Semantics.ClockedInterpreters.X86 where

open import Framework.Primitives using (Int)
open import Language.Prim using (sub)
open import FPC.Language.Type
open import FPC.Language.X86
open import FPC.Framework.AllUtil using (All; []; _∷_; lookup)
open import FPC.Framework.Slots using (Slots; read; write; restrict; empty)
open import Semantics.Interp.Clock
open import FPC.Semantics.ClockedInterpreters.GlobalFun using (module Vals)
open import FPC.Semantics.ClockedInterpreters.Imp using (Fr) renaming (atom to
  value-of)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

module _ (Σ : List DSig) where
  open Vals Σ

  {- the values of a register type, α being η -}
  RV : Ctx → RTy → Set
  RV η (ty A) = Val A
  RV η (codeα A B) = Val (code η A B)
  RV η tupα = Val (tup η)

  MV : Ctx → Maybe RTy → Set
  MV η (just τ) = RV η τ
  MV η nothing = ⊤

  record RegVals (η : Ctx) (Γ : Regs) : Set where
    constructor rv
    field
      ax : MV η (Regs.ax Γ)
      di : MV η (Regs.di Γ)
      si : MV η (Regs.si Γ)

  {- the environment of the open closure -}
  Opened : ∀ {X : Set} → Ctx → Maybe X → Set
  Opened η nothing = ⊤
  Opened η (just _) = Val (tup η)

  Flag : Bool → Set
  Flag true = Bool
  Flag false = ⊤

  {- the registers, frame, open closure and flag of a state of type ψ -}
  record Mach (η : Ctx) {Δ : Ctx} (ψ : St Δ) : Set where
    constructor ⟨_,_,_,_⟩
    field
      regs : RegVals η (St.rs ψ)
      frame : Slots Val Δ (St.ini ψ)
      clo : Opened η (St.op ψ)
      flag : Flag (St.fl ψ)

open Mach public

module _ {Σ : List DSig} where
  open Vals Σ

  _⦅_⦆ : ∀ {η Γ} → RegVals Σ η Γ → (r : Reg) → MV Σ η (Γ ‹ r ›)
  ρ ⦅ rax ⦆ = RegVals.ax ρ
  ρ ⦅ rdi ⦆ = RegVals.di ρ
  ρ ⦅ rsi ⦆ = RegVals.si ρ

  _[_≔_] : ∀ {η Γ τ} → RegVals Σ η Γ → (r : Reg) → MV Σ η τ
    → RegVals Σ η (Γ [ r ↦ τ ])
  ρ [ rax ≔ v ] = rv v (RegVals.di ρ) (RegVals.si ρ)
  ρ [ rdi ≔ v ] = rv (RegVals.ax ρ) v (RegVals.si ρ)
  ρ [ rsi ≔ v ] = rv (RegVals.ax ρ) (RegVals.di ρ) v

  cast : ∀ {η m τ} → m ≡ just τ → MV Σ η m → RV Σ η τ
  cast refl v = v

  wipeᵥ : ∀ {η η'} m → MV Σ η m → MV Σ η' (wipeα m)
  wipeᵥ (just (ty A)) v = v
  wipeᵥ (just (codeα _ _)) v = tt
  wipeᵥ (just tupα) v = tt
  wipeᵥ nothing v = tt

  wipeᵣ : ∀ {η η' Γ} → RegVals Σ η Γ → RegVals Σ η' (wipe Γ)
  wipeᵣ {Γ = Γ} ρ =
    rv (wipeᵥ (Regs.ax Γ) (RegVals.ax ρ)) (wipeᵥ (Regs.di Γ) (RegVals.di ρ))
      (wipeᵥ (Regs.si Γ) (RegVals.si ρ))

  arg : ∀ {η Δ} {ψ : St Δ} {τ} → Arg Σ ψ τ → Mach Σ η ψ → RV Σ η τ
  arg (atom a) m = value-of (frame m) a
  arg (reg r e) m = cast e (regs m ⦅ r ⦆)
  arg (a ↑) m = fold (arg a m)
  arg (a ↓) m = unfold-v (arg a m)

  args : ∀ {η Δ Δ'} {ψ : St Δ} → All (λ A → Arg Σ ψ (ty A)) Δ' → Mach Σ η ψ
    → All Val Δ'
  args [] m = []
  args (a ∷ as) m = arg a m ∷ args as m

  {- d := v -}
  put : ∀ {η Δ} {ψ ψ' : St Δ} {τ} → Dst ψ τ ψ' → RV Σ η τ → Mach Σ η ψ
    → Mach Σ η ψ'
  put (reg r) v m = ⟨ regs m [ r ≔ v ] , frame m , clo m , flag m ⟩
  put (slot x p) v m =
    ⟨ regs m , restrict p (write (frame m) x v) , tt , flag m ⟩

  obj : ∀ {η Δ} {ψ : St Δ} {A} → Obj Σ ψ A → Mach Σ η ψ → Val A
  obj (pair c e) m = pack (arg c m) (arg e m)
  obj (tuple as) m = tup (args as m)
  obj (inl a) m = inl (arg a m)
  obj (inr a) m = inr (arg a m)

  {- what cmpq compares, and what sete stores, as the primitive eq gives it -}
  equal : Val (base Int) → Val (base Int) → Bool
  equal (const n) (const k) = does (n ≟ k)

  bit : Bool → Val (tup [] ⊹ tup [])
  bit b = if b then inl (tup []) else inr (tup [])

  {- a closure: the types of its environment, its code and its environment -}
  size : ∀ {A B} → Val (A ⇒ B) → Ctx
  size (pack {Δ} c e) = Δ

  code-of : ∀ {A B} (v : Val (A ⇒ B)) → Val (code (size v) A B)
  code-of (pack c e) = c

  env-of : ∀ {A B} (v : Val (A ⇒ B)) → Val (tup (size v))
  env-of (pack c e) = e

{- the interpreter for a program with the definitions ds -}
module _ {Σ : List DSig}
  (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ) where
  open Vals Σ

  run : ∀ {Δ R Bs ψ} → ℕ → Blocks Σ Δ R Bs → ∀ η → Mach Σ η ψ
    → Seq Σ Δ R Bs ψ
    → Result (Val R)
  jump : ∀ {Δ R Bs I} → ℕ → Blocks Σ Δ R Bs → Ctx → Bs ∋ I → Fr Δ I
    → Result (Val R)
  call : ∀ {η A B} → ℕ → Val (code η A B) → Val (tup η) → Val A → Result (Val B)

  run ck bs η m (movq a d ∷ k) = run ck bs η (put d (arg a m) m) k
  run ck bs η m (subq a r e ∷ k) =
    run ck bs η
      (put (reg {τ = ℤty} r)
        (δ sub (cast {η = η} e (regs m ⦅ r ⦆)) (arg a m)) m) k
  run ck bs η m (cmpq a₂ a₁ ∷ k) =
    run ck bs η ⟨ regs m , frame m , clo m , equal (arg a₁ m) (arg a₂ m) ⟩ k
  run ck bs η m (sete d ∷ k) = run ck bs η (put d (bit (flag m)) m) k
  run ck bs η m (alloc o d ∷ k) = run ck bs η (put d (obj o m) m) k
  run ck bs η m (load i a d ∷ k) = run ck bs η (put d (nth i (arg a m)) m) k
  run ck bs η m (loadfst x i r ∷ k) =
    let v = read (frame m) x i in
    run ck bs (size v)
      ⟨ wipeᵣ (regs m) [ r ≔ code-of v ] , frame m , env-of v , flag m ⟩ k
  run ck bs η m (loadsnd r ∷ k) =
    run ck bs η ⟨ regs m [ r ≔ clo m ] , frame m , clo m , flag m ⟩ k
  run ck bs η m (callq a e₁ e₂ ∷ k) =
    call ck (arg a m) (cast e₁ (regs m ⦅ rdi ⦆)) (cast e₂ (regs m ⦅ rsi ⦆))
      >>= λ v →
    run ck bs η ⟨ rv v tt tt , frame m , tt , tt ⟩ k
  run ck bs η m (retq e) = ret (cast e (regs m ⦅ rax ⦆))
  run ck bs η m (jmp l) = jump ck bs η l (frame m)
  run ck bs η m (case x i y z l₁ l₂) =
    either (read (frame m) x i) (λ v → jump ck bs η l₁ (write (frame m) y v))
      (λ v → jump ck bs η l₂ (write (frame m) z v))

  jump ck (bs ▷ k) η Z φ = run ck bs η ⟨ rv tt tt tt , φ , tt , tt ⟩ k
  jump ck (bs ▷ k) η (S l) φ = jump ck bs η l φ

  call zero c e w = timeout
  call {η} (suc ck) (code f) e w =
    run ck (Body.blocks (lookup ds f)) η
      ⟨ rv tt e w , empty (Body.frame (lookup ds f)) , tt , tt ⟩
      (Body.start (lookup ds f))

{- a program runs the start of main, with no slot, no register and no flag -}
sem : ∀ {A} → Program A → Semantics
sem {A} (program {Σ} ds (body Δ bs k)) =
  semantics (Val A) obs
  (λ ck → run ds ck bs [] ⟨ rv tt tt tt , empty Δ , tt , tt ⟩ k)
  where open Vals Σ
