{-

  A clocked interpreter for X86ᵀ (Language/Typed/X86.agda), the output
  of select instructions, with the values of the Clos5ᵀ interpreter
  (Semantics/Interp/Typed/Clos5.agda), on the typed states of the X86ᵀ
  machine (Semantics/CEK/Typed/X86.agda): the registers, frame, open
  closure and flag (Mach) have the types of the start of the sequence
  that runs in them; η is α, the length of the open closure's
  environment, so a register of type codeα holds code η. The frame
  holds the slots assigned so far, as in CFGᵀ
  (Semantics/Interp/Typed/CFG.agda); an unset register, an unset flag
  and the open closure (when there is none) hold nothing (⊤).

  The instructions of a sequence run in order, each passing its state
  to the rest (so the interpreter is in continuation-passing style, as
  select is), then its jump: retq returns %rax, jmp l and je l₁ l₂ run
  block l with the blocks older than it. callq runs the start of the
  definition of its code with %rdi and %rsi, and the caller continues
  with the result in %rax. As in CFGᵀ, only calls tick the clock, so
  the interpreter is structurally recursive on the clock, the list of
  blocks and the sequence. The only error is chk's: a value of another
  kind than its tag (project?, as project in the typed interpreters).

-}

module Semantics.Interp.Typed.X86 where

open import Framework.Primitives using (Int)
open import Language.Prim using (sub)
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.X86
open import Framework.Lookup using (_!_; forget)
open import Semantics.Interp.Clock
open import Semantics.Interp.Typed.Clos5 using (module Vals)
open import Semantics.Interp.Typed.Imp using () renaming (atom to value-of)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

module _ (Σ : List ℕ) where
  open Vals Σ

  {- the values of a register type, α being η -}
  RV : ℕ → RTy → Set
  RV η (ty A) = Val A
  RV η codeα = Val (code η)
  RV η tupα = Val ⟪ tup η ⟫

  MV : ℕ → Maybe RTy → Set
  MV η (just τ) = RV η τ
  MV η nothing = ⊤

  record RegVals (η : ℕ) (Γ : Regs) : Set where
    constructor rv
    field
      ax : MV η (Regs.ax Γ)
      di : MV η (Regs.di Γ)
      si : MV η (Regs.si Γ)

  {- the code and environment of the open closure -}
  Opened : ∀ {X : Set} → ℕ → Maybe X → Set
  Opened η nothing = ⊤
  Opened η (just _) = Val (code η) × Val ⟪ tup η ⟫

  Flag : Bool → Set
  Flag true = Bool
  Flag false = ⊤

  {- the registers, frame, open closure and flag of a state of type ψ -}
  record Mach (η : ℕ) (ψ : St) : Set where
    constructor ⟨_,_,_,_⟩
    field
      regs : RegVals η (St.rs ψ)
      frame : Env (St.fr ψ)
      opened : Opened η (St.op ψ)
      flag : Flag (St.fl ψ)

open Mach public

module _ {Σ : List ℕ} where
  open Vals Σ

  _⦅_⦆ : ∀ {η Γ} → RegVals Σ η Γ → (r : Reg) → MV Σ η (Γ ‹ r ›)
  ρ ⦅ rax ⦆ = RegVals.ax ρ
  ρ ⦅ rdi ⦆ = RegVals.di ρ
  ρ ⦅ rsi ⦆ = RegVals.si ρ

  _[_≔_] : ∀ {η Γ τ} → RegVals Σ η Γ → (r : Reg) → MV Σ η τ → RegVals Σ η (Γ [ r ↦ τ ])
  ρ [ rax ≔ v ] = rv v (RegVals.di ρ) (RegVals.si ρ)
  ρ [ rdi ≔ v ] = rv (RegVals.ax ρ) v (RegVals.si ρ)
  ρ [ rsi ≔ v ] = rv (RegVals.ax ρ) (RegVals.di ρ) v

  cast : ∀ {η m τ} → m ≡ just τ → MV Σ η m → RV Σ η τ
  cast refl v = v

  forgetᵥ : ∀ {η η'} m → MV Σ η m → MV Σ η' (forgetα m)
  forgetᵥ (just (ty A)) v = v
  forgetᵥ (just codeα) v = tt
  forgetᵥ (just tupα) v = tt
  forgetᵥ nothing v = tt

  wipeᵣ : ∀ {η η' Γ} → RegVals Σ η Γ → RegVals Σ η' (wipe Γ)
  wipeᵣ {Γ = Γ} ρ =
    rv (forgetᵥ (Regs.ax Γ) (RegVals.ax ρ)) (forgetᵥ (Regs.di Γ) (RegVals.di ρ)) (forgetᵥ (Regs.si Γ) (RegVals.si ρ))

  arg : ∀ {η ψ τ} → Arg Σ ψ τ → Mach Σ η ψ → RV Σ η τ
  arg (atom a) m = value-of (frame m) a
  arg (reg r e) m = cast e (regs m ⦅ r ⦆)
  arg (_↑ {G} a) m = dyn G (arg a m)

  args : ∀ {η ψ j} → Vec (Arg Σ ψ (ty Any)) j → Mach Σ η ψ → Vec (Val Any) j
  args [] m = []
  args (a ∷ as) m = arg a m ∷ args as m

  {- d := v -}
  put : ∀ {n η ψ τ ψ'} → Dst n ψ τ ψ' → RV Σ η τ → Mach Σ η ψ → Mach Σ η ψ'
  put (reg r) v m = ⟨ regs m [ r ≔ v ] , frame m , opened m , flag m ⟩
  put (slot p _) v m = ⟨ regs m , v ∷ forget p (frame m) , tt , flag m ⟩

  obj : ∀ {η ψ A} → Obj Σ ψ A → Mach Σ η ψ → Val A
  obj (pair c e) m = pack (arg c m) (arg e m)
  obj (tuple as) m = tup (args as m)
  obj (inl a) m = inl (arg a m)
  obj (inr a) m = inr (arg a m)

  field′ : ∀ {A B} → Field A B → Val A → Val B
  field′ (get i) v = nth i v
  field′ payload v = either v (λ u → u) (λ u → u)

  {- what cmpq compares, and what sete stores, as the primitive eq gives it -}
  equal : Val ⟪ base Int ⟫ → Val ⟪ base Int ⟫ → Bool
  equal (const n) (const k) = does (n ≟ k)

  bit : Bool → Val ⟪ sum ⟫
  bit b = if b then inl (dyn (tup 0) (tup [])) else inr (dyn (tup 0) (tup []))

  {- a closure: the length of its environment, its code and its environment -}
  size : Val ⟪ fun ⟫ → ℕ
  size (pack {n} c e) = n

  code-of : (v : Val ⟪ fun ⟫) → Val (code (size v))
  code-of (pack c e) = c

  env-of : (v : Val ⟪ fun ⟫) → Val ⟪ tup (size v) ⟫
  env-of (pack c e) = e

{- the interpreter for a program with the definitions ds -}
module _ {Σ : List ℕ} (ds : All (λ m → Body Σ (called m)) Σ) where
  open Vals Σ

  run : ∀ {n Bs ψ} → ℕ → Blocks Σ n Bs → ∀ η → Mach Σ η ψ → Seq Σ n Bs ψ → Result (Val Any)
  jump : ∀ {n Bs Δ} → ℕ → Blocks Σ n Bs → ℕ → Bs ∋ Δ → Env Δ → Result (Val Any)
  call : ∀ {η} → ℕ → Val (code η) → Val ⟪ tup η ⟫ → Val Any → Result (Val Any)

  run ck bs η m (movq a d ∷ k) = run ck bs η (put d (arg a m) m) k
  run ck bs η m (subq a r e ∷ k) =
    run ck bs η (put {n = 0} (reg {τ = ℤty} r) (δ sub (cast {η = η} e (regs m ⦅ r ⦆)) (arg a m)) m) k
  run ck bs η m (cmpq a₂ a₁ ∷ k) = run ck bs η ⟨ regs m , frame m , opened m , equal (arg a₁ m) (arg a₂ m) ⟩ k
  run ck bs η m (sete d ∷ k) = run ck bs η (put d (bit (flag m)) m) k
  run ck bs η m (testinl a ∷ k) = run ck bs η ⟨ regs m , frame m , opened m , either (arg a m) (λ _ → true) (λ _ → false) ⟩ k
  run ck bs η m (alloc o d ∷ k) = run ck bs η (put d (obj o m) m) k
  run ck bs η m (load f a d ∷ k) = run ck bs η (put d (field′ f (arg a m)) m) k
  run ck bs η m (loadfst x r ∷ k) =
    let v = frame m ! x in
    run ck bs (size v) ⟨ wipeᵣ (regs m) [ r ≔ code-of v ] , frame m , (code-of v , env-of v) , flag m ⟩ k
  run ck bs η m (loadsnd r ∷ k) = run ck bs η ⟨ regs m [ r ≔ proj₂ (opened m) ] , frame m , opened m , flag m ⟩ k
  run ck bs η m (callq a e₁ e₂ ∷ k) =
    call ck (arg a m) (cast e₁ (regs m ⦅ rdi ⦆)) (cast e₂ (regs m ⦅ rsi ⦆)) >>= λ v →
    run ck bs η ⟨ rv v tt tt , frame m , tt , tt ⟩ k
  run ck bs η m (chk t x d ∷ k) =
    project? t (frame m ! x) >>= λ v → run ck bs η (put d v ⟨ regs m [ rax ≔ tt ] , frame m , opened m , tt ⟩) k
  run ck bs η m (retq e) = ret (cast e (regs m ⦅ rax ⦆))
  run ck bs η m (jmp l) = jump ck bs η l (frame m)
  run ck bs η m (je l₁ l₂) = jump ck bs η (if flag m then l₁ else l₂) (frame m)

  jump ck (bs ▷ k) η Z φ = run ck bs η ⟨ rv tt tt tt , φ , tt , tt ⟩ k
  jump ck (bs ▷ k) η (S l) φ = jump ck bs η l φ

  call zero c e w = timeout
  call {η} (suc ck) (code f) e w = run ck (Body.blocks (ds ! f)) η ⟨ rv tt e w , [] , tt , tt ⟩ (Body.start (ds ! f))

{- a program runs the start of main, with no slot, no register and no flag -}
sem : Program → Semantics
sem (program {Σ} ds (body n bs k)) = semantics (Val Any) obs (λ ck → run ds ck bs 0 ⟨ rv tt tt tt , [] , tt , tt ⟩ k)
  where open Vals Σ
