{-

  A machine for X86ᵀ (Language/Typed/X86.agda), a pilot
  (Theorems/TAL.agda): the X86 machine (Semantics/CEK/X86.agda) on typed
  states, with the values of the Clos5ᵀ machine (Semantics/CEK/Typed/Clos5.agda).
  A state
    run k bs σ η m
  runs the sequence k, with the blocks bs it may jump to, the call
  stack σ, and the registers, frame, open closure and flag m (Mach),
  whose types are those of k's start; η is α, the length of the open
  closure's environment, so a register of type codeα holds code η.
  The frame holds the slots assigned so far, as the CFGᵀ machine's
  does; an unset register, an unset flag and the open closure (when
  there is none) hold nothing (⊤).

  An instruction reads its operands, which have the types it needs, and
  writes its destination, as in X86. load fst x opens the closure in
  slot x (η := the length of its environment), and records its code
  and environment, which load snd reads. callq runs the start of the
  definition of its code with %rdi and %rsi, pushing the rest of the
  caller's sequence, its blocks and its frame; retq returns %rax to it.
  The only error is chk's: a value of another kind than its tag
  (proj?, as project in the typed machines).

-}

module Semantics.CEK.Typed.X86 where

open import Language.Prim using (sub)
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.X86
open import Framework.Lookup using (_!_; forget)
open import Semantics.Observation using (o-error)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Semantics.CEK.Typed.Clos5
  using (Val; code; pack; const; tup; inl; inr; dyn; obs; int; elems; choose; δᵀ; proj?) public
open import Semantics.CEK.Typed.Imp using (Frame) renaming (atom to value-of) public

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

module _ (Σ : List ℕ) where

  {- the values of a register type, α being η -}
  RV : ℕ → RTy → Set
  RV η (ty A) = Val Σ A
  RV η codeα = Val Σ (code η)
  RV η tupα = Val Σ ⟪ tup η ⟫

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
  Opened η (just _) = Val Σ (code η) × Val Σ ⟪ tup η ⟫

  Flag : Bool → Set
  Flag true = Bool
  Flag false = ⊤

  {- the registers, frame, open closure and flag of a state of type ψ -}
  record Mach (η : ℕ) (ψ : St) : Set where
    constructor ⟨_,_,_,_⟩
    field
      regs : RegVals η (St.rs ψ)
      frame : Frame Σ (St.fr ψ)
      opened : Opened η (St.op ψ)
      flag : Flag (St.fl ψ)

open Mach public

module _ {Σ : List ℕ} where

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

  args : ∀ {η ψ j} → Vec (Arg Σ ψ (ty Any)) j → Mach Σ η ψ → Vec (Val Σ Any) j
  args [] m = []
  args (a ∷ as) m = arg a m ∷ args as m

  {- d := v -}
  put : ∀ {n η ψ τ ψ'} → Dst n ψ τ ψ' → RV Σ η τ → Mach Σ η ψ → Mach Σ η ψ'
  put (reg r) v m = ⟨ regs m [ r ≔ v ] , frame m , opened m , flag m ⟩
  put (slot p _) v m = ⟨ regs m , v ∷ forget p (frame m) , tt , flag m ⟩

  obj : ∀ {η ψ A} → Obj Σ ψ A → Mach Σ η ψ → Val Σ A
  obj (pair c e) m = pack (arg c m) (arg e m)
  obj (tuple as) m = tup (args as m)
  obj (inl a) m = inl (arg a m)
  obj (inr a) m = inr (arg a m)

  field′ : ∀ {A B} → Field A B → Val Σ A → Val Σ B
  field′ (get i) v = lookup (elems v) i
  field′ payload v = choose v (λ u → u) (λ u → u)

  {- what sete stores, as the primitive eq gives it -}
  bit : Bool → Val Σ ⟪ sum ⟫
  bit b = if b then inl (dyn (tup 0) (tup [])) else inr (dyn (tup 0) (tup []))

  is-inl : Val Σ ⟪ sum ⟫ → Bool
  is-inl v = choose v (λ _ → true) (λ _ → false)

  {- a closure: the length of its environment, its code and its environment -}
  size : Val Σ ⟪ fun ⟫ → ℕ
  size (pack {n} c e) = n

  code-of : (v : Val Σ ⟪ fun ⟫) → Val Σ (code (size v))
  code-of (pack c e) = c

  env-of : (v : Val Σ ⟪ fun ⟫) → Val Σ ⟪ tup (size v) ⟫
  env-of (pack c e) = e

data Stack (Σ : List ℕ) : Set where
  halt : Stack Σ
  retK : ∀ {n Bs Δ} → Seq Σ n Bs (returned Δ) → Blocks Σ n Bs → Frame Σ Δ → Stack Σ → Stack Σ   {- the caller -}

data State (Σ : List ℕ) : Set where
  run : ∀ {n Bs ψ} → Seq Σ n Bs ψ → Blocks Σ n Bs → Stack Σ → (η : ℕ) → Mach Σ η ψ → State Σ

{- the machine for a program with the definitions ds -}
module _ {Σ : List ℕ} (ds : All (λ m → Body Σ (called m)) Σ) where

  {- run a block, in the frame φ -}
  go : ∀ {n Δ} → Blk Σ n Δ → Stack Σ → ∀ η → Frame Σ Δ → State Σ
  go (blk bs k) σ η φ = run k bs σ η ⟨ rv tt tt tt , φ , tt , tt ⟩

  {- call code f with the environment e and the argument w -}
  enter : ∀ {η} → Val Σ (code η) → Val Σ ⟪ tup η ⟫ → Val Σ Any → Stack Σ → Next (State Σ)
  enter {η} (code f) e w σ = next (run (Body.start (ds ! f)) (Body.blocks (ds ! f)) σ η ⟨ rv tt e w , [] , tt , tt ⟩)

  {- the check of chk, then the move -}
  checked : ∀ {n Bs η A ψ ψ'} → Maybe (Val Σ A) → Dst n ψ (ty A) ψ' → Seq Σ n Bs ψ' → Blocks Σ n Bs → Stack Σ
    → Mach Σ η ψ → Next (State Σ)
  checked {η = η} (just v) d k bs σ m = next (run k bs σ η (put d v m))
  checked nothing d k bs σ m = stop o-error

  step : State Σ → Next (State Σ)
  step (run (movq a d ∷ k) bs σ η m) = next (run k bs σ η (put d (arg a m) m))
  step (run (subq a r e ∷ k) bs σ η m) =
    next (run k bs σ η (put {n = 0} (reg {τ = ℤty} r) (δᵀ sub (int (cast {η = η} e (regs m ⦅ r ⦆))) (int (arg a m))) m))
  step (run (cmpq a₂ a₁ ∷ k) bs σ η m) =
    next (run k bs σ η ⟨ regs m , frame m , opened m , does (int (arg a₁ m) ≟ int (arg a₂ m)) ⟩)
  step (run (sete d ∷ k) bs σ η m) = next (run k bs σ η (put d (bit (flag m)) m))
  step (run (testinl a ∷ k) bs σ η m) = next (run k bs σ η ⟨ regs m , frame m , opened m , is-inl (arg a m) ⟩)
  step (run (alloc o d ∷ k) bs σ η m) = next (run k bs σ η (put d (obj o m) m))
  step (run (load f a d ∷ k) bs σ η m) = next (run k bs σ η (put d (field′ f (arg a m)) m))
  step (run (loadfst x r ∷ k) bs σ η m) =
    let v = frame m ! x in
    next (run k bs σ (size v) ⟨ wipeᵣ (regs m) [ r ≔ code-of v ] , frame m , (code-of v , env-of v) , flag m ⟩)
  step (run (loadsnd r ∷ k) bs σ η m) = next (run k bs σ η ⟨ regs m [ r ≔ proj₂ (opened m) ] , frame m , opened m , flag m ⟩)
  step (run (callq a e₁ e₂ ∷ k) bs σ η m) =
    enter (arg a m) (cast e₁ (regs m ⦅ rdi ⦆)) (cast e₂ (regs m ⦅ rsi ⦆)) (retK k bs (frame m) σ)
  step (run (chk t x d ∷ k) bs σ η m) =
    checked (proj? t (frame m ! x)) d k bs σ ⟨ regs m [ rax ≔ tt ] , frame m , opened m , tt ⟩
  step (run (retq e) bs halt η m) = stop (obs (cast e (regs m ⦅ rax ⦆)))
  step (run (retq e) bs (retK k bs' φ σ) η m) = next (run k bs' σ η ⟨ rv (cast e (regs m ⦅ rax ⦆)) tt tt , φ , tt , tt ⟩)
  step (run (jmp l) bs σ η m) = next (go (block bs l) σ η (frame m))
  step (run (je l₁ l₂) bs σ η m) = next (if flag m then go (block bs l₁) σ η (frame m) else go (block bs l₂) σ η (frame m))

{- a program starts with the start of main, with no slot, no register
   and no flag -}
sem : Program → Machine
sem (program ds (body n bs k)) = machine (State _) (step ds) (run k bs halt 0 ⟨ rv tt tt tt , [] , tt , tt ⟩)
