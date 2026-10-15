{-

  A machine for X86μ (Mu/Language/X86.agda), as the X86ᵀ machine
  (Semantics/CEK/Typed/X86.agda), with the values of the Clos5μ machine
  (Mu/Semantics/CEK/Clos5.agda). A state
    run k bs σ η m
  runs the sequence k, with the blocks bs it may jump to, the call
  stack σ, and the registers, frame, open closure and flag m (Mach),
  whose types are those of k's start; η is α, the types of the open
  closure's environment (the witness that the type of a closure hides),
  so a register of type codeα A B holds a value of type code η A B, and
  one of type tupα a tuple of type tup η. The frame holds the slots
  assigned so far; an unset register, an unset flag and the open
  closure (when there is none) hold nothing (⊤).

  load fst x opens the closure in slot x (η := the types of its
  environment), and records its code and environment, which load snd
  reads. callq runs the start of the definition of its code with %rdi
  and %rsi, pushing the rest of the caller's sequence, its blocks and
  its frame; retq returns %rax to it. ↑ and ↓ fold and unfold a value;
  case assigns the payload of an injection and jumps by its side.
  Nothing fails.

-}

module Mu.Semantics.CEK.X86 where

open import Language.Prim using (sub)
open import Mu.Language.Type
open import Mu.Language.X86
open import Framework.Lookup using (forget)
open import Mu.Framework.AllUtil using (All; []; _∷_; lookup)
open import Semantics.CEK.Smallstep using (Machine; Next; next; stop; machine)
open import Mu.Semantics.CEK.Clos5
  using (Val; code; pack; const; tup; inl; inr; fold; obs; int; elems; choose; unfoldᵥ; δᵀ) public
open import Mu.Semantics.CEK.Imp using (Frame) renaming (atom to value-of) public

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (does)

module _ (Σ : List DSig) where

  {- the values of a register type, α being η -}
  RV : Ctx → RTy → Set
  RV η (ty A) = Val Σ A
  RV η (codeα A B) = Val Σ (code η A B)
  RV η tupα = Val Σ (tup η)

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
  Opened η (just _) = Val Σ (tup η)

  Flag : Bool → Set
  Flag true = Bool
  Flag false = ⊤

  {- the registers, frame, open closure and flag of a state of type ψ -}
  record Mach (η : Ctx) (ψ : St) : Set where
    constructor ⟨_,_,_,_⟩
    field
      regs : RegVals η (St.rs ψ)
      frame : Frame Σ (St.fr ψ)
      envα : Opened η (St.op ψ)
      flag : Flag (St.fl ψ)

open Mach public

module _ {Σ : List DSig} where

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
  forgetᵥ (just (codeα _ _)) v = tt
  forgetᵥ (just tupα) v = tt
  forgetᵥ nothing v = tt

  wipeᵣ : ∀ {η η' Γ} → RegVals Σ η Γ → RegVals Σ η' (wipe Γ)
  wipeᵣ {Γ = Γ} ρ =
    rv (forgetᵥ (Regs.ax Γ) (RegVals.ax ρ)) (forgetᵥ (Regs.di Γ) (RegVals.di ρ)) (forgetᵥ (Regs.si Γ) (RegVals.si ρ))

  arg : ∀ {η ψ τ} → Arg Σ ψ τ → Mach Σ η ψ → RV Σ η τ
  arg (atom a) m = value-of (frame m) a
  arg (reg r e) m = cast e (regs m ⦅ r ⦆)
  arg (a ↑) m = fold (arg a m)
  arg (a ↓) m = unfoldᵥ (arg a m)

  args : ∀ {η ψ Δ} → All (λ A → Arg Σ ψ (ty A)) Δ → Mach Σ η ψ → All (Val Σ) Δ
  args [] m = []
  args (a ∷ as) m = arg a m ∷ args as m

  {- d := v -}
  put : ∀ {n η ψ τ ψ'} → Dst n ψ τ ψ' → RV Σ η τ → Mach Σ η ψ → Mach Σ η ψ'
  put (reg r) v m = ⟨ regs m [ r ≔ v ] , frame m , envα m , flag m ⟩
  put (slot p _) v m = ⟨ regs m , v ∷ forget p (frame m) , tt , flag m ⟩

  obj : ∀ {η ψ A} → Obj Σ ψ A → Mach Σ η ψ → Val Σ A
  obj (pair c e) m = pack (arg c m) (arg e m)
  obj (tuple as) m = tup (args as m)
  obj (inl a) m = inl (arg a m)
  obj (inr a) m = inr (arg a m)

  {- what sete stores, as the primitive eq gives it -}
  bit : Bool → Val Σ (tup [] ⊹ tup [])
  bit b = if b then inl (tup []) else inr (tup [])

  {- a closure: the types of its environment, its code and its environment -}
  size : ∀ {A B} → Val Σ (A ⇒ B) → Ctx
  size (pack {Δ} c e) = Δ

  code-of : ∀ {A B} (v : Val Σ (A ⇒ B)) → Val Σ (code (size v) A B)
  code-of (pack c e) = c

  env-of : ∀ {A B} (v : Val Σ (A ⇒ B)) → Val Σ (tup (size v))
  env-of (pack c e) = e

data Stack (Σ : List DSig) : Type → Set where
  halt : ∀ {A} → Stack Σ A
  retK : ∀ {n R Bs Δ B} → Seq Σ n R Bs (returned Δ B) → Blocks Σ n R Bs → Frame Σ Δ → Stack Σ R → Stack Σ B   {- the caller -}

data State (Σ : List DSig) : Set where
  run : ∀ {n R Bs ψ} → Seq Σ n R Bs ψ → Blocks Σ n R Bs → Stack Σ R → (η : Ctx) → Mach Σ η ψ → State Σ

{- the machine for a program with the definitions ds -}
module _ {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ) where

  {- run a block, in the frame φ -}
  go : ∀ {n R Δ} → Blk Σ n R Δ → Stack Σ R → ∀ η → Frame Σ Δ → State Σ
  go (blk bs k) σ η φ = run k bs σ η ⟨ rv tt tt tt , φ , tt , tt ⟩

  {- call code f with the environment e and the argument w -}
  enter : ∀ {η A B} → Val Σ (code η A B) → Val Σ (tup η) → Val Σ A → Stack Σ B → Next (State Σ)
  enter {η} (code f) e w σ = next (run (Body.start (lookup ds f)) (Body.blocks (lookup ds f)) σ η ⟨ rv tt e w , [] , tt , tt ⟩)

  step : State Σ → Next (State Σ)
  step (run (movq a d ∷ k) bs σ η m) = next (run k bs σ η (put d (arg a m) m))
  step (run (subq a r e ∷ k) bs σ η m) =
    next (run k bs σ η (put {n = 0} (reg {τ = ℤty} r) (δᵀ sub (int (cast {η = η} e (regs m ⦅ r ⦆))) (int (arg a m))) m))
  step (run (cmpq a₂ a₁ ∷ k) bs σ η m) =
    next (run k bs σ η ⟨ regs m , frame m , envα m , does (int (arg a₁ m) ≟ int (arg a₂ m)) ⟩)
  step (run (sete d ∷ k) bs σ η m) = next (run k bs σ η (put d (bit (flag m)) m))
  step (run (alloc o d ∷ k) bs σ η m) = next (run k bs σ η (put d (obj o m) m))
  step (run (load i a d ∷ k) bs σ η m) = next (run k bs σ η (put d (lookup (elems (arg a m)) i) m))
  step (run (loadfst x r ∷ k) bs σ η m) =
    let v = lookup (frame m) x in
    next (run k bs σ (size v) ⟨ wipeᵣ (regs m) [ r ≔ code-of v ] , frame m , env-of v , flag m ⟩)
  step (run (loadsnd r ∷ k) bs σ η m) = next (run k bs σ η ⟨ regs m [ r ≔ envα m ] , frame m , envα m , flag m ⟩)
  step (run (callq a e₁ e₂ ∷ k) bs σ η m) =
    enter (arg a m) (cast e₁ (regs m ⦅ rdi ⦆)) (cast e₂ (regs m ⦅ rsi ⦆)) (retK k bs (frame m) σ)
  step (run (retq e) bs halt η m) = stop (obs (cast e (regs m ⦅ rax ⦆)))
  step (run (retq e) bs (retK k bs' φ σ) η m) = next (run k bs' σ η ⟨ rv (cast e (regs m ⦅ rax ⦆)) tt tt , φ , tt , tt ⟩)
  step (run (jmp l) bs σ η m) = next (go (block bs l) σ η (frame m))
  step (run (case x p _ l₁ l₂) bs σ η m) =
    next (choose (lookup (frame m) x) (λ u → go (block bs l₁) σ η (u ∷ forget p (frame m)))
                                      (λ u → go (block bs l₂) σ η (u ∷ forget p (frame m))))

{- a program starts with the start of main, with no slot, no register
   and no flag -}
sem : ∀ {A} → Program A → Machine
sem (program ds (body n bs k)) = machine (State _) (step ds) (run k bs halt [] ⟨ rv tt tt tt , [] , tt , tt ⟩)
