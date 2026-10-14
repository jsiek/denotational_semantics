{-

  Correctness of typed select instructions (CFGᵀ → X86,
  Compiler/Typed/Select.agda) by a simulation of the CFGᵀ machine by the
  untyped X86 machine (Both, proof/Framework/Both.agda), for every CFGᵀ
  program: X86 is unchanged and keeps its own trapped errors, and the
  proof shows that select's code reaches none of them.

  An X86 value is the erasure of a typed value (⌊_⌋): a code pointer is
  its definition's level, a closure a pair, and an injection into Any
  the value itself. The X86 frame holds the erasure of slot x of the
  CFGᵀ frame at the level of x (Agree), and is large enough for the
  tail and the blocks (Fits; proof/Compiler/Typed/SelectFacts.agda). The
  X86 call stack holds, for each CFGᵀ return frame (seqK, retK), the
  caller's frame and the instructions that move %rax where the caller
  wants it (_~_).

  One CFGᵀ step (a statement) is matched by the few X86 instructions
  selected for it: they compute its value into its destination (sel),
  or err exactly where the CFGᵀ machine does (a failed project, whose
  test instruction errs: sel-proj), or call (callc). A return pops the
  X86 stack as the CFGᵀ continuation says (back). Reading a slot, an
  unset register or a missing label or definition, and a value of the
  wrong kind other than at a project's test, never happen: Agree, Fits
  and SelectFacts rule them out.

  This proof, between the machines of CFGᵀ and X86, is shared by the
  CEK machine + simulation and the reduction semantics + simulation
  developments.

-}

module proof.Correctness.Typed.CEK.SelectSim where

open import Framework.Primitives using (Base; Nat; Int; 𝔹; Unit; Void; Blame)
open import Language.Prim using (sub; eq; bool)
open import Language.Typed.Type hiding (_≟_)
open import Framework.Membership using (_⊑_; ⊑-∋)
open import Framework.Lookup using (_!_; forget)
open import Framework.ListUtil using (_‼_; has-length; proj)
open import Language.Typed.CFG as CFG using (Tail; return; seq; goto; case; Blocks; Body; Blk; blk; block)
import Language.Typed.Imp as Imp
open import Compiler.Typed.Select
open import proof.Compiler.Typed.SelectFacts using (global-sel; block-sel; depth-≥; block-depth)
open import proof.Framework.Lookup using (lvl-<; lvl-⊑; forget-!)
open import Semantics.Observation using (Obs; o-const; o-tuple; o-inl; o-inr; o-error)
open import proof.Semantics.CEK.Smallstep using (Machine; Next; next; stop; Star; ε; _◅_; _◅◅_; Plus; plus; step⁺; star-plus)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent)
open import proof.Framework.Both Obs using (Both; halt; move; both-fsim)
import Language.X86 as L
open L using (Instr; Loc; Arg; Jump; Reg; rax; rdi; rsi; reg; var; loc; imm; movq; subq; callq; retq; jmp; je)
import Semantics.CEK.X86 as X
import Semantics.CEK.Values as XV
import Semantics.CEK.Typed.Clos5 as V
import Semantics.CEK.Typed.CFG as G
import Semantics.CEK.Typed.Imp as I
open G using (atom; Res; value; fail; call; run)

open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ; _≟_) renaming (_-_ to _-ℤ_)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; length; replicate)
open import Data.List.Properties using (++-identityʳ; length-replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _⊔_; _∸_; _+_; s≤s; z≤n)
import Data.Nat as N
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; <⇒≢; m≤n+m∸n; ≤-reflexive)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; lookup; map; toList)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; does)

{- Erasure ---------------------------------------------------------------------}

⌊_⌋ : ∀ {Σ A} → V.Val Σ A → X.Val
⌊_⌋* : ∀ {Σ n} → Vec (V.Val Σ Any) n → List X.Val
⌊ V.code f ⌋ = X.code (lvl f)
⌊ V.pack c e ⌋ = X.pair ⌊ c ⌋ ⌊ e ⌋
⌊ V.const {B} c ⌋ = X.const B c
⌊ V.tup vs ⌋ = X.tup ⌊ vs ⌋*
⌊ V.inl v ⌋ = X.inl ⌊ v ⌋
⌊ V.inr v ⌋ = X.inr ⌊ v ⌋
⌊ V.dyn G v ⌋ = ⌊ v ⌋
⌊ [] ⌋* = []
⌊ v ∷ vs ⌋* = ⌊ v ⌋ ∷ ⌊ vs ⌋*

obs-⌊⌋ : ∀ {Σ A} (v : V.Val Σ A) → X.obs ⌊ v ⌋ ≡ V.obs v
obs-⌊⌋* : ∀ {Σ n} (vs : Vec (V.Val Σ Any) n) → XV.obs-list ⌊ vs ⌋* ≡ V.obs-vec vs
obs-⌊⌋ (V.code f) = refl
obs-⌊⌋ (V.pack c e) = refl
obs-⌊⌋ (V.const c) = refl
obs-⌊⌋ (V.tup vs) = cong o-tuple (obs-⌊⌋* vs)
obs-⌊⌋ (V.inl v) = cong o-inl (obs-⌊⌋ v)
obs-⌊⌋ (V.inr v) = cong o-inr (obs-⌊⌋ v)
obs-⌊⌋ (V.dyn G v) = obs-⌊⌋ v
obs-⌊⌋* [] = refl
obs-⌊⌋* (v ∷ vs) = cong₂′ (obs-⌊⌋ v) (obs-⌊⌋* vs)
  where cong₂′ : ∀ {a b : Obs} {as bs} → a ≡ b → as ≡ bs → a ∷ as ≡ b ∷ bs
        cong₂′ refl refl = refl

len-⌊⌋ : ∀ {Σ n} (vs : Vec (V.Val Σ Any) n) → length ⌊ vs ⌋* ≡ n
len-⌊⌋ [] = refl
len-⌊⌋ (v ∷ vs) = cong suc (len-⌊⌋ vs)

has-len : ∀ {A : Set} (vs : List A) n → length vs ≡ n → has-length n vs ≡ true
has-len [] zero e = refl
has-len (v ∷ vs) (suc n) e = has-len vs n (cong N.pred e)

{- component i of a tuple, in X86 -}
proj-ok : ∀ {Σ n} (vs : Vec (V.Val Σ Any) n) (i : Fin n) → proj i ⌊ vs ⌋* ≡ just ⌊ lookup vs i ⌋
proj-ok {n = suc n} (v ∷ vs) zero = cong (λ b → if b then just ⌊ v ⌋ else nothing) (has-len _ n (len-⌊⌋ vs))
proj-ok (v ∷ vs) (suc i) = proj-ok vs i

has-len⁻ : ∀ {A : Set} (vs : List A) n → has-length n vs ≡ true → length vs ≡ n
has-len⁻ [] zero e = refl
has-len⁻ [] (suc n) ()
has-len⁻ (v ∷ vs) zero ()
has-len⁻ (v ∷ vs) (suc n) e = cong suc (has-len⁻ vs n e)

proj-bad : ∀ {A : Set} (vs : List A) {k} (i : Fin k) → length vs ≢ k → proj i vs ≡ nothing
proj-bad [] zero ne = refl
proj-bad [] (suc i) ne = refl
proj-bad (v ∷ vs) {suc k} zero ne with has-length k vs in e
... | true = ⊥-elim (ne (cong suc (has-len⁻ vs k e)))
... | false = refl
proj-bad (v ∷ vs) (suc i) ne = proj-bad vs i (ne ∘ cong suc)

{- Frames ----------------------------------------------------------------------}

module _ {Σ : List ℕ} where

  {- the X86 frame holds slot x at the level of x -}
  record Agree {Δ} (φ : G.Frame Σ Δ) (φₓ : X.Frame) : Set where
    constructor agree
    field at : ∀ {B} (x : Δ ∋ B) → φₓ ‼ lvl x ≡ just ⌊ φ ! x ⌋

  {- the X86 frame is large enough for the tail and its blocks -}
  record Fits {Bs Δ} (t : Tail Σ Bs Δ) (bs : Blocks Σ Bs) (φₓ : X.Frame) : Set where
    constructor mkfits
    field
      tl : depth t ≤ length φₓ
      bl : blocks-depth bs ≤ length φₓ

  arg-ok : ∀ {Δ A} {φ : G.Frame Σ Δ} {φₓ ρ} → Agree φ φₓ → ∀ (a : Imp.Atm Σ Δ A)
    → X.arg φₓ ρ (select-atm a) ≡ just ⌊ atom φ a ⌋
  arg-ok ag (Imp.var x) = Agree.at ag x
  arg-ok ag (Imp.lit B c) = refl
  arg-ok ag (Imp.ref f) = refl

upd : ∀ (φ : X.Frame) k w → k < length φ
  → Σ[ φ' ∈ X.Frame ] φ X.[ k ]≔ w ≡ just φ' × φ' ‼ k ≡ just w × (∀ j → j ≢ k → φ' ‼ j ≡ φ ‼ j) × length φ' ≡ length φ
upd (u ∷ φ) zero w _ = w ∷ φ , refl , refl , (λ { zero ne → ⊥-elim (ne refl) ; (suc j) _ → refl }) , refl
upd (u ∷ φ) (suc k) w (s≤s lt) with upd φ k w lt
... | φ' , e , r , o , l = u ∷ φ' , cong (mmap (u ∷_)) e , r , (λ { zero _ → refl ; (suc j) ne → o j (ne ∘ cong suc) }) , cong suc l

{- slot |Δ'| := v, forgetting the slots from |Δ'| on -}
write : ∀ {Σ Δ Δ' A} {φ : G.Frame Σ Δ} {φₓ} → Agree φ φₓ → (p : Δ' ⊑ Δ) → length Δ' < length φₓ → (v : V.Val Σ A)
  → Σ[ φₓ' ∈ X.Frame ] φₓ X.[ length Δ' ]≔ ⌊ v ⌋ ≡ just φₓ' × Agree (v ∷ forget p φ) φₓ' × length φₓ' ≡ length φₓ
write {φ = φ} {φₓ} ag p lt v with upd φₓ _ ⌊ v ⌋ lt
... | φₓ' , e , r , o , l = φₓ' , e , agree ag' , l
  where
  ag' : ∀ {B} (x : _ ∋ B) → φₓ' ‼ lvl x ≡ just ⌊ (v ∷ forget p φ) ! x ⌋
  ag' Z = r
  ag' (S y) = trans (o (lvl y) (<⇒≢ (lvl-< y)))
    (trans (cong (φₓ ‼_) (sym (lvl-⊑ p y)))
      (trans (Agree.at ag (⊑-∋ p y)) (cong (just ∘ ⌊_⌋) (sym (forget-! p φ y)))))

{- The simulation, for a program with definitions ds and main body b₀ ---------}

module Sim {Σ : List ℕ} (ds : All (λ n → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) Σ) (b₀ : Body Σ []) where

  P = CFG.program ds b₀
  xds = select-defs ds
  L₁ = G.sem P
  L₂ = X.sem (select P)

  ins : ∀ {Bs Δ} → Tail Σ Bs Δ → List Instr
  ins t = L.Block.instrs (select-tail t)

  end : ∀ {Bs Δ} → Tail Σ Bs Δ → Jump
  end t = L.Block.jump (select-tail t)

  {- the CFGᵀ continuation, and the X86 call stack -}
  infix 4 _~_
  data _~_ : G.Cont Σ → X.Stack → Set where
    halt : G.halt ~ X.halt
    seqK : ∀ {Bs Δ Δ'} {p : Δ' ⊑ Δ} {φ} {t : Tail Σ Bs (Any ∷ Δ')} {bs κ φₓ σ} → Agree φ φₓ → Fits t bs φₓ → κ ~ σ
      → G.seqK p φ t bs κ ~ X.retK (movq (loc (reg rax)) (var (length Δ')) ∷ ins t) (end t) (select-blocks bs) φₓ σ
    retK : ∀ {κ σ bs₂ φₓ} → κ ~ σ → G.retK κ ~ X.retK (movq (loc (reg rax)) (reg rax) ∷ []) retq bs₂ φₓ σ

  data Match : G.State Σ → X.State → Set where
    exec~ : ∀ {Bs Δ} {t : Tail Σ Bs Δ} {φ bs κ σ f φₓ ρ} → Agree φ φₓ → Fits t bs φₓ → κ ~ σ
      → Match (G.exec t φ bs κ) (X.run (ins t) (end t) (select-blocks bs) σ f φₓ ρ)

  B = Both {L₁ = L₁} {L₂ = L₂} Match

  private variable
    A : Ty
    Δ : Ctx
    d : Loc
    is : List Instr
    j : Jump
    bs₂ : List L.Block
    σ : X.Stack
    f : Maybe Data.Bool.Bool
    φₓ : X.Frame
    ρ : X.Regs
    s₁ : G.State Σ
    s₂ : X.State

  {- one X86 step, and steps that store w into d, or err -}
  infix 2 _⟶_
  record _⟶_ (s s' : X.State) : Set where
    constructor ⟨_⟩
    field step≡ : X.step xds s ≡ next s'

  infixr 5 _▸_ _▸⁺_
  _▸_ : ∀ {s s' t} → s ⟶ s' → Star L₂ s' t → Star L₂ s t
  ⟨ e ⟩ ▸ σ = e ◅ σ

  _▸⁺_ : ∀ {s s' t} → s ⟶ s' → Star L₂ s' t → Plus L₂ s t
  ⟨ e ⟩ ▸⁺ σ = plus e σ

  {- return %rax to the caller -}
  ret-pop : ∀ {is j bs bs₂ φ σ f φₓ ρ w} → ρ rax ≡ just w
    → X.run [] retq bs₂ (X.retK is j bs φ σ) f φₓ ρ ⟶ X.run is j bs σ nothing φ (X.regs (just w) nothing nothing)
  ret-pop {is} {j} {bs} {φ = φ} {σ} e = ⟨ cong (λ m → X.back m is j bs φ σ) e ⟩

  {- slot k := %rax -}
  mv-var : ∀ {is j bs σ f φₓ φₓ' ρ k w} → ρ rax ≡ just w → φₓ X.[ k ]≔ w ≡ just φₓ'
    → X.run (movq (loc (reg rax)) (var k) ∷ is) j bs σ f φₓ ρ ⟶ X.run is j bs σ f φₓ' ρ
  mv-var {is} {j} {bs} {σ} {f} {φₓ} {ρ = ρ} {k} e u =
    ⟨ trans (cong (λ m → X.put (var k) m φₓ ρ (X.run is j bs σ f)) e) (cong (λ m → X.upd m ρ (X.run is j bs σ f)) u) ⟩

  record Puts (t : X.State) (d : Loc) (is : List Instr) (j : Jump) (bs₂ : List L.Block) (σ : X.Stack)
    (φₓ : X.Frame) (w : X.Val) : Set where
    constructor puts
    field
      {ρ'} : X.Regs
      {f'} : Maybe Data.Bool.Bool
      put≡ : X.step xds t ≡ X.put d (just w) φₓ ρ' (X.run is j bs₂ σ f')

  record Fails (t : X.State) : Set where
    constructor fails
    field stop≡ : X.step xds t ≡ stop o-error

  {- how the code selected for a simple expression runs -}
  data XOut (d : Loc) (is : List Instr) (j : Jump) (bs₂ : List L.Block) (σ : X.Stack) (φₓ : X.Frame)
    : ∀ {A} → Res {Σ} A → X.State → Set where
    xval : ∀ {A} {v : V.Val Σ A} {s t} → Star L₂ s t → Puts t d is j bs₂ σ φₓ ⌊ v ⌋ → XOut d is j bs₂ σ φₓ (value v) s
    xfail : ∀ {A s t} → Star L₂ s t → Fails t → XOut d is j bs₂ σ φₓ (fail {A = A}) s
    xcall : ∀ {n} {g : Σ ∋ n} {e w s φ₀ ρ₀} → Agree (w ∷ e ∷ []) φ₀
      → Fits (Body.start (ds ! g)) (Body.blocks (ds ! g)) φ₀
      → Plus L₂ s (X.run (ins (Body.start (ds ! g))) (end (Body.start (ds ! g))) (select-blocks (Body.blocks (ds ! g)))
                      (X.retK (movq (loc (reg rax)) d ∷ is) j bs₂ φₓ σ) nothing φ₀ ρ₀)
      → XOut d is j bs₂ σ φₓ (call (V.pack (V.code g) e) w) s

  module _ {is j bs₂ σ f φₓ ρ} where

    m-reg : ∀ {a r w} → X.arg φₓ ρ a ≡ just w
      → X.run (movq a (reg r) ∷ is) j bs₂ σ f φₓ ρ ⟶ X.run is j bs₂ σ f φₓ (ρ X.[ r ↦ just w ])
    m-reg e = ⟨ cong (λ m → X.put (reg _) m φₓ ρ (X.run is j bs₂ σ f)) e ⟩

    m-put : ∀ {a d w} → X.arg φₓ ρ a ≡ just w → Puts (X.run (movq a d ∷ is) j bs₂ σ f φₓ ρ) d is j bs₂ σ φₓ w
    m-put e = puts (cong (λ m → X.put _ m φₓ ρ (X.run is j bs₂ σ f)) e)

    l-reg : ∀ {fl a r w} → (X.arg φₓ ρ a >>= X.get-field fl) ≡ just w
      → X.run (L.load fl a (reg r) ∷ is) j bs₂ σ f φₓ ρ ⟶ X.run is j bs₂ σ f φₓ (ρ X.[ r ↦ just w ])
    l-reg e = ⟨ cong (λ m → X.put (reg _) m φₓ ρ (X.run is j bs₂ σ f)) e ⟩

    l-put : ∀ {fl a d w} → (X.arg φₓ ρ a >>= X.get-field fl) ≡ just w
      → Puts (X.run (L.load fl a d ∷ is) j bs₂ σ f φₓ ρ) d is j bs₂ σ φₓ w
    l-put e = puts (cong (λ m → X.put _ m φₓ ρ (X.run is j bs₂ σ f)) e)

    l-fail : ∀ {fl a d v} → X.arg φₓ ρ a ≡ just v → X.get-field fl v ≡ nothing → Fails (X.run (L.load fl a d ∷ is) j bs₂ σ f φₓ ρ)
    l-fail {d = d} e e' = fails (cong (λ m → X.put d m φₓ ρ (X.run is j bs₂ σ f)) (trans (cong (_>>= _) e) e'))

    a-put : ∀ {sh as d w} → X.args φₓ ρ [] as (X.build sh) ≡ just w
      → Puts (X.run (L.alloc sh as d ∷ is) j bs₂ σ f φₓ ρ) d is j bs₂ σ φₓ w
    a-put e = puts (cong (λ m → X.put _ m φₓ ρ (X.run is j bs₂ σ f)) e)

    t-step : ∀ {a v b} → X.arg φₓ ρ a ≡ just v → X.is-inl v ≡ just b
      → X.run (L.testinl a ∷ is) j bs₂ σ f φₓ ρ ⟶ X.run is j bs₂ σ (just b) φₓ ρ
    t-step e e' = ⟨ cong (λ m → X.test m (λ f' → X.run is j bs₂ σ f' φₓ ρ)) (trans (cong (_>>= _) e) e') ⟩

    t-fail : ∀ {a v} → X.arg φₓ ρ a ≡ just v → X.is-inl v ≡ nothing → Fails (X.run (L.testinl a ∷ is) j bs₂ σ f φₓ ρ)
    t-fail e e' = fails (cong (λ m → X.test m (λ f' → X.run is j bs₂ σ f' φₓ ρ)) (trans (cong (_>>= _) e) e'))

    lp-var : ∀ {fl a v w k φₓ'} → X.arg φₓ ρ a ≡ just v → X.get-field fl v ≡ just w → φₓ X.[ k ]≔ w ≡ just φₓ'
      → X.run (L.load fl a (var k) ∷ is) j bs₂ σ f φₓ ρ ⟶ X.run is j bs₂ σ f φₓ' ρ
    lp-var e e' u = ⟨ trans (cong (λ m → X.put (var _) m φₓ ρ (X.run is j bs₂ σ f)) (trans (cong (_>>= _) e) e'))
                           (cong (λ m → X.upd m ρ (X.run is j bs₂ σ f)) u) ⟩

  bind₁ : ∀ {B : Set} {m : Maybe X.Val} {v} (k : X.Val → Maybe B) → m ≡ just v → (m >>= k) ≡ k v
  bind₁ k refl = refl

  bind₂ : ∀ {B : Set} {m₁ m₂ : Maybe X.Val} {v w} (k : X.Val → X.Val → Maybe B) → m₁ ≡ just v → m₂ ≡ just w
    → (m₁ >>= λ x → m₂ >>= λ y → k x y) ≡ k v w
  bind₂ k refl refl = refl

  args-ok : ∀ {Δ j} {φ : G.Frame Σ Δ} {φₓ ρ} → Agree φ φₓ → ∀ vs (as : Vec (Imp.Atm Σ Δ Any) j)
    (k : List X.Val → Maybe X.Val) → X.args φₓ ρ vs (toList (map select-atm as)) k ≡ k (vs ʳ++ ⌊ map (atom φ) as ⌋*)
  args-ok ag vs [] k = refl
  args-ok {φ = φ} {φₓ} {ρ} ag vs (a ∷ as) k =
    trans (bind₁ (λ v → X.args φₓ ρ (v ∷ vs) (toList (map select-atm as)) k) (arg-ok ag a)) (args-ok ag (⌊ atom φ a ⌋ ∷ vs) as k)

  get-ok : ∀ {n} (v : V.Val Σ ⟪ tup n ⟫) i → X.get-field (L.get i) ⌊ v ⌋ ≡ just ⌊ lookup (V.elems v) i ⌋
  get-ok (V.tup vs) i = proj-ok vs i

  sub-ok : ∀ (u w : V.Val Σ ⟪ base Int ⟫) → X.prim? sub ⌊ u ⌋ ⌊ w ⌋ ≡ just ⌊ V.δᵀ {Σ} sub (V.int u) (V.int w) ⌋
  sub-ok (V.const n) (V.const m) = refl

  eq-ok : ∀ (u w : V.Val Σ ⟪ base Int ⟫)
    → Σ[ b ∈ Data.Bool.Bool ] X.cmp ⌊ u ⌋ ⌊ w ⌋ ≡ just b × X.bit b ≡ ⌊ V.δᵀ {Σ} eq (V.int u) (V.int w) ⌋
  eq-ok (V.const n) (V.const m) with does (n ≟ m)
  ... | true = true , refl , refl
  ... | false = false , refl , refl

  {- the test of a project, then the move -}
  sel-proj : ∀ {d is j bs₂ σ f φₓ ρ} (t : Tag) (v : V.Val Σ Any) {a} → (∀ {ρ} → X.arg φₓ ρ a ≡ just ⌊ v ⌋)
    → XOut d is j bs₂ σ φₓ (I.ok? (V.proj? t v)) (X.run ((check t a ++ movq a d ∷ []) ++ is) j bs₂ σ f φₓ ρ)
  sel-proj tint (V.dyn (base Int) (V.const n)) e = xval (m-reg e ▸ ⟨ refl ⟩ ▸ ε) (m-put e)
  sel-proj tint (V.dyn (base Nat) (V.const n)) e = xfail (m-reg e ▸ ε) (fails refl)
  sel-proj tint (V.dyn (base 𝔹) (V.const n)) e = xfail (m-reg e ▸ ε) (fails refl)
  sel-proj tint (V.dyn (base Unit) (V.const n)) e = xfail (m-reg e ▸ ε) (fails refl)
  sel-proj tint (V.dyn (base Void) (V.const ())) e
  sel-proj tint (V.dyn (base Blame) (V.const n)) e = xfail (m-reg e ▸ ε) (fails refl)
  sel-proj tint (V.dyn (tup m) (V.tup vs)) e = xfail (m-reg e ▸ ε) (fails refl)
  sel-proj tint (V.dyn sum (V.inl v)) e = xfail (m-reg e ▸ ε) (fails refl)
  sel-proj tint (V.dyn sum (V.inr v)) e = xfail (m-reg e ▸ ε) (fails refl)
  sel-proj tint (V.dyn fun (V.pack c en)) e = xfail (m-reg e ▸ ε) (fails refl)
  sel-proj tsum (V.dyn (base B) (V.const c)) e = xfail ε (t-fail e refl)
  sel-proj tsum (V.dyn (tup m) (V.tup vs)) e = xfail ε (t-fail e refl)
  sel-proj tsum (V.dyn sum (V.inl v)) e = xval (t-step e refl ▸ ε) (m-put e)
  sel-proj tsum (V.dyn sum (V.inr v)) e = xval (t-step e refl ▸ ε) (m-put e)
  sel-proj tsum (V.dyn fun (V.pack c en)) e = xfail ε (t-fail e refl)
  sel-proj tfun (V.dyn (base B) (V.const c)) e = xfail ε (l-fail e refl)
  sel-proj tfun (V.dyn (tup m) (V.tup vs)) e = xfail ε (l-fail e refl)
  sel-proj tfun (V.dyn sum (V.inl v)) e = xfail ε (l-fail e refl)
  sel-proj tfun (V.dyn sum (V.inr v)) e = xfail ε (l-fail e refl)
  sel-proj tfun (V.dyn fun (V.pack c en)) e = xval (l-reg (bind₁ (X.get-field L.fst) e) ▸ ε) (m-put e)
  sel-proj (ttup n i) (V.dyn (base B) (V.const c)) e = xfail ε (l-fail e refl)
  sel-proj (ttup n i) (V.dyn sum (V.inl v)) e = xfail ε (l-fail e refl)
  sel-proj (ttup n i) (V.dyn sum (V.inr v)) e = xfail ε (l-fail e refl)
  sel-proj (ttup n i) (V.dyn fun (V.pack c en)) e = xfail ε (l-fail e refl)
  sel-proj (ttup n i) (V.dyn (tup m) (V.tup vs)) e with m N.≟ suc n
  ... | yes refl = xval (l-reg (trans (bind₁ (X.get-field (L.get i)) e) (proj-ok vs i)) ▸ ε) (m-put e)
  ... | no ne = xfail ε (l-fail e (proj-bad ⌊ vs ⌋* i (ne ∘ trans (sym (len-⌊⌋ vs)))))

  {- a call: open the closure, call its code, run the prologue -}
  sel-call : ∀ {d is j bs₂ σ f φₓ ρ} (F : V.Val Σ ⟪ fun ⟫) (w : V.Val Σ Any) {a₁ a₂}
    → (∀ {ρ} → X.arg φₓ ρ a₁ ≡ just ⌊ F ⌋) → (∀ {ρ} → X.arg φₓ ρ a₂ ≡ just ⌊ w ⌋)
    → XOut d is j bs₂ σ φₓ (call F w)
        (X.run (L.load L.fst a₁ (reg rax) ∷ L.load L.snd a₁ (reg rdi) ∷ movq a₂ (reg rsi) ∷ callq (loc (reg rax))
                ∷ movq (loc (reg rax)) d ∷ is) j bs₂ σ f φₓ ρ)
  sel-call {d} {is} {j} {bs₂} {σ} {f} {φₓ} {ρ} (V.pack (V.code g) e) w e₁ e₂ =
    xcall ag₀ (mkfits (≤-trans (m≤n⊔m _ _) len₀) (≤-trans (m≤m⊔n _ _) len₀))
      (l-reg (bind₁ (X.get-field L.fst) e₁) ▸⁺
        (l-reg (bind₁ (X.get-field L.snd) e₁) ▸ m-reg e₂
          ▸ ⟨ cong (λ m → X.call m k (just ⌊ e ⌋) (just ⌊ w ⌋)) (global-sel ds g) ⟩ ▸ ⟨ refl ⟩ ▸ ⟨ refl ⟩ ▸ ε))
    where
    b = ds ! g
    k = X.retK (movq (loc (reg rax)) d ∷ is) j bs₂ φₓ σ
    N = blocks-depth (Body.blocks b) ⊔ depth (Body.start b)
    ag₀ : Agree (w ∷ e ∷ []) (⌊ e ⌋ ∷ ⌊ w ⌋ ∷ X.zeros (N ∸ 2))
    ag₀ = agree λ { Z → refl ; (S Z) → refl }
    len₀ : N ≤ length (⌊ e ⌋ ∷ ⌊ w ⌋ ∷ X.zeros (N ∸ 2))
    len₀ = ≤-trans (m≤n+m∸n N 2) (≤-reflexive (cong (2 +_) (sym (length-replicate (N ∸ 2)))))

  {- the code selected for a simple expression -}
  sel : ∀ {Δ A} {φ : G.Frame Σ Δ} {φₓ} → Agree φ φₓ → ∀ (s : Imp.Simple Σ Δ A) {d is j bs₂ σ f ρ}
    → XOut d is j bs₂ σ φₓ (run s φ) (X.run (select-simple s d ++ is) j bs₂ σ f φₓ ρ)
  sel ag (Imp.atm a) = xval ε (m-put (arg-ok ag a))
  sel ag (Imp.pack c e) = xval ε (a-put (bind₂ (λ x y → X.build L.pair (x ∷ y ∷ [])) (arg-ok ag c) (arg-ok ag e)))
  sel {φ = φ} ag (Imp.callc g a) = sel-call (atom φ g) (atom φ a) (arg-ok ag g) (arg-ok ag a)
  sel ag (Imp.tuple as) = xval ε (a-put (args-ok ag [] as (X.build L.tuple)))
  sel {φ = φ} ag (Imp.get i a) = xval ε (l-put (trans (bind₁ (X.get-field (L.get i)) (arg-ok ag a)) (get-ok (atom φ a) i)))
  sel ag (Imp.inl a) = xval ε (a-put (bind₁ (λ v → X.build L.inl (v ∷ [])) (arg-ok ag a)))
  sel ag (Imp.inr a) = xval ε (a-put (bind₁ (λ v → X.build L.inr (v ∷ [])) (arg-ok ag a)))
  sel {φ = φ} ag (Imp.prim sub a b) =
    xval (m-reg (arg-ok ag a) ▸ ⟨ cong (λ m → X.put (reg rax) m _ _ _)
                                       (trans (bind₁ (λ w → just ⌊ atom φ a ⌋ >>= λ v → X.prim? sub v w) (arg-ok ag b))
                                              (sub-ok (atom φ a) (atom φ b))) ⟩ ▸ ε)
         (m-put refl)
  sel {φ = φ} {φₓ} ag (Imp.prim eq a b) {d} {is} {j} {bs₂} {σ} {f} {ρ} with eq-ok (atom φ a) (atom φ b)
  ... | bo , c , e =
    xval (⟨ cong (λ m → X.test m (λ f' → X.run (L.sete d ∷ is) j bs₂ σ f' φₓ ρ))
                 (trans (bind₂ (λ v w → X.cmp v w) (arg-ok ag a) (arg-ok ag b)) c) ⟩ ▸ ε)
         (puts (cong (λ w → X.put d (just w) φₓ ρ (X.run is j bs₂ σ (just bo))) e))
  sel ag (Imp.inject G a) = xval ε (m-put (arg-ok ag a))
  sel {φ = φ} ag (Imp.project t a) = sel-proj t (atom φ a) (arg-ok ag a)

  refit : ∀ {Bs Δ} {t : Tail Σ Bs Δ} {bs φₓ φₓ'} → length φₓ' ≡ length φₓ → Fits t bs φₓ → Fits t bs φₓ'
  refit len (mkfits a b) = mkfits (subst (_ ≤_) (sym len) a) (subst (_ ≤_) (sym len) b)

  blk-fits : ∀ {Bs Δ Δ'} {t : Tail Σ Bs Δ} (bs : Blocks Σ Bs) (l : Bs ∋ Δ') {φₓ} → Fits t bs φₓ
    → Fits (Blk.tail (block bs l)) (Blk.blocks (block bs l)) φₓ
  blk-fits bs l (mkfits _ q) with block-depth bs l
  ... | p₁ , p₂ = mkfits (≤-trans p₁ q) (≤-trans p₂ q)

  {- the X86 returns %rax to the stack, as the CFGᵀ continuation does with its value -}
  back : ∀ {κ σ bs₂ f φₓ ρ s₁ s₂} {v : V.Val Σ Any} → κ ~ σ → ρ rax ≡ just ⌊ v ⌋ → G.step ds s₁ ≡ G.cont ds v κ
    → Star L₂ s₂ (X.run [] retq bs₂ σ f φₓ ρ) → B s₁ s₂
  back {v = v} halt e st τ = halt st τ (trans (cong X.halt? e) (cong stop (obs-⌊⌋ v)))
  back {v = v} (seqK {Δ' = Δ'} {p = p} {t = t} {bs = bs} {φₓ = φₓ'} ag fits k) e st τ
    with write ag p (≤-trans (depth-≥ t) (Fits.tl fits)) v
  ... | φ'' , u , ag' , len =
    move (step⁺ st) (star-plus τ (ret-pop e ▸⁺ (mv-var refl u ▸ ε))) (exec~ ag' (refit len fits) k)
  back (retK k) e st τ = back k refl st (τ ◅◅ (ret-pop e ▸ ⟨ refl ⟩ ▸ ε))

  {- return s -}
  retn~ : ∀ {κ σ bs₂ φₓ r s₁ s₂} → G.step ds s₁ ≡ G.retn ds κ r → κ ~ σ
    → XOut (reg rax) [] retq bs₂ σ φₓ r s₂ → B s₁ s₂
  retn~ st k (xval τ (puts e)) = back k refl st (τ ◅◅ (e ◅ ε))
  retn~ st k (xfail τ (fails e)) = halt st τ e
  retn~ st k (xcall ag fits π) = move (step⁺ st) π (exec~ ag fits (retK k))

  {- seq p s t -}
  assign~ : ∀ {Bs Δ Δ' A} {p : Δ' ⊑ Δ} {φ φₓ} {t : Tail Σ Bs (A ∷ Δ')} {bs κ σ r s₁ s₂}
    → G.step ds s₁ ≡ G.assign ds p φ t bs κ r → Agree φ φₓ → Fits t bs φₓ → κ ~ σ
    → XOut (var (length Δ')) (ins t) (end t) (select-blocks bs) σ φₓ r s₂ → B s₁ s₂
  assign~ {p = p} {t = t} {bs = bs} {σ = σ} st ag fits k (xval {v = v} τ (puts {ρ'} {f'} e))
    with write ag p (≤-trans (depth-≥ t) (Fits.tl fits)) v
  ... | φ'' , u , ag' , len =
    move (step⁺ st) (star-plus τ (⟨ trans e (cong (λ m → X.upd m ρ' (X.run (ins t) (end t) (select-blocks bs) σ f')) u) ⟩ ▸⁺ ε))
         (exec~ ag' (refit len fits) k)
  assign~ st ag fits k (xfail τ (fails e)) = halt st τ e
  assign~ st ag fits k (xcall ag₀ fits₀ π) = move (step⁺ st) π (exec~ ag₀ fits₀ (seqK ag fits k))

  {- case a p l₁ l₂ -}
  case~ : ∀ {Bs Δ Δ'} {a : Imp.Atm Σ Δ ⟪ sum ⟫} {p : Δ' ⊑ Δ} {l₁ l₂ : Bs ∋ (Any ∷ Δ')} {φ φₓ bs κ σ f ρ s₁}
    (v : V.Val Σ ⟪ sum ⟫) → (∀ {ρ} → X.arg φₓ ρ (select-atm a) ≡ just ⌊ v ⌋) → Agree φ φₓ
    → Fits (case a p l₁ l₂) bs φₓ → κ ~ σ
    → G.step ds s₁ ≡ next (V.choose v (λ u → G.go ds (block bs l₁) (u ∷ forget p φ) κ) (λ u → G.go ds (block bs l₂) (u ∷ forget p φ) κ))
    → B s₁ (X.run (ins (case a p l₁ l₂)) (end (case a p l₁ l₂)) (select-blocks bs) σ f φₓ ρ)
  case~ {Δ = Δ} {Δ'} {p = p} {l₁ = l₁} {bs = bs} {σ = σ} {ρ = ρ} (V.inl u) e ag fits k st
    with write ag p (≤-trans (m≤n⊔m (length Δ) (suc (length Δ'))) (Fits.tl fits)) u
  ... | φ'' , w , ag' , len =
    move (step⁺ st) (t-step e refl ▸⁺ (lp-var e refl w ▸ ⟨ cong (λ m → X.goto m σ (just true) φ'' ρ) (block-sel bs l₁) ⟩ ▸ ε))
         (exec~ ag' (blk-fits bs l₁ (refit len fits)) k)
  case~ {Δ = Δ} {Δ'} {p = p} {l₂ = l₂} {bs = bs} {σ = σ} {ρ = ρ} (V.inr u) e ag fits k st
    with write ag p (≤-trans (m≤n⊔m (length Δ) (suc (length Δ'))) (Fits.tl fits)) u
  ... | φ'' , w , ag' , len =
    move (step⁺ st) (t-step e refl ▸⁺ (lp-var e refl w ▸ ⟨ cong (λ m → X.goto m σ (just false) φ'' ρ) (block-sel bs l₂) ⟩ ▸ ε))
         (exec~ ag' (blk-fits bs l₂ (refit len fits)) k)

  sim : ∀ {s₁ s₂} → Match s₁ s₂ → B s₁ s₂
  sim (exec~ {t = return s} {φ = φ} {bs = bs} {σ = σ} {f = f} {φₓ = φₓ} {ρ = ρ} ag fits k) =
    retn~ refl k (subst (λ is → XOut (reg rax) [] retq (select-blocks bs) σ φₓ (run s φ) (X.run is retq (select-blocks bs) σ f φₓ ρ))
                        (++-identityʳ _) (sel ag s))
  sim (exec~ {t = seq p s t} ag fts k) = assign~ refl ag (mkfits (≤-trans (m≤n⊔m _ _) (Fits.tl fts)) (Fits.bl fts)) k (sel ag s)
  sim (exec~ {t = goto l} {bs = bs} ag fits k) =
    move (step⁺ refl) (step⁺ (cong (λ m → X.goto m _ _ _ _) (block-sel bs l))) (exec~ ag (blk-fits bs l fits) k)
  sim (exec~ {t = case a p l₁ l₂} {φ = φ} ag fits k) = case~ (atom φ a) (arg-ok ag a) ag fits k refl

  fsim = both-fsim Match (exec~ (agree λ ()) (mkfits (≤-trans (m≤n⊔m _ _) n≤) (≤-trans (m≤m⊔n _ _) n≤)) halt) sim
    where n≤ = ≤-reflexive (sym (length-replicate _))

{- The end theorem ---------------------------------------------------------------}

select-correct : ∀ P → Equivalent (G.sem P) (X.sem (select P))
select-correct (CFG.program ds b) = equivalent (Sim.fsim ds b)
