{-

  An assurance, not part of the compiler or of the comparison: erasing
  X86ᵀ (Language/Typed/X86.agda) to X86 (erase,
  Language/Typed/X86Erase.agda) keeps the meaning of every X86ᵀ
  program, in the CEK column's machines (Semantics/CEK/Typed/X86.agda,
  Semantics/CEK/X86.agda). The statements are in
  Theorems/X86Erasure.agda.

  A simulation of the X86ᵀ machine by the X86 machine (Both,
  proof/Framework/Both.agda): one X86ᵀ instruction or jump is matched by
  its erased instructions, one each but chk's, whose test errs exactly
  when chk does (ck-ok). An X86 value is the erasure of a typed value
  (⌊_⌋, proof/Assurance/X86Agree.agda). The match (MAg) says
  * the X86 frame holds the erasure of each typed slot at its level
    (Agree), and has at least the body's n slots, so a
    write to a slot below n, the only ones X86ᵀ writes, succeeds: X86's
    frame of max(2, n) zeros, or n for main, against X86ᵀ's frame of the
    assigned slots only;
  * a register of a type holds the erasure of its typed value, and an
    unset register anything (so X86's %rax = 0 at the start of main, and
    whatever the check of chk leaves in %rax, are unconstrained); the
    same for the flag;
  * when a closure is open (load fst x), the X86 slot x is the pair of
    the code and environment X86ᵀ recorded: so load snd x reads the same
    environment from the frame as X86ᵀ does from the record. Writing a
    slot, or a call, closes the closure, so the slot does not change
    while it is open.
  X86's other trapped errors (a missing slot, label or definition, an
  unset register or flag, a value of the wrong kind) never happen.

-}

module proof.Assurance.X86Erasure where

open import Framework.Primitives using (Nat; Int; 𝔹; Unit; Void; Blame)
open import Language.Prim using (sub)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.X86
open import Language.Typed.X86Erase
open import Compiler.SelectX86 using (check)
open import Framework.Lookup using (_!_)
open import Framework.ListUtil using (_‼_)
open import proof.Framework.Lookup using (lvl-<)
open import proof.Framework.ListUtil using (‼-snoc-<; ‼-snoc-length)
open import Semantics.Observation using (Obs; o-error)
open import proof.Semantics.CEK.Smallstep
  using (Machine; Next; next; stop; Final; Star; ε; _◅_; Plus; step⁺; star-plus)
open import proof.Semantics.CEK.Simulation using (Equivalent; equivalent)
open import proof.Framework.Both Obs using (Both; halt; move; both-fsim)
open import proof.Assurance.X86Agree using (⌊_⌋; ⌊_⌋*; obs-⌊⌋; Agree; agree; arg-ok; write; proj-ok; proj-bad; len-⌊⌋)
import Language.X86 as L
import Semantics.CEK.X86 as X
import Semantics.CEK.Values as XV
import Semantics.CEK.Typed.X86 as T
import Semantics.CEK.Typed.Clos5 as V

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Integer using (_≟_)
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; length; reverse; _∷ʳ_)
open import Data.List.Properties using (unfold-reverse; length-reverse; length-replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; suc; _≤_; _<?_)
import Data.Nat as N
open import Data.Nat.Properties using (≤-trans; <-≤-trans; m≤n+m∸n; ≤-reflexive; <⇒≢)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (Vec; []; _∷_; map; toList)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; does)
open import Relation.Nullary.Decidable using (recompute)

{- Definitions and labels exist ------------------------------------------------}

len-defs : ∀ {Σ ns} (ds : All (λ m → Body Σ (called m)) ns) → length (eDefs ds) ≡ length ns
len-defs [] = refl
len-defs (d ∷ ds) = cong suc (len-defs ds)

global-e : ∀ {Σ ns n} (ds : All (λ m → Body Σ (called m)) ns) (f : ns ∋ n)
  → X.global (eDefs ds) (lvl f) ≡ just (eBody (ds ! f))
global-e {ns = n ∷ ns} (d ∷ ds) f rewrite unfold-reverse (eBody d) (eDefs ds) = go f
  where
  xs = reverse (eDefs ds)
  len : length xs ≡ length ns
  len = trans (length-reverse (eDefs ds)) (len-defs ds)
  go : ∀ {m} (f : (n ∷ ns) ∋ m) → (xs ∷ʳ eBody d) ‼ lvl f ≡ just (eBody ((d ∷ ds) ! f))
  go Z = subst (λ k → (xs ∷ʳ eBody d) ‼ k ≡ just (eBody d)) len (‼-snoc-length xs (eBody d))
  go (S f) = trans (‼-snoc-< xs (eBody d) (lvl f) (subst (lvl f N.<_) (sym len) (lvl-< f))) (global-e ds f)

len-blocks : ∀ {Σ n Bs} (bs : Blocks Σ n Bs) → length (eBlocks bs) ≡ length Bs
len-blocks [] = refl
len-blocks (bs ▷ k) = cong suc (len-blocks bs)

block-e : ∀ {Σ n Bs Δ} (bs : Blocks Σ n Bs) (l : Bs ∋ Δ)
  → X.block-at (eBlocks bs) (lvl l) ≡ just (eSeq (Blk.start (block bs l)) , eBlocks (Blk.blocks (block bs l)))
block-e {Bs = _ ∷ Bs} (bs ▷ k) Z with length Bs N.≟ length (eBlocks bs)
... | yes _ = refl
... | no ne = ⊥-elim (ne (sym (len-blocks bs)))
block-e (bs ▷ k) (S l) with lvl l N.≟ length (eBlocks bs)
... | yes e = ⊥-elim (<⇒≢ (lvl-< l) (trans e (len-blocks bs)))
... | no _ = block-e bs l

{- Values, registers, the flag and the open closure -----------------------------}

bind₁ : ∀ {A B : Set} {m : Maybe A} {v} (k : A → Maybe B) → m ≡ just v → (m >>= k) ≡ k v
bind₁ k refl = refl

{- r := w -}
preg : ∀ {r mw w φ ρ} (K : X.Frame → X.Regs → X.State) → mw ≡ just w → X.put (L.reg r) mw φ ρ K ≡ next (K φ (ρ X.[ r ↦ just w ]))
preg K refl = refl

module _ {Σ : List ℕ} where

  {- the erasure of a register's value -}
  er : ∀ {η} τ → T.RV Σ η τ → X.Val
  er (ty A) v = ⌊ v ⌋
  er codeα v = ⌊ v ⌋
  er tupα v = ⌊ v ⌋

  {- a register of a type holds the erasure of its value; an unset one, anything -}
  RAg : ∀ {η} (m : Maybe RTy) → T.MV Σ η m → Maybe X.Val → Set
  RAg (just τ) v w = w ≡ just (er τ v)
  RAg nothing v w = ⊤

  record RegsAg {η Γ} (ρt : T.RegVals Σ η Γ) (ρ : X.Regs) : Set where
    constructor ragree
    field
      ax : RAg (Regs.ax Γ) (T.RegVals.ax ρt) (ρ rax)
      di : RAg (Regs.di Γ) (T.RegVals.di ρt) (ρ rdi)
      si : RAg (Regs.si Γ) (T.RegVals.si ρt) (ρ rsi)

  FlagAg : (F : Bool) → T.Flag Σ F → Maybe Bool → Set
  FlagAg true b f = f ≡ just b
  FlagAg false _ _ = ⊤

  {- the slot of the open closure is the pair of the recorded code and environment -}
  OpenAg : ∀ {η Δ} (O : Maybe (Δ ∋ ⟪ fun ⟫)) → T.Opened Σ η O → X.Frame → Set
  OpenAg nothing _ φ = ⊤
  OpenAg (just x) (c , e) φ = φ ‼ lvl x ≡ just (X.pair ⌊ c ⌋ ⌊ e ⌋)

  {- the registers, frame, open closure and flag, in a body of n slots -}
  record MAg (n : ℕ) {η ψ} (m : T.Mach Σ η ψ) (f : Maybe Bool) (φ : X.Frame) (ρ : X.Regs) : Set where
    constructor mag
    field
      fr : Agree (T.frame m) φ
      len : n ≤ length φ
      rg : RegsAg (T.regs m) ρ
      fl : FlagAg (St.fl ψ) (T.flag m) f
      op : OpenAg (St.op ψ) (T.opened m) φ

  reg-ag : ∀ {η Γ} {ρt : T.RegVals Σ η Γ} {ρ} → RegsAg ρt ρ → ∀ r → RAg (Γ ‹ r ›) (ρt T.⦅ r ⦆) (ρ r)
  reg-ag ag rax = RegsAg.ax ag
  reg-ag ag rdi = RegsAg.di ag
  reg-ag ag rsi = RegsAg.si ag

  cast-ok : ∀ {η m τ} (e : m ≡ just τ) {v : T.MV Σ η m} {w} → RAg m v w → w ≡ just (er τ (T.cast e v))
  cast-ok refl a = a

  set-ag : ∀ {η Γ} {ρt : T.RegVals Σ η Γ} {ρ} r {τ} (v : T.RV Σ η τ) → RegsAg ρt ρ
    → RegsAg (T._[_≔_] {τ = just τ} ρt r v) (ρ X.[ r ↦ just (er τ v) ])
  set-ag rax v (ragree a d s) = ragree refl d s
  set-ag rdi v (ragree a d s) = ragree a refl s
  set-ag rsi v (ragree a d s) = ragree a d refl

  {- chk unsets %rax -}
  clr : ∀ {η Γ} {ρt : T.RegVals Σ η Γ} {ρ ρ'} → RegsAg ρt ρ → ρ' rdi ≡ ρ rdi → ρ' rsi ≡ ρ rsi
    → RegsAg (T._[_≔_] {τ = nothing} ρt rax tt) ρ'
  clr {Γ = Γ} (ragree a d s) e₁ e₂ = ragree tt (subst (RAg (Regs.di Γ) _) (sym e₁) d) (subst (RAg (Regs.si Γ) _) (sym e₂) s)

  forget-ag : ∀ {η η'} m {v : T.MV Σ η m} {w} → RAg m v w → RAg {η = η'} (forgetα m) (T.forgetᵥ m v) w
  forget-ag (just (ty A)) a = a
  forget-ag (just codeα) a = tt
  forget-ag (just tupα) a = tt
  forget-ag nothing a = tt

  wipe-ag : ∀ {η η' Γ} {ρt : T.RegVals Σ η Γ} {ρ} → RegsAg ρt ρ → RegsAg (T.wipeᵣ {η' = η'} ρt) ρ
  wipe-ag {Γ = Γ} (ragree a d s) = ragree (forget-ag (Regs.ax Γ) a) (forget-ag (Regs.di Γ) d) (forget-ag (Regs.si Γ) s)

  arg-e : ∀ {n η ψ τ} (a : Arg Σ ψ τ) {m : T.Mach Σ η ψ} {f φ ρ} → MAg n m f φ ρ
    → X.arg φ ρ (eArg a) ≡ just (er τ (T.arg a m))
  arg-e (atom a) ag = arg-ok (MAg.fr ag) a
  arg-e (reg r e) ag = cast-ok e (reg-ag (MAg.rg ag) r)
  arg-e (a ↑) ag = arg-e a ag

  args-e : ∀ {n η ψ j} (as : Vec (Arg Σ ψ (ty Any)) j) {m : T.Mach Σ η ψ} {f φ ρ} → MAg n m f φ ρ
    → ∀ vs (K : List X.Val → Maybe X.Val) → X.args φ ρ vs (toList (map eArg as)) K ≡ K (vs ʳ++ ⌊ T.args as m ⌋*)
  args-e [] ag vs K = refl
  args-e (a ∷ as) {m} {φ = φ} {ρ} ag vs K =
    trans (bind₁ (λ v → X.args φ ρ (v ∷ vs) (toList (map eArg as)) K) (arg-e a ag)) (args-e as ag (⌊ T.arg a m ⌋ ∷ vs) K)

  {- d := v -}
  put-reg : ∀ {n η Γ Δ O F} {m : T.Mach Σ η (st Γ Δ O F)} {f φ ρ} r {τ} (v : T.RV Σ η τ) → MAg n m f φ ρ
    → MAg n {ψ = st (Γ [ r ↦ just τ ]) Δ O F} T.⟨ T._[_≔_] {τ = just τ} (T.regs m) r v , T.frame m , T.opened m , T.flag m ⟩
          f φ (ρ X.[ r ↦ just (er τ v) ])
  put-reg r v (mag fr len rg fl op) = mag fr len (set-ag r v rg) fl op

  put-ok : ∀ {n η ψ τ ψ'} (d : Dst n ψ τ ψ') (v : T.RV Σ η τ) {m : T.Mach Σ η ψ} {f φ ρ mw}
    → mw ≡ just (er τ v) → MAg n m f φ ρ → (K : X.Frame → X.Regs → X.State)
    → Σ[ φ' ∈ X.Frame ] Σ[ ρ' ∈ X.Regs ] X.put (eDst d) mw φ ρ K ≡ next (K φ' ρ') × MAg n (T.put d v m) f φ' ρ'
  put-ok (reg r) v refl ag K = _ , _ , refl , put-reg r v ag
  put-ok (slot {Δ' = Δ'} p lt) v refl ag K
    with write (MAg.fr ag) p (<-≤-trans (recompute (length Δ' <? _) lt) (MAg.len ag)) v
  ... | φ' , u , ag' , l =
    φ' , _ , cong (λ r → X.upd r _ K) u , mag ag' (subst (_ ≤_) (sym l) (MAg.len ag)) (MAg.rg ag) (MAg.fl ag) tt

  {- the instructions on erased values -}
  sub-ok : ∀ (u w : V.Val Σ ⟪ base Int ⟫) → XV.prim? sub ⌊ u ⌋ ⌊ w ⌋ ≡ just ⌊ V.δᵀ {Σ} sub (V.int u) (V.int w) ⌋
  sub-ok (V.const n) (V.const m) = refl

  cmp-ok : ∀ (u w : V.Val Σ ⟪ base Int ⟫) → X.cmp ⌊ u ⌋ ⌊ w ⌋ ≡ just (does (V.int u ≟ V.int w))
  cmp-ok (V.const n) (V.const m) = refl

  bit-ok : ∀ b → X.bit b ≡ ⌊ T.bit {Σ} b ⌋
  bit-ok true = refl
  bit-ok false = refl

  inl-ok : ∀ (v : V.Val Σ ⟪ sum ⟫) → X.is-inl ⌊ v ⌋ ≡ just (T.is-inl v)
  inl-ok (V.inl v) = refl
  inl-ok (V.inr v) = refl

  get-ok : ∀ {j} (v : V.Val Σ ⟪ tup j ⟫) i → X.get-field (L.get i) ⌊ v ⌋ ≡ just ⌊ T.field′ (get i) v ⌋
  get-ok (V.tup vs) i = proj-ok vs i

  pay-ok : ∀ (v : V.Val Σ ⟪ sum ⟫) → X.get-field L.payload ⌊ v ⌋ ≡ just ⌊ T.field′ payload v ⌋
  pay-ok (V.inl v) = refl
  pay-ok (V.inr v) = refl

  fst-ok : ∀ (v : V.Val Σ ⟪ fun ⟫) → X.get-field L.fst ⌊ v ⌋ ≡ just ⌊ T.code-of v ⌋
  fst-ok (V.pack c e) = refl

  pair-ok : ∀ (v : V.Val Σ ⟪ fun ⟫) → ⌊ v ⌋ ≡ X.pair ⌊ T.code-of v ⌋ ⌊ T.env-of v ⌋
  pair-ok (V.pack c e) = refl

  {- the definition a code pointer points to -}
  def-of : ∀ {η} → V.Val Σ (code η) → Σ ∋ η
  def-of (V.code f) = f

  code-ok : ∀ {η} (c : V.Val Σ (code η)) → ⌊ c ⌋ ≡ X.code (lvl (def-of c))
  code-ok (V.code f) = refl

  enter-ok : ∀ (ds : All (λ m → Body Σ (called m)) Σ) {η} (c : V.Val Σ (code η)) e w σ
    → T.enter ds c e w σ
      ≡ next (T.run (Body.start (ds ! def-of c)) (Body.blocks (ds ! def-of c)) σ η T.⟨ T.rv tt e w , [] , tt , tt ⟩)
  enter-ok ds (V.code f) e w σ = refl

  proj-⌊⌋ : ∀ t (v : V.Val Σ Any) {u} → V.proj? t v ≡ just u → ⌊ v ⌋ ≡ ⌊ u ⌋
  proj-⌊⌋ t (V.dyn H v) e with H ≟F flat t
  proj-⌊⌋ t (V.dyn H v) refl | yes refl = refl
  proj-⌊⌋ t (V.dyn H v) () | no _

  obs-ok : ∀ {A} (v : V.Val Σ A) → V.obs v ≡ o-error → ⊥
  obs-ok (V.code f) ()
  obs-ok (V.pack c e) ()
  obs-ok (V.const c) ()
  obs-ok (V.tup vs) ()
  obs-ok (V.inl v) ()
  obs-ok (V.inr v) ()
  obs-ok (V.dyn G v) e = obs-ok v e

{- The simulation, for a program with definitions ds and main body b₀ ------------}

module Sim {Σ : List ℕ} (ds : All (λ m → Body Σ (called m)) Σ) (b₀ : Body Σ (entry [])) where

  P = program ds b₀
  xds = eDefs ds
  L₁ = T.sem P
  L₂ = X.sem (erase P)

  {- the rest of an erased sequence, given the flag and the frame and registers -}
  xrun : ∀ {n Bs ψ} → Seq Σ n Bs ψ → Blocks Σ n Bs → X.Stack → Maybe Bool → X.Frame → X.Regs → X.State
  xrun k bs σ = X.run (L.Block.instrs (eSeq k)) (L.Block.jump (eSeq k)) (eBlocks bs) σ

  {- the X86ᵀ call stack, and the X86 one -}
  infix 4 _~_
  data _~_ : T.Stack Σ → X.Stack → Set where
    halt : T.halt ~ X.halt
    retK : ∀ {n Bs Δ} {k : Seq Σ n Bs (returned Δ)} {bs φ σ φₓ σₓ} → Agree φ φₓ → n ≤ length φₓ → σ ~ σₓ
      → T.retK k bs φ σ ~ X.retK (L.Block.instrs (eSeq k)) (L.Block.jump (eSeq k)) (eBlocks bs) φₓ σₓ

  data Match : T.State Σ → X.State → Set where
    run~ : ∀ {n Bs ψ} {k : Seq Σ n Bs ψ} {bs σ η m σₓ f φ ρ} → MAg n m f φ ρ → σ ~ σₓ
      → Match (T.run k bs σ η m) (xrun k bs σₓ f φ ρ)

  B = Both {L₁ = L₁} {L₂ = L₂} Match

  one : ∀ {s₁ s₁' s₂ s₂'} → T.step ds s₁ ≡ next s₁' → X.step xds s₂ ≡ next s₂' → Match s₁' s₂' → B s₁ s₂
  one e₁ e₂ m = move (step⁺ e₁) (step⁺ e₂) m

  {- how the erased check of chk t runs, up to its move K -}
  data CkOut (t : Tag) {η Γ} (ρt : T.RegVals Σ η Γ) (s : X.State) (K : Maybe Bool → X.Regs → X.State)
    : Maybe (V.Val Σ ⟪ flat t ⟫) → Set where
    ok : ∀ {u f' ρ'} → Star L₂ s (K f' ρ') → RegsAg (T._[_≔_] {τ = nothing} ρt rax tt) ρ' → CkOut t ρt s K (just u)
    bad : ∀ {s'} → Star L₂ s s' → Final L₂ s' o-error → CkOut t ρt s K nothing

  module _ {η Γ} {ρt : T.RegVals Σ η Γ} {a D is j bs σ f φ ρ} (rg : RegsAg ρt ρ) where

    K : Maybe Bool → X.Regs → X.State
    K f' ρ' = X.run (L.movq a D ∷ is) j bs σ f' φ ρ'

    {- the instructions of a check -}
    mv : ∀ {w is'} → X.arg φ ρ a ≡ just w
      → X.step xds (X.run (L.movq a (L.reg rax) ∷ is') j bs σ f φ ρ) ≡ next (X.run is' j bs σ f φ (ρ X.[ rax ↦ just w ]))
    mv {is' = is'} e = preg (X.run is' j bs σ f) e

    ld : ∀ {fl w v is'} → X.arg φ ρ a ≡ just v → X.get-field fl v ≡ just w
      → X.step xds (X.run (L.load fl a (L.reg rax) ∷ is') j bs σ f φ ρ) ≡ next (X.run is' j bs σ f φ (ρ X.[ rax ↦ just w ]))
    ld {fl} {is' = is'} e e' = preg (X.run is' j bs σ f) (trans (bind₁ (X.get-field fl) e) e')

    ld-bad : ∀ {fl v is'} → X.arg φ ρ a ≡ just v → X.get-field fl v ≡ nothing
      → Final L₂ (X.run (L.load fl a (L.reg rax) ∷ is') j bs σ f φ ρ) o-error
    ld-bad {fl} e e' = cong (λ m → X.put (L.reg rax) m φ ρ _) (trans (bind₁ (X.get-field fl) e) e')

    ts : ∀ {v b is'} → X.arg φ ρ a ≡ just v → X.is-inl v ≡ just b
      → X.step xds (X.run (L.testinl a ∷ is') j bs σ f φ ρ) ≡ next (X.run is' j bs σ (just b) φ ρ)
    ts e e' = cong (λ m → X.test m _) (trans (bind₁ X.is-inl e) e')

    ts-bad : ∀ {v is'} → X.arg φ ρ a ≡ just v → X.is-inl v ≡ nothing → Final L₂ (X.run (L.testinl a ∷ is') j bs σ f φ ρ) o-error
    ts-bad e e' = cong (λ m → X.test m _) (trans (bind₁ X.is-inl e) e')

    rg₁ : ∀ {w} → RegsAg (T._[_≔_] {τ = nothing} ρt rax tt) (ρ X.[ rax ↦ w ])
    rg₁ = clr rg refl refl

    rg₂ : ∀ {w w'} → RegsAg (T._[_≔_] {τ = nothing} ρt rax tt) ((ρ X.[ rax ↦ w ]) X.[ rax ↦ w' ])
    rg₂ = clr rg refl refl

    ck-ok : ∀ t (v : V.Val Σ Any) → X.arg φ ρ a ≡ just ⌊ v ⌋
      → CkOut t ρt (X.run ((check t a ++ L.movq a D ∷ []) ++ is) j bs σ f φ ρ) K (V.proj? t v)
    ck-ok tint (V.dyn (base Int) (V.const n)) e = ok (mv e ◅ refl ◅ ε) rg₂
    ck-ok tint (V.dyn (base Nat) (V.const n)) e = bad (mv e ◅ ε) refl
    ck-ok tint (V.dyn (base 𝔹) (V.const n)) e = bad (mv e ◅ ε) refl
    ck-ok tint (V.dyn (base Unit) (V.const n)) e = bad (mv e ◅ ε) refl
    ck-ok tint (V.dyn (base Void) (V.const ())) e
    ck-ok tint (V.dyn (base Blame) (V.const n)) e = bad (mv e ◅ ε) refl
    ck-ok tint (V.dyn (tup m) (V.tup vs)) e = bad (mv e ◅ ε) refl
    ck-ok tint (V.dyn sum (V.inl v)) e = bad (mv e ◅ ε) refl
    ck-ok tint (V.dyn sum (V.inr v)) e = bad (mv e ◅ ε) refl
    ck-ok tint (V.dyn fun (V.pack c en)) e = bad (mv e ◅ ε) refl
    ck-ok tsum (V.dyn (base B) (V.const c)) e = bad ε (ts-bad e refl)
    ck-ok tsum (V.dyn (tup m) (V.tup vs)) e = bad ε (ts-bad e refl)
    ck-ok tsum (V.dyn sum (V.inl v)) e = ok (ts e refl ◅ ε) (clr rg refl refl)
    ck-ok tsum (V.dyn sum (V.inr v)) e = ok (ts e refl ◅ ε) (clr rg refl refl)
    ck-ok tsum (V.dyn fun (V.pack c en)) e = bad ε (ts-bad e refl)
    ck-ok tfun (V.dyn (base B) (V.const c)) e = bad ε (ld-bad {fl = L.fst} e refl)
    ck-ok tfun (V.dyn (tup m) (V.tup vs)) e = bad ε (ld-bad {fl = L.fst} e refl)
    ck-ok tfun (V.dyn sum (V.inl v)) e = bad ε (ld-bad {fl = L.fst} e refl)
    ck-ok tfun (V.dyn sum (V.inr v)) e = bad ε (ld-bad {fl = L.fst} e refl)
    ck-ok tfun (V.dyn fun (V.pack c en)) e = ok (ld {fl = L.fst} e refl ◅ ε) rg₁
    ck-ok (ttup n i) (V.dyn (base B) (V.const c)) e = bad ε (ld-bad {fl = L.get i} e refl)
    ck-ok (ttup n i) (V.dyn sum (V.inl v)) e = bad ε (ld-bad {fl = L.get i} e refl)
    ck-ok (ttup n i) (V.dyn sum (V.inr v)) e = bad ε (ld-bad {fl = L.get i} e refl)
    ck-ok (ttup n i) (V.dyn fun (V.pack c en)) e = bad ε (ld-bad {fl = L.get i} e refl)
    ck-ok (ttup n i) (V.dyn (tup m) (V.tup vs)) e with m N.≟ suc n
    ... | yes refl = ok (ld {fl = L.get i} e (proj-ok vs i) ◅ ε) rg₁
    ... | no ne = bad ε (ld-bad {fl = L.get i} e (proj-bad ⌊ vs ⌋* i (ne ∘ trans (sym (len-⌊⌋ vs)))))

  sim : ∀ {s₁ s₂} → Match s₁ s₂ → B s₁ s₂
  sim (run~ {k = movq a d ∷ k} {bs} {σ} {η} {m} {σₓ} {f} ag sk)
    with put-ok d (T.arg a m) (arg-e a ag) ag (xrun k bs σₓ f)
  ... | _ , _ , e , ag' = one refl e (run~ ag' sk)
  sim (run~ {k = subq a r e ∷ k} {bs} {σ} {η} {m} {σₓ} {f} ag sk) =
    one refl (preg (xrun k bs σₓ f) (trans (bind₁ _ (arg-e a ag)) (trans (bind₁ _ (cast-ok e (reg-ag (MAg.rg ag) r))) (sub-ok u w))))
        (run~ (put-reg r _ ag) sk)
    where u = T.cast e (T.regs m T.⦅ r ⦆)
          w = T.arg a m
  sim (run~ {k = cmpq a₂ a₁ ∷ k} {bs} {m = m} {σₓ} {φ = φ} {ρ} (mag fr len rg fl op) sk) =
    one refl (cong (λ z → X.test z (λ f' → xrun k bs σₓ f' φ ρ))
                   (trans (bind₁ _ (arg-e a₁ ag)) (trans (bind₁ _ (arg-e a₂ ag)) (cmp-ok (T.arg a₁ m) (T.arg a₂ m)))))
        (run~ (mag fr len rg refl op) sk)
    where ag = mag fr len rg fl op
  sim (run~ {k = sete d ∷ k} {bs} {σ} {η} {m} {σₓ} (mag fr len rg refl op) sk)
    with put-ok d (T.bit (T.flag m)) (cong just (bit-ok (T.flag m))) (mag fr len rg refl op) (xrun k bs σₓ (just (T.flag m)))
  ... | _ , _ , e , ag' = one refl e (run~ ag' sk)
  sim (run~ {k = testinl a ∷ k} {bs} {m = m} {σₓ} {φ = φ} {ρ} (mag fr len rg fl op) sk) =
    one refl (cong (λ z → X.test z (λ f' → xrun k bs σₓ f' φ ρ)) (trans (bind₁ _ (arg-e a (mag fr len rg fl op))) (inl-ok (T.arg a m))))
        (run~ (mag fr len rg refl op) sk)
  sim (run~ {k = alloc (pair c e) d ∷ k} {bs} {σ} {η} {m} {σₓ} {f} ag sk)
    with put-ok d (T.obj (pair c e) m) (trans (bind₁ _ (arg-e c ag)) (bind₁ _ (arg-e e ag))) ag (xrun k bs σₓ f)
  ... | _ , _ , e' , ag' = one refl e' (run~ ag' sk)
  sim (run~ {k = alloc (tuple as) d ∷ k} {bs} {σ} {η} {m} {σₓ} {f} ag sk)
    with put-ok d (T.obj (tuple as) m) (args-e as ag [] (X.build L.tuple)) ag (xrun k bs σₓ f)
  ... | _ , _ , e' , ag' = one refl e' (run~ ag' sk)
  sim (run~ {k = alloc (inl a) d ∷ k} {bs} {σ} {η} {m} {σₓ} {f} ag sk)
    with put-ok d (T.obj (inl a) m) (bind₁ _ (arg-e a ag)) ag (xrun k bs σₓ f)
  ... | _ , _ , e' , ag' = one refl e' (run~ ag' sk)
  sim (run~ {k = alloc (inr a) d ∷ k} {bs} {σ} {η} {m} {σₓ} {f} ag sk)
    with put-ok d (T.obj (inr a) m) (bind₁ _ (arg-e a ag)) ag (xrun k bs σₓ f)
  ... | _ , _ , e' , ag' = one refl e' (run~ ag' sk)
  sim (run~ {k = load (get i) a d ∷ k} {bs} {σ} {η} {m} {σₓ} {f} ag sk)
    with put-ok d (T.field′ (get i) (T.arg a m)) (trans (bind₁ _ (arg-e a ag)) (get-ok (T.arg a m) i)) ag (xrun k bs σₓ f)
  ... | _ , _ , e' , ag' = one refl e' (run~ ag' sk)
  sim (run~ {k = load payload a d ∷ k} {bs} {σ} {η} {m} {σₓ} {f} ag sk)
    with put-ok d (T.field′ payload (T.arg a m)) (trans (bind₁ _ (arg-e a ag)) (pay-ok (T.arg a m))) ag (xrun k bs σₓ f)
  ... | _ , _ , e' , ag' = one refl e' (run~ ag' sk)
  sim (run~ {k = loadfst x r ∷ k} {bs} {m = m} {σₓ} {f} (mag fr len rg fl op) sk) =
    one refl (preg (xrun k bs σₓ f) (trans (bind₁ _ (Agree.at fr x)) (fst-ok v)))
        (run~ (mag fr len (set-ag r (T.code-of v) (wipe-ag rg)) fl (trans (Agree.at fr x) (cong just (pair-ok v)))) sk)
    where v = T.frame m ! x
  sim (run~ {ψ = st Γ Δ (just x) F} {k = loadsnd r ∷ k} {bs} {m = T.⟨ ρt , φt , (c , e) , b ⟩} {σₓ} {f} (mag fr len rg fl op) sk) =
    one refl (preg (xrun k bs σₓ f) (bind₁ _ op)) (run~ (mag fr len (set-ag r e rg) fl op) sk)
  sim (run~ {k = callq a e₁ e₂ ∷ k} {bs} {σ} {η} {m} {σₓ} {f} {φ} {ρ} ag sk) =
    move (step⁺ (enter-ok ds c (T.cast e₁ (T.regs m T.⦅ rdi ⦆)) (T.cast e₂ (T.regs m T.⦅ rsi ⦆)) (T.retK k bs (T.frame m) σ)))
         (step⁺ (trans (cong (λ z → X.callq? xds z σ' ρ) (trans (arg-e a ag) (cong just (code-ok c))))
                  (trans (cong (λ z → X.call z σ' (ρ rdi) (ρ rsi)) (global-e ds (def-of c)))
                    (trans (cong (λ z → X.call (just b) σ' z (ρ rsi)) (cast-ok e₁ (reg-ag (MAg.rg ag) rdi)))
                           (cong (λ z → X.call (just b) σ' (just (er tupα (T.cast e₁ (T.regs m T.⦅ rdi ⦆)))) z)
                                 (cast-ok e₂ (reg-ag (MAg.rg ag) rsi)))))))
         (run~ (mag (agree λ ()) len₀ (ragree tt refl refl) tt tt) (retK (MAg.fr ag) (MAg.len ag) sk))
    where
    c = T.arg a m
    b = eBody (ds ! def-of c)
    σ' = X.retK (L.Block.instrs (eSeq k)) (L.Block.jump (eSeq k)) (eBlocks bs) φ σₓ
    n₀ = Body.locals (ds ! def-of c)
    len₀ : n₀ ≤ length (XV.zeros (2 N.+ (n₀ N.∸ 2)))
    len₀ = ≤-trans (m≤n+m∸n n₀ 2) (≤-reflexive (sym (length-replicate (2 N.+ (n₀ N.∸ 2)))))
  sim (run~ {k = chk t x d ∷ k} {bs} {σ} {η} {m} {σₓ} {f} {φ} {ρ} (mag fr len rg fl op) sk) =
    chk~ (V.proj? t (T.frame m ! x)) refl (ck-ok rg t (T.frame m ! x) (Agree.at fr x))
    where
    chk~ : ∀ r → V.proj? t (T.frame m ! x) ≡ r
      → CkOut t (T.regs m) (X.run ((check t (slot-of x) ++ L.movq (slot-of x) (eDst d) ∷ []) ++ L.Block.instrs (eSeq k))
                                  (L.Block.jump (eSeq k)) (eBlocks bs) σₓ f φ ρ)
                           (K {a = slot-of x} {eDst d} {L.Block.instrs (eSeq k)} {L.Block.jump (eSeq k)} {eBlocks bs} {σₓ} {f} {φ} rg) r
      → B _ _
    chk~ (just u) eq (ok {f' = f'} τ rg')
      with put-ok d u (trans (Agree.at fr x) (cong just (proj-⌊⌋ t (T.frame m ! x) eq))) (mag fr len rg' tt op) (xrun k bs σₓ f')
    ... | _ , _ , e , ag' = move (step⁺ (cong (λ r → T.checked ds r d k bs σ _) eq)) (star-plus τ (step⁺ e)) (run~ ag' sk)
    chk~ nothing eq (bad τ e) = halt (cong (λ r → T.checked ds r d k bs σ _) eq) τ e
  sim (run~ {k = retq e} {σ = T.halt} {m = m} {f = f} {φ} {ρ} ag halt) =
    halt refl ε (trans (cong X.halt? (cast-ok e (reg-ag (MAg.rg ag) rax))) (cong stop (obs-⌊⌋ (T.cast e (T.regs m T.⦅ rax ⦆)))))
  sim (run~ {k = retq e} {σ = T.retK k bs' φt σ} {m = m} ag (retK fr' len' sk)) =
    one refl (cong (λ z → X.back z _ _ _ _ _) (cast-ok e (reg-ag (MAg.rg ag) rax))) (run~ (mag fr' len' (ragree refl tt tt) tt tt) sk)
  sim (run~ {k = jmp l} {bs} {σₓ = σₓ} {f} {φ} {ρ} (mag fr len rg fl op) sk) =
    one refl (cong (λ z → X.goto z σₓ f φ ρ) (block-e bs l)) (run~ (mag fr len (ragree tt tt tt) tt tt) sk)
  sim (run~ {k = je l₁ l₂} {bs} {m = T.⟨ ρt , φt , o , true ⟩} {σₓ} {φ = φ} {ρ} (mag fr len rg refl op) sk) =
    one refl (cong (λ z → X.goto z σₓ (just true) φ ρ) (block-e bs l₁)) (run~ (mag fr len (ragree tt tt tt) tt tt) sk)
  sim (run~ {k = je l₁ l₂} {bs} {m = T.⟨ ρt , φt , o , false ⟩} {σₓ} {φ = φ} {ρ} (mag fr len rg refl op) sk) =
    one refl (cong (λ z → X.goto z σₓ (just false) φ ρ) (block-e bs l₂)) (run~ (mag fr len (ragree tt tt tt) tt tt) sk)

  fsim = both-fsim Match (run~ (mag (agree λ ()) (≤-reflexive (sym (length-replicate _))) (ragree tt tt tt) tt tt) halt) sim

{- The end theorem ----------------------------------------------------------------}

erase-correct : ∀ P → Equivalent (T.sem P) (X.sem (erase P))
erase-correct (program ds b) = equivalent (Sim.fsim ds b)

{- The X86ᵀ machine errs only at a chk that fails: any property Q of such states
   holds of a state that stops with o-error -}
only-chk : ∀ {Σ} (ds : All (λ m → Body Σ (called m)) Σ) (Q : T.State Σ → Set)
  → (∀ {n Bs Γ Δ O F ψ'} {t} {x : Δ ∋ Any} {d : Dst n (st (Γ [ rax ↦ nothing ]) Δ O false) (ty ⟪ flat t ⟫) ψ'}
       {k : Seq Σ n Bs ψ'} {bs σ η} {m : T.Mach Σ η (st Γ Δ O F)} → V.proj? t (T.frame m ! x) ≡ nothing → Q (T.run (chk t x d ∷ k) bs σ η m))
  → ∀ s → T.step ds s ≡ stop o-error → Q s
only-chk ds Q q (T.run (movq a d ∷ k) bs σ η m) ()
only-chk ds Q q (T.run (subq a r e ∷ k) bs σ η m) ()
only-chk ds Q q (T.run (cmpq a₂ a₁ ∷ k) bs σ η m) ()
only-chk ds Q q (T.run (sete d ∷ k) bs σ η m) ()
only-chk ds Q q (T.run (testinl a ∷ k) bs σ η m) ()
only-chk ds Q q (T.run (alloc o d ∷ k) bs σ η m) ()
only-chk ds Q q (T.run (load fl a d ∷ k) bs σ η m) ()
only-chk ds Q q (T.run (loadfst x r ∷ k) bs σ η m) ()
only-chk ds Q q (T.run (loadsnd r ∷ k) bs σ η m) ()
only-chk ds Q q (T.run (callq a e₁ e₂ ∷ k) bs σ η m) e
  with trans (sym (enter-ok ds (T.arg a m) (T.cast e₁ (T.regs m T.⦅ rdi ⦆)) (T.cast e₂ (T.regs m T.⦅ rsi ⦆)) (T.retK k bs (T.frame m) σ))) e
... | ()
only-chk ds Q q (T.run (chk t x d ∷ k) bs σ η m) e = go (V.proj? t (T.frame m ! x)) refl e
  where
  go : ∀ r → V.proj? t (T.frame m ! x) ≡ r → T.checked ds r d k bs σ _ ≡ stop o-error → Q (T.run (chk t x d ∷ k) bs σ η m)
  go (just u) eq ()
  go nothing eq _ = q eq
only-chk ds Q q (T.run (retq e) bs T.halt η m) e' = ⊥-elim (obs-ok (T.cast e (T.regs m T.⦅ rax ⦆)) (cong unstop e'))
  where
  unstop : Next (T.State _) → Obs
  unstop (next _) = o-error
  unstop (stop o) = o
only-chk ds Q q (T.run (retq e) bs (T.retK k bs' φ σ) η m) ()
only-chk ds Q q (T.run (jmp l) bs σ η m) ()
only-chk ds Q q (T.run (je l₁ l₂) bs σ η m) ()
