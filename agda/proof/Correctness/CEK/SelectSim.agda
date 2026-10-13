{-

  Correctness of the select-instructions pass (CFG → X86,
  Compiler/Select.agda) by a forward simulation of the CFG machine by the
  X86 machine (see the design note in Semantics/CEK/Smallstep.agda).

  The frames are the same; the registers matter only where a value is in
  flight (%rax after a simple expression or a return, %rdi and %rsi at a
  call). The X86 call stack holds, for each CFG return continuation
  callK φ D, the caller's frame φ and the instructions that move %rax to
  where D wants the result (Dest), then continue as D.

  A CFG statement takes several steps (one per operand), the X86 one a
  few instructions, which must error exactly when the CFG does. So
  from each synchronisation point (Match: the start of a tail, or a
  return) the proof gives a script (F) of how the two machines move
  to the next one: the CFG steps while X86 waits (Lag, measured by the
  length of the rest of the script), then both step (go), or both stop. The
  X86 runs an instruction at the CFG step that checks what the
  instruction checks: the operands of a simple expression as the CFG
  evaluates them (Run), the destination slot when the CFG assigns it.
  The calls read their operands in another order (%rdi and %rsi before
  the code), so their moves are taken at the start of the statement.

  There is no precondition. This proof, between the machines of CFG and
  X86, is shared by the CEK machine + simulation and the reduction
  semantics + simulation developments.

-}

module proof.Correctness.CEK.SelectSim where

open import Language.Imp as Imp using (Atm; atm; app; fst; snd; tuple; get; prim)
open import Language.Prim using (sub; eq; int; bool)
open import Language.CFG as C using (Tail; return; seq; goto; case; block)
open import Language.X86
  using (Instr; Block; Loc; Jump; var; reg; rax; rdi; rsi; loc; movq; sete; callq; retq; je; payload)
open import Compiler.Select

open import Semantics.Observation
open import Framework.Primitives using (Int)
open import proof.Semantics.CEK.Smallstep using (next; stop; Plus; plus; Star; ε; _◅_; Reach)
open import proof.Semantics.CEK.Simulation
  using (Answers≺; stops; steps; answers-at; FSim; Lag; lag-now; lag-step; lag-fsim; Equivalent; equivalent; equiv-trans)
import Language.X86 as L
import Semantics.CEK.Imp as M
import Semantics.CEK.CFG as G
import Semantics.CEK.X86 as X
open X using (code; pair; const; tup; inl; inr; obs; _[_↦_]; _[_]≔_)
open import proof.Framework.ListUtil using (_‼_; reverse-map-‼)

open import Data.Bool using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length; map; reverse; _++_)
open import Data.List.Properties using (length-map; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing; _>>=_) renaming (map to mmap)
open import Data.Nat using (ℕ; suc; _≟_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

{- Lemmas about the pass ------------------------------------------------------------}

ins : Tail → List Instr
ins t = Block.instrs (select-tail t)

end : Tail → Jump
end t = Block.jump (select-tail t)

sels : List Tail → List Block
sels = map select-tail

selp : Tail × List Tail → Block × List Block
selp (t , bs) = select-tail t , sels bs

sel-ok : ∀ {φ ρ} a → X.arg φ ρ (select-atm a) ≡ G.atom φ a
sel-ok (Imp.var x) = refl
sel-ok (Imp.lit B k) = refl
sel-ok (Imp.fun-ref k) = refl

blk-map : ∀ bs l → X.block-at (sels bs) l ≡ mmap selp (block bs l)
blk-map [] l = refl
blk-map (t ∷ bs) l with l ≟ length bs | l ≟ length (sels bs)
... | yes _ | yes _ = refl
... | no _ | no _ = blk-map bs l
... | yes p | no q = ⊥-elim (q (trans p (sym (length-map select-tail bs))))
... | no p | yes q = ⊥-elim (p (trans q (length-map select-tail bs)))

load-ok : ∀ v → (M.resume v M.fstK ≡ M.value (X.get-field L.fst v))
  × (M.resume v M.sndK ≡ M.value (X.get-field L.snd v))
  × (∀ {n} (i : Fin n) → M.resume v (M.getK i) ≡ M.value (X.get-field (L.get i) v))
load-ok (code _) = refl , refl , λ _ → refl
load-ok (pair _ _) = refl , refl , λ _ → refl
load-ok (const _ _) = refl , refl , λ _ → refl
load-ok (tup _) = refl , refl , λ _ → refl
load-ok (inl _) = refl , refl , λ _ → refl
load-ok (inr _) = refl , refl , λ _ → refl

δ?-eq : ∀ o o' {n} → δ? eq o o' ≢ just (int n)
δ?-eq (o-const Int _) (o-const Int _) ()

eq-ok : ∀ v w → X.prim? eq v w ≡ mmap X.bit (X.cmp v w)
eq-ok v w with δ? eq (obs v) (obs w) in e
... | nothing = refl
... | just (bool b) = refl
... | just (int n) = ⊥-elim (δ?-eq (obs v) (obs w) e)

eq-ok′ : ∀ m m' → (m >>= λ v → m' >>= λ w → X.prim? eq v w) ≡ mmap X.bit (m >>= λ v → m' >>= λ w → X.cmp v w)
eq-ok′ nothing m' = refl
eq-ok′ (just v) nothing = refl
eq-ok′ (just v) (just w) = eq-ok v w

{- The simulation, for a program with definitions ds and main body n₀ bs₀ t₀ -------}

module Sim (ds : List C.Body) (n₀ : ℕ) (bs₀ : List Tail) (t₀ : Tail) where

  P = C.program ds (C.body n₀ bs₀ t₀)
  xds = map (select-body prologue) ds
  L₁ = G.sem P
  L₂ = X.sem (select P)

  private variable
    i n x l l₁ l₂ : ℕ
    a : Atm
    t : Tail
    bs : List Tail
    bs₂ : List Block
    is : List Instr
    j : Jump
    d : Loc
    φ : X.Frame
    ρ : X.Regs
    f : Maybe Bool
    v : X.Val
    r : Maybe X.Val
    o : Obs
    K D κ κ' : G.Cont
    σ : X.Stack
    s s' s₁ s₁' : G.State
    s₂ s₂' : X.State

  mutual
    {- the CFG continuation of a body, and the X86 call stack -}
    infix 4 _~_
    data _~_ : G.Cont → X.Stack → Set where
      halt : G.halt ~ X.halt
      callK : Dest D d is j bs₂ σ → G.callK φ D ~ X.retK (movq (loc (reg rax)) d ∷ is) j bs₂ φ σ

    {- D, given a value, continues as the X86 does after storing it in d -}
    data Dest : G.Cont → Loc → List Instr → Jump → List Block → X.Stack → Set where
      seqD : K ~ σ → Dest (G.seqK x t bs K) (var x) (ins t) (end t) (sels bs) σ
      retD : K ~ σ → Dest K (reg rax) [] retq bs₂ σ

  mutual
    {- the synchronisation points -}
    data Match : G.State → X.State → Set where
      exec~ : K ~ σ → Match (G.exec t φ bs K) (X.run (ins t) (end t) (sels bs) σ f φ ρ)
      ret~ : K ~ σ → ρ rax ≡ just v → Match (G.ret v φ K) (X.run [] retq bs₂ σ f φ ρ)
      now : F s₁ s₂ → Match s₁ s₂

    {- how the machines move to the next one, after the CFG's lag -}
    data Sync : G.State → X.State → Set where
      stop : G.step ds s₁ ≡ stop o → X.step xds s₂ ≡ stop o → Sync s₁ s₂
      go : G.step ds s₁ ≡ next s₁' → Plus L₂ s₂ s₂' → Match s₁' s₂' → Sync s₁ s₂

    F : G.State → X.State → Set
    F s₁ s₂ = Σ[ i ∈ ℕ ] Lag L₁ Sync i s₁ s₂

  {- the CFG evaluates, in the frame φ, an expression whose value r goes
     to κ, or errors -}
  data Run (φ : X.Frame) (κ : G.Cont) : G.State → Maybe X.Val → Set where
    last : G.step ds s ≡ G.res ds (M.value r) φ κ → Run φ κ s r
    fail : G.step ds s ≡ stop o-error → Run φ κ s nothing
    step : G.step ds s ≡ next s' → Run φ κ s' r → Run φ κ s r

  ev : ∀ {ρ} a {k : X.Val → Maybe X.Val} → G.step ds s ≡ G.res ds (M.value (G.atom φ a)) φ κ'
    → (∀ v → Run φ κ (G.ret v φ κ') (k v)) → Run φ κ s (X.arg φ ρ (select-atm a) >>= k)
  ev {φ = φ} {ρ = ρ} a g c rewrite sel-ok {φ} {ρ} a with G.atom φ a
  ... | nothing = fail g
  ... | just v = step g (c v)

  atm-run : ∀ {ρ} a → G.step ds s ≡ G.res ds (M.value (G.atom φ a)) φ κ → Run φ κ s (X.arg φ ρ (select-atm a))
  atm-run {φ = φ} {ρ = ρ} a g rewrite sel-ok {φ} {ρ} a = last g

  evs : ∀ {m} a → G.atom φ a ≡ m → G.step ds (G.eval a φ κ) ≡ G.res ds (M.value m) φ κ
  evs {φ = φ} {κ = κ} a e = cong (λ m → G.res ds (M.value m) φ κ) e

  {- scripts -}

  {- the CFG assigns v to slot x and runs t, as the X86 does -}
  write : X.step xds s₂ ≡ X.upd (φ [ x ]≔ v) ρ (X.run (ins t) (end t) (sels bs) σ f) → K ~ σ
    → F (G.ret v φ (G.seqK x t bs K)) s₂
  write {φ = φ} {x = x} {v = v} {t = t} {bs = bs} {K = K} h k with φ [ x ]≔ v in e
  ... | nothing = lag-now (stop (cong (λ m → G.jump m (just (t , bs)) K) e) h)
  ... | just φ' = lag-now (go (cong (λ m → G.jump m (just (t , bs)) K) e) (plus h ε) (exec~ k))

  jumpF : ∀ {mb} → G.step ds s₁ ≡ G.jump (just φ) mb K
    → X.step xds s₂ ≡ X.goto (mmap selp mb) σ f φ ρ → K ~ σ → F s₁ s₂
  jumpF {mb = nothing} g h k = lag-now (stop g h)
  jumpF {mb = just (t , bs)} g h k = lag-now (go g (plus h ε) (exec~ k))

  {- %rax holds v; the X86 moves it to d and continues as D -}
  to-dest : ∀ {D d is j bs₂ σ f φ ρ v} → Dest D d is j bs₂ σ → ρ rax ≡ just v
    → Reach L₂ Match (G.ret v φ D) (X.run (movq (loc (reg rax)) d ∷ is) j bs₂ σ f φ ρ)
  to-dest {φ = φ} {ρ} (seqD k) e = _ , ε , now (write (cong (λ m → X.put (var _) m φ ρ _) e) k)
  to-dest {φ = φ} {ρ} (retD k) e = _ , cong (λ m → X.put (reg rax) m φ ρ _) e ◅ ε , ret~ k refl

  {- the CFG errors, and the X86 has -}
  doom : Run φ κ s₁ nothing → X.step xds s₂ ≡ stop o-error → F s₁ s₂
  doom (last g) h = lag-now (stop g h)
  doom (fail g) h = lag-now (stop g h)
  doom (step g r) h = lag-step g (doom r h)

  {- the X86 stores r in %rax at the CFG step that produces it -}
  stage : ∀ {k} → Run φ κ s₁ r → X.step xds s₂ ≡ X.put (reg rax) r φ ρ k
    → (∀ v → Reach L₂ Match (G.ret v φ κ) (k φ (ρ [ rax ↦ just v ]))) → F s₁ s₂
  stage {r = nothing} r h c = doom r h
  stage {r = just v} {k = k} (step g r) h c = lag-step g (stage {k = k} r h c)
  stage {r = just v} (last g) h c with c v
  ... | _ , τ , m = lag-now (go g (plus h τ) m)

  {- the X86 stores r in d, a slot when the CFG assigns it -}
  pend : Dest D d is j bs₂ σ → Run φ D s₁ r → X.step xds s₂ ≡ X.put d r φ ρ (X.run is j bs₂ σ f) → F s₁ s₂
  pend (retD k) r h = stage r h λ v → _ , ε , ret~ k refl
  pend {r = nothing} (seqD k) r h = doom r h
  pend {r = just v} (seqD k) (step g r) h = lag-step g (pend (seqD k) r h)
  pend {r = just v} (seqD k) (last g) h = lag-step g (write h k)

  {- eq: the X86 sets the flag at the CFG step that produces the value -}
  cmpF : ∀ {mb} → Dest D d is j bs₂ σ → Run φ D s₁ (mmap X.bit mb)
    → X.step xds s₂ ≡ X.test mb (λ f' → X.run (sete d ∷ is) j bs₂ σ f' φ ρ) → F s₁ s₂
  cmpF {mb = nothing} dst r h = doom r h
  cmpF {mb = just b} dst (step g r) h = lag-step g (cmpF {mb = just b} dst r h)
  cmpF {mb = just b} (seqD k) (last g) h = lag-now (go g (plus h ε) (now (write refl k)))
  cmpF {mb = just b} (retD k) (last g) h = lag-now (go g (plus h (refl ◅ ε)) (ret~ k refl))

  tup-run : ∀ {ρ} vs as → G.step ds s ≡ G.res ds (M.tuple-next vs as) φ D
    → Run φ D s (X.args φ ρ vs (map select-atm as) (X.build L.tuple))
  tup-run vs [] g = last g
  tup-run vs (a ∷ as) g = step g (ev a refl λ v → tup-run (v ∷ vs) as refl)

  glob : ∀ k → X.global xds k ≡ mmap (select-body prologue) (G.global ds k)
  glob = reverse-map-‼ (select-body prologue) ds

  callB : ∀ {ve va} mb → Dest D d is j bs₂ σ → G.step ds s₁ ≡ G.call mb ve va φ D
    → X.step xds s₂ ≡ X.call (mmap (select-body prologue) mb) (X.retK (movq (loc (reg rax)) d ∷ is) j bs₂ φ σ)
                              (just ve) (just va) → Sync s₁ s₂
  callB nothing dst g h = stop g h
  callB (just (C.body n bs t)) dst g h = go g (plus h (refl ◅ refl ◅ ε)) (exec~ (callK dst))


  {- the call, after its operands -}
  callF : ∀ {ve va} vf → Dest D d is j bs₂ σ
    → X.step xds s₂ ≡ X.callq? xds (just vf) (X.retK (movq (loc (reg rax)) d ∷ is) j bs₂ φ σ)
                                   (ρ [ rdi ↦ just ve ] [ rsi ↦ just va ])
    → Sync (G.ret va φ (G.frm (M.appA vf ve) D)) s₂
  callF (code k) dst h = callB (G.global ds k) dst refl (trans h (cong (λ m → X.call m _ _ _) (glob k)))
  callF (pair _ _) dst h = stop refl h
  callF (const _ _) dst h = stop refl h
  callF (tup _) dst h = stop refl h
  callF (inl _) dst h = stop refl h
  callF (inr _) dst h = stop refl h

  app-sc : ∀ {D d is j bs₂ σ f φ ρ s₁} fn e a → Dest D d is j bs₂ σ → G.step ds s₁ ≡ next (G.eval fn φ (G.frm (M.appF e a) D))
    → F s₁ (X.run (select-simple (app fn e a) d ++ is) j bs₂ σ f φ ρ)
  app-sc {D} {d} {is} {j} {bs₂} {σ} {f} {φ} {ρ} {s₁} fn e a dst g = sc _ _ _ refl refl refl
    where
    k = X.retK (movq (loc (reg rax)) d ∷ is) j bs₂ φ σ
    is₁ = callq (select-atm fn) ∷ movq (loc (reg rax)) d ∷ is
    xe = λ {m} (ee : G.atom φ e ≡ m) →
      cong (λ m → X.put (reg rdi) m φ ρ (X.run (movq (select-atm a) (reg rsi) ∷ is₁) j bs₂ σ f)) (trans (sel-ok {ρ = ρ} e) ee)
    xa = λ {m ρ} (ea : G.atom φ a ≡ m) → cong (λ m → X.put (reg rsi) m φ ρ (X.run is₁ j bs₂ σ f)) (trans (sel-ok {ρ = ρ} a) ea)
    xf = λ {m ρ} (ef : G.atom φ fn ≡ m) → cong (λ m → X.callq? xds m k ρ) (trans (sel-ok {ρ = ρ} fn) ef)
    sc : ∀ mf me ma → G.atom φ fn ≡ mf → G.atom φ e ≡ me → G.atom φ a ≡ ma
      → F s₁ (X.run (select-simple (app fn e a) d ++ is) j bs₂ σ f φ ρ)
    sc nothing nothing _ ef ee ea = lag-step g (lag-now (stop (evs fn ef) (xe ee)))
    sc (just vf) nothing _ ef ee ea = lag-step g (lag-step (evs fn ef) (lag-step refl (lag-now (stop (evs e ee) (xe ee)))))
    sc nothing (just ve) nothing ef ee ea = lag-now (go g (plus (xe ee) ε) (now (lag-now (stop (evs fn ef) (xa ea)))))
    sc (just vf) (just ve) nothing ef ee ea = lag-now (go g (plus (xe ee) ε)
      (now (lag-step (evs fn ef) (lag-step refl (lag-step (evs e ee) (lag-step refl (lag-now (stop (evs a ea) (xa ea)))))))))
    sc nothing (just ve) (just va) ef ee ea = lag-now (go g (plus (xe ee) (xa ea ◅ ε)) (now (lag-now (stop (evs fn ef) (xf ef)))))
    sc (just vf) (just ve) (just va) ef ee ea = lag-now (go g (plus (xe ee) (xa ea ◅ ε))
      (now (lag-step (evs fn ef) (lag-step refl (lag-step (evs e ee) (lag-step refl (lag-step (evs a ea) (lag-now (callF vf dst (xf ef))))))))))

  simple : ∀ s → Dest D d is j bs₂ σ → G.step ds s₁ ≡ G.res ds (G.first φ s) φ D
    → F s₁ (X.run (select-simple s d ++ is) j bs₂ σ f φ ρ)
  simple (atm a) dst g = pend dst (atm-run a g) refl
  simple (app fn e a) dst g = app-sc fn e a dst g
  simple (Imp.pair a b) dst g = pend dst (step g (ev a refl λ v → step refl (ev b refl λ w → last refl))) refl
  simple (fst a) dst g = pend dst (step g (ev a refl λ v → last (cong (λ r → G.res ds r _ _) (proj₁ (load-ok v))))) refl
  simple (snd a) dst g =
    pend dst (step g (ev a refl λ v → last (cong (λ r → G.res ds r _ _) (proj₁ (proj₂ (load-ok v)))))) refl
  simple (get i a) dst g =
    pend dst (step g (ev a refl λ v → last (cong (λ r → G.res ds r _ _) (proj₂ (proj₂ (load-ok v)) i)))) refl
  simple (tuple as) dst g = pend dst (tup-run [] as g) refl
  simple (Imp.inl a) dst g = pend dst (step g (ev a refl λ v → last refl)) refl
  simple (Imp.inr a) dst g = pend dst (step g (ev a refl λ v → last refl)) refl
  simple (prim sub a b) dst g = stage (step g (atm-run a refl)) refl λ va →
    _ , ε , now (stage (step refl (ev b refl λ vb → last refl)) refl λ v → to-dest dst refl)
  simple {φ = φ} {ρ = ρ} (prim eq a b) dst g =
    cmpF dst (subst (Run _ _ _) (eq-ok′ (X.arg φ ρ (select-atm a)) (X.arg φ ρ (select-atm b)))
                    (step g (ev a refl λ v → step refl (ev b refl λ w → last refl)))) refl

  {- case: the X86 tests and loads at the CFG step that evaluates a, and
     jumps at the next -}
  branch : ∀ {mφ b} → G.step ds s₁ ≡ G.jump mφ (block bs l) K
    → X.step xds s₂ ≡ X.upd mφ ρ (X.run [] (je l₁ l₂) (sels bs) σ (just b))
    → (∀ φ' → X.step xds (X.run [] (je l₁ l₂) (sels bs) σ (just b) φ' ρ) ≡ X.goto (mmap selp (block bs l)) σ (just b) φ' ρ)
    → K ~ σ → Reach L₂ Match s₁ s₂
  branch {mφ = nothing} g h c k = _ , ε , now (lag-now (stop g h))
  branch {mφ = just φ'} g h c k = _ , h ◅ ε , now (jumpF g (c φ') k)

  xt : ∀ {is j bs₂ σ f φ ρ m} a → G.atom φ a ≡ m
    → X.step xds (X.run (L.testinl (select-atm a) ∷ is) j bs₂ σ f φ ρ) ≡ X.test (m >>= X.is-inl) (λ f' → X.run is j bs₂ σ f' φ ρ)
  xt a e = cong (λ m → X.test (m >>= X.is-inl) _) (trans (sel-ok a) e)

  caseF : ∀ {φ a x l₁ l₂ bs K σ f ρ} mv → G.atom φ a ≡ mv → K ~ σ
    → F (G.exec (case a x l₁ l₂) φ bs K) (X.run (ins (case a x l₁ l₂)) (end (case a x l₁ l₂)) (sels bs) σ f φ ρ)
  caseF {φ} {a} {x} {l₁} {l₂} {bs} {K} {σ} {f} {ρ} mv ea k = cs mv ea
    where
    xa = λ {m} → xt {L.load payload (select-atm a) (var x) ∷ []} {je l₁ l₂} {sels bs} {σ} {f} {φ} {ρ} {m} a
    cs : ∀ mv → G.atom φ a ≡ mv
      → F (G.exec (case a x l₁ l₂) φ bs K) (X.run (ins (case a x l₁ l₂)) (end (case a x l₁ l₂)) (sels bs) σ f φ ρ)
    cs nothing ea = lag-step refl (lag-now (stop (evs a ea) (xa ea)))
    cs (just (inl w)) ea with branch {bs = bs} {l = l₁} refl
      (cong (λ m → X.put (var x) (m >>= X.get-field payload) φ ρ _) (trans (sel-ok {ρ = ρ} a) ea))
      (λ _ → cong (λ m → X.goto m _ _ _ _) (blk-map bs l₁)) k
    ... | _ , τ , m = lag-step refl (lag-now (go (evs a ea) (plus (xa ea) τ) m))
    cs (just (inr w)) ea with branch {bs = bs} {l = l₂} refl
      (cong (λ m → X.put (var x) (m >>= X.get-field payload) φ ρ _) (trans (sel-ok {ρ = ρ} a) ea))
      (λ _ → cong (λ m → X.goto m _ _ _ _) (blk-map bs l₂)) k
    ... | _ , τ , m = lag-step refl (lag-now (go (evs a ea) (plus (xa ea) τ) m))
    cs (just (code _)) ea = lag-step refl (lag-step (evs a ea) (lag-now (stop refl (xa ea))))
    cs (just (pair _ _)) ea = lag-step refl (lag-step (evs a ea) (lag-now (stop refl (xa ea))))
    cs (just (const _ _)) ea = lag-step refl (lag-step (evs a ea) (lag-now (stop refl (xa ea))))
    cs (just (tup _)) ea = lag-step refl (lag-step (evs a ea) (lag-now (stop refl (xa ea))))

  {- the script from each synchronisation point -}
  fate : Match s₁ s₂ → F s₁ s₂
  fate (now fa) = fa
  fate (ret~ halt e) = lag-now (stop refl (cong X.halt? e))
  fate (ret~ {v = v} (callK dst) e) with to-dest {ρ = X.regs (just v) nothing nothing} dst refl
  ... | _ , τ , m = lag-now (go refl (plus (cong (λ m → X.back m _ _ _ _ _) e) τ) m)
  fate (exec~ {t = return s} k) =
    subst (λ is → F (G.exec (return s) _ _ _) (X.run is retq _ _ _ _ _)) (++-identityʳ _) (simple s (retD k) refl)
  fate (exec~ {t = seq x s t} k) = simple s (seqD k) refl
  fate (exec~ {t = goto l} {bs = bs} k) = jumpF refl (cong (λ m → X.goto m _ _ _ _) (blk-map bs l)) k
  fate (exec~ {t = case a x l₁ l₂} k) = caseF _ refl k

  sim : Sync s₁ s₂ → Answers≺ L₂ (Lag L₁ Sync) i (G.step ds s₁) s₂
  sim (stop g h) = answers-at g (stops h)
  sim (go g π m) = answers-at g (steps π (proj₂ (fate m)))

  fsim : FSim (G.sem P) L₂
  fsim = lag-fsim (fate (exec~ halt)) sim

{- The end theorem ---------------------------------------------------------------}

select-correct : ∀ P → Equivalent (G.sem P) (X.sem (select P))
select-correct (C.program ds (C.body n bs t)) = equivalent (Sim.fsim ds n bs t)
