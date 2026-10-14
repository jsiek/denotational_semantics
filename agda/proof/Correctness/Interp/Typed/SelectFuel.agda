{-

  Correctness of typed select instructions (CFGᵀ → X86), clock for clock
  (see the design note in Semantics/Interp/Clock.agda): the pass keeps
  every call, and in both interpreters only calls tick, so for every
  clock the X86 program gives the erasure (er) of the CFGᵀ program's
  result. There is no precondition.

  X86 is untyped: a typed value is erased to the untyped value of the
  same shape (a reference to a definition to its level, a closure to a
  pair, dyn G v to v). The X86 frame holds the erased typed frame, slot
  x at its level (Rep), and has as many slots as every tail run in it
  needs (depth). The instructions of select-simple s d run in
  continuation-passing style (simple-ok); a project's check errs exactly
  where the typed project fails (proj-ok). Definitions and labels exist
  and frames are large enough by the typing (proof/Compiler/Typed/SelectFacts.agda).

-}

module proof.Correctness.Interp.Typed.SelectFuel where

open import Framework.Primitives using (Base; Nat; Int; 𝔹; Unit; Void; Blame)
open import Language.Prim using (sub; eq; bool)
open import Language.Typed.Type hiding (_≟_)
open import Framework.Membership using (_⊑_; ⊑-∋)
open import Framework.Lookup using (_!_; forget)
open import proof.Framework.Membership using (lvl-<; lvl-⊑; forget-!)
open import Framework.ListUtil using (_‼_; proj)
open import proof.Framework.VecProj using (proj-pw; proj-bad)
import Language.Typed.Imp as I
open I using (var; lit; ref)
open import Language.Typed.CFG as CFG using (Tail; return; seq; goto; case; Blocks; _▷_; Body; body)
open import Compiler.Typed.Select
open import proof.Compiler.Typed.SelectFacts using (global-sel; len-blocks; depth-≥)
import Language.X86 as L
open L using (Block; block; Loc; var; reg; rax; rdi; rsi; retq; jmp; je; imm; label; loc; movq; subq; cmpq; sete; testinl; alloc; load; callq)
open import Semantics.Observation using (Obs; o-const; o-fun; o-tuple; o-inl; o-inr)
open import proof.Semantics.Interp.Clock
import Semantics.Interp.Clos5 as U
open import Semantics.Interp.Imp using (_[_]≔_; zero-val)
import Semantics.Interp.X86 as X
open X using (regs)
import Semantics.Interp.Typed.Clos5 as C
import Semantics.Interp.Typed.CFG as G
open import Semantics.Interp.Typed.Imp using (atom; eval-simple)

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
import Data.Integer as Z
open import Data.List using (List; []; _∷_; _++_; _ʳ++_; length; reverse; replicate)
open import Data.List.Properties using (++-identityʳ; ++-assoc; reverse-involutive; length-replicate)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe.Relation.Binary.Pointwise as M
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _⊔_; _∸_; _+_; s≤s; _≟_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; <⇒≢; m≤n+m∸n; ≤-reflexive)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_; lookup; toList; map)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; does)

fm : ∀ {A B : Set} {m : Maybe A} {u} {f : A → Result B} → m ≡ just u → (from-maybe m >>= f) ≡ f u
fm refl = refl

{- assigning slot k of a frame that has it -}
set-ok : ∀ (φ : List U.Val) k v → k < length φ
  → Σ[ φ' ∈ _ ] (φ [ k ]≔ v ≡ just φ') × length φ' ≡ length φ × φ' ‼ k ≡ just v × (∀ x → x ≢ k → φ' ‼ x ≡ φ ‼ x)
set-ok (u ∷ φ) zero v _ = v ∷ φ , refl , refl , refl , λ { zero ne → ⊥-elim (ne refl) ; (suc x) _ → refl }
set-ok (u ∷ φ) (suc k) v (s≤s lt) with set-ok φ k v lt
... | φ' , e , l , h , o rewrite e = u ∷ φ' , refl , cong suc l , h , λ { zero _ → refl ; (suc x) ne → o x λ e → ne (cong suc e) }

module _ {Σ : List ℕ} (dsC : All (λ n → Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) Σ) where
  open C.Vals Σ
  private ds' = select-defs dsC

  {- Erasure -------------------------------------------------------------------}

  er : ∀ {A} → Val A → U.Val
  ers : ∀ {n} → Vec (Val Any) n → List U.Val
  er (code f) = U.code (lvl f)
  er (pack c e) = U.pair (er c) (er e)
  er (const {B} k) = U.const B k
  er (tup vs) = U.tup (ers vs)
  er (inl v) = U.inl (er v)
  er (inr v) = U.inr (er v)
  er (dyn G v) = er v
  ers [] = []
  ers (v ∷ vs) = er v ∷ ers vs

  obs-er : ∀ {A} (v : Val A) → obs v ≡ U.obs (er v)
  obs-ers : ∀ {n} (vs : Vec (Val Any) n) → obs-vec vs ≡ U.obs-list (ers vs)
  obs-er (code f) = refl
  obs-er (pack c e) = refl
  obs-er (const k) = refl
  obs-er (tup vs) = cong o-tuple (obs-ers vs)
  obs-er (inl v) = cong o-inl (obs-er v)
  obs-er (inr v) = cong o-inr (obs-er v)
  obs-er (dyn G v) = obs-er v
  obs-ers [] = refl
  obs-ers (v ∷ vs) = cong₂' (obs-er v) (obs-ers vs)
    where cong₂' : ∀ {o o' : Obs} {os os'} → o ≡ o' → os ≡ os' → Data.List._∷_ o os ≡ o' ∷ os'
          cong₂' refl refl = refl

  ers-pw : ∀ {n} (vs : Vec (Val Any) n) → Pointwise (λ u v → u ≡ er v) (ers vs) (toList vs)
  ers-pw [] = []
  ers-pw (v ∷ vs) = refl ∷ ers-pw vs

  proj-ers : ∀ {n} (i : Fin n) (vs : Vec (Val Any) n) → proj i (ers vs) ≡ just (er (lookup vs i))
  proj-ers i vs with proj i (ers vs) | proj-pw i (ers-pw vs)
  ... | just _ | M.just refl = refl

  {- the X86 frame φ' holds the erased frame φ, each slot at its level -}
  record Rep {Δ} (φ : Env Δ) (φ' : List U.Val) : Set where
    constructor rep
    field slot : ∀ {A} (x : Δ ∋ A) → φ' ‼ lvl x ≡ just (er (φ ! x))
  open Rep

  rep-set : ∀ {Δ Δ' A} {φ : Env Δ} {φ' φ''} (p : Δ' ⊑ Δ) (v : Val A) → Rep φ φ'
    → φ'' ‼ length Δ' ≡ just (er v) → (∀ x → x ≢ length Δ' → φ'' ‼ x ≡ φ' ‼ x) → Rep (v ∷ forget p φ) φ''
  rep-set {φ = φ} {φ'} p v R h o = rep λ { Z → h ; (S y) →
    trans (o (lvl y) (<⇒≢ (lvl-< y))) (trans (cong (φ' ‼_) (sym (lvl-⊑ p y)))
      (trans (slot R (⊑-∋ p y)) (cong (λ u → just (er u)) (sym (forget-! p φ y))))) }

  arg-ok : ∀ {Δ A} {φ : Env Δ} {φ'} ρ → Rep φ φ' → (a : I.Atm Σ Δ A) → X.arg (φ' , ρ) (select-atm a) ≡ ret (er (atom φ a))
  arg-ok ρ R (var x) rewrite slot R x = refl
  arg-ok ρ R (lit B c) = refl
  arg-ok ρ R (ref f) = refl

  args-ok : ∀ {Δ n B} {φ : Env Δ} {φ'} ρ → Rep φ φ' → (as : Vec (I.Atm Σ Δ Any) n) (us : List U.Val) {f : List U.Val → Result B}
    → X.args (φ' , ρ) us (toList (map select-atm as)) f ≡ f (ers (map (atom φ) as) ʳ++ us)
  args-ok ρ R [] us = refl
  args-ok ρ R (a ∷ as) us rewrite arg-ok ρ R a = args-ok ρ R as _

  sub-ok : ∀ (v w : Val ⟪ base Int ⟫) → U.prim? sub (er v) (er w) ≡ just (er (δ sub v w))
  sub-ok (const n) (const m) = refl

  eq-ok : ∀ n m → U.out (bool (does (n Z.≟ m))) ≡ er (δ eq (const n) (const m))
  eq-ok n m with does (n Z.≟ m)
  ... | true = refl
  ... | false = refl

  {- Clock for clock -------------------------------------------------------------}

  module _ (ck : ℕ)
    (calls : ∀ {n} (g : Σ ∋ n) e w
      → X.call ds' ck (just (select-body prologue (dsC ! g))) (er e) (er w) ≡ (G.call dsC ck (pack (code g) e) w >>= λ v → ret (er v)))
    where

    Run : List Block → List L.Instr → L.Jump → X.State → Result U.Val
    Run bs' is j s = X.run ds' ck bs' s is j

    {- the check of project t, on a value v of flat type G at slot k -}
    proj-ok : ∀ t {G} (v : Val ⟪ G ⟫) {φ' : List U.Val} {k} ρ {d bs' is j} {K : Val ⟪ flat t ⟫ → Result U.Val}
      → φ' ‼ k ≡ just (er v)
      → (∀ w ρ' → er w ≡ er v → K w ≡ Run bs' (movq (loc (var k)) d ∷ is) j (φ' , ρ'))
      → (project? t (dyn G v) >>= K) ≡ Run bs' (check t (loc (var k)) ++ movq (loc (var k)) d ∷ is) j (φ' , ρ)
    proj-ok tint (const {Int} c) ρ e h rewrite e = h _ _ refl
    proj-ok tint (const {Nat} c) ρ e h rewrite e = refl
    proj-ok tint (const {𝔹} c) ρ e h rewrite e = refl
    proj-ok tint (const {Unit} c) ρ e h rewrite e = refl
    proj-ok tint (const {Void} c) ρ e h rewrite e = refl
    proj-ok tint (const {Blame} c) ρ e h rewrite e = refl
    proj-ok tint (tup vs) ρ e h rewrite e = refl
    proj-ok tint (inl v) ρ e h rewrite e = refl
    proj-ok tint (inr v) ρ e h rewrite e = refl
    proj-ok tint (pack c v) ρ e h rewrite e = refl
    proj-ok tsum (inl v) ρ e h rewrite e = h _ _ refl
    proj-ok tsum (inr v) ρ e h rewrite e = h _ _ refl
    proj-ok tsum (const c) ρ e h rewrite e = refl
    proj-ok tsum (tup vs) ρ e h rewrite e = refl
    proj-ok tsum (pack c v) ρ e h rewrite e = refl
    proj-ok tfun (pack c v) ρ e h rewrite e = h _ _ refl
    proj-ok tfun (const c) ρ e h rewrite e = refl
    proj-ok tfun (tup vs) ρ e h rewrite e = refl
    proj-ok tfun (inl v) ρ e h rewrite e = refl
    proj-ok tfun (inr v) ρ e h rewrite e = refl
    proj-ok (ttup n i) (tup {m} vs) ρ e h with m ≟ suc n
    ... | yes refl rewrite e | proj-ers i vs = h _ _ refl
    ... | no ne rewrite e | proj-bad i ne (ers-pw vs) = refl
    proj-ok (ttup n i) (const c) ρ e h rewrite e = refl
    proj-ok (ttup n i) (inl v) ρ e h rewrite e = refl
    proj-ok (ttup n i) (inr v) ρ e h rewrite e = refl
    proj-ok (ttup n i) (pack c v) ρ e h rewrite e = refl

    {- s, computed into d, then the rest of a block -}
    simple-ok : ∀ {Δ A} (s : I.Simple Σ Δ A) d {φ : Env Δ} {φ'} ρ {bs' is j} {k : Val A → Result U.Val} → Rep φ φ'
      → (∀ v ρ' → k v ≡ X.write (φ' , ρ') d (er v) (Run bs' is j))
      → (eval-simple (G.call dsC ck) φ s >>= k) ≡ Run bs' (select-simple s d ++ is) j (φ' , ρ)
    simple-ok (I.atm a) d ρ R h rewrite arg-ok ρ R a = h _ ρ
    simple-ok (I.pack a b) d ρ R h rewrite arg-ok ρ R a | arg-ok ρ R b = h _ ρ
    simple-ok (I.callc (var x) (var y)) d {φ} ρ R h with φ ! x | slot R x
    ... | pack (code g) e | r rewrite r | slot R y | global-sel dsC g =
      sym (trans (bind≡ (calls g e _) λ _ → refl)
                 (trans (bind-assoc (G.call dsC ck (pack (code g) e) _))
                        (bind-cong (G.call dsC ck (pack (code g) e) _) λ v → sym (h v _))))
    simple-ok (I.tuple as) d {φ} {φ'} ρ {bs'} {is} {j} R h =
      trans (h _ ρ) (sym (trans (args-ok ρ R as [])
        (cong (λ l → X.write (φ' , ρ) d (U.tup l) (Run bs' is j)) (reverse-involutive (ers (map (atom φ) as))))))
    simple-ok (I.get i (var x)) d {φ} ρ R h with φ ! x | slot R x
    ... | tup vs | r rewrite r | proj-ers i vs = h _ ρ
    simple-ok (I.inl a) d ρ R h rewrite arg-ok ρ R a = h _ ρ
    simple-ok (I.inr a) d ρ R h rewrite arg-ok ρ R a = h _ ρ
    simple-ok (I.prim sub a b) d {φ} ρ R h
      rewrite arg-ok ρ R a | arg-ok (record ρ { %rax = just (er (atom φ a)) }) R b | sub-ok (atom φ a) (atom φ b) = h _ _
    simple-ok (I.prim eq a b) d {φ} ρ R h rewrite arg-ok ρ R a | arg-ok ρ R b with atom φ a | atom φ b
    ... | const n | const m rewrite eq-ok n m = h _ _
    simple-ok (I.inject G a) d ρ R h rewrite arg-ok ρ R a = h _ ρ
    simple-ok (I.project t (var x)) d {φ} {φ'} ρ {bs'} {is} {j} R h with φ ! x | slot R x
    ... | dyn G v | r =
      trans (proj-ok t v ρ r λ w ρ' e → trans (h w ρ') (sym (trans (fm r) (cong (λ u → X.write (φ' , ρ') d u (Run bs' is j)) (sym e)))))
            (cong (λ l → Run bs' l j (φ' , ρ)) (sym (++-assoc (check t (loc (var (lvl x)))) _ is)))

    {- t, and block l, with the blocks bs, in a frame large enough -}
    tail-ok : ∀ {Bs Δ} (t : Tail Σ Bs Δ) (bs : Blocks Σ Bs) {φ : Env Δ} {φ'} ρ → Rep φ φ'
      → depth t ≤ length φ' → blocks-depth bs ≤ length φ'
      → Run (select-blocks bs) (Block.instrs (select-tail t)) (Block.jump (select-tail t)) (φ' , ρ)
        ≡ (G.tail dsC ck bs φ t >>= λ v → ret (er v))
    jump-ok : ∀ {Bs Δ} (bs : Blocks Σ Bs) (l : Bs ∋ Δ) {φ : Env Δ} {φ'} ρ → Rep φ φ' → blocks-depth bs ≤ length φ'
      → X.jump ds' ck (select-blocks bs) (φ' , ρ) (lvl l) ≡ (G.jump dsC ck bs l φ >>= λ v → ret (er v))

    tail-ok (return s) bs ρ R dt db =
      trans (cong (λ is → Run (select-blocks bs) is retq _) (sym (++-identityʳ (select-simple s (reg rax)))))
            (sym (simple-ok s (reg rax) ρ R λ v ρ' → refl))
    tail-ok (seq {Δ'} p s t) bs {φ} {φ'} ρ R dt db =
      sym (trans (bind-assoc (eval-simple (G.call dsC ck) φ s)) (simple-ok s (var (length Δ')) ρ R h))
      where
      lt : length Δ' < length φ'
      lt = ≤-trans (depth-≥ t) (≤-trans (m≤n⊔m _ _) dt)
      h : ∀ v ρ' → (G.tail dsC ck bs (v ∷ forget p φ) t >>= λ u → ret (er u))
        ≡ X.write (φ' , ρ') (var (length Δ')) (er v) (Run (select-blocks bs) (Block.instrs (select-tail t)) (Block.jump (select-tail t)))
      h v ρ' with set-ok φ' (length Δ') (er v) lt
      ... | φ'' , e , l , hk , o rewrite e =
        sym (tail-ok t bs {φ' = φ''} ρ' (rep-set p v R hk o) (subst (_ ≤_) (sym l) (≤-trans (m≤n⊔m _ _) dt)) (subst (_ ≤_) (sym l) db))
    tail-ok (goto l) bs ρ R dt db = jump-ok bs l ρ R db
    tail-ok (case {Δ'} (var x) p l₁ l₂) bs {φ} {φ'} ρ R dt db with φ ! x | slot R x
    ... | inl v | r rewrite r with set-ok φ' (length Δ') (er v) (≤-trans (m≤n⊔m _ _) dt)
    ...   | φ'' , e , l , hk , o rewrite e = jump-ok bs l₁ _ (rep-set p v R hk o) (subst (_ ≤_) (sym l) db)
    tail-ok (case {Δ'} (var x) p l₁ l₂) bs {φ} {φ'} ρ R dt db | inr v | r rewrite r with set-ok φ' (length Δ') (er v) (≤-trans (m≤n⊔m _ _) dt)
    ...   | φ'' , e , l , hk , o rewrite e = jump-ok bs l₂ _ (rep-set p v R hk o) (subst (_ ≤_) (sym l) db)

    jump-ok {_ ∷ Bs} (bs ▷ t) Z ρ R db with length Bs ≟ length (select-blocks bs)
    ... | yes _ = tail-ok t bs ρ R (≤-trans (m≤m⊔n _ _) db) (≤-trans (m≤n⊔m _ _) db)
    ... | no ne = ⊥-elim (ne (sym (len-blocks bs)))
    jump-ok (bs ▷ t) (S l) ρ R db with lvl l ≟ length (select-blocks bs)
    ... | yes e = ⊥-elim (<⇒≢ (lvl-< l) (trans e (len-blocks bs)))
    ... | no _ = jump-ok bs l ρ R (≤-trans (m≤n⊔m _ _) db)

  {- a body runs in a frame of its depth -}
  calls≡ : ∀ ck {n} (g : Σ ∋ n) e w
    → X.call ds' ck (just (select-body prologue (dsC ! g))) (er e) (er w) ≡ (G.call dsC ck (pack (code g) e) w >>= λ v → ret (er v))
  calls≡ zero g e w = refl
  calls≡ (suc ck) g e w with dsC ! g
  ... | body bs t =
    tail-ok ck (calls≡ ck) t bs _ (rep λ { Z → refl ; (S Z) → refl })
      (≤-trans (m≤n⊔m _ _) N≤) (≤-trans (m≤m⊔n _ _) N≤)
    where N≤ : blocks-depth bs ⊔ depth t ≤ length (zero-val ∷ zero-val ∷ replicate (blocks-depth bs ⊔ depth t ∸ 2) zero-val)
          N≤ = ≤-trans (m≤n+m∸n (blocks-depth bs ⊔ depth t) 2)
                 (≤-reflexive (cong (λ k → suc (suc k)) (sym (length-replicate (blocks-depth bs ⊔ depth t ∸ 2)))))

{- the result of the X86 program is the erased result of the CFGᵀ one -}
erased : ∀ {A B : Set} {g : A → B} {r₁ r₂} → r₂ ≡ (r₁ >>= λ v → ret (g v)) → RelResult (λ v u → g v ≡ u) r₁ r₂
erased {r₁ = timeout} refl = timeout
erased {r₁ = error} refl = error
erased {r₁ = ret v} refl = ret refl

select-correct : ∀ (P : CFG.Program) → Equivalent (G.sem P) (X.sem (select P))
select-correct (CFG.program {Σ} ds (body bs t)) = clocked (λ v u → er ds v ≡ u) (λ {v} e → trans (obs-er ds v) (cong U.obs e)) λ ck →
  erased (tail-ok ds ck (calls≡ ds ck) t bs _ (rep λ ()) (≤-trans (m≤n⊔m _ _) N≤) (≤-trans (m≤m⊔n _ _) N≤))
  where N≤ = ≤-reflexive (sym (length-replicate (blocks-depth bs ⊔ depth t)))
