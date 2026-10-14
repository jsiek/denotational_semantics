{-

  Definitions shared by the soundness and adequacy proofs for X86ᵀ in
  the graph model with errors (see GraphErr/X86.agda for the overview),
  for the machine of the definitions ds:

  * a state over a stack: the state with its stack below another (s ⊕ σ),
    which runs as the state does until it returns (step-⊕, ↠-⊕), so that
    the runs of a computation are those from the empty stack (Rets, the
    return of a value, Errs, an error, Res, either, for an element);
  * the locations of a state related to the sets of a semantic state by
    a relation P on elements and values (Locs P): the slots of its frame,
    the registers and the flag that its type has; a write of the machine
    and of the semantics keeps them related (put-rel, slot-rel);
  * the table of the program (T⁺), which gives definition f the meanings
    of the older ones (tbl-at): when the code of each definition depends
    only on the older ones (Indep), definition f means the same under
    the whole table (fix-S) and under the older ones and anything related
    to the rest (fix-C).

-}

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; suc; _<_; _≟_; _<?_)
open import Language.Typed.X86

module proof.Adequacy.GraphErr.X86Common {Σ : List ℕ} (ds : All (λ m → Body Σ (called m)) Σ) where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ν; Con; Con-⌈⌉; _•_)
open import proof.Framework.GraphModel.ErrorMonad using (ΛΛᵐ-val; errcode-con) renaming (Val to Valᴰ)
open import Framework.GraphModel.Env using (Env)
open import Framework.GraphModel.ErrorMonad using (errcode)
open import Semantics.GraphErr.Typed.Ops using (init; kindᶠ)
open import Framework.GraphModel.ErrorMonad using (Kind)
open import Semantics.GraphErr.Typed.Imp using (Table)
open import Semantics.GraphErr.Typed.Clos5 using (tbl)
open import Semantics.GraphErr.Typed.X86 using (RegsD; called-regs; codeₜ) renaming (_[_≔_] to _[_≔ˢ_])
open import proof.Semantics.GraphErr.Typed.Clos5 using (tbl-val)
open import Language.Typed.Type hiding (_≟_)
open import Framework.Membership using (_⊑_; ⊑-∋)
open import Framework.Lookup using (_!_; forget)
open import proof.Framework.Lookup using (forget-!; lvl-<)
open import proof.Correctness.GraphErr.SelectCorrect using (drop-idx)
open import Semantics.GraphErr.Typed.CFG using (drop)
open import Semantics.Observation using (Obs; o-error)
open import Semantics.CEK.Smallstep using (Next; next; stop)
open import Semantics.CEK.Typed.X86
open import proof.Framework.Runs using (module Runs)

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Properties using (<⇒≢; n<1+n; m<n⇒m<1+n; <-trans)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (yes; no; ¬_)

open Runs (step ds) public

{- States over stacks ---------------------------------------------------------------}

infixr 5 _++ˢ_
_++ˢ_ : Stack Σ → Stack Σ → Stack Σ
halt ++ˢ σ = σ
retK k bs φ σ' ++ˢ σ = retK k bs φ (σ' ++ˢ σ)

infixl 5 _⊕_
_⊕_ : State Σ → Stack Σ → State Σ
run k bs σ' η m ⊕ σ = run k bs (σ' ++ˢ σ) η m

⊕-halt : ∀ s → s ⊕ halt ≡ s
⊕-halt (run k bs σ η m) = cong (λ σ → run k bs σ η m) (++halt σ)
  where
  ++halt : ∀ σ → σ ++ˢ halt ≡ σ
  ++halt halt = refl
  ++halt (retK k bs φ σ) = cong (retK k bs φ) (++halt σ)

{- a state that steps steps the same over another stack -}
step-⊕ : ∀ s σ {s'} → step ds s ≡ next s' → step ds (s ⊕ σ) ≡ next (s' ⊕ σ)
step-⊕ (run (movq a d ∷ k) bs σ₀ η m) σ refl = refl
step-⊕ (run (subq a r e ∷ k) bs σ₀ η m) σ refl = refl
step-⊕ (run (cmpq a₂ a₁ ∷ k) bs σ₀ η m) σ refl = refl
step-⊕ (run (sete d ∷ k) bs σ₀ η m) σ refl = refl
step-⊕ (run (testinl a ∷ k) bs σ₀ η m) σ refl = refl
step-⊕ (run (alloc o d ∷ k) bs σ₀ η m) σ refl = refl
step-⊕ (run (load f a d ∷ k) bs σ₀ η m) σ refl = refl
step-⊕ (run (loadfst x r ∷ k) bs σ₀ η m) σ refl = refl
step-⊕ (run (loadsnd r ∷ k) bs σ₀ η m) σ refl = refl
step-⊕ (run (callq a e₁ e₂ ∷ k) bs σ₀ η m) σ q with arg a m
... | code f with q
... | refl = refl
step-⊕ (run (chk t x d ∷ k) bs σ₀ η m) σ q with proj? t (frame m ! x)
... | just v with q
... | refl = refl
step-⊕ (run (chk t x d ∷ k) bs σ₀ η m) σ () | nothing
step-⊕ (run (retq e) bs (retK k bs' φ σ₀) η m) σ refl = refl
step-⊕ (run (jmp l) bs σ₀ η m) σ refl = refl
step-⊕ (run (je l₁ l₂) bs σ₀ η m) σ q with flag m
... | true with q
... | refl = refl
step-⊕ (run (je l₁ l₂) bs σ₀ η m) σ q | false with q
... | refl = refl

↠-⊕ : ∀ {s t} σ → s ↠ t → (s ⊕ σ) ↠ (t ⊕ σ)
↠-⊕ σ done = done
↠-⊕ σ (_∷↠_ {s} q τ) = step-⊕ s σ q ∷↠ ↠-⊕ σ τ

{- Returns and errors ---------------------------------------------------------------}

{- a state that returns v from the empty stack -}
data Returns : State Σ → Val Σ Any → Set where
  rets : ∀ {n Bs Γ Δ O F η} {bs : Blocks Σ n Bs} {m : Mach Σ η (st Γ Δ O F)} (e : Γ ‹ rax › ≡ just (ty Any))
    → Returns (run (retq e) bs halt η m) (cast e (regs m ⦅ rax ⦆))

ret-η : ∀ {t v} → Returns t v → ℕ
ret-η (rets {η = η} e) = η

{- over a return frame, it continues the caller -}
ret-next : ∀ {t v} (r : Returns t v) {n Bs Δ} (k : Seq Σ n Bs (returned Δ)) bs φ σ
  → step ds (t ⊕ retK k bs φ σ) ≡ next (run k bs σ (ret-η r) ⟨ rv v tt tt , φ , tt , tt ⟩)
ret-next (rets e) k bs φ σ = refl

ret-stop : ∀ {t v} → Returns t v → step ds t ≡ stop (obs v)
ret-stop (rets e) = refl

{- from s over any stack, the machine stops with an error -}
Errs : State Σ → Set
Errs s = ∀ σ → Σ[ t ∈ State Σ ] (s ⊕ σ) ↠ t × step ds t ≡ stop o-error

{- from s, the machine returns v -}
Rets : State Σ → Val Σ Any → Set
Rets s v = Σ[ t ∈ State Σ ] s ↠ t × Returns t v

{- ω means an error, any other element the return of a value with P -}
Res : State Σ → Value → (Val Σ Any → Set) → Set
Res s w P = (w ≡ ω × Errs s) ⊎ Σ[ v ∈ Val Σ Any ] Rets s v × P v

Res-pre : ∀ {s s' w P} → s ↠ s' → Res s' w P → Res s w P
Res-pre τ (inj₁ ⟨ e , er ⟩) = inj₁ ⟨ e , (λ σ → let ⟨ t , ⟨ τ' , q ⟩ ⟩ = er σ in ⟨ t , ⟨ ↠-⊕ σ τ ++↠ τ' , q ⟩ ⟩) ⟩
Res-pre τ (inj₂ ⟨ v , ⟨ ⟨ t , ⟨ τ' , r ⟩ ⟩ , p ⟩ ⟩) = inj₂ ⟨ v , ⟨ ⟨ t , ⟨ τ ++↠ τ' , r ⟩ ⟩ , p ⟩ ⟩

Res-step : ∀ {s s' w P} → step ds s ≡ next s' → Res s' w P → Res s w P
Res-step q = Res-pre (q ∷↠ done)

obs≢err : ∀ {A} (v : Val Σ A) → obs v ≢ o-error
obs≢err (dyn G v) = obs≢err v
obs≢err (code f) ()
obs≢err (pack c e) ()
obs≢err (const k) ()
obs≢err (tup ws) ()
obs≢err (inl v) ()
obs≢err (inr v) ()

Rets-det : ∀ {s v₁ v₂} → Rets s v₁ → Rets s v₂ → v₁ ≡ v₂
Rets-det ⟨ t , ⟨ τ₁ , r₁ ⟩ ⟩ ⟨ t₂ , ⟨ τ₂ , r₂ ⟩ ⟩ with ↠-final-det τ₁ τ₂ (ret-stop r₁) (ret-stop r₂)
Rets-det ⟨ _ , ⟨ _ , rets e ⟩ ⟩ ⟨ _ , ⟨ _ , rets .e ⟩ ⟩ | refl = refl

{- a run does not both return and err -}
Rets-Errs : ∀ {s v} → Rets s v → Errs s → ⊥
Rets-Errs {s} {v} ⟨ t , ⟨ τ , r ⟩ ⟩ er with er halt
... | ⟨ t' , ⟨ τ' , q ⟩ ⟩ with ↠-final-det τ (subst (_↠ t') (⊕-halt s) τ') (ret-stop r) q
... | refl = obs≢err v (stop-inj (trans (sym (ret-stop r)) q))
  where
  stop-inj : ∀ {o o' : Obs} → stop {S = State Σ} o ≡ stop o' → o ≡ o'
  stop-inj refl = refl

{- Values ----------------------------------------------------------------------------}

pack-η : ∀ (v : Val Σ ⟪ fun ⟫) → v ≡ pack (code-of v) (env-of v)
pack-η (pack c e) = refl

{- the kinds of flat types are distinct -}
kindᶠ-inj : ∀ {G H} → kindᶠ G ≡ kindᶠ H → G ≡ H
kindᶠ-inj {G} {H} e = trans (sym (inv G)) (trans (cong back e) (inv H))
  where
  back : Kind → Flat
  back (Kind.base B) = base B
  back (Kind.tup n) = tup n
  back Kind.inj = sum
  back _ = fun
  inv : ∀ G → back (kindᶠ G) ≡ G
  inv (base B) = refl
  inv (tup n) = refl
  inv sum = refl
  inv fun = refl

{- Related locations ---------------------------------------------------------------}

{- the slot of the open closure holds it -}
Op : ∀ {η Δ} (O : Maybe (Δ ∋ ⟪ fun ⟫)) → Frame Σ Δ → Opened Σ η O → Set
Op nothing φ _ = ⊤
Op (just x) φ o = φ ! x ≡ pack (proj₁ o) (proj₂ o)

{- the value in a register, of type τ -}
rty : ℕ → RTy → Ty
rty η (ty A) = A
rty η codeα = code η
rty η tupα = ⟪ tup η ⟫

toV : ∀ {η} τ → RV Σ η τ → Val Σ (rty η τ)
toV (ty A) v = v
toV codeα v = v
toV tupα v = v

module Locs (P : ∀ {A} → Value → Val Σ A → Set) where

  {- every element of D, with v -}
  PS : ∀ {A} → 𝒫 Value → Val Σ A → Set
  PS D v = ∀ d → d ∈ D → P d v

  PR : ∀ {η} τ → 𝒫 Value → RV Σ η τ → Set
  PR τ D v = PS D (toV τ v)

  PM : ∀ {η} mt → 𝒫 Value → MV Σ η mt → Set
  PM (just τ) D v = PR τ D v
  PM nothing D v = ⊤

  PF : ∀ b → 𝒫 Value → Flag Σ b → Set
  PF true F b = PS F (bit b)
  PF false F _ = ⊤

  {- the slots, registers and flag of m and the semantic ρ, R and F -}
  record Rel {η ψ} (m : Mach Σ η ψ) (ρ : Env Value) (R : RegsD) (F : 𝒫 Value) : Set where
    constructor mr
    field
      fr : ∀ {A} (x : St.fr ψ ∋ A) → PS (ρ (idx x)) (frame m ! x)
      rg : ∀ r → PM (St.rs ψ ‹ r ›) (R r) (regs m ⦅ r ⦆)
      fl : PF (St.fl ψ) F (flag m)
      op : Op (St.op ψ) (frame m) (opened m)
  open Rel public

  cast-rel : ∀ {η mt τ} (e : mt ≡ just τ) {D} {v : MV Σ η mt} → PM mt D v → PR τ D (cast e v)
  cast-rel refl h = h

  {- writing register r -}
  reg-rel : ∀ {η Γ Δ O F'} {m : Mach Σ η (st Γ Δ O F')} {ρ R F} r {τ v D} → PR τ D v → Rel m ρ R F
    → Rel {ψ = st (Γ [ r ↦ just τ ]) Δ O F'} ⟨ regs m [ r ≔ v ] , frame m , opened m , flag m ⟩ ρ (R [ r ≔ˢ D ]) F
  reg-rel rax h (mr f g l o) = mr f (λ { rax → h ; rdi → g rdi ; rsi → g rsi }) l o
  reg-rel rdi h (mr f g l o) = mr f (λ { rax → g rax ; rdi → h ; rsi → g rsi }) l o
  reg-rel rsi h (mr f g l o) = mr f (λ { rax → g rax ; rdi → g rdi ; rsi → h }) l o

  {- writing slot k, which forgets the slots after it -}
  slot-rel : ∀ {η Γ Δ Δ' O F' A} {m : Mach Σ η (st Γ Δ O F')} {ρ R F} (p : Δ' ⊑ Δ) {v : Val Σ A} {D} → PS D v → Rel m ρ R F
    → Rel {ψ = st Γ (A ∷ Δ') nothing F'} ⟨ regs m , v ∷ forget p (frame m) , tt , flag m ⟩ (D • drop p ρ) R F
  slot-rel {m = m} {ρ} p h (mr f g l o) = mr fr′ g l tt
    where
    fr′ : ∀ {A} (x : _ ∋ A) → _
    fr′ Z = h
    fr′ (S y) = subst₂ PS (sym (drop-idx p ρ y)) (sym (forget-! p (frame m) y)) (f (⊑-∋ p y))

  {- the flag, set -}
  flag-rel : ∀ {η Γ Δ O F'} {m : Mach Σ η (st Γ Δ O F')} {ρ R F} b {G} → PS G (bit b) → Rel m ρ R F
    → Rel {ψ = st Γ Δ O true} ⟨ regs m , frame m , opened m , b ⟩ ρ R G
  flag-rel b h (mr f g l o) = mr f g h o

  {- the registers after a call or a return -}
  ret-rel : ∀ {η Δ} {φ : Frame Σ Δ} {ρ C v} → (∀ {A} (x : Δ ∋ A) → PS (ρ (idx x)) (φ ! x)) → PS C v
    → Rel {η} {returned Δ} ⟨ rv v tt tt , φ , tt , tt ⟩ ρ (called-regs C) init
  ret-rel f h = mr f (λ { rax → h ; rdi → tt ; rsi → tt }) tt tt

  {- %rax and the flag, unset by chk -}
  rax-rel : ∀ {η Γ Δ O F'} {m : Mach Σ η (st Γ Δ O F')} {ρ R F G} → Rel m ρ R F
    → Rel {ψ = st (Γ [ rax ↦ nothing ]) Δ O false} ⟨ regs m [ rax ≔ tt ] , frame m , opened m , tt ⟩ ρ (R [ rax ≔ˢ init ]) G
  rax-rel (mr f g l o) = mr f (λ { rax → tt ; rdi → g rdi ; rsi → g rsi }) tt o

  {- opening the closure in slot x forgets the code and environment of the last one -}
  wipe-rel : ∀ {η Γ Δ O F'} {m : Mach Σ η (st Γ Δ O F')} {ρ R F} (x : Δ ∋ ⟪ fun ⟫) → Rel m ρ R F
    → Rel {ψ = st (wipe Γ) Δ (just x) F'} ⟨ wipeᵣ (regs m) , frame m , ⟨ code-of (frame m ! x) , env-of (frame m ! x) ⟩ , flag m ⟩ ρ R F
  wipe-rel {Γ = Γ} {m = m} x (mr f g l o) =
    mr f (λ { rax → fg (Regs.ax Γ) (g rax) ; rdi → fg (Regs.di Γ) (g rdi) ; rsi → fg (Regs.si Γ) (g rsi) }) l (pack-η (frame m ! x))
    where
    fg : ∀ {η η'} mt {D v} → PM {η} mt D v → PM {η'} (forgetα mt) D (forgetᵥ mt v)
    fg (just (ty A)) h = h
    fg (just codeα) h = tt
    fg (just tupα) h = tt
    fg nothing h = tt

{- The table of the program -----------------------------------------------------------}

T⁺ : Table
T⁺ = tbl (codeₜ {Σ}) ds

{- the entries of a table are sets of values, consistent ones -}
Good : Table → Set
Good T = ∀ k → Valᴰ (T k) × Con (T k)

{- the code of each definition depends only on the older ones -}
Indep : Set₁
Indep = ∀ {n} (f : Σ ∋ n) {T T'} → Good T → Good T' → (∀ j → j < lvl f → T j ≃ T' j)
  → codeₜ T (ds ! f) ≃ codeₜ T' (ds ! f)

{- the table T below p, and D above -}
cut : ℕ → 𝒫 Value → Table → Table
cut p D T j with j <? p
... | yes _ = T j
... | no _ = D

cut-below : ∀ {p D T j} → j < p → cut p D T j ≡ T j
cut-below {p} {j = j} j< with j <? p
... | yes _ = refl
... | no ¬< = ⊥-elim (¬< j<)

cut-good : ∀ {p D T} → Valᴰ D → Con D → Good T → Good (cut p D T)
cut-good {p} vD cD gT j with j <? p
... | yes _ = gT j
... | no _ = ⟨ vD , cD ⟩

{- definition f, which the machine finds in ds, is the code of the
   table of the older ones, which is errcode above them -}
tbl-at : ∀ {n} (f : Σ ∋ n) → Σ[ T ∈ Table ] T⁺ (lvl f) ≡ codeₜ T (ds ! f) × (∀ j → T j ≡ cut (lvl f) errcode T⁺ j)
tbl-at f = at ds f
  where
  c = codeₜ {Σ}
  cons : ∀ {ns m j} (p : _) (ps : All (λ m → Body Σ (called m)) ns) → j ≢ length ns → tbl c {m ∷ ns} (p ∷ ps) j ≡ tbl c ps j
  cons {ns} {j = j} p ps ne with j ≟ length ns
  ... | yes e = ⊥-elim (ne e)
  ... | no _ = refl
  out : ∀ {ns} (ps : All (λ m → Body Σ (called m)) ns) j → ¬ (j < length ns) → tbl c ps j ≡ errcode
  out [] j _ = refl
  out {_ ∷ ns} (p ∷ ps) j ¬< with j ≟ length ns
  ... | yes refl = ⊥-elim (¬< (n<1+n _))
  ... | no _ = out ps j (λ j< → ¬< (m<n⇒m<1+n j<))
  at : ∀ {ns n} (ps : All (λ m → Body Σ (called m)) ns) (f : ns ∋ n)
    → Σ[ T ∈ Table ] tbl c ps (lvl f) ≡ c T (ps ! f) × (∀ j → T j ≡ cut (lvl f) errcode (tbl c ps) j)
  at {_ ∷ ns} (p ∷ ps) Z with length ns ≟ length ns
  ... | no ne = ⊥-elim (ne refl)
  ... | yes _ = ⟨ tbl c ps , ⟨ refl , pw ⟩ ⟩
    where
    pw : ∀ j → tbl c ps j ≡ cut (length ns) errcode (tbl c (p ∷ ps)) j
    pw j with j <? length ns
    ... | yes j< = sym (cons p ps (<⇒≢ j<))
    ... | no ¬< = out ps j ¬<
  at {_ ∷ ns} (p ∷ ps) (S f) with lvl f ≟ length ns | at ps f
  ... | yes e | _ = ⊥-elim (<⇒≢ (lvl-< f) e)
  ... | no ne | ⟨ T , ⟨ e , pw ⟩ ⟩ = ⟨ T , ⟨ e , (λ j → trans (pw j) (agree j)) ⟩ ⟩
    where
    agree : ∀ j → cut (lvl f) errcode (tbl c ps) j ≡ cut (lvl f) errcode (tbl c (p ∷ ps)) j
    agree j with j <? lvl f
    ... | yes j< = sym (cons p ps (<⇒≢ (<-trans j< (lvl-< f))))
    ... | no _ = refl

module _ (TC : ∀ k → Con (T⁺ k)) (ind : Indep) {n} (f : Σ ∋ n) where

  private
    gT⁺ : Good T⁺
    gT⁺ k = ⟨ tbl-val (λ _ → ΛΛᵐ-val) ds k , TC k ⟩
    T = proj₁ (tbl-at f)
    e = proj₁ (proj₂ (tbl-at f))
    pw = proj₂ (proj₂ (tbl-at f))
    gT : Good T
    gT j = subst (λ D → Valᴰ D × Con D) (sym (pw j)) (cut-good {lvl f} ΛΛᵐ-val errcode-con gT⁺ j)
    below : ∀ {D} j → j < lvl f → T j ≃ cut (lvl f) D T⁺ j
    below {D} j j< = ≃-reflexive (trans (pw j) (trans (cut-below {D = errcode} {T⁺} j<) (sym (cut-below {D = D} {T⁺} j<))))

  {- the code of f under the whole table is part of its entry -}
  fix-S : codeₜ T⁺ (ds ! f) ⊆ T⁺ (lvl f)
  fix-S d d∈ = subst (d ∈_) (sym e) (proj₁ (ind f gT⁺ gT (λ j j< → ≃-trans (≃-reflexive (sym (cut-below {D = errcode} {T⁺} j<))) (≃-sym (below {errcode} j j<)))) d d∈)

  {- its entry is its code under the older ones, and the empty function above them -}
  fix-C : T⁺ (lvl f) ⊆ codeₜ (cut (lvl f) ⌈ ν ⌉ T⁺) (ds ! f)
  fix-C d d∈ = proj₁ (ind f gT (cut-good {lvl f} ⟨ (λ { _ refl () }) , ⟨ ν , refl ⟩ ⟩ (Con-⌈⌉ ν) gT⁺) (below {⌈ ν ⌉})) d (subst (d ∈_) e d∈)
