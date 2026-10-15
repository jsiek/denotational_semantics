{-

  Adequacy of the graph model of X86μ (Mu/Semantics/Graph/X86.agda) for
  the X86μ machine (Mu/Semantics/CEK/X86.agda): every element of the
  denotation of a program is witnessed by a run of the machine. As for
  X86ᵀ (proof/Adequacy/X86LogRel.agda), with the logical relation 𝕍 of
  the Clos5μ values (Mu/proof/Adequacy/Clos5Values.agda), code f being
  related to Λ X. Λ Y. w when the machine runs definition f on values
  related to X and Y, on any stack, to a return of a value related to w
  (Run, Ret). The fundamental lemma (adequate) is by induction on the
  sequence, given that the blocks it may jump to are adequate (AdeqB):
  the frame, the registers and the flag of the semantics are related to
  those of the machine (𝕄), and the open closure is that of its slot
  (OpR). A call returns the same value for every element of its
  denotation, since runs are deterministic (Ret-det).

  The machine runs a definition to its return independently of the
  stack it returns to (Retq), so that what runs after a call is related
  for the state the return leaves. Typed code never reads an unset
  register or flag, so these are related to anything. fold and unfold
  (↑, ↓) are the identity on denotations, and 𝕍 d (fold v) is 𝕍 d v;
  case takes the injection in its slot apart, as 𝒞 does.

-}

open import Data.List using (List; []; _∷_)
open import Mu.Language.X86
open import Mu.Framework.AllUtil using (All)

module Mu.proof.Adequacy.X86LogRel {Σ : List DSig} (ds : All (λ s → Body Σ (DSig.cod s) (called s)) Σ) where

open import Framework.Primitives using (Int)
open import Language.Prim using (sub; eq)
open import Mu.Language.Type
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; _↦_; ν; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _•_) renaming (const to dconst)
open import proof.Framework.GraphModel.Ops using (nthD; ⋆) renaming (car to carD)
open import proof.Semantics.Graph.Prim using (primD)
open import Mu.proof.Semantics.Graph.Ops using (Table; tables; init)
open import Mu.Semantics.Graph.CFG using (drop)
open import Mu.Semantics.Graph.X86 using (⟦_⟧ˢ; codeₜ; ⟦_⟧ₜ; 𝒪; 𝒪s; object; called-regs; RegsD)
  renaming (put to putₛ; _[_≔_] to _[_≔ₛ_]; args to argsₛ; blocks to blocksₛ)
open import Mu.Semantics.CEK.X86
open import proof.Semantics.CEK.Smallstep using (Terminates; next)
open import Framework.Lookup using (forget)
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import Mu.Framework.AllUtil using ([]; _∷_; lookup; pos)
open import Mu.proof.Adequacy.X86Common ds
open import Mu.proof.Adequacy.Clos5Values using (module Rel; ℬ-inv; pair-inv; inl-inv; inr-inv; 𝒯-inv)

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.List using (length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

{- Runs to a return ----------------------------------------------------------------}

{- a retq of a body of result B, which returns to any stack -}
record Retq (B : Type) : Set where
  constructor retq-at
  field
    {n} : ℕ
    {Bs} : List Ctx
    {Γ} : Regs
    {Δ} : Ctx
    {O} : Maybe (Open Δ)
    {F} : Bool
    bs : Blocks Σ n B Bs
    η : Ctx
    m : Mach Σ η (st Γ Δ O F)
    e : Γ ‹ rax › ≡ just (ty B)

  at : Stack Σ B → State Σ
  at σ = run (retq e) bs σ η m

  val : Val Σ B
  val = cast e (regs m ⦅ rax ⦆)

open Retq using (at; val)

{- from Q σ, the machine returns v to σ, for every stack σ -}
Ret : ∀ {B} → (Stack Σ B → State Σ) → Val Σ B → Set
Ret Q v = Σ[ R ∈ Retq _ ] (∀ σ → Q σ ↠ at R σ) × val R ≡ v

private
  AVal : Set
  AVal = Σ[ A ∈ Type ] Val Σ A

  ret-val : State Σ → Maybe AVal
  ret-val (run (retq e) bs σ η m) = just ⟨ _ , cast e (regs m ⦅ rax ⦆) ⟩
  ret-val _ = nothing

  just-inj : ∀ {B} {a b : Val Σ B} → _≡_ {A = Maybe AVal} (just ⟨ B , a ⟩) (just ⟨ B , b ⟩) → a ≡ b
  just-inj refl = refl

Ret-det : ∀ {B S} {v₁ v₂ : Val Σ B} → Ret S v₁ → Ret S v₂ → v₁ ≡ v₂
Ret-det {B} ⟨ R₁ , ⟨ τ₁ , refl ⟩ ⟩ ⟨ R₂ , ⟨ τ₂ , refl ⟩ ⟩ = just-inj (cong ret-val (↠-final-det (τ₁ halt) (τ₂ halt) refl refl))

Ret-step : ∀ {B} {S S' : Stack Σ B → State Σ} {v} → (∀ σ → step ds (S σ) ≡ next (S' σ)) → Ret S' v → Ret S v
Ret-step stp ⟨ R , ⟨ τ , e ⟩ ⟩ = ⟨ R , ⟨ (λ σ → stp σ ∷↠ τ σ) , e ⟩ ⟩

{- The logical relation (Clos5Values.agda): code f runs definition f ------------------}

Run : ∀ {Δ A B} → Σ ∋ sig Δ A B → Val Σ (tup Δ) → Val Σ A → (Val Σ B → Set) → Set
Run f e a P = Σ[ v ∈ Val Σ _ ] Ret (start (code f) e a) v × P v

open Rel Run public

{- for the contents of registers -}
𝕍ᵐ : ∀ {η} m → Value → MV Σ η m → Set
𝕍ᵐ (just (ty A)) d v = 𝕍 d v
𝕍ᵐ (just (codeα A B)) d v = 𝕍 d v
𝕍ᵐ (just tupα) d v = 𝕍 d v
𝕍ᵐ nothing d v = ⊤

cast-𝕍 : ∀ {η m τ d} {v : MV Σ η m} (e : m ≡ just τ) → 𝕍ᵐ m d v → 𝕍ᵐ (just τ) d (cast e v)
cast-𝕍 refl r = r

ℝ : ∀ {η Γ} → RegsD → RegVals Σ η Γ → Set
ℝ {Γ = Γ} R ρ = ∀ r d → d ∈ R r → 𝕍ᵐ (Γ ‹ r ›) d (ρ ⦅ r ⦆)

ℝ-upd : ∀ r {η Γ τ} {R : RegsD} {ρ : RegVals Σ η Γ} {D} {v : MV Σ η τ} → ℝ R ρ → (∀ d → d ∈ D → 𝕍ᵐ τ d v)
  → ℝ (R [ r ≔ₛ D ]) (_[_≔_] {τ = τ} ρ r v)
ℝ-upd rax G h = λ { rax → h ; rdi → G rdi ; rsi → G rsi }
ℝ-upd rdi G h = λ { rax → G rax ; rdi → h ; rsi → G rsi }
ℝ-upd rsi G h = λ { rax → G rax ; rdi → G rdi ; rsi → h }

forget-𝕍 : ∀ {η η' d} m {v : MV Σ η m} → 𝕍ᵐ m d v → 𝕍ᵐ {η'} (forgetα m) d (forgetᵥ m v)
forget-𝕍 (just (ty A)) r = r
forget-𝕍 (just (codeα A B)) r = tt
forget-𝕍 (just tupα) r = tt
forget-𝕍 nothing r = tt

ℝ-wipe : ∀ {η η' Γ R} {ρ : RegVals Σ η Γ} → ℝ R ρ → ℝ R (wipeᵣ {η' = η'} ρ)
ℝ-wipe {Γ = rt a b c} G = λ { rax d d∈ → forget-𝕍 a (G rax d d∈) ; rdi d d∈ → forget-𝕍 b (G rdi d d∈) ; rsi d d∈ → forget-𝕍 c (G rsi d d∈) }

FlR : ∀ {f} → 𝒫 Value → Flag Σ f → Set
FlR {true} F b = ∀ d → d ∈ F → 𝕍 d (bit {Σ} b)
FlR {false} F _ = ⊤

{- the frame, registers, flag and open closure of the semantics and the machine -}
record 𝕄 {η ψ} (ρ : _) (R : RegsD) (F : 𝒫 Value) (m : Mach Σ η ψ) : Set where
  constructor 𝕞
  field
    fr : 𝔾 ρ (frame m)
    rg : ℝ R (regs m)
    fl : FlR F (flag m)
    op : OpR (frame m) (St.op ψ) η (envα m)

𝔾-drop : ∀ {Δ' Δ} (p : Δ' ⊑ Δ) {ρ} {φ : Frame Σ Δ} → 𝔾 ρ φ → 𝔾 (drop p ρ) (forget p φ)
𝔾-drop here⊑ G = G
𝔾-drop (there⊑ p) {φ = v ∷ φ} G = 𝔾-drop p (λ x → G (S x))

{- the environment of the open closure is related to the second component of its slot -}
snd-𝕍 : ∀ {Δ A B} {φ : Frame Σ Δ} {x : Δ ∋ A ⇒ B} {η o d d'} → OpR φ (just (opened x)) η o
  → 𝕍 ⦅ d' , d ⦆ (lookup φ x) → 𝕍 d o
snd-𝕍 {φ = φ} {x} agree = snd (lookup φ x)
  where snd : ∀ (v : Val Σ _) {d d'} → 𝕍 ⦅ d' , d ⦆ v → 𝕍 d (env-of v)
        snd (pack c e) r = proj₂ r

{- Values -----------------------------------------------------------------------}

int-𝕍 : ∀ {n} (v : Val Σ (base Int)) → 𝕍 (dconst n) v → int v ≡ n
int-𝕍 (const k) refl = refl

prim-𝕍 : ∀ p {D E} (u v : Val Σ (base Int)) → (∀ d → d ∈ D → 𝕍 d u) → (∀ d → d ∈ E → 𝕍 d v)
  → ∀ d → d ∈ primD p ⟨ D , ⟨ E , ptt ⟩ ⟩ → 𝕍 d (δᵀ p (int u) (int v))
prim-𝕍 p u v hD hE d ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩
  rewrite int-𝕍 u (hD _ n∈) | int-𝕍 v (hE _ m∈) = 𝕍-δ p n m

unfold-𝕍 : ∀ {A c d} (v : Val Σ (μ A {c})) → 𝕍 d v → 𝕍 d (unfoldᵥ v)
unfold-𝕍 (fold v) r = r

elems-𝕍 : ∀ {Δ A d} (i : Δ ∋ A) (v : Val Σ (tup Δ)) → 𝕍 (tup[ pos i ] d) v → 𝕍 d (lookup (elems v) i)
elems-𝕍 i (tup ws) r = 𝕍At-lookup i _ ws r

{- The fundamental lemma, for a table related to the code pointers ----------------}

module _ {T : Table Σ} (𝕋T : 𝕋 T) where

  arg-𝕍 : ∀ {η ψ τ ρ R F} {m : Mach Σ η ψ} (a : Arg Σ ψ τ) → 𝕄 ρ R F m → ∀ d → d ∈ 𝒪 T a ρ R → 𝕍ᵐ (just τ) d (arg a m)
  arg-𝕍 (atom (var x)) M = 𝕄.fr M x
  arg-𝕍 (atom (lit B c)) M d d∈ with ℬ-inv d d∈
  ... | refl = refl
  arg-𝕍 (atom (ref f)) M = 𝕋T f
  arg-𝕍 (reg r e) M d d∈ = cast-𝕍 e (𝕄.rg M r d d∈)
  arg-𝕍 (a ↑) M = arg-𝕍 a M
  arg-𝕍 {m = m} (a ↓) M d d∈ = unfold-𝕍 (arg a m) (arg-𝕍 a M d d∈)

  obj-𝕍 : ∀ {η ψ A ρ R F} {m : Mach Σ η ψ} (o : Obj Σ ψ A) → 𝕄 ρ R F m → ∀ d → d ∈ object T o ρ R → 𝕍 d (obj o m)
  obj-𝕍 (pair c e) M d d∈ with pair-inv d d∈
  ... | ⟨ u , ⟨ u' , ⟨ refl , ⟨ u∈ , u'∈ ⟩ ⟩ ⟩ ⟩ = ⟨ arg-𝕍 c M u u∈ , arg-𝕍 e M u' u'∈ ⟩
  obj-𝕍 (tuple []) M d d∈ with 𝒯-inv 0 d d∈
  ... | inj₁ ⟨ refl , refl ⟩ = tt
  ... | inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ () , _ ⟩ ⟩ ⟩ ⟩
  obj-𝕍 {ρ = ρ} {R} {m = m} (tuple (a ∷ as)) M d d∈ with 𝒯-inv _ d d∈
  ... | inj₁ ⟨ () , _ ⟩
  ... | inj₂ ⟨ _ , ⟨ i , ⟨ u , ⟨ refl , ⟨ refl , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = comp (a ∷ as) i u u∈
    where
    comp : ∀ {Δ} (as : All (λ A → Arg Σ _ (ty A)) Δ) (i : Fin (length Δ)) u → u ∈ nthD (𝒪s T as ρ R) i
      → 𝕍At i u (args as m)
    comp (a ∷ as) zero u u∈ = ⟨ refl , arg-𝕍 a M u u∈ ⟩
    comp (a ∷ as) (suc i) u u∈ = comp as i u u∈
  obj-𝕍 (inl a) M d d∈ with inl-inv d d∈
  ... | ⟨ u , ⟨ refl , u∈ ⟩ ⟩ = arg-𝕍 a M u u∈
  obj-𝕍 (inr a) M d d∈ with inr-inv d d∈
  ... | ⟨ u , ⟨ refl , u∈ ⟩ ⟩ = arg-𝕍 a M u u∈

  {- d := D, in the semantics and the machine -}
  put-𝕄 : ∀ {n ψ τ ψ'} (d : Dst n ψ τ ψ') {η} {m : Mach Σ η ψ} {v : RV Σ η τ} {D κ ρ R F w} → 𝕄 ρ R F m
    → (∀ x → x ∈ D → 𝕍ᵐ (just τ) x v) → w ∈ putₛ T d D κ ρ R F
    → Σ[ ρ' ∈ _ ] Σ[ R' ∈ RegsD ] Σ[ F' ∈ 𝒫 Value ] 𝕄 ρ' R' F' (put d v m) × w ∈ κ ρ' R' F'
  put-𝕄 (reg r) (𝕞 G Rg Fl Op) h w∈ = ⟨ _ , ⟨ _ , ⟨ _ , ⟨ 𝕞 G (ℝ-upd r Rg h) Fl Op , w∈ ⟩ ⟩ ⟩ ⟩
  put-𝕄 (slot p _) {v = v} (𝕞 G Rg Fl Op) h ⟨ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩ =
    ⟨ _ , ⟨ _ , ⟨ _ , ⟨ 𝕞 G' Rg Fl none , w∈ ⟩ ⟩ ⟩ ⟩
    where
    G' : 𝔾 (mem V • drop p _) (v ∷ forget p _)
    G' Z d d∈ = h d (V⊆ d d∈)
    G' (S x) = 𝔾-drop p G x

  {- callq: an element of the result is related to what the code returns -}
  call-𝕍 : ∀ {η Γ Δ O F A B ρ R F'} {m : Mach Σ η (st Γ Δ O F)} (a : Arg Σ (st Γ Δ O F) (codeα A B))
    (e₁ : Γ ‹ rdi › ≡ just tupα) (e₂ : Γ ‹ rsi › ≡ just (ty A)) → 𝕄 ρ R F' m
    → ∀ w → w ∈ ⋆ ⟨ ⋆ ⟨ 𝒪 T a ρ R , ⟨ R rdi , ptt ⟩ ⟩ , ⟨ R rsi , ptt ⟩ ⟩
    → Σ[ v ∈ Val Σ B ] Ret (start (arg a m) (cast e₁ (regs m ⦅ rdi ⦆)) (cast e₂ (regs m ⦅ rsi ⦆))) v × 𝕍 w v
  call-𝕍 {m = m} a e₁ e₂ M w ⟨ Y , ⟨ ⟨ X , ⟨ f∈ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ =
    call (arg a m) (arg-𝕍 a M _ f∈) (all→𝕍s X λ d d∈ → cast-𝕍 e₁ (𝕄.rg M rdi d (X⊆ d d∈)))
      (all→𝕍s Y λ d d∈ → cast-𝕍 e₂ (𝕄.rg M rsi d (Y⊆ d d∈)))
    where
    call : ∀ {η A B} (c : Val Σ (code η A B)) {e a X Y w} → 𝕍 (X ↦ (Y ↦ w)) c → 𝕍s X e → 𝕍s Y a
      → Σ[ v ∈ Val Σ B ] Ret (start c e a) v × 𝕍 w v
    call (code f) {e} {a} r Xe Ya = r e Xe a Ya

  {- the blocks bs are adequate -}
  AdeqB : ∀ {n R Bs} → Blocks Σ n R Bs → Set₁
  AdeqB {R = R} {Bs} bs = ∀ {Δ} (l : Bs ∋ Δ) {η ρ} {φ : Frame Σ Δ} {w} → 𝔾 ρ φ → w ∈ blocksₛ T bs l ρ
    → Σ[ v ∈ Val Σ R ] Ret (λ σ → go ds (block bs l) σ η φ) v × 𝕍 w v

  adequate : ∀ {n R Bs ψ} (k : Seq Σ n R Bs ψ) {bs : Blocks Σ n R Bs} → AdeqB bs → ∀ {η} {m : Mach Σ η ψ} {ρ R' F w}
    → 𝕄 ρ R' F m → w ∈ ⟦_⟧ˢ T k (blocksₛ T bs) ρ R' F → Σ[ v ∈ Val Σ R ] Ret (λ σ → run k bs σ η m) v × 𝕍 w v

  ⇐ : ∀ {B} {S S' : Stack Σ B → State Σ} {w} → (∀ σ → step ds (S σ) ≡ next (S' σ)) → Σ[ v ∈ Val Σ B ] Ret S' v × 𝕍 w v
    → Σ[ v ∈ Val Σ B ] Ret S v × 𝕍 w v
  ⇐ stp ⟨ v , ⟨ r , r𝕍 ⟩ ⟩ = ⟨ v , ⟨ Ret-step stp r , r𝕍 ⟩ ⟩

  {- a write of a value related to D, then k -}
  put-adeq : ∀ {n R Bs ψ τ ψ'} (d : Dst n ψ τ ψ') (k : Seq Σ n R Bs ψ') {bs : Blocks Σ n R Bs} → AdeqB bs → ∀ {η} {m : Mach Σ η ψ}
    {v : RV Σ η τ} {D ρ R' F w} → 𝕄 ρ R' F m → (∀ x → x ∈ D → 𝕍ᵐ (just τ) x v)
    → w ∈ putₛ T d D (⟦_⟧ˢ T k (blocksₛ T bs)) ρ R' F → Σ[ v' ∈ Val Σ R ] Ret (λ σ → run k bs σ η (put d v m)) v' × 𝕍 w v'
  put-adeq d k AB M h w∈ with put-𝕄 d M h w∈
  ... | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ M' , w∈' ⟩ ⟩ ⟩ ⟩ = adequate k AB M' w∈'

  adequate (movq a d ∷ k) AB M w∈ = ⇐ (λ _ → refl) (put-adeq d k AB M (arg-𝕍 a M) w∈)
  adequate (subq a r e ∷ k) AB {m = m} M w∈ =
    ⇐ (λ _ → refl) (put-adeq (reg r) k AB M (prim-𝕍 sub (cast e (regs m ⦅ r ⦆)) (arg a m) (λ d d∈ → cast-𝕍 e (𝕄.rg M r d d∈)) (arg-𝕍 a M)) w∈)
  adequate (cmpq a₂ a₁ ∷ k) AB {m = m} M w∈ =
    ⇐ (λ _ → refl) (adequate k AB (𝕞 (𝕄.fr M) (𝕄.rg M) (prim-𝕍 eq (arg a₁ m) (arg a₂ m) (arg-𝕍 a₁ M) (arg-𝕍 a₂ M)) (𝕄.op M)) w∈)
  adequate (sete d ∷ k) AB M w∈ = ⇐ (λ _ → refl) (put-adeq d k AB M (𝕄.fl M) w∈)
  adequate (alloc o d ∷ k) AB M w∈ = ⇐ (λ _ → refl) (put-adeq d k AB M (obj-𝕍 o M) w∈)
  adequate (load i a d ∷ k) AB {m = m} M w∈ =
    ⇐ (λ _ → refl) (put-adeq d k AB M (λ x x∈ → elems-𝕍 i (arg a m) (arg-𝕍 a M _ x∈)) w∈)
  adequate (loadfst x r ∷ k) AB {m = m} {ρ = ρ} (𝕞 G Rg Fl Op) w∈ =
    ⇐ (λ _ → refl) (adequate k AB (𝕞 G (ℝ-upd r (ℝ-wipe Rg) car) Fl agree) w∈)
    where
    car : ∀ d → d ∈ carD ⟨ ρ (idx x) , ptt ⟩ → 𝕍 d (code-of (lookup (frame m) x))
    car d ⟨ d' , d∈ ⟩ = fst (lookup (frame m) x) (G x _ d∈)
      where fst : (v : Val Σ _) → 𝕍 ⦅ d , d' ⦆ v → 𝕍 d (code-of v)
            fst (pack c e) r = proj₁ r
  adequate (loadsnd {x = opened x} r ∷ k) AB {m = m} (𝕞 G Rg Fl Op) w∈ =
    ⇐ (λ _ → refl) (adequate k AB (𝕞 G (ℝ-upd r Rg λ { d ⟨ d' , d∈ ⟩ → snd-𝕍 Op (G x _ d∈) }) Fl Op) w∈)
  adequate (callq a e₁ e₂ ∷ k) AB {m = m} M ⟨ ⟨ w₀ , w₀∈ ⟩ , w∈ ⟩ with call-𝕍 a e₁ e₂ M w₀ w₀∈
  ... | ⟨ _ , ⟨ ⟨ Rc , ⟨ τc , refl ⟩ ⟩ , _ ⟩ ⟩
      with adequate k AB {η = Retq.η Rc} {m = ⟨ rv (val Rc) tt tt , frame m , tt , tt ⟩}
             (𝕞 (𝕄.fr M) (λ { rax d d∈ → let ⟨ _ , ⟨ r , rv' ⟩ ⟩ = call-𝕍 a e₁ e₂ M d d∈ in
                                         subst (𝕍 d) (Ret-det r ⟨ Rc , ⟨ τc , refl ⟩ ⟩) rv'
                             ; rdi _ _ → tt ; rsi _ _ → tt }) tt none) w∈
  ... | ⟨ v' , ⟨ ⟨ Rk , ⟨ τk , ek ⟩ ⟩ , rv' ⟩ ⟩ =
    ⟨ v' , ⟨ ⟨ Rk , ⟨ (λ σ → enter-start (arg a m) ∷↠ (τc _ ++↠ (refl ∷↠ τk σ))) , ek ⟩ ⟩ , rv' ⟩ ⟩
  adequate (retq e) AB {η = η} {m = m} M w∈ = ⟨ _ , ⟨ ⟨ retq-at _ η m e , ⟨ (λ σ → done) , refl ⟩ ⟩ , cast-𝕍 e (𝕄.rg M rax _ w∈) ⟩ ⟩
  adequate (jmp l) AB M w∈ = ⇐ (λ _ → refl) (AB l (𝕄.fr M) w∈)
  adequate (case x p _ l₁ l₂) {bs} AB {η} {m = m} M (inj₁ ⟨ u , ⟨ U , ⟨ allL , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) =
    ⇐ (λ _ → refl) (sel (lookup (frame m) x) (λ d d∈ → 𝕄.fr M x _ (allL d d∈)))
    where
    sel : (v : Val Σ _) → (∀ d → d ∈ mem (u ∷ U) → 𝕍 (left d) v) → Σ[ v' ∈ Val Σ _ ]
      Ret (λ σ → choose v (λ u → go ds (block bs l₁) σ η (u ∷ forget p (frame m))) (λ u → go ds (block bs l₂) σ η (u ∷ forget p (frame m)))) v' × 𝕍 _ v'
    sel (inl a) h = AB l₁ (λ { Z → h ; (S y) → 𝔾-drop p (𝕄.fr M) y }) w∈
    sel (inr a) h = ⊥-elim (h u (here refl))
  adequate (case x p _ l₁ l₂) {bs} AB {η} {m = m} M (inj₂ ⟨ u , ⟨ U , ⟨ allR , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) =
    ⇐ (λ _ → refl) (sel (lookup (frame m) x) (λ d d∈ → 𝕄.fr M x _ (allR d d∈)))
    where
    sel : (v : Val Σ _) → (∀ d → d ∈ mem (u ∷ U) → 𝕍 (right d) v) → Σ[ v' ∈ Val Σ _ ]
      Ret (λ σ → choose v (λ u → go ds (block bs l₁) σ η (u ∷ forget p (frame m))) (λ u → go ds (block bs l₂) σ η (u ∷ forget p (frame m)))) v' × 𝕍 _ v'
    sel (inr a) h = AB l₂ (λ { Z → h ; (S y) → 𝔾-drop p (𝕄.fr M) y }) w∈
    sel (inl a) h = ⊥-elim (h u (here refl))

  blocks-adeq : ∀ {n R Bs} (bs : Blocks Σ n R Bs) → AdeqB bs
  blocks-adeq (bs ▷ k) Z G w∈ = adequate k (blocks-adeq bs) (𝕞 G (λ { rax _ _ → tt ; rdi _ _ → tt ; rsi _ _ → tt }) tt none) w∈
  blocks-adeq (bs ▷ k) (S l) = blocks-adeq bs l

{- The table of the program ---------------------------------------------------------}

tab-ds : 𝕋 (tables codeₜ ds)
tab-ds = tab codeₜ ds λ {T} 𝕋T {Δ} {A} {B} f → code-𝕍 _ λ X Y w w∈ e Xe a Ya →
  adequate 𝕋T (Body.start (lookup ds f)) (blocks-adeq 𝕋T (Body.blocks (lookup ds f)))
    (𝕞 (λ ()) (λ { rax _ _ → tt ; rdi d d∈ → 𝕍s-∈ X Xe d∈ ; rsi d d∈ → 𝕍s-∈ Y Ya d∈ }) tt none) w∈

{- Adequacy --------------------------------------------------------------------------}

adequacy : ∀ {A} (b : Body Σ A (entry [])) {w} → w ∈ ⟦ program ds b ⟧ₜ
  → Σ[ v ∈ Val Σ A ] Terminates (sem (program ds b)) (obs v) × 𝕍 w v
adequacy (body n bs k) w∈ with adequate tab-ds k (blocks-adeq tab-ds bs) (𝕞 (λ ()) (λ { rax _ _ → tt ; rdi _ _ → tt ; rsi _ _ → tt }) tt none) w∈
... | ⟨ v , ⟨ ⟨ R , ⟨ τ , refl ⟩ ⟩ , r ⟩ ⟩ = ⟨ val R , ⟨ ⟨ at R halt , ⟨ ↠→star (τ halt) , refl ⟩ ⟩ , r ⟩ ⟩
