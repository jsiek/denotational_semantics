{-

  Adequacy of the graph model of X86ᵀ (Semantics/Graph/Typed/X86.agda)
  for the X86ᵀ machine (Semantics/CEK/Typed/X86.agda): every element of
  the denotation of a program is witnessed by a run of the machine. As
  for untyped X86 (Untyped/proof/Adequacy/X86LogRel.agda), with the
  logical relation 𝕍 of the Clos5ᵀ values (Clos5Values.agda), code f
  being related to Λ X. Λ Y. w when the machine runs definition f on
  values related to X and Y, on any stack, to a return of a value
  related to w (Run, Ret). The fundamental lemma (adequate) is by
  induction on the sequence, given that the blocks it may jump to are
  adequate (AdeqB): the frame, the registers and the flag of the
  semantics are related to those of the machine (𝕄), and so is the code
  and environment of the open closure to its slot. A call returns the
  same value for every element of its denotation, since runs are
  deterministic (Ret-det).

  The machine runs a definition to its return independently of the
  stack it returns to (Retq), so that what runs after a call is related
  for the state the return leaves. Typed code never reads an unset
  register or flag, so these are related to anything.

-}

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Language.Typed.X86

module proof.Adequacy.X86LogRel {Σ : List ℕ} (ds : All (λ m → Body Σ (called m)) Σ) where

open import Framework.Primitives using (Int)
open import Language.Prim using (sub; eq)
open import Language.Typed.Type hiding (_≟_)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; _↦_; ν; ⦅_,_⦆; left; right; ⟨⟩; _•_) renaming (const to dconst)
open import proof.Framework.GraphModel.Ops using (nthD; ⋆) renaming (car to carD)
open import proof.Semantics.Graph.Prim using (primD)
open import proof.Semantics.Graph.Typed.Ops using (Table; tables; fun₄; projectᵍ; init)
open import Semantics.Graph.Typed.CFG using (drop)
open import Semantics.Graph.Typed.X86 using (⟦_⟧ˢ; codeₜ; ⟦_⟧ₜ; 𝒪; 𝒪s; object; isinl; called-regs; RegsD)
  renaming (put to putₛ; field′ to fieldₛ; _[_≔_] to _[_≔ₛ_]; args to argsₛ; blocks to blocksₛ)
open import Semantics.CEK.Typed.X86
open import Semantics.Observation using (Obs)
open import proof.Semantics.CEK.Smallstep using (Terminates; next)
open import Framework.Lookup using (_!_; forget)
open import Framework.Membership using (_⊑_; here⊑; there⊑)
open import proof.Adequacy.X86Common ds
open import proof.Adequacy.Clos5Values using (module Rel; ℬ-inv; pair-inv; inl-inv; inr-inv; 𝒯-inv; proj?-ok)

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_; toList)
open import Data.Vec.Properties using (length-toList)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

{- Runs to a return ----------------------------------------------------------------}

{- a retq, which returns to any stack -}
record Retq : Set where
  constructor retq-at
  field
    {n} : ℕ
    {Bs} : List Ctx
    {Γ} : Regs
    {Δ} : Ctx
    {O} : Maybe (Δ ∋ ⟪ fun ⟫)
    {F} : Bool
    bs : Blocks Σ n Bs
    η : ℕ
    m : Mach Σ η (st Γ Δ O F)
    e : Γ ‹ rax › ≡ just (ty Any)

  at : Stack Σ → State Σ
  at σ = run (retq e) bs σ η m

  val : Val Σ Any
  val = cast e (regs m ⦅ rax ⦆)

open Retq using (at; val)

{- from Q σ, the machine returns v to σ, for every stack σ -}
Ret : (Stack Σ → State Σ) → Val Σ Any → Set
Ret Q v = Σ[ R ∈ Retq ] (∀ σ → Q σ ↠ at R σ) × val R ≡ v

private
  ret-val : State Σ → Maybe (Val Σ Any)
  ret-val (run (retq e) bs σ η m) = just (cast e (regs m ⦅ rax ⦆))
  ret-val _ = nothing

  just-inj : ∀ {A : Set} {a b : A} → just a ≡ just b → a ≡ b
  just-inj refl = refl

Ret-det : ∀ {S v₁ v₂} → Ret S v₁ → Ret S v₂ → v₁ ≡ v₂
Ret-det ⟨ R₁ , ⟨ τ₁ , refl ⟩ ⟩ ⟨ R₂ , ⟨ τ₂ , refl ⟩ ⟩ = just-inj (cong ret-val (↠-final-det (τ₁ halt) (τ₂ halt) refl refl))

Ret-step : ∀ {S S' v} → (∀ σ → step ds (S σ) ≡ next (S' σ)) → Ret S' v → Ret S v
Ret-step stp ⟨ R , ⟨ τ , e ⟩ ⟩ = ⟨ R , ⟨ (λ σ → stp σ ∷↠ τ σ) , e ⟩ ⟩

{- The logical relation (Clos5Values.agda): code f runs definition f ------------------}

Run : ∀ {n} → Σ ∋ n → Val Σ ⟪ tup n ⟫ → Val Σ Any → (Val Σ Any → Set) → Set
Run f e a P = Σ[ v ∈ Val Σ Any ] Ret (start (code f) e a) v × P v

open Rel Run public

{- for the contents of registers -}
𝕍ᵐ : ∀ {η} m → Value → MV Σ η m → Set
𝕍ᵐ (just (ty A)) d v = 𝕍 d v
𝕍ᵐ (just codeα) d v = 𝕍 d v
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
forget-𝕍 (just codeα) r = tt
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
    op : OpR (St.op ψ) (frame m) (opened m)

𝔾-drop : ∀ {Δ' Δ} (p : Δ' ⊑ Δ) {ρ} {φ : Frame Σ Δ} → 𝔾 ρ φ → 𝔾 (drop p ρ) (forget p φ)
𝔾-drop here⊑ G = G
𝔾-drop (there⊑ p) {φ = v ∷ φ} G = 𝔾-drop p (λ x → G (S x))

{- Values -----------------------------------------------------------------------}

int-𝕍 : ∀ {n} (v : Val Σ ⟪ base Int ⟫) → 𝕍 (dconst n) v → int v ≡ n
int-𝕍 (const k) refl = refl

prim-𝕍 : ∀ p {D E} (u v : Val Σ ⟪ base Int ⟫) → (∀ d → d ∈ D → 𝕍 d u) → (∀ d → d ∈ E → 𝕍 d v)
  → ∀ d → d ∈ primD p ⟨ D , ⟨ E , ptt ⟩ ⟩ → 𝕍 d (δᵀ p (int u) (int v))
prim-𝕍 p u v hD hE d ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩
  rewrite int-𝕍 u (hD _ n∈) | int-𝕍 v (hE _ m∈) = 𝕍-δ p n m

isinl-𝕍 : ∀ {D} (v : Val Σ ⟪ sum ⟫) → (∀ d → d ∈ D → 𝕍 d v) → ∀ d → d ∈ isinl D → 𝕍 d (bit (is-inl v))
isinl-𝕍 (inl u) h _ (inj₁ ⟨ _ , ⟨ _ , refl ⟩ ⟩) = tt
isinl-𝕍 (inr u) h _ (inj₂ ⟨ _ , ⟨ _ , refl ⟩ ⟩) = tt
isinl-𝕍 (inl u) h _ (inj₂ ⟨ _ , ⟨ u∈ , refl ⟩ ⟩) = ⊥-elim (h _ u∈)
isinl-𝕍 (inr u) h _ (inj₁ ⟨ _ , ⟨ u∈ , refl ⟩ ⟩) = ⊥-elim (h _ u∈)

{- what chk finds in a slot related to D -}
chk-𝕍 : ∀ t (v : Val Σ Any) {D} → (∀ d → d ∈ D → 𝕍 d v) → nonempty (projectᵍ fun₄ t D)
  → Σ[ u ∈ Val Σ ⟪ flat t ⟫ ] proj? t v ≡ just u × (∀ d → d ∈ projectᵍ fun₄ t D → 𝕍 d u)
chk-𝕍 t (dyn H u) h ⟨ _ , ⟨ ⟨ d₀ , ⟨ d₀∈ , acc ⟩ ⟩ , _ ⟩ ⟩ with tag t d₀ u acc (h d₀ d₀∈)
... | refl = ⟨ u , ⟨ proj?-ok t u , (λ d d∈ → h d (proj₂ d∈)) ⟩ ⟩

{- The fundamental lemma, for a table related to the code pointers ----------------}

module _ {T : Table Σ} (𝕋T : 𝕋 T) where

  arg-𝕍 : ∀ {η ψ τ ρ R F} {m : Mach Σ η ψ} (a : Arg Σ ψ τ) → 𝕄 ρ R F m → ∀ d → d ∈ 𝒪 T a ρ R → 𝕍ᵐ (just τ) d (arg a m)
  arg-𝕍 (atom (var x)) M = 𝕄.fr M x
  arg-𝕍 (atom (lit B c)) M d d∈ with ℬ-inv d d∈
  ... | refl = refl
  arg-𝕍 (atom (ref f)) M = 𝕋T f
  arg-𝕍 (reg r e) M d d∈ = cast-𝕍 e (𝕄.rg M r d d∈)
  arg-𝕍 (a ↑) M = arg-𝕍 a M

  field-𝕍 : ∀ {A B} (f : Field A B) {D} (v : Val Σ A) → (∀ d → d ∈ D → 𝕍 d v) → ∀ d → d ∈ fieldₛ T f D → 𝕍 d (field′ f v)
  field-𝕍 (get i) (tup ws) h d d∈ = 𝕍At-lookup i d ws (h _ d∈)
  field-𝕍 payload (inl u) h d (inj₁ l) = h _ l
  field-𝕍 payload (inr u) h d (inj₂ r) = h _ r
  field-𝕍 payload (inl u) h d (inj₂ r) = ⊥-elim (h _ r)
  field-𝕍 payload (inr u) h d (inj₁ l) = ⊥-elim (h _ l)

  obj-𝕍 : ∀ {η ψ A ρ R F} {m : Mach Σ η ψ} (o : Obj Σ ψ A) → 𝕄 ρ R F m → ∀ d → d ∈ object T o ρ R → 𝕍 d (obj o m)
  obj-𝕍 (pair c e) M d d∈ with pair-inv d d∈
  ... | ⟨ u , ⟨ u' , ⟨ refl , ⟨ u∈ , u'∈ ⟩ ⟩ ⟩ ⟩ = ⟨ arg-𝕍 c M u u∈ , arg-𝕍 e M u' u'∈ ⟩
  obj-𝕍 {ρ = ρ} {R} {m = m} (tuple {m = j} as) M d d∈ with 𝒯-inv j d d∈
  obj-𝕍 (tuple []) M d d∈ | inj₁ ⟨ refl , refl ⟩ = tt
  ... | inj₂ ⟨ _ , ⟨ i , ⟨ u , ⟨ refl , ⟨ refl , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = comp as i u u∈
    where
    comp : ∀ {j} (as : Vec (Arg Σ _ (ty Any)) j) i u → u ∈ nthD (𝒪s T as ρ R) i → 𝕍At i u (toList (args as m))
    comp (a ∷ as) zero u u∈ = ⟨ length-toList (args as m) , arg-𝕍 a M u u∈ ⟩
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
    ⟨ _ , ⟨ _ , ⟨ _ , ⟨ 𝕞 G' Rg Fl tt , w∈ ⟩ ⟩ ⟩ ⟩
    where
    G' : 𝔾 (mem V • drop p _) (v ∷ forget p _)
    G' Z d d∈ = h d (V⊆ d d∈)
    G' (S x) = 𝔾-drop p G x

  {- callq: an element of the result is related to what the code returns -}
  call-𝕍 : ∀ {η Γ Δ O F ρ R F'} {m : Mach Σ η (st Γ Δ O F)} (a : Arg Σ (st Γ Δ O F) codeα)
    (e₁ : Γ ‹ rdi › ≡ just tupα) (e₂ : Γ ‹ rsi › ≡ just (ty Any)) → 𝕄 ρ R F' m
    → ∀ w → w ∈ ⋆ ⟨ ⋆ ⟨ 𝒪 T a ρ R , ⟨ R rdi , ptt ⟩ ⟩ , ⟨ R rsi , ptt ⟩ ⟩
    → Σ[ v ∈ Val Σ Any ] Ret (start (arg a m) (cast e₁ (regs m ⦅ rdi ⦆)) (cast e₂ (regs m ⦅ rsi ⦆))) v × 𝕍 w v
  call-𝕍 {m = m} a e₁ e₂ M w ⟨ Y , ⟨ ⟨ X , ⟨ f∈ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ =
    call (arg a m) (arg-𝕍 a M _ f∈) (all→𝕍s X λ d d∈ → cast-𝕍 e₁ (𝕄.rg M rdi d (X⊆ d d∈)))
      (all→𝕍s Y λ d d∈ → cast-𝕍 e₂ (𝕄.rg M rsi d (Y⊆ d d∈)))
    where
    call : ∀ {η} (c : Val Σ (code η)) {e a X Y w} → 𝕍 (X ↦ (Y ↦ w)) c → 𝕍s X e → 𝕍s Y a
      → Σ[ v ∈ Val Σ Any ] Ret (start c e a) v × 𝕍 w v
    call (code f) {e} {a} r Xe Ya = r e Xe a Ya

  {- the blocks bs are adequate -}
  AdeqB : ∀ {n Bs} → Blocks Σ n Bs → Set₁
  AdeqB {Bs = Bs} bs = ∀ {Δ} (l : Bs ∋ Δ) {η ρ} {φ : Frame Σ Δ} {w} → 𝔾 ρ φ → w ∈ blocksₛ T bs l ρ
    → Σ[ v ∈ Val Σ Any ] Ret (λ σ → go ds (block bs l) σ η φ) v × 𝕍 w v

  adequate : ∀ {n Bs ψ} (k : Seq Σ n Bs ψ) {bs : Blocks Σ n Bs} → AdeqB bs → ∀ {η} {m : Mach Σ η ψ} {ρ R F w}
    → 𝕄 ρ R F m → w ∈ ⟦_⟧ˢ T k (blocksₛ T bs) ρ R F → Σ[ v ∈ Val Σ Any ] Ret (λ σ → run k bs σ η m) v × 𝕍 w v

  ⇐ : ∀ {S S' w} → (∀ σ → step ds (S σ) ≡ next (S' σ)) → Σ[ v ∈ Val Σ Any ] Ret S' v × 𝕍 w v
    → Σ[ v ∈ Val Σ Any ] Ret S v × 𝕍 w v
  ⇐ stp ⟨ v , ⟨ r , r𝕍 ⟩ ⟩ = ⟨ v , ⟨ Ret-step stp r , r𝕍 ⟩ ⟩

  {- a write of a value related to D, then k -}
  put-adeq : ∀ {n Bs ψ τ ψ'} (d : Dst n ψ τ ψ') (k : Seq Σ n Bs ψ') {bs : Blocks Σ n Bs} → AdeqB bs → ∀ {η} {m : Mach Σ η ψ}
    {v : RV Σ η τ} {D ρ R F w} → 𝕄 ρ R F m → (∀ x → x ∈ D → 𝕍ᵐ (just τ) x v)
    → w ∈ putₛ T d D (⟦_⟧ˢ T k (blocksₛ T bs)) ρ R F → Σ[ v' ∈ Val Σ Any ] Ret (λ σ → run k bs σ η (put d v m)) v' × 𝕍 w v'
  put-adeq d k AB M h w∈ with put-𝕄 d M h w∈
  ... | ⟨ _ , ⟨ _ , ⟨ _ , ⟨ M' , w∈' ⟩ ⟩ ⟩ ⟩ = adequate k AB M' w∈'

  adequate (movq a d ∷ k) AB M w∈ = ⇐ (λ _ → refl) (put-adeq d k AB M (arg-𝕍 a M) w∈)
  adequate (subq a r e ∷ k) AB {m = m} M w∈ =
    ⇐ (λ _ → refl) (put-adeq (reg r) k AB M (prim-𝕍 sub (cast e (regs m ⦅ r ⦆)) (arg a m) (λ d d∈ → cast-𝕍 e (𝕄.rg M r d d∈)) (arg-𝕍 a M)) w∈)
  adequate (cmpq a₂ a₁ ∷ k) AB {m = m} M w∈ =
    ⇐ (λ _ → refl) (adequate k AB (𝕞 (𝕄.fr M) (𝕄.rg M) (prim-𝕍 eq (arg a₁ m) (arg a₂ m) (arg-𝕍 a₁ M) (arg-𝕍 a₂ M)) (𝕄.op M)) w∈)
  adequate (sete d ∷ k) AB M w∈ = ⇐ (λ _ → refl) (put-adeq d k AB M (𝕄.fl M) w∈)
  adequate (testinl a ∷ k) AB {m = m} M w∈ =
    ⇐ (λ _ → refl) (adequate k AB (𝕞 (𝕄.fr M) (𝕄.rg M) (isinl-𝕍 (arg a m) (arg-𝕍 a M)) (𝕄.op M)) w∈)
  adequate (alloc o d ∷ k) AB M w∈ = ⇐ (λ _ → refl) (put-adeq d k AB M (obj-𝕍 o M) w∈)
  adequate (load f a d ∷ k) AB {m = m} M w∈ = ⇐ (λ _ → refl) (put-adeq d k AB M (field-𝕍 f (arg a m) (arg-𝕍 a M)) w∈)
  adequate (loadfst x r ∷ k) AB {m = m} {ρ = ρ} (𝕞 G Rg Fl Op) w∈ =
    ⇐ (λ _ → refl) (adequate k AB (𝕞 G (ℝ-upd r (ℝ-wipe Rg) car) Fl (pack-eta (frame m ! x))) w∈)
    where
    car : ∀ d → d ∈ carD ⟨ ρ (idx x) , ptt ⟩ → 𝕍 d (code-of (frame m ! x))
    car d ⟨ d' , d∈ ⟩ = fst (frame m ! x) (G x _ d∈)
      where fst : (v : Val Σ ⟪ fun ⟫) → 𝕍 ⦅ d , d' ⦆ v → 𝕍 d (code-of v)
            fst (pack c e) r = proj₁ r
  adequate (loadsnd {x = x} r ∷ k) AB {m = m} (𝕞 G Rg Fl Op) w∈ =
    ⇐ (λ _ → refl) (adequate k AB (𝕞 G (ℝ-upd r Rg λ { d ⟨ d' , d∈ ⟩ → proj₂ (subst (𝕍 ⦅ d' , d ⦆) (sym Op) (G x _ d∈)) }) Fl Op) w∈)
  adequate (callq a e₁ e₂ ∷ k) AB {m = m} M ⟨ ⟨ w₀ , w₀∈ ⟩ , w∈ ⟩ with call-𝕍 a e₁ e₂ M w₀ w₀∈
  ... | ⟨ _ , ⟨ ⟨ Rc , ⟨ τc , refl ⟩ ⟩ , _ ⟩ ⟩
      with adequate k AB {η = Retq.η Rc} {m = ⟨ rv (val Rc) tt tt , frame m , tt , tt ⟩}
             (𝕞 (𝕄.fr M) (λ { rax d d∈ → let ⟨ _ , ⟨ r , rv' ⟩ ⟩ = call-𝕍 a e₁ e₂ M d d∈ in
                                         subst (𝕍 d) (Ret-det r ⟨ Rc , ⟨ τc , refl ⟩ ⟩) rv'
                             ; rdi _ _ → tt ; rsi _ _ → tt }) tt tt) w∈
  ... | ⟨ v' , ⟨ ⟨ Rk , ⟨ τk , ek ⟩ ⟩ , rv' ⟩ ⟩ =
    ⟨ v' , ⟨ ⟨ Rk , ⟨ (λ σ → enter-start (arg a m) ∷↠ (τc _ ++↠ (refl ∷↠ τk σ))) , ek ⟩ ⟩ , rv' ⟩ ⟩
  adequate (chk t x d ∷ k) AB {m = m} (𝕞 G Rg Fl Op) ⟨ ne , w∈ ⟩ with chk-𝕍 t (frame m ! x) (G x) ne
  ... | ⟨ u , ⟨ e , h ⟩ ⟩ =
    ⇐ (λ σ → cong (λ p → checked ds p d k _ σ _) e) (put-adeq d k AB (𝕞 G (ℝ-upd rax Rg λ _ _ → tt) tt Op) h w∈)
  adequate (retq e) AB {η = η} {m = m} M w∈ = ⟨ _ , ⟨ ⟨ retq-at _ η m e , ⟨ (λ σ → done) , refl ⟩ ⟩ , cast-𝕍 e (𝕄.rg M rax _ w∈) ⟩ ⟩
  adequate (jmp l) AB M w∈ = ⇐ (λ _ → refl) (AB l (𝕄.fr M) w∈)
  adequate (je l₁ l₂) AB {m = ⟨ _ , _ , _ , true ⟩} M (inj₁ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) = ⇐ (λ _ → refl) (AB l₁ (𝕄.fr M) w∈)
  adequate (je l₁ l₂) AB {m = ⟨ _ , _ , _ , false ⟩} M (inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩) = ⇐ (λ _ → refl) (AB l₂ (𝕄.fr M) w∈)
  adequate (je l₁ l₂) AB {m = ⟨ _ , _ , _ , false ⟩} M (inj₁ ⟨ u , ⟨ _ , ⟨ allL , _ ⟩ ⟩ ⟩) = ⊥-elim (𝕄.fl M _ (allL u (here refl)))
  adequate (je l₁ l₂) AB {m = ⟨ _ , _ , _ , true ⟩} M (inj₂ ⟨ u , ⟨ _ , ⟨ allR , _ ⟩ ⟩ ⟩) = ⊥-elim (𝕄.fl M _ (allR u (here refl)))

  blocks-adeq : ∀ {n Bs} (bs : Blocks Σ n Bs) → AdeqB bs
  blocks-adeq (bs ▷ k) Z G w∈ = adequate k (blocks-adeq bs) (𝕞 G (λ { rax _ _ → tt ; rdi _ _ → tt ; rsi _ _ → tt }) tt tt) w∈
  blocks-adeq (bs ▷ k) (S l) = blocks-adeq bs l

{- The table of the program ---------------------------------------------------------}

tab-ds : 𝕋 (tables codeₜ ds)
tab-ds = tab codeₜ ds λ {T} 𝕋T {n} f → code-𝕍 _ λ X Y w w∈ e Xe a Ya →
  adequate 𝕋T (Body.start (ds ! f)) (blocks-adeq 𝕋T (Body.blocks (ds ! f)))
    (𝕞 (λ ()) (λ { rax _ _ → tt ; rdi d d∈ → 𝕍s-∈ X Xe d∈ ; rsi d d∈ → 𝕍s-∈ Y Ya d∈ }) tt tt) w∈

{- Adequacy --------------------------------------------------------------------------}

adequacy : ∀ (b : Body Σ (entry [])) {w} → w ∈ ⟦ program ds b ⟧ₜ
  → Σ[ v ∈ Val Σ Any ] Terminates (sem (program ds b)) (obs v) × 𝕍 w v
adequacy (body n bs k) w∈ with adequate tab-ds k (blocks-adeq tab-ds bs) (𝕞 (λ ()) (λ { rax _ _ → tt ; rdi _ _ → tt ; rsi _ _ → tt }) tt tt) w∈
... | ⟨ v , ⟨ ⟨ R , ⟨ τ , refl ⟩ ⟩ , r ⟩ ⟩ = ⟨ val R , ⟨ ⟨ at R halt , ⟨ ↠→star (τ halt) , refl ⟩ ⟩ , r ⟩ ⟩
