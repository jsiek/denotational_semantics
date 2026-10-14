{-

  For X86ᵀ adequacy (X86Soundness.agda), lemmas about the semantics of
  X86ᵀ in the graph model with errors
  (Semantics/GraphErr/Typed/X86.agda): the meaning of a sequence is
  monotone in the meanings of the blocks it may jump to, and in the
  slots, registers and flag that its type has (Le); it does not read the
  others (mono), so a write that the type forgets (an unset register,
  the code and environment of the last closure opened) need not be
  undone.

-}

module proof.Adequacy.GraphErr.X86Mono where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; _•_)
open import proof.Framework.GraphModel.ErrorMonad using (≫=-mono; binds-mono; ⇂-mono; 𝒞⇂-⊆)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres)
open import proof.Framework.GraphModel.Continuity using (pair-good; 𝒯-good; inl-good; inr-good)
open import proof.Semantics.GraphErr.Typed.Clos2 using (prim-good; project-good)
open import proof.Correctness.GraphErr.SelectCorrect using (drop-idx)
open import Framework.GraphModel.DOpSig using (■)
open import Framework.GraphModel.Ops using (⋆; 𝒞; payloadD; 𝒯) renaming (inl to inlD; inr to inrD; proj to projD)
open import Framework.GraphModel.ErrorMonad using (Λᵐ; isinlD; _⇂_; ValPayload)
open import Framework.GraphModel.Env using (Env)
open import Semantics.GraphErr.Typed.Ops using (init; primᵗ; projectᵠ)
open import Semantics.GraphErr.Typed.Imp using (Table; letᵗ)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Semantics.GraphErr.Typed.CFG using (BEnv; drop)
open import Semantics.GraphErr.Typed.X86
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.X86
open import Framework.Membership using (_⊑_; ⊑-∋)

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; replicate)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []) renaming (_∷_ to _∷ᵛ_)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst₂)

{- the slots, registers and flag that a state of type ψ has, included -}
record Le (ψ : St) (ρ ρ' : Env Value) (R R' : RegsD) (F F' : 𝒫 Value) : Set where
  constructor le
  field
    fr : ∀ {A} (x : St.fr ψ ∋ A) → ρ (idx x) ⊆ ρ' (idx x)
    rg : ∀ r {τ} → St.rs ψ ‹ r › ≡ just τ → R r ⊆ R' r
    fl : St.fl ψ ≡ true → F ⊆ F'
open Le public

{- writes, and the registers and flag after a call, a check or a jump -}
le-reg : ∀ {Γ Δ O F₀ ρ ρ' R R' F F' D D'} r {τ} → Le (st Γ Δ O F₀) ρ ρ' R R' F F' → D ⊆ D'
  → Le (st (Γ [ r ↦ just τ ]) Δ O F₀) ρ ρ' (R [ r ≔ D ]) (R' [ r ≔ D' ]) F F'
le-reg rax (le f g l) D⊆ = le f (λ { rax _ → D⊆ ; rdi → g rdi ; rsi → g rsi }) l
le-reg rdi (le f g l) D⊆ = le f (λ { rax → g rax ; rdi _ → D⊆ ; rsi → g rsi }) l
le-reg rsi (le f g l) D⊆ = le f (λ { rax → g rax ; rdi → g rdi ; rsi _ → D⊆ }) l

le-slot : ∀ {Γ Δ Δ' O F₀ A ρ ρ' R R' F F' X X'} (p : Δ' ⊑ Δ) → Le (st Γ Δ O F₀) ρ ρ' R R' F F' → X ⊆ X'
  → Le (st Γ (A ∷ Δ') nothing F₀) (X • drop p ρ) (X' • drop p ρ') R R' F F'
le-slot {ρ = ρ} {ρ'} p (le f g l) X⊆ =
  le (λ { Z → X⊆ ; (S y) → subst₂ _⊆_ (sym (drop-idx p ρ y)) (sym (drop-idx p ρ' y)) (f (⊑-∋ p y)) }) g l

le-flag : ∀ {Γ Δ O F₀ ρ ρ' R R' F F' G G'} → Le (st Γ Δ O F₀) ρ ρ' R R' F F' → G ⊆ G' → Le (st Γ Δ O true) ρ ρ' R R' G G'
le-flag (le f g l) G⊆ = le f g (λ _ → G⊆)

le-wipe : ∀ {Γ Δ O F₀ ρ ρ' R R' F F'} {x : Δ ∋ ⟪ fun ⟫} → Le (st Γ Δ O F₀) ρ ρ' R R' F F'
  → Le (st (wipe Γ) Δ (just x) F₀) ρ ρ' R R' F F'
le-wipe {Γ} (le f g l) = le f (λ { rax e → g rax (fj (Regs.ax Γ) e) ; rdi e → g rdi (fj (Regs.di Γ) e) ; rsi e → g rsi (fj (Regs.si Γ) e) }) l
  where
  fj : ∀ m {τ} → forgetα m ≡ just τ → m ≡ just τ
  fj (just (ty A)) e = e
  fj (just codeα) ()
  fj (just tupα) ()
  fj nothing ()

le-rax : ∀ {Γ Δ O F₀ ρ ρ' R R' F F'} → Le (st Γ Δ O F₀) ρ ρ' R R' F F'
  → Le (st (Γ [ rax ↦ nothing ]) Δ O false) ρ ρ' (R [ rax ≔ init ]) (R' [ rax ≔ init ]) init init
le-rax (le f g l) = le f (λ { rax () ; rdi → g rdi ; rsi → g rsi }) (λ ())

le-ret : ∀ {Δ ρ ρ' C C'} → (∀ {A} (x : Δ ∋ A) → ρ (idx x) ⊆ ρ' (idx x)) → C ⊆ C'
  → Le (returned Δ) ρ ρ' (called-regs C) (called-regs C') init init
le-ret f C⊆ = le f (λ { rax _ → C⊆ ; rdi () ; rsi () }) (λ ())

le-entry : ∀ {Δ ρ ρ'} → (∀ {A} (x : Δ ∋ A) → ρ (idx x) ⊆ ρ' (idx x)) → Le (entry Δ) ρ ρ' (λ _ → init) (λ _ → init) init init
le-entry f = le f (λ { rax () ; rdi () ; rsi () }) (λ ())

let-mono : ∀ {D D' F F'} → D ⊆ D' → (∀ X → F X ⊆ F' X) → letᵗ D F ⊆ letᵗ D' F'
let-mono {F = F} {F'} D⊆ F⊆ = ≫=-mono {F = λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} {λ X → ⋆ ⟨ Λᵐ ⟨ F' , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} D⊆ λ X⊆ w → λ { ⟨ V , ⟨ ⟨ ⟨ w∈ , r ⟩ , n ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ →
  ⟨ V , ⟨ ⟨ ⟨ F⊆ _ w w∈ , r ⟩ , n ⟩ , ⟨ (λ d d∈ → X⊆ d (V⊆ d d∈)) , ne ⟩ ⟩ ⟩ }

{- Monotonicity -----------------------------------------------------------------------}

module _ {Σ : List ℕ} (T : Table) where

  {- blocks, on frames included on their slots -}
  BLe : ∀ {Bs} → BEnv Bs → BEnv Bs → Set₁
  BLe B B' = ∀ {Δ} (l : _ ∋ Δ) {ρ ρ'} → (∀ {A} (x : Δ ∋ A) → ρ (idx x) ⊆ ρ' (idx x)) → B l ρ ⊆ B' l ρ'

  𝒪-mono : ∀ {ψ τ} (a : Arg Σ ψ τ) {ρ ρ' R R' F F'} → Le ψ ρ ρ' R R' F F' → 𝒪 T a ρ R ⊆ 𝒪 T a ρ' R'
  𝒪-mono (atom (var x)) l = fr l x
  𝒪-mono (atom (lit B c)) l = λ _ z → z
  𝒪-mono (atom (ref f)) l = λ _ z → z
  𝒪-mono (reg r e) l = rg l r e
  𝒪-mono (a ↑) l = 𝒪-mono a l

  𝒪s-mono : ∀ {ψ j} (as : Vec (Arg Σ ψ (ty Any)) j) {ρ ρ' R R' F F'} → Le ψ ρ ρ' R R' F F'
    → results-rel-pres _⊆_ (replicate j ■) (𝒪s T as ρ R) (𝒪s T as ρ' R')
  𝒪s-mono [] l = ptt
  𝒪s-mono (a ∷ᵛ as) l = ⟨ lift (𝒪-mono a l) , 𝒪s-mono as l ⟩

  object-mono : ∀ {ψ A} (o : Obj Σ ψ A) {ρ ρ' R R' F F'} → Le ψ ρ ρ' R R' F F' → object T o ρ R ⊆ object T o ρ' R'
  object-mono (pair c e) l = binds-mono 2 ⟨ lift (𝒪-mono c l) , ⟨ lift (𝒪-mono e l) , ptt ⟩ ⟩ (λ Xs⊆ → lower (mono (pair-good {⊤}) _ _ Xs⊆))
  object-mono (tuple {m = m} as) l = binds-mono m {K = 𝒯 m} {𝒯 m} (𝒪s-mono as l) (λ Xs⊆ → lower (mono (𝒯-good {⊤} _) _ _ Xs⊆))
  object-mono (inl a) l = ≫=-mono {F = λ X → inlD ⟨ X , ptt ⟩} {λ X → inlD ⟨ X , ptt ⟩} (𝒪-mono a l) (λ X⊆ → lower (mono (inl-good {⊤}) _ _ ⟨ lift X⊆ , ptt ⟩))
  object-mono (inr a) l = ≫=-mono {F = λ X → inrD ⟨ X , ptt ⟩} {λ X → inrD ⟨ X , ptt ⟩} (𝒪-mono a l) (λ X⊆ → lower (mono (inr-good {⊤}) _ _ ⟨ lift X⊆ , ptt ⟩))

  field-mono : ∀ {A B} (f : Field A B) {D D'} → D ⊆ D' → field′ {Σ} T f D ⊆ field′ {Σ} T f D'
  field-mono (get i) D⊆ = ≫=-mono {F = λ X → projD i ⟨ X , ptt ⟩} {λ X → projD i ⟨ X , ptt ⟩} D⊆ (λ X⊆ d → X⊆ _)
  field-mono payload D⊆ = ≫=-mono {F = λ X → payloadD (X ⇂ ValPayload)} {λ X → payloadD (X ⇂ ValPayload)} D⊆ (λ X⊆ d → λ { (inj₁ l) → inj₁ (⇂-mono {P = ValPayload} X⊆ _ l) ; (inj₂ r) → inj₂ (⇂-mono {P = ValPayload} X⊆ _ r) })

  put-mono : ∀ {n ψ τ ψ'} (d : Dst n ψ τ ψ') {κ κ' : Kont} → (∀ {ρ ρ' R R' F F'} → Le ψ' ρ ρ' R R' F F' → κ ρ R F ⊆ κ' ρ' R' F')
    → ∀ {ρ ρ' R R' F F' D D'} → Le ψ ρ ρ' R R' F F' → D ⊆ D' → put {Σ} T d D κ ρ R F ⊆ put {Σ} T d D' κ' ρ' R' F'
  put-mono (reg r) k l D⊆ = k (le-reg r l D⊆)
  put-mono (slot p _) k l D⊆ = let-mono D⊆ (λ X → k (le-slot {X = X} {X} p l (λ _ z → z)))

  putˢ-mono : ∀ {n ψ τ ψ'} (d : Dst n ψ τ ψ') {κ κ' : Kont} → (∀ {ρ ρ' R R' F F'} → Le ψ' ρ ρ' R R' F F' → κ ρ R F ⊆ κ' ρ' R' F')
    → ∀ {ρ ρ' R R' F F' D D'} → Le ψ ρ ρ' R R' F F' → D ⊆ D' → putˢ {Σ} T d D κ ρ R F ⊆ putˢ {Σ} T d D' κ' ρ' R' F'
  putˢ-mono (reg r) {κ} {κ'} k {ρ} {ρ'} {R} {R'} {F} {F'} {D} {D'} l D⊆ =
    ≫=-mono {F = λ _ → κ ρ (R [ r ≔ D ]) F} {λ _ → κ' ρ' (R' [ r ≔ D' ]) F'} D⊆ (λ _ → k (le-reg r l D⊆))
  putˢ-mono (slot p lt) = put-mono (slot p lt)

  mono-seq : ∀ {n Bs ψ} (k : Seq Σ n Bs ψ) {B B' : BEnv Bs} → BLe B B' → ∀ {ρ ρ' R R' F F'} → Le ψ ρ ρ' R R' F F'
    → ⟦_⟧ˢ T k B ρ R F ⊆ ⟦_⟧ˢ T k B' ρ' R' F'
  mono-seq (movq a d ∷ k) b l = put-mono d (mono-seq k b) l (𝒪-mono a l)
  mono-seq (subq a r e ∷ k) b l = mono-seq k b (le-reg r l (lower (mono (prim-good _) _ _ ⟨ lift (rg l r e) , ⟨ lift (𝒪-mono a l) , ptt ⟩ ⟩)))
  mono-seq (cmpq a₂ a₁ ∷ k) b l = mono-seq k b (le-flag l (lower (mono (prim-good _) _ _ ⟨ lift (𝒪-mono a₁ l) , ⟨ lift (𝒪-mono a₂ l) , ptt ⟩ ⟩)))
  mono-seq (sete d ∷ k) b l = put-mono d (mono-seq k b) l (fl l refl)
  mono-seq (testinl a ∷ k) b l = mono-seq k b (le-flag l (≫=-mono {F = isinlD} {isinlD} (𝒪-mono a l)
    (λ X⊆ d → λ { (inj₁ ⟨ u , ⟨ u∈ , e ⟩ ⟩) → inj₁ ⟨ u , ⟨ X⊆ _ u∈ , e ⟩ ⟩ ; (inj₂ ⟨ u , ⟨ u∈ , e ⟩ ⟩) → inj₂ ⟨ u , ⟨ X⊆ _ u∈ , e ⟩ ⟩ })))
  mono-seq (alloc o d ∷ k) b l = put-mono d (mono-seq k b) l (object-mono o l)
  mono-seq (load f a d ∷ k) b l = put-mono d (mono-seq k b) l (field-mono f (𝒪-mono a l))
  mono-seq (loadfst x r ∷ k) b l = mono-seq k b (le-reg r (le-wipe l) (λ u → λ { ⟨ u' , p∈ ⟩ → ⟨ u' , fr l x _ p∈ ⟩ }))
  mono-seq (loadsnd {x = x} r ∷ k) b l = mono-seq k b (le-reg r l (λ u → λ { ⟨ u' , p∈ ⟩ → ⟨ u' , fr l x _ p∈ ⟩ }))
  mono-seq (callq a e₁ e₂ ∷ k) {B} {B'} b {ρ} {ρ'} l = ≫=-mono {F = λ _ → ⟦_⟧ˢ T k B ρ (called-regs _) init} {λ _ → ⟦_⟧ˢ T k B' ρ' (called-regs _) init} C⊆ (λ _ → mono-seq k b (le-ret (fr l) C⊆))
    where
    C⊆ = λ w → λ { ⟨ V , ⟨ ⟨ U , ⟨ e∈ , ⟨ U⊆ , U≢ ⟩ ⟩ ⟩ , ⟨ V⊆ , V≢ ⟩ ⟩ ⟩ →
      ⟨ V , ⟨ ⟨ U , ⟨ 𝒪-mono a l _ e∈ , ⟨ (λ d d∈ → rg l rdi e₁ d (U⊆ d d∈)) , U≢ ⟩ ⟩ ⟩ , ⟨ (λ d d∈ → rg l rsi e₂ d (V⊆ d d∈)) , V≢ ⟩ ⟩ ⟩ }
  mono-seq (chk t x d ∷ k) b l = putˢ-mono d (mono-seq k b) (le-rax l) (lower (mono (project-good kind₄ t) _ _ ⟨ lift (fr l x) , ptt ⟩))
  mono-seq (retq e) b l = rg l rax e
  mono-seq (jmp l') b l = b l' (fr l)
  mono-seq (je l₁ l₂) {B} {B'} b {ρ} {ρ'} l = ≫=-mono {F = λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ (λ _ → B l₁ ρ) , ⟨ (λ _ → B l₂ ρ) , ptt ⟩ ⟩ ⟩} {λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ (λ _ → B' l₁ ρ') , ⟨ (λ _ → B' l₂ ρ') , ptt ⟩ ⟩ ⟩} (fl l refl) (λ X⊆ → 𝒞⇂-⊆ {A = λ _ → B l₁ ρ} {λ _ → B' l₁ ρ'} {λ _ → B l₂ ρ} {λ _ → B' l₂ ρ'} X⊆
    (λ _ _ _ _ → b l₁ {ρ} {ρ'} (fr l)) (λ _ _ _ _ → b l₂ {ρ} {ρ'} (fr l)))

  blocks-mono : ∀ {n Bs} (bs : Blocks Σ n Bs) → BLe (blocks T bs) (blocks T bs)
  blocks-mono (bs ▷ k) Z f = mono-seq k (blocks-mono bs) (le-entry f)
  blocks-mono (bs ▷ k) (S l) = blocks-mono bs l
