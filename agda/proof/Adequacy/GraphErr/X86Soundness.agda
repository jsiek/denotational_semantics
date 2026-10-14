{-

  Soundness of the X86ᵀ machine with respect to the graph model with
  errors (Semantics/GraphErr/Typed/X86.agda): what the machine of the
  definitions ds computes is in the denotation of the program, and when
  it stops with an error, ω is, when the code of each definition
  depends only on the older ones and the table is consistent (see
  GraphErr/X86.agda).

  As for untyped X86 (Untyped/proof/Adequacy/GraphErr/X86Soundness.agda),
  each state denotes a set (𝒮) that a step can only shrink (step-⊆):
  the meaning of its sequence on finite parts (Ap) of the meanings 𝒱 v
  of the values v in its slots, registers and flag (those its type has,
  Fits), under its stack (𝒦), whose return frames hold a finite part of
  the result of the callee. A step back keeps the parts of the
  locations the step leaves, and adds parts of its operands (Need) that
  give the parts of its result; the meaning of the rest is monotone in
  them (mono-seq). A value means a set without ω, consistent, as the
  table is, so a slot binds a finite part of it (letᵗ), and code is
  called on finite parts of %rdi and %rsi, whose entries are in the
  table: the code of a definition under the whole table is part of its
  entry (fix-S). Only chk stops with an error, on a value whose meaning
  has an element of another kind than its tag (𝒱-kind).

-}

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ)
open import Language.Typed.X86

module proof.Adequacy.GraphErr.X86Soundness {Σ : List ℕ} (ds : All (λ m → Body Σ (called m)) Σ) where

open import proof.Adequacy.GraphErr.X86Common ds
open import Framework.Primitives using (base-rep; Int)
open import Language.Prim using (Prim; sub; eq; δ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _•_; _~_; _≈_; Con; Every⇒≈; ≈-single) renaming (const to dconst)
open import proof.Framework.GraphModel.ErrorMonad using (≫=-mono; binds-intro; conv-⌊⌋s; ΛΛᵐ-entry; ΛΛᵐ-val; ⌊_⌋s)
open import proof.Semantics.GraphErr.Typed.Clos5 using (tbl-val)
open import Framework.GraphModel.ErrorMonad using (Kind; kind; _≫=_; ⌊_⌋; isinlD; ValPayload; _⇂_; strictᵐ; NoErr; Conv)
open import Framework.GraphModel.DOpSig using (Results; ■)
open import Framework.GraphModel.OpsBase using (ℬ; nthD)
open import Framework.GraphModel.Ops using (𝒯; ⋆; car; cdr; payloadD)
open import Framework.GraphModel.Env using (Env)
open import Semantics.Graph.Prim using () renaming (out to dout)
open import Semantics.GraphErr.Typed.Ops using (init; kindᶠ; hit; projectᵠ; primᵗ)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Semantics.GraphErr.Typed.CFG using (drop; letᵗ)
open import Semantics.GraphErr.Typed.X86 using (RegsD; called-regs; 𝒪; 𝒪s; object; ⟦_⟧ˢ; codeₜ; ⟦_⟧ₜ)
  renaming (_[_≔_] to _[_≔ˢ_]; put to putᴰ; putˢ to putˢᴰ; field′ to fieldᴰ; blocks to blocksᴰ; run to runᴰ; args to argsᴰ)
open import proof.Semantics.GraphErr.Typed.X86 using (Le; le; mono-seq; blocks-mono; le-ret; le-entry; le-reg; putˢ-mono)
open import proof.Correctness.GraphErr.SelectCorrect using (drop-idx)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋)
open import Framework.Lookup using (_!_; forget)
open import Semantics.Observation using (Obs; o-error; o-const)
open import Semantics.CEK.Smallstep using (next; stop)
open import Semantics.CEK.Typed.X86

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc) renaming (_≟_ to _≟ᶠ_)
open import Data.Integer using () renaming (_≟_ to _≟ℤ_)
open import Data.List using (_++_; map)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (suc; zero)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no; does)

module _ (TC : ∀ k → Con (T⁺ k)) (ind : Indep) where

  {- Meanings of values ---------------------------------------------------------------}

  {- d ∈𝒱 v: d is in the meaning of v -}
  infix 4 _∈𝒱_
  data _∈𝒱_ : ∀ {A} → Value → Val Σ A → Set where
    code∈ : ∀ {n} {f : Σ ∋ n} {d} → d ∈ T⁺ (lvl f) → d ∈𝒱 code f
    pack∈ : ∀ {n} {c : Val Σ (code n)} {e u u'} → u ∈𝒱 c → u' ∈𝒱 e → ⦅ u , u' ⦆ ∈𝒱 pack c e
    const∈ : ∀ {B} {k : base-rep B} → dconst k ∈𝒱 const {Σ} k
    unit∈ : ⟨⟩ ∈𝒱 tup {Σ} []
    tup∈ : ∀ {n} {ws : Vec (Val Σ Any) (suc n)} i {e} → e ∈𝒱 lookup ws i → tup[ i ] e ∈𝒱 tup ws
    inl∈ : ∀ {v : Val Σ Any} {u} → u ∈𝒱 v → left u ∈𝒱 inl v
    inr∈ : ∀ {v : Val Σ Any} {u} → u ∈𝒱 v → right u ∈𝒱 inr v
    dyn∈ : ∀ {G} {v : Val Σ ⟪ G ⟫} {d} → d ∈𝒱 v → d ∈𝒱 dyn G v

  {- an element of the meaning of each value -}
  pt : ∀ {A} → Val Σ A → Value
  pt∈ : ∀ {A} (v : Val Σ A) → pt v ∈𝒱 v
  pt (code f) = proj₁ (proj₂ (tbl-val (λ _ → ΛΛᵐ-val) ds (lvl f)))
  pt (pack c e) = ⦅ pt c , pt e ⦆
  pt (const k) = dconst k
  pt (tup []) = ⟨⟩
  pt (tup (w ∷ ws)) = tup[ zero ] (pt w)
  pt (inl v) = left (pt v)
  pt (inr v) = right (pt v)
  pt (dyn G v) = pt v
  pt∈ (code f) = code∈ (proj₂ (proj₂ (tbl-val (λ _ → ΛΛᵐ-val) ds (lvl f))))
  pt∈ (pack c e) = pack∈ (pt∈ c) (pt∈ e)
  pt∈ (const k) = const∈
  pt∈ (tup []) = unit∈
  pt∈ (tup (w ∷ ws)) = tup∈ zero (pt∈ w)
  pt∈ (inl v) = inl∈ (pt∈ v)
  pt∈ (inr v) = inr∈ (pt∈ v)
  pt∈ (dyn G v) = dyn∈ (pt∈ v)

  {- no value means an error -}
  noω : ∀ {A d} {v : Val Σ A} → d ∈𝒱 v → d ≢ ω
  noω (code∈ {f = f} d∈) = proj₁ (tbl-val (λ _ → ΛΛᵐ-val) ds (lvl f)) _ d∈
  noω (dyn∈ d∈) = noω d∈
  noω (pack∈ _ _) ()
  noω const∈ ()
  noω unit∈ ()
  noω (tup∈ _ _) ()
  noω (inl∈ _) ()
  noω (inr∈ _) ()

  {- the elements of a value of flat type H are of its kind -}
  𝒱-kind : ∀ {H d} {v : Val Σ ⟪ H ⟫} → d ∈𝒱 v → kind₄ (kind d) ≡ kindᶠ H
  𝒱-kind (pack∈ _ _) = refl
  𝒱-kind const∈ = refl
  𝒱-kind unit∈ = refl
  𝒱-kind (tup∈ _ _) = refl
  𝒱-kind (inl∈ _) = refl
  𝒱-kind (inr∈ _) = refl

  {- every value means a consistent set, as the table is -}
  𝒱-con : ∀ {A d d'} {v : Val Σ A} → d ∈𝒱 v → d' ∈𝒱 v → d ~ d'
  𝒱-con (code∈ {f = f} a) (code∈ b) = TC (lvl f) _ _ a b
  𝒱-con (pack∈ a b) (pack∈ a' b') = ⟨ 𝒱-con a a' , 𝒱-con b b' ⟩
  𝒱-con const∈ const∈ = ⟨ refl , refl ⟩
  𝒱-con unit∈ unit∈ = tt
  𝒱-con (tup∈ i a) (tup∈ j a') with i ≟ᶠ j
  ... | yes refl = ⟨ refl , inj₂ ⟨ refl , 𝒱-con a a' ⟩ ⟩
  ... | no ne = ⟨ refl , inj₁ ne ⟩
  𝒱-con (inl∈ a) (inl∈ a') = 𝒱-con a a'
  𝒱-con (inr∈ a) (inr∈ a') = 𝒱-con a a'
  𝒱-con (dyn∈ a) (dyn∈ a') = 𝒱-con a a'

  {- a finite part of the meaning of a value, bound to a slot or called on -}
  part : ∀ {A} {v : Val Σ A} V → (∀ d → d ∈ mem V → d ∈𝒱 v) → V ≈ V × NoErr V
  part V h = ⟨ Every⇒≈ V V (λ a b a∈ b∈ → 𝒱-con (h a a∈) (h b b∈)) , (λ ω∈ → noω (h ω ω∈) refl) ⟩

  {- Parts of the locations of a state -------------------------------------------------}

  record Ap : Set where
    constructor ap
    field
      sl : ℕ → List Value
      rg : Reg → List Value
      fl : List Value
  open Ap

  ρ̂ : Ap → Env Value
  ρ̂ A i = mem (sl A i)

  R̂ : Ap → RegsD
  R̂ A r = mem (rg A r)

  infixl 6 _∪ₐ_
  _∪ₐ_ : Ap → Ap → Ap
  A ∪ₐ B = ap (λ i → sl A i ++ sl B i) (λ r → rg A r ++ rg B r) (fl A ++ fl B)

  ∅ₐ : Ap
  ∅ₐ = ap (λ _ → []) (λ _ → []) []

  infix 4 _⊑ₐ_
  _⊑ₐ_ : Ap → Ap → Set
  A ⊑ₐ B = (∀ i → ρ̂ A i ⊆ ρ̂ B i) × (∀ r → R̂ A r ⊆ R̂ B r) × (mem (fl A) ⊆ mem (fl B))

  ⊑-refl : ∀ {A} → A ⊑ₐ A
  ⊑-refl = ⟨ (λ _ _ z → z) , ⟨ (λ _ _ z → z) , (λ _ z → z) ⟩ ⟩

  ∪ˡ : ∀ {A B C} → A ∪ₐ B ⊑ₐ C → A ⊑ₐ C
  ∪ˡ ⟨ s , ⟨ r , f ⟩ ⟩ = ⟨ (λ i d d∈ → s i d (∈-++⁺ˡ d∈)) , ⟨ (λ x d d∈ → r x d (∈-++⁺ˡ d∈)) , (λ d d∈ → f d (∈-++⁺ˡ d∈)) ⟩ ⟩

  ∪ʳ : ∀ {A B C} → A ∪ₐ B ⊑ₐ C → B ⊑ₐ C
  ∪ʳ {A} ⟨ s , ⟨ r , f ⟩ ⟩ =
    ⟨ (λ i d d∈ → s i d (∈-++⁺ʳ (sl A i) d∈)) , ⟨ (λ x d d∈ → r x d (∈-++⁺ʳ (rg A x) d∈)) , (λ d d∈ → f d (∈-++⁺ʳ (fl A) d∈)) ⟩ ⟩

  ++ˡ : ∀ {xs ys : List Value} → mem xs ⊆ mem (xs ++ ys)
  ++ˡ _ = ∈-++⁺ˡ

  open Locs _∈𝒱_ using (PS; PR; PM; PF)

  {- the parts of the locations that the type of m has are parts of their values -}
  record Fits {η ψ} (m : Mach Σ η ψ) (A : Ap) : Set where
    constructor fits
    field
      ffr : ∀ {B} (x : St.fr ψ ∋ B) → PS (ρ̂ A (idx x)) (frame m ! x)
      frg : ∀ r → PM (St.rs ψ ‹ r ›) (R̂ A r) (regs m ⦅ r ⦆)
      ffl : PF (St.fl ψ) (mem (fl A)) (flag m)
  open Fits

  ++S : ∀ {A} {v : Val Σ A} xs ys → PS (mem xs) v → PS (mem ys) v → PS (mem (xs ++ ys)) v
  ++S xs ys h h' d d∈ = [ h d , h' d ]′ (∈-++⁻ xs d∈)

  ∪-fits : ∀ {η ψ} {m : Mach Σ η ψ} {A B} → Fits m A → Fits m B → Fits m (A ∪ₐ B)
  ∪-fits {A = A} {B} (fits f g l) (fits f' g' l') =
    fits (λ x → ++S (sl A _) (sl B _) (f x) (f' x)) (λ r → M _ (g r) (g' r)) (F _ l l')
    where
    M : ∀ {η} mt {r} {v : MV Σ η mt} → PM mt (R̂ A r) v → PM mt (R̂ B r) v → PM mt (R̂ (A ∪ₐ B) r) v
    M (just τ) {r} = ++S (rg A r) (rg B r)
    M nothing _ _ = tt
    F : ∀ b {f} → PF b (mem (fl A)) f → PF b (mem (fl B)) f → PF b (mem (fl (A ∪ₐ B))) f
    F true = ++S (fl A) (fl B)
    F false _ _ = tt

  PM-[] : ∀ {η} mt {v : MV Σ η mt} → PM mt (mem []) v
  PM-[] (just τ) _ ()
  PM-[] nothing = tt

  PF-[] : ∀ b {f} → PF b (mem []) f
  PF-[] true _ ()
  PF-[] false = tt

  fits∅ : ∀ {η ψ} {m : Mach Σ η ψ} → Fits m ∅ₐ
  fits∅ = fits (λ _ _ ()) (λ r → PM-[] _) (PF-[] _)

  single : ∀ {A w} {v : Val Σ A} → w ∈𝒱 v → PS (mem (w ∷ [])) v
  single w∈ _ (here refl) = w∈

  {- Parts of operands -------------------------------------------------------------------}

  {- parts of the operands of m that give each part w of v through Src -}
  Need : ∀ {η ψ A} → Mach Σ η ψ → Val Σ A → (Ap → 𝒫 Value) → Set
  Need m v Src = ∀ w → w ∈𝒱 v → Σ[ N ∈ Ap ] Fits m N × (∀ A → N ⊑ₐ A → w ∈ Src A)

  needs : ∀ {η ψ A} {m : Mach Σ η ψ} {v : Val Σ A} {Src} → Need m v Src → ∀ W → PS (mem W) v
    → Σ[ N ∈ Ap ] Fits m N × (∀ A → N ⊑ₐ A → mem W ⊆ Src A)
  needs h [] _ = ⟨ ∅ₐ , ⟨ fits∅ , (λ _ _ _ ()) ⟩ ⟩
  needs h (w ∷ W) W⊆ with h w (W⊆ w (here refl)) | needs h W (λ d d∈ → W⊆ d (there d∈))
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ | ⟨ N' , ⟨ f' , g' ⟩ ⟩ =
    ⟨ N ∪ₐ N' , ⟨ ∪-fits f f' , (λ A N⊑ → λ { _ (here refl) → g A (∪ˡ N⊑) ; d (there d∈) → g' A (∪ʳ N⊑) d d∈ }) ⟩ ⟩

  slotAt : ∀ {Δ : Ctx} {B} → Δ ∋ B → List Value → ℕ → List Value
  slotAt Z W zero = W
  slotAt Z W (suc i) = []
  slotAt (S x) W zero = []
  slotAt (S x) W (suc i) = slotAt x W i

  {- parts of slot x -}
  slot-need : ∀ {η ψ B} {m : Mach Σ η ψ} (x : St.fr ψ ∋ B) W → PS (mem W) (frame m ! x)
    → Σ[ N ∈ Ap ] Fits m N × (∀ A → N ⊑ₐ A → mem W ⊆ ρ̂ A (idx x))
  slot-need {m = m} x W h = ⟨ ap (slotAt x W) (λ _ → []) [] , ⟨ fits (at x (frame m) h) (λ r → PM-[] _) (PF-[] _)
    , (λ A N⊑ d d∈ → proj₁ N⊑ (idx x) d (subst (λ L → d ∈ mem L) (sym (here' x)) d∈)) ⟩ ⟩
    where
    at : ∀ {Δ : Ctx} {B} (x : Δ ∋ B) (φ : Frame Σ Δ) → PS (mem W) (φ ! x) → ∀ {C} (y : Δ ∋ C) → PS (mem (slotAt x W (idx y))) (φ ! y)
    at Z φ h Z = h
    at Z φ h (S y) _ ()
    at (S x) φ h Z _ ()
    at (S x) (_ ∷ φ) h (S y) = at x φ h y
    here' : ∀ {Δ : Ctx} {B} (x : Δ ∋ B) → slotAt x W (idx x) ≡ W
    here' Z = refl
    here' (S x) = here' x

  {- parts of register r -}
  reg-need : ∀ {η ψ} {m : Mach Σ η ψ} r W → PM (St.rs ψ ‹ r ›) (mem W) (regs m ⦅ r ⦆)
    → Σ[ N ∈ Ap ] Fits m N × (∀ A → N ⊑ₐ A → mem W ⊆ R̂ A r)
  reg-need rax W h = ⟨ ap (λ _ → []) (λ { rax → W ; _ → [] }) [] , ⟨ fits (λ _ _ ()) (λ { rax → h ; rdi → PM-[] _ ; rsi → PM-[] _ }) (PF-[] _)
    , (λ A N⊑ → proj₁ (proj₂ N⊑) rax) ⟩ ⟩
  reg-need rdi W h = ⟨ ap (λ _ → []) (λ { rdi → W ; _ → [] }) [] , ⟨ fits (λ _ _ ()) (λ { rax → PM-[] _ ; rdi → h ; rsi → PM-[] _ }) (PF-[] _)
    , (λ A N⊑ → proj₁ (proj₂ N⊑) rdi) ⟩ ⟩
  reg-need rsi W h = ⟨ ap (λ _ → []) (λ { rsi → W ; _ → [] }) [] , ⟨ fits (λ _ _ ()) (λ { rax → PM-[] _ ; rdi → PM-[] _ ; rsi → h }) (PF-[] _)
    , (λ A N⊑ → proj₁ (proj₂ N⊑) rsi) ⟩ ⟩

  uncast : ∀ {η mt τ} (e : mt ≡ just τ) {D} {v : MV Σ η mt} → PR τ D (cast e v) → PM mt D v
  uncast refl h = h

  one : ∀ {η ψ w} {m : Mach Σ η ψ} {Src : Ap → 𝒫 Value} → Σ[ N ∈ Ap ] Fits m N × (∀ A → N ⊑ₐ A → mem (w ∷ []) ⊆ Src A)
    → Σ[ N ∈ Ap ] Fits m N × (∀ A → N ⊑ₐ A → w ∈ Src A)
  one ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → g A N⊑ _ (here refl)) ⟩ ⟩

  𝒪-need : ∀ {η ψ τ} (a : Arg Σ ψ τ) {m : Mach Σ η ψ} → Need m (toV τ (arg a m)) (λ A → 𝒪 T⁺ a (ρ̂ A) (R̂ A))
  𝒪-need (atom (var x)) w w∈ = one (slot-need x (w ∷ []) (single w∈))
  𝒪-need (atom (lit B c)) w const∈ = ⟨ ∅ₐ , ⟨ fits∅ , (λ _ _ → ⟨ refl , refl ⟩) ⟩ ⟩
  𝒪-need (atom (ref f)) w (code∈ w∈) = ⟨ ∅ₐ , ⟨ fits∅ , (λ _ _ → w∈) ⟩ ⟩
  𝒪-need (reg r e) w w∈ = one (reg-need r (w ∷ []) (uncast e (single w∈)))
  𝒪-need (a ↑) w (dyn∈ w∈) = 𝒪-need a w w∈

  {- the parts of a pair of parts, from those of its operands -}
  pair∈ : ∀ {A B} {u u' : Value} {v : Val Σ A} {v' : Val Σ B} {S S' : Ap → 𝒫 Value} {η ψ} {m : Mach Σ η ψ}
    → u ∈𝒱 v → u' ∈𝒱 v' → Need m v S → Need m v' S'
    → Σ[ N ∈ Ap ] Fits m N × (∀ A → N ⊑ₐ A → u ∈ ⌊ S A ⌋ × u' ∈ ⌊ S' A ⌋)
  pair∈ u∈ u'∈ h h' with h _ u∈ | h' _ u'∈
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ | ⟨ N' , ⟨ f' , g' ⟩ ⟩ =
    ⟨ N ∪ₐ N' , ⟨ ∪-fits f f' , (λ A N⊑ → ⟨ ⟨ g A (∪ˡ N⊑) , noω u∈ ⟩ , ⟨ g' A (∪ʳ N⊑) , noω u'∈ ⟩ ⟩) ⟩ ⟩

  obj-need : ∀ {η ψ A} (o : Obj Σ ψ A) {m : Mach Σ η ψ} → Need m (obj o m) (λ A → object T⁺ o (ρ̂ A) (R̂ A))
  obj-need (pair c e) w (pack∈ u∈ u'∈) with pair∈ u∈ u'∈ (𝒪-need c) (𝒪-need e)
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → let ⟨ a , b ⟩ = g A N⊑ in inj₂ ⟨ ⟨ _ , a ⟩ , inj₂ ⟨ ⟨ _ , b ⟩ , ⟨ a , b ⟩ ⟩ ⟩) ⟩ ⟩
  obj-need (tuple []) w unit∈ = ⟨ ∅ₐ , ⟨ fits∅ , (λ _ _ → tt) ⟩ ⟩
  obj-need {ψ = ψ} (tuple as@(_ ∷ _)) {m} w (tup∈ i e∈) with 𝒪-need (lookup as i) _ (subst (_ ∈𝒱_) (lookup-args as i) e∈) | pts as
    where
    lookup-args : ∀ {j} (as : Vec (Arg Σ ψ (ty Any)) j) i → lookup (args as m) i ≡ arg (lookup as i) m
    lookup-args (a ∷ as) zero = refl
    lookup-args (a ∷ as) (suc i) = lookup-args as i
    pts : ∀ {j} (as : Vec (Arg Σ ψ (ty Any)) j)
      → Σ[ N ∈ Ap ] Fits m N × (∀ A → N ⊑ₐ A → ∀ i → Conv (nthD (𝒪s T⁺ as (ρ̂ A) (R̂ A)) i))
    pts [] = ⟨ ∅ₐ , ⟨ fits∅ , (λ _ _ ()) ⟩ ⟩
    pts (a ∷ as) with 𝒪-need a _ (pt∈ (arg a m)) | pts as
    ... | ⟨ N , ⟨ f , g ⟩ ⟩ | ⟨ N' , ⟨ f' , g' ⟩ ⟩ = ⟨ N ∪ₐ N' , ⟨ ∪-fits f f' ,
      (λ A N⊑ → λ { zero → ⟨ _ , ⟨ g A (∪ˡ N⊑) , noω (pt∈ (arg a m)) ⟩ ⟩ ; (suc i) → g' A (∪ʳ N⊑) i }) ⟩ ⟩
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ | ⟨ N' , ⟨ f' , g' ⟩ ⟩ = ⟨ N ∪ₐ N' , ⟨ ∪-fits f f' , (λ A N⊑ →
    binds-intro _ {K = 𝒯 _} (g' A (∪ʳ N⊑)) ⟨ refl , ⟨ nth as i {A} (⟨ g A (∪ˡ N⊑) , noω e∈ ⟩) , conv-⌊⌋s _ (g' A (∪ʳ N⊑)) ⟩ ⟩) ⟩ ⟩
    where
    nth : ∀ {j} (as : Vec (Arg Σ ψ (ty Any)) j) i {A e} → e ∈ ⌊ 𝒪 T⁺ (lookup as i) (ρ̂ A) (R̂ A) ⌋
      → e ∈ nthD ⌊ 𝒪s T⁺ as (ρ̂ A) (R̂ A) ⌋s i
    nth (a ∷ as) zero e∈ = e∈
    nth (a ∷ as) (suc i) {A} e∈ = nth as i {A} e∈
  obj-need (inl a) w (inl∈ u∈) with 𝒪-need a _ u∈
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → inj₂ ⟨ ⟨ _ , ⟨ g A N⊑ , noω u∈ ⟩ ⟩ , ⟨ g A N⊑ , noω u∈ ⟩ ⟩) ⟩ ⟩
  obj-need (inr a) w (inr∈ u∈) with 𝒪-need a _ u∈
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → inj₂ ⟨ ⟨ _ , ⟨ g A N⊑ , noω u∈ ⟩ ⟩ , ⟨ g A N⊑ , noω u∈ ⟩ ⟩) ⟩ ⟩

  {- the fields of tuples and injections -}
  field-need : ∀ {η ψ B C} (f : Field B C) {m : Mach Σ η ψ} (v : Val Σ B) {S} → Need m v S
    → Need m (field′ f v) (λ A → fieldᴰ {Σ} T⁺ f (S A))
  field-need (get i) (tup ws@(_ ∷ _)) h w w∈ with h _ (tup∈ i w∈)
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → inj₂ ⟨ ⟨ _ , ⟨ g A N⊑ , (λ ()) ⟩ ⟩ , ⟨ g A N⊑ , (λ ()) ⟩ ⟩) ⟩ ⟩
  field-need payload (inl u) h w w∈ with h _ (inl∈ w∈)
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → inj₂ ⟨ ⟨ _ , ⟨ g A N⊑ , (λ ()) ⟩ ⟩ , inj₁ ⟨ ⟨ g A N⊑ , (λ ()) ⟩ , noω w∈ ⟩ ⟩) ⟩ ⟩
  field-need payload (inr u) h w w∈ with h _ (inr∈ w∈)
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → inj₂ ⟨ ⟨ _ , ⟨ g A N⊑ , (λ ()) ⟩ ⟩ , inj₂ ⟨ ⟨ g A N⊑ , (λ ()) ⟩ , noω w∈ ⟩ ⟩) ⟩ ⟩

  {- primitives, on two integers -}
  prim-need : ∀ p {η ψ} {m : Mach Σ η ψ} (u u' : Val Σ ⟪ base Int ⟫) {S S'} → Need m u S → Need m u' S'
    → Need m (δᵀ p (int u) (int u')) (λ A → primᵗ p (S A) (S' A))
  prim-need p (const n) (const n') h h' w w∈ with pair∈ const∈ const∈ h h'
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → let ⟨ a , b ⟩ = g A N⊑ in
    inj₂ ⟨ ⟨ _ , a ⟩ , inj₂ ⟨ ⟨ _ , b ⟩ , ⟨ n , ⟨ n' , ⟨ a , ⟨ b , out p w∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩) ⟩ ⟩
    where
    out : ∀ p {w} → w ∈𝒱 δᵀ {Σ} p n n' → w ≡ dout (δ p n n')
    out sub const∈ = refl
    out eq w∈ with does (n ≟ℤ n')
    out eq (inl∈ (dyn∈ unit∈)) | true = refl
    out eq (inr∈ (dyn∈ unit∈)) | false = refl

  {- the flag that testinl sets -}
  isinl-need : ∀ {η ψ} {m : Mach Σ η ψ} (v : Val Σ ⟪ sum ⟫) {S} → Need m v S → Need m (bit (is-inl v)) (λ A → S A ≫= isinlD)
  isinl-need (inl u) h w (inl∈ (dyn∈ unit∈)) with h _ (inl∈ (pt∈ u))
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → inj₂ ⟨ ⟨ _ , ⟨ g A N⊑ , (λ ()) ⟩ ⟩ , inj₁ ⟨ _ , ⟨ ⟨ g A N⊑ , (λ ()) ⟩ , refl ⟩ ⟩ ⟩) ⟩ ⟩
  isinl-need (inr u) h w (inr∈ (dyn∈ unit∈)) with h _ (inr∈ (pt∈ u))
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → inj₂ ⟨ ⟨ _ , ⟨ g A N⊑ , (λ ()) ⟩ ⟩ , inj₂ ⟨ _ , ⟨ ⟨ g A N⊑ , (λ ()) ⟩ , refl ⟩ ⟩ ⟩) ⟩ ⟩

  {- the code and environment of a closure, from its slot -}
  SlotNeed : ∀ {η ψ A} → Mach Σ η ψ → Val Σ A → (Ap → 𝒫 Value) → Set
  SlotNeed m v Q = ∀ W → PS (mem W) v → Σ[ N ∈ Ap ] Fits m N × (∀ A → N ⊑ₐ A → mem W ⊆ Q A)

  car-need : ∀ {η ψ} {m : Mach Σ η ψ} (v : Val Σ ⟪ fun ⟫) {S} → SlotNeed m v S → Need m (code-of v) (λ A → car ⟨ S A , ptt ⟩)
  car-need (pack c e) h w w∈ with h _ (single (pack∈ w∈ (pt∈ e)))
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → ⟨ _ , g A N⊑ _ (here refl) ⟩) ⟩ ⟩

  cdr-need : ∀ {η' η ψ} {m : Mach Σ η ψ} {v : Val Σ ⟪ fun ⟫} {c : Val Σ (code η')} {e S} → v ≡ pack c e → SlotNeed m v S
    → Need m e (λ A → cdr ⟨ S A , ptt ⟩)
  cdr-need {c = c} refl h w w∈ with h _ (single (pack∈ (pt∈ c) w∈))
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → ⟨ _ , g A N⊑ _ (here refl) ⟩) ⟩ ⟩

  {- chk, on a value of its tag: an element of the component that the tag tests -}
  hw : ∀ t → Val Σ ⟪ flat t ⟫ → Value
  hw (ttup n i) (tup ws) = tup[ i ] (pt (lookup ws i))
  hw tfun v = pt v
  hw tsum v = pt v
  hw tint v = pt v

  hw∈ : ∀ t v → hw t v ∈𝒱 v
  hw∈ (ttup n i) (tup ws) = tup∈ i (pt∈ (lookup ws i))
  hw∈ tfun v = pt∈ v
  hw∈ tsum v = pt∈ v
  hw∈ tint v = pt∈ v

  hit-ok : ∀ t v {X} → hw t v ∈ X → hit t X
  hit-ok (ttup n i) (tup ws) h = ⟨ _ , h ⟩
  hit-ok tfun v h = tt
  hit-ok tsum v h = tt
  hit-ok tint v h = tt

  chk-need : ∀ t {η ψ} {m : Mach Σ η ψ} (u : Val Σ Any) {v S} → proj? t u ≡ just v → SlotNeed m u S
    → Need m v (λ A → projectᵠ kind₄ t (S A))
  chk-need t (dyn H v) e h w w∈ with H ≟F flat t
  chk-need t (dyn H v) refl h w w∈ | yes refl with h (w ∷ hw t v ∷ []) (λ { _ (here refl) → dyn∈ w∈ ; _ (there (here refl)) → dyn∈ (hw∈ t v) })
  ... | ⟨ N , ⟨ f , g ⟩ ⟩ = ⟨ N , ⟨ f , (λ A N⊑ → inj₂ ⟨ ⟨ _ , ⟨ g A N⊑ _ (here refl) , noω w∈ ⟩ ⟩
    , inj₂ ⟨ ⟨ g A N⊑ _ (here refl) , noω w∈ ⟩ , ⟨ hit-ok t v ⟨ g A N⊑ _ (there (here refl)) , noω (hw∈ t v) ⟩ , 𝒱-kind w∈ ⟩ ⟩ ⟩) ⟩ ⟩
  chk-need t (dyn H v) () h w w∈ | no _

  {- States ------------------------------------------------------------------------------}

  F̂ : Ap → 𝒫 Value
  F̂ A = mem (fl A)

  {- the meaning of a sequence, with its blocks -}
  𝕂 : ∀ {n Bs ψ} → Seq Σ n Bs ψ → Blocks Σ n Bs → Env Value → RegsD → 𝒫 Value → 𝒫 Value
  𝕂 k bs = ⟦_⟧ˢ T⁺ k (blocksᴰ T⁺ bs)

  𝕂-mono : ∀ {n Bs ψ} (k : Seq Σ n Bs ψ) bs {ρ ρ' R R' F F'} → Le ψ ρ ρ' R R' F F' → 𝕂 k bs ρ R F ⊆ 𝕂 k bs ρ' R' F'
  𝕂-mono k bs = mono-seq T⁺ k (blocks-mono T⁺ bs)

  {- the stack: each caller's rest, on a finite part of the result of its callee -}
  𝒦 : Stack Σ → 𝒫 Value → 𝒫 Value
  𝒦 halt D = D
  𝒦 (retK {Δ = Δ} k bs φ σ) D d = Σ[ A ∈ Ap ] Σ[ W ∈ List Value ] (∀ {B} (x : Δ ∋ B) → PS (ρ̂ A (idx x)) (φ ! x))
    × mem W ⊆ D × d ∈ 𝒦 σ (strictᵐ (mem W) (𝕂 k bs (ρ̂ A) (called-regs (mem W)) init))

  𝒦-mono : ∀ σ {D E} → D ⊆ E → 𝒦 σ D ⊆ 𝒦 σ E
  𝒦-mono halt D⊆ = D⊆
  𝒦-mono (retK k bs φ σ) D⊆ d ⟨ A , ⟨ W , ⟨ f , ⟨ W⊆ , d∈ ⟩ ⟩ ⟩ ⟩ = ⟨ A , ⟨ W , ⟨ f , ⟨ (λ e e∈ → D⊆ e (W⊆ e e∈)) , d∈ ⟩ ⟩ ⟩ ⟩

  𝒦-ω : ∀ σ {D} → ω ∈ D → ω ∈ 𝒦 σ D
  𝒦-ω halt ω∈ = ω∈
  𝒦-ω (retK k bs φ σ) ω∈ = ⟨ ∅ₐ , ⟨ ω ∷ [] , ⟨ (λ _ _ ()) , ⟨ (λ { _ (here refl) → ω∈ }) , 𝒦-ω σ (inj₁ ⟨ refl , here refl ⟩) ⟩ ⟩ ⟩ ⟩

  𝒮 : State Σ → 𝒫 Value
  𝒮 (run k bs σ η m) d = Σ[ A ∈ Ap ] Fits m A × d ∈ 𝒦 σ (𝕂 k bs (ρ̂ A) (R̂ A) (F̂ A))

  {- a step back that keeps the stack and the blocks -}
  Back : ∀ {n Bs ψ ψ' η η'} → Mach Σ η ψ → Mach Σ η' ψ' → Seq Σ n Bs ψ' → Blocks Σ n Bs → (Ap → 𝒫 Value) → Set
  Back m m' k bs Sem = ∀ A' → Fits m' A' → Σ[ A ∈ Ap ] Fits m A × 𝕂 k bs (ρ̂ A') (R̂ A') (F̂ A') ⊆ Sem A

  back : ∀ {n Bs ψ ψ' η η'} σ (k : Seq Σ n Bs ψ) bs (k' : Seq Σ n Bs ψ') {m : Mach Σ η ψ} {m' : Mach Σ η' ψ'}
    → Back m m' k' bs (λ A → 𝕂 k bs (ρ̂ A) (R̂ A) (F̂ A)) → 𝒮 (run k' bs σ η' m') ⊆ 𝒮 (run k bs σ η m)
  back σ k bs k' h d ⟨ A' , ⟨ f' , d∈ ⟩ ⟩ with h A' f'
  ... | ⟨ A , ⟨ f , I ⟩ ⟩ = ⟨ A , ⟨ f , 𝒦-mono σ I d d∈ ⟩ ⟩

  {- writes, back: the part of the destination is that of the value written -}
  clr : Reg → Ap → Ap
  clr rax A = ap (sl A) (λ { rax → [] ; r → rg A r }) (fl A)
  clr rdi A = ap (sl A) (λ { rdi → [] ; r → rg A r }) (fl A)
  clr rsi A = ap (sl A) (λ { rsi → [] ; r → rg A r }) (fl A)

  reg-back : ∀ r {Γ Δ O F₀ η τ} {m : Mach Σ η (st Γ Δ O F₀)} {v : RV Σ η τ} {A'}
    → Fits {ψ = st (Γ [ r ↦ just τ ]) Δ O F₀} ⟨ regs m [ r ≔ v ] , frame m , opened m , flag m ⟩ A'
    → PR τ (R̂ A' r) v × Fits m (clr r A') × (∀ N {X} → R̂ A' r ⊆ X
      → Le (st (Γ [ r ↦ just τ ]) Δ O F₀) (ρ̂ A') (ρ̂ (clr r A' ∪ₐ N)) (R̂ A') (R̂ (clr r A' ∪ₐ N) [ r ≔ˢ X ]) (F̂ A') (F̂ (clr r A' ∪ₐ N)))
  reg-back rax (fits f g l) = ⟨ g rax , ⟨ fits f (λ { rax → PM-[] _ ; rdi → g rdi ; rsi → g rsi }) l
    , (λ N X⊆ → le (λ x → ++ˡ) (λ { rax _ → X⊆ ; rdi _ → ++ˡ ; rsi _ → ++ˡ }) (λ _ → ++ˡ)) ⟩ ⟩
  reg-back rdi (fits f g l) = ⟨ g rdi , ⟨ fits f (λ { rax → g rax ; rdi → PM-[] _ ; rsi → g rsi }) l
    , (λ N X⊆ → le (λ x → ++ˡ) (λ { rax _ → ++ˡ ; rdi _ → X⊆ ; rsi _ → ++ˡ }) (λ _ → ++ˡ)) ⟩ ⟩
  reg-back rsi (fits f g l) = ⟨ g rsi , ⟨ fits f (λ { rax → g rax ; rdi → g rdi ; rsi → PM-[] _ }) l
    , (λ N X⊆ → le (λ x → ++ˡ) (λ { rax _ → ++ˡ ; rdi _ → ++ˡ ; rsi _ → X⊆ }) (λ _ → ++ˡ)) ⟩ ⟩

  undrop : ∀ {Δ' Δ : Ctx} → Δ' ⊑ Δ → (ℕ → List Value) → ℕ → List Value
  undrop here⊑ f = f
  undrop (there⊑ p) f zero = []
  undrop (there⊑ p) f (suc i) = undrop p f i

  undrop-at : ∀ {Δ' Δ : Ctx} {B} (p : Δ' ⊑ Δ) f (y : Δ' ∋ B) → undrop p f (idx (⊑-∋ p y)) ≡ f (idx y)
  undrop-at here⊑ f y = refl
  undrop-at (there⊑ p) f y = undrop-at p f y

  undrop-fits : ∀ {Δ' Δ : Ctx} (p : Δ' ⊑ Δ) {f} (φ : Frame Σ Δ) → (∀ {B} (y : Δ' ∋ B) → PS (mem (f (idx y))) (forget p φ ! y))
    → ∀ {B} (x : Δ ∋ B) → PS (mem (undrop p f (idx x))) (φ ! x)
  undrop-fits here⊑ φ h x = h x
  undrop-fits (there⊑ p) (_ ∷ φ) h Z = λ _ ()
  undrop-fits (there⊑ p) (_ ∷ φ) h (S x) = undrop-fits p φ h x

  put-back : ∀ {n Bs ψ τ ψ' η} (d : Dst n ψ τ ψ') {k : Seq Σ n Bs ψ'} {bs} {m : Mach Σ η ψ} (v : RV Σ η τ) {Src}
    → Need m (toV τ v) Src → Back m (put d v m) k bs (λ A → putᴰ {Σ} T⁺ d (Src A) (𝕂 k bs) (ρ̂ A) (R̂ A) (F̂ A))
  put-back (reg r) {k} {bs} v h A' f' with reg-back r f'
  ... | ⟨ pr , ⟨ fc , L ⟩ ⟩ with needs h (rg A' r) pr
  ... | ⟨ N , ⟨ fN , g ⟩ ⟩ = ⟨ clr r A' ∪ₐ N , ⟨ ∪-fits fc fN , 𝕂-mono k bs (L N (g _ (∪ʳ ⊑-refl))) ⟩ ⟩
  put-back (slot p lt) {k} {bs} {m} v {Src} h A' (fits f g l) with needs h (pt v ∷ sl A' 0) V𝒱
    where
    V𝒱 : PS (mem (pt v ∷ sl A' 0)) v
    V𝒱 _ (here refl) = pt∈ v
    V𝒱 d (there d∈) = f Z d d∈
  ... | ⟨ N , ⟨ fN , gN ⟩ ⟩ = ⟨ A , ⟨ ∪-fits (fits (undrop-fits p (frame m) (λ y → f (S y))) g l) fN , I ⟩ ⟩
    where
    A = ap (undrop p (λ i → sl A' (suc i))) (rg A') (fl A') ∪ₐ N
    V = pt v ∷ sl A' 0
    V⊆ : mem V ⊆ Src A
    V⊆ = gN A (∪ʳ ⊑-refl)
    V𝒱 : PS (mem V) v
    V𝒱 _ (here refl) = pt∈ v
    V𝒱 d (there d∈) = f Z d d∈
    fr' : ∀ {B} (x : _ ∋ B) → ρ̂ A' (idx x) ⊆ (mem V • drop p (ρ̂ A)) (idx x)
    fr' Z e e∈ = there e∈
    fr' (S y) e e∈ = subst (e ∈_) (sym (drop-idx p (ρ̂ A) y)) (∈-++⁺ˡ (subst (λ L → e ∈ mem L) (sym (undrop-at p _ y)) e∈))
    I : 𝕂 k bs (ρ̂ A') (R̂ A') (F̂ A') ⊆ letᵗ (Src A) (λ X → 𝕂 k bs (X • drop p (ρ̂ A)) (R̂ A) (F̂ A))
    I d d∈ = inj₂ ⟨ ⟨ pt v , ⟨ V⊆ _ (here refl) , noω (pt∈ v) ⟩ ⟩ , ⟨ V , ⟨ ⟨ ⟨ 𝕂-mono k bs (le fr' (λ r _ → ++ˡ) (λ _ → ++ˡ)) d d∈
      , ⟨ (λ ()) , proj₁ (part V V𝒱) ⟩ ⟩ , proj₂ (part V V𝒱) ⟩ , ⟨ (λ e e∈ → ⟨ V⊆ e e∈ , noω (V𝒱 e e∈) ⟩) , (λ ()) ⟩ ⟩ ⟩ ⟩

  {- chk's strict write -}
  putˢ-back : ∀ {n Bs ψ A ψ' η} (d : Dst n ψ (ty A) ψ') {k : Seq Σ n Bs ψ'} {bs} {m : Mach Σ η ψ} (v : Val Σ A) {Src}
    → Need m v Src → Back m (put d v m) k bs (λ A → putˢᴰ {Σ} T⁺ d (Src A) (𝕂 k bs) (ρ̂ A) (R̂ A) (F̂ A))
  putˢ-back (reg r) {k} {bs} v h A' f' with reg-back r f'
  ... | ⟨ pr , ⟨ fc , L ⟩ ⟩ with needs h (pt v ∷ rg A' r) (λ { _ (here refl) → pt∈ v ; d (there d∈) → pr d d∈ })
  ... | ⟨ N , ⟨ fN , g ⟩ ⟩ = ⟨ clr r A' ∪ₐ N , ⟨ ∪-fits fc fN , (λ d d∈ →
    inj₂ ⟨ ⟨ pt v , ⟨ g _ (∪ʳ ⊑-refl) _ (here refl) , noω (pt∈ v) ⟩ ⟩ , 𝕂-mono k bs (L N (λ e e∈ → g _ (∪ʳ ⊑-refl) e (there e∈))) d d∈ ⟩) ⟩ ⟩
  putˢ-back (slot p lt) {k} {bs} {m} v {Src} = put-back (slot p lt) {k} {bs} {m} v {Src}

  {- the flag, back -}
  flag-back : ∀ {n Bs Γ Δ O F₀ η} {k : Seq Σ n Bs (st Γ Δ O true)} {bs} {m : Mach Σ η (st Γ Δ O F₀)} b {Src}
    → Need m (bit b) Src → Back m ⟨ regs m , frame m , opened m , b ⟩ k bs (λ A → 𝕂 k bs (ρ̂ A) (R̂ A) (Src A))
  flag-back {k = k} {bs} b h A' (fits f g l) with needs h (fl A') l
  ... | ⟨ N , ⟨ fN , gN ⟩ ⟩ = ⟨ ap (sl A') (rg A') [] ∪ₐ N , ⟨ ∪-fits (fits f g (PF-[] _)) fN ,
    𝕂-mono k bs (le (λ x → ++ˡ) (λ r _ → ++ˡ) (λ _ → gN _ (∪ʳ ⊑-refl))) ⟩ ⟩

  {- opening a closure, back: the code and environment of the last one, forgotten, were parts of their values -}
  keepL : Maybe RTy → List Value → List Value
  keepL (just (ty A)) W = W
  keepL _ W = []

  wipe-back : ∀ {Γ Δ O F₀ η η'} {m : Mach Σ η (st Γ Δ O F₀)} {x : Δ ∋ ⟪ fun ⟫} {o' A₁}
    → Fits {η'} {st (wipe Γ) Δ (just x) F₀} ⟨ wipeᵣ (regs m) , frame m , o' , flag m ⟩ A₁
    → Fits m (ap (sl A₁) (λ r → keepL (Γ ‹ r ›) (rg A₁ r)) (fl A₁))
      × Le (st (wipe Γ) Δ (just x) F₀) (ρ̂ A₁) (ρ̂ A₁) (R̂ A₁) (λ r → mem (keepL (Γ ‹ r ›) (rg A₁ r))) (F̂ A₁) (F̂ A₁)
  wipe-back {Γ} (fits f g l) =
    ⟨ fits f (λ { rax → kf (Regs.ax Γ) (g rax) ; rdi → kf (Regs.di Γ) (g rdi) ; rsi → kf (Regs.si Γ) (g rsi) }) l
    , le (λ _ _ z → z) (λ { rax e → kl (Regs.ax Γ) e ; rdi e → kl (Regs.di Γ) e ; rsi e → kl (Regs.si Γ) e }) (λ _ _ z → z) ⟩
    where
    kf : ∀ {η η'} mt {W} {v : MV Σ η mt} → PM {η'} (forgetα mt) (mem W) (forgetᵥ mt v) → PM mt (mem (keepL mt W)) v
    kf (just (ty A)) h = h
    kf (just codeα) _ _ ()
    kf (just tupα) _ _ ()
    kf nothing _ = tt
    kl : ∀ mt {τ W} → forgetα mt ≡ just τ → mem W ⊆ mem (keepL mt W)
    kl (just (ty A)) _ _ z = z
    kl (just codeα) ()
    kl (just tupα) ()
    kl nothing ()

  loadfst-back : ∀ {n Bs Γ Δ O F₀ η} (x : Δ ∋ ⟪ fun ⟫) r {k : Seq Σ n Bs (st (wipe Γ [ r ↦ just codeα ]) Δ (just x) F₀)} {bs}
    {m : Mach Σ η (st Γ Δ O F₀)}
    → Back m ⟨ wipeᵣ (regs m) [ r ≔ code-of (frame m ! x) ] , frame m , ⟨ code-of (frame m ! x) , env-of (frame m ! x) ⟩ , flag m ⟩ k bs
        (λ A → 𝕂 k bs (ρ̂ A) (R̂ A [ r ≔ˢ car ⟨ ρ̂ A (idx x) , ptt ⟩ ]) (F̂ A))
  loadfst-back x r {k} {bs} {m} A' f'
    with put-back (reg r) {k} {bs} {m = ⟨ wipeᵣ (regs m) , frame m , ⟨ code-of (frame m ! x) , env-of (frame m ! x) ⟩ , flag m ⟩}
           _ (car-need (frame m ! x) (slot-need x)) A' f'
  ... | ⟨ A₁ , ⟨ f₁ , ⊆₁ ⟩ ⟩ with wipe-back f₁
  ... | ⟨ f , lw ⟩ = ⟨ _ , ⟨ f , (λ d d∈ → 𝕂-mono k bs (le-reg r lw (λ _ z → z)) d (⊆₁ d d∈)) ⟩ ⟩

  {- a jump, back: the frame -}
  go-back : ∀ {n Bs Δ η σ} (bs : Blocks Σ n Bs) (l : Bs ∋ Δ) {φ : Frame Σ Δ} {d} → d ∈ 𝒮 (go ds (block bs l) σ η φ)
    → Σ[ A ∈ Ap ] (∀ {B} (x : Δ ∋ B) → PS (ρ̂ A (idx x)) (φ ! x)) × d ∈ 𝒦 σ (blocksᴰ T⁺ bs l (ρ̂ A))
  go-back {σ = σ} bs l {d = d} ⟨ A' , ⟨ f' , d∈ ⟩ ⟩ =
    ⟨ A' , ⟨ ffr f' , 𝒦-mono σ (λ e e∈ → subst (e ∈_) (sym (at bs l)) (𝕂-mono (Blk.start (block bs l)) (Blk.blocks (block bs l)) (le (λ x _ z → z) (λ { rax () ; rdi () ; rsi () }) (λ ())) e e∈)) d d∈ ⟩ ⟩
    where
    at : ∀ {n Bs Δ} (bs : Blocks Σ n Bs) (l : Bs ∋ Δ) → blocksᴰ T⁺ bs l (ρ̂ A')
      ≡ 𝕂 (Blk.start (block bs l)) (Blk.blocks (block bs l)) (ρ̂ A') (λ _ → init) init
    at (bs ▷ k) Z = refl
    at (bs ▷ k) (S l) = at bs l

  frame-only : ∀ {η Γ Δ O F₀} {m : Mach Σ η (st Γ Δ O F₀)} {A} → (∀ {B} (x : Δ ∋ B) → PS (ρ̂ A (idx x)) (frame m ! x))
    → Fits m (ap (sl A) (λ _ → []) [])
  frame-only f = fits f (λ r → PM-[] _) (PF-[] _)

  {- chk, back: %rax and the flag, unset, have no parts -}
  chk-back : ∀ {n Bs Γ Δ O F₀ η ψ'} t (x : Δ ∋ Any) (d : Dst n (st (Γ [ rax ↦ nothing ]) Δ O false) (ty ⟪ flat t ⟫) ψ')
    {k : Seq Σ n Bs ψ'} {bs} {m : Mach Σ η (st Γ Δ O F₀)} {v} → proj? t (frame m ! x) ≡ just v
    → Back m (put d v ⟨ regs m [ rax ≔ tt ] , frame m , opened m , tt ⟩) k bs
        (λ A → putˢᴰ {Σ} T⁺ d (projectᵠ kind₄ t (ρ̂ A (idx x))) (𝕂 k bs) (ρ̂ A) (R̂ A [ rax ≔ˢ init ]) init)
  chk-back t x d {k} {bs} {m} {v} pe A' f' with putˢ-back d {k} {bs} v (chk-need t (frame m ! x) pe (slot-need x)) A' f'
  ... | ⟨ A₁ , ⟨ fits f g l , ⊆₁ ⟩ ⟩ = ⟨ ap (sl A₁) (λ { rax → [] ; r → rg A₁ r }) [] , ⟨ fits f (λ { rax → PM-[] _ ; rdi → g rdi ; rsi → g rsi }) (PF-[] _)
    , (λ d' d'∈ → putˢ-mono {Σ} T⁺ d {𝕂 k bs} {𝕂 k bs} (𝕂-mono k bs) (le (λ _ _ z → z) (λ { rax () ; rdi _ _ z → z ; rsi _ _ z → z }) (λ ())) (λ _ z → z) d' (⊆₁ d' d'∈)) ⟩ ⟩

  {- Invariant: the slot of the open closure holds it -----------------------------------}

  Inv : State Σ → Set
  Inv (run {ψ = ψ} k bs σ η m) = Op (St.op ψ) (frame m) (opened m)

  op-put : ∀ {n ψ τ ψ' η} (d : Dst n ψ τ ψ') {m : Mach Σ η ψ} {v} → Op (St.op ψ) (frame m) (opened m)
    → Op (St.op ψ') (frame (put d v m)) (opened (put d v m))
  op-put (reg r) o = o
  op-put (slot p _) o = tt

  inv-step : ∀ s {s'} → Inv s → step ds s ≡ next s' → Inv s'
  inv-step (run (movq a d ∷ k) bs σ η m) o refl = op-put d o
  inv-step (run (subq a r e ∷ k) bs σ η m) o refl = o
  inv-step (run (cmpq a₂ a₁ ∷ k) bs σ η m) o refl = o
  inv-step (run (sete d ∷ k) bs σ η m) o refl = op-put d o
  inv-step (run (testinl a ∷ k) bs σ η m) o refl = o
  inv-step (run (alloc o' d ∷ k) bs σ η m) o refl = op-put d o
  inv-step (run (load f a d ∷ k) bs σ η m) o refl = op-put d o
  inv-step (run (loadfst x r ∷ k) bs σ η m) o refl = pack-η (frame m ! x)
  inv-step (run (loadsnd r ∷ k) bs σ η m) o refl = o
  inv-step (run (callq a e₁ e₂ ∷ k) bs σ η m) o q with arg a m
  ... | code f with q
  ... | refl = tt
  inv-step (run (chk t x d ∷ k) bs σ η m) o q with proj? t (frame m ! x)
  ... | just v with q
  ... | refl = op-put d o
  inv-step (run (chk t x d ∷ k) bs σ η m) o () | nothing
  inv-step (run (retq e) bs (retK k bs' φ σ) η m) o refl = tt
  inv-step (run (jmp l) bs σ η m) o refl = tt
  inv-step (run (je l₁ l₂) bs σ η m) o q with flag m
  ... | true with q
  ... | refl = tt
  inv-step (run (je l₁ l₂) bs σ η m) o q | false with q
  ... | refl = tt

  {- Steps ---------------------------------------------------------------------------------}

  step-⊆ : ∀ s {s'} → Inv s → step ds s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
  step-⊆ (run (movq a d ∷ k) bs σ η m) o refl = back σ (movq a d ∷ k) bs k (put-back d {k} {bs} (arg a m) (𝒪-need a))
  step-⊆ (run (subq a r e ∷ k) bs σ η m) o refl = back σ (subq a r e ∷ k) bs k (put-back (reg r) {k} {bs} _ (prim-need sub _ _ (𝒪-need (reg r e)) (𝒪-need a)))
  step-⊆ (run (cmpq a₂ a₁ ∷ k) bs σ η m) o refl = back σ (cmpq a₂ a₁ ∷ k) bs k (flag-back {k = k} {bs} _ (prim-need eq _ _ (𝒪-need a₁) (𝒪-need a₂)))
  step-⊆ (run (sete d ∷ k) bs σ η m) o refl = back σ (sete d ∷ k) bs k (put-back d {k} {bs} (bit (flag m)) λ w w∈ →
    ⟨ ap (λ _ → []) (λ _ → []) (w ∷ []) , ⟨ fits (λ _ _ ()) (λ r → PM-[] _) (single w∈) , (λ A N⊑ → proj₂ (proj₂ N⊑) _ (here refl)) ⟩ ⟩)
  step-⊆ (run (testinl a ∷ k) bs σ η m) o refl = back σ (testinl a ∷ k) bs k (flag-back {k = k} {bs} _ (isinl-need _ (𝒪-need a)))
  step-⊆ (run (alloc o' d ∷ k) bs σ η m) o refl = back σ (alloc o' d ∷ k) bs k (put-back d {k} {bs} (obj o' m) (obj-need o'))
  step-⊆ (run (load f a d ∷ k) bs σ η m) o refl = back σ (load f a d ∷ k) bs k (put-back d {k} {bs} (field′ f (arg a m)) (field-need f _ (𝒪-need a)))
  step-⊆ (run (loadfst x r ∷ k) bs σ η m) o refl = back σ (loadfst x r ∷ k) bs k (loadfst-back x r {k} {bs})
  step-⊆ (run (loadsnd {x = x} r ∷ k) bs σ η m) o refl = back σ (loadsnd {x = x} r ∷ k) bs k (put-back (reg r) {k} {bs} (proj₂ (opened m)) (cdr-need o (slot-need x)))
  step-⊆ (run (callq a e₁ e₂ ∷ k) bs σ η m) o q with arg a m | 𝒪-need a {m}
  ... | code f | na with q
  ... | refl = λ { d ⟨ A' , ⟨ f' , ⟨ A₂ , ⟨ W , ⟨ fφ , ⟨ W⊆ , d∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ → CALL A' f' A₂ W fφ W⊆ d d∈ }
    where
    e' = cast e₁ (regs m ⦅ rdi ⦆)
    w' = cast e₂ (regs m ⦅ rsi ⦆)
    CALL : ∀ A' → Fits ⟨ rv tt e' w' , [] , tt , tt ⟩ A' → ∀ A₂ W → (∀ {B} (x : _ ∋ B) → PS (ρ̂ A₂ (idx x)) (frame m ! x))
      → mem W ⊆ 𝕂 (Body.start (ds ! f)) (Body.blocks (ds ! f)) (ρ̂ A') (R̂ A') (F̂ A')
      → ∀ d → d ∈ 𝒦 σ (strictᵐ (mem W) (𝕂 k bs (ρ̂ A₂) (called-regs (mem W)) init)) → d ∈ 𝒮 (run (callq a e₁ e₂ ∷ k) bs σ η m)
    CALL A' f' A₂ W fφ W⊆ d d∈ = ⟨ A , ⟨ ∪-fits (∪-fits (∪-fits (frame-only {A = A₂} fφ) fa) fd) fs ,
      𝒦-mono σ (≫=-mono {F = λ _ → 𝕂 k bs (ρ̂ A₂) (called-regs (mem W)) init} {λ _ → 𝕂 k bs (ρ̂ A) (called-regs C) init} W⊆C
        (λ _ → 𝕂-mono k bs (le-ret (λ x → proj₁ (∪ˡ {F₀} {Na} (∪ˡ {F₀ ∪ₐ Na} {Nd} (∪ˡ {F₀ ∪ₐ Na ∪ₐ Nd} {Ns} (⊑-refl {A})))) (idx x)) W⊆C))) d d∈ ⟩ ⟩
      where
      X = pt e' ∷ rg A' rdi
      Y = pt w' ∷ rg A' rsi
      X𝒱 : PS (mem X) e'
      X𝒱 _ (here refl) = pt∈ e'
      X𝒱 d (there d∈) = frg f' rdi d d∈
      Y𝒱 : PS (mem Y) w'
      Y𝒱 _ (here refl) = pt∈ w'
      Y𝒱 d (there d∈) = frg f' rsi d d∈
      ent : ∀ c → c ∈ mem W → (X ↦ (Y ↦ c)) ∈𝒱 code f
      ent c c∈ = code∈ (fix-S TC ind f _ (ΛΛᵐ-entry {F = λ X Y → runᴰ T⁺ (ds ! f) (λ _ → init) (argsᴰ X Y) init}
        (𝕂-mono (Body.start (ds ! f)) (Body.blocks (ds ! f)) {R' = argsᴰ (mem X) (mem Y)} (le (λ ()) (λ { rax () ; rdi _ _ → there ; rsi _ _ → there }) (λ ())) c (W⊆ c c∈))
        (λ ()) (proj₁ (part X X𝒱)) (proj₂ (part X X𝒱)) (λ ()) (proj₁ (part Y Y𝒱)) (proj₂ (part Y Y𝒱))))
      E = map (λ c → X ↦ (Y ↦ c)) W
      na' = needs na E (λ d d∈ → let ⟨ c , ⟨ c∈ , e ⟩ ⟩ = ∈-map⁻ _ d∈ in subst (_∈𝒱 code f) (sym e) (ent c c∈))
      nd = reg-need rdi X (uncast e₁ X𝒱)
      ns = reg-need rsi Y (uncast e₂ Y𝒱)
      fa = proj₁ (proj₂ na')
      fd = proj₁ (proj₂ nd)
      fs = proj₁ (proj₂ ns)
      F₀ = ap (sl A₂) (λ _ → []) []
      Na = proj₁ na'
      Nd = proj₁ nd
      Ns = proj₁ ns
      A = F₀ ∪ₐ Na ∪ₐ Nd ∪ₐ Ns
      C = ⋆ ⟨ ⋆ ⟨ 𝒪 T⁺ a (ρ̂ A) (R̂ A) , ⟨ R̂ A rdi , ptt ⟩ ⟩ , ⟨ R̂ A rsi , ptt ⟩ ⟩
      W⊆C : mem W ⊆ C
      W⊆C c c∈ = ⟨ Y , ⟨ ⟨ X , ⟨ proj₂ (proj₂ na') A (∪ʳ {F₀} {Na} (∪ˡ {F₀ ∪ₐ Na} {Nd} (∪ˡ {F₀ ∪ₐ Na ∪ₐ Nd} {Ns} (⊑-refl {A})))) _ (∈-map⁺ _ c∈)
        , ⟨ proj₂ (proj₂ nd) A (∪ʳ {F₀ ∪ₐ Na} {Nd} (∪ˡ {F₀ ∪ₐ Na ∪ₐ Nd} {Ns} (⊑-refl {A}))) , (λ ()) ⟩ ⟩ ⟩ , ⟨ proj₂ (proj₂ ns) A (∪ʳ {F₀ ∪ₐ Na ∪ₐ Nd} {Ns} (⊑-refl {A})) , (λ ()) ⟩ ⟩ ⟩
  step-⊆ (run (chk t x d ∷ k) bs σ η m) o q with proj? t (frame m ! x) in pe
  ... | just v with q
  ... | refl = back σ (chk t x d ∷ k) bs k (chk-back t x d {k} {bs} pe)
  step-⊆ (run (retq e) bs (retK k bs' φ σ) η m) o refl d ⟨ A' , ⟨ f' , d∈ ⟩ ⟩ with reg-need {m = m} rax W (uncast e W𝒱)
    where
    v = cast e (regs m ⦅ rax ⦆)
    W = pt v ∷ rg A' rax
    W𝒱 : PS (mem W) v
    W𝒱 _ (here refl) = pt∈ v
    W𝒱 d (there d∈) = frg f' rax d d∈
  ... | ⟨ N , ⟨ fN , gN ⟩ ⟩ = ⟨ N , ⟨ fN , ⟨ A' , ⟨ _ , ⟨ ffr f' , ⟨ gN N ⊑-refl , 𝒦-mono σ (λ d' d'∈ →
    inj₂ ⟨ ⟨ _ , ⟨ here refl , noω (pt∈ (cast e (regs m ⦅ rax ⦆))) ⟩ ⟩ , 𝕂-mono k bs' (le (λ _ _ z → z) (λ { rax _ _ → there ; rdi () ; rsi () }) (λ ())) d' d'∈ ⟩) d d∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  step-⊆ (run (jmp l) bs σ η m) o refl d d∈ with go-back {σ = σ} bs l d∈
  ... | ⟨ A , ⟨ f , d∈' ⟩ ⟩ = ⟨ _ , ⟨ frame-only {A = A} f , d∈' ⟩ ⟩
  step-⊆ (run (je l₁ l₂) bs σ η m) o q with flag m in fe
  ... | true with q
  ... | refl = λ d d∈ → let ⟨ A , ⟨ f , d∈' ⟩ ⟩ = go-back {σ = σ} bs l₁ d∈ in
    ⟨ ap (sl A) (λ _ → []) (left ⟨⟩ ∷ []) , ⟨ fits f (λ r → PM-[] _) (subst (λ b → PS (mem (left ⟨⟩ ∷ [])) (bit b)) (sym fe) (single (pt∈ (bit true))))
    , 𝒦-mono σ (λ d' d'∈ → inj₂ ⟨ ⟨ _ , ⟨ here refl , (λ ()) ⟩ ⟩ ,
      inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ here refl , (λ ()) ⟩ , (λ ()) ⟩ }) , ⟨ d'∈ , ≈-single ⟩ ⟩ ⟩ ⟩ ⟩) d d∈' ⟩ ⟩
  step-⊆ (run (je l₁ l₂) bs σ η m) o q | false with q
  ... | refl = λ d d∈ → let ⟨ A , ⟨ f , d∈' ⟩ ⟩ = go-back {σ = σ} bs l₂ d∈ in
    ⟨ ap (sl A) (λ _ → []) (right ⟨⟩ ∷ []) , ⟨ fits f (λ r → PM-[] _) (subst (λ b → PS (mem (right ⟨⟩ ∷ [])) (bit b)) (sym fe) (single (pt∈ (bit false))))
    , 𝒦-mono σ (λ d' d'∈ → inj₂ ⟨ ⟨ _ , ⟨ here refl , (λ ()) ⟩ ⟩ ,
      inj₂ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ here refl , (λ ()) ⟩ , (λ ()) ⟩ }) , ⟨ d'∈ , ≈-single ⟩ ⟩ ⟩ ⟩ ⟩) d d∈' ⟩ ⟩

  ↠-⊆ : ∀ {s t} → Inv s → s ↠ t → 𝒮 t ⊆ 𝒮 s
  ↠-⊆ o done = λ _ z → z
  ↠-⊆ {s} o (q ∷↠ τ) d d∈ = step-⊆ s o q d (↠-⊆ (inv-step s o q) τ d d∈)

  {- Final states -------------------------------------------------------------------------}

  {- a value of another kind than the tag of chk -}
  proj-fail : ∀ t (u : Val Σ Any) → proj? t u ≡ nothing → kind₄ (kind (pt u)) ≢ kindᶠ (flat t)
  proj-fail t (dyn H v) e k with H ≟F flat t
  proj-fail t (dyn H v) () k | yes refl
  ... | no ne = ne (kindᶠ-inj (trans (sym (𝒱-kind (pt∈ v))) k))

  final : ∀ s {o} → step ds s ≡ stop o → (o ≡ o-error × ω ∈ 𝒮 s) ⊎ Σ[ v ∈ Val Σ Any ] o ≡ obs v × pt v ∈ 𝒮 s
  final (run (movq a d ∷ k) bs σ η m) ()
  final (run (subq a r e ∷ k) bs σ η m) ()
  final (run (cmpq a₂ a₁ ∷ k) bs σ η m) ()
  final (run (sete d ∷ k) bs σ η m) ()
  final (run (testinl a ∷ k) bs σ η m) ()
  final (run (alloc o d ∷ k) bs σ η m) ()
  final (run (load f a d ∷ k) bs σ η m) ()
  final (run (loadfst x r ∷ k) bs σ η m) ()
  final (run (loadsnd r ∷ k) bs σ η m) ()
  final (run (callq a e₁ e₂ ∷ k) bs σ η m) q with arg a m
  ... | code f with q
  ... | ()
  final (run (chk t x d ∷ k) bs σ η m) q with proj? t (frame m ! x) in pe
  ... | just v with q
  ... | ()
  final (run (chk t x d ∷ k) bs σ η m) refl | nothing with slot-need {m = m} x (pt (frame m ! x) ∷ []) (single (pt∈ (frame m ! x)))
  ... | ⟨ N , ⟨ fN , gN ⟩ ⟩ = inj₁ ⟨ refl , ⟨ N , ⟨ fN , 𝒦-ω σ (ω-put d (inj₂ ⟨ ⟨ _ , ⟨ u∈ , noω (pt∈ (frame m ! x)) ⟩ ⟩
    , inj₁ ⟨ refl , ⟨ _ , ⟨ ⟨ u∈ , noω (pt∈ (frame m ! x)) ⟩ , proj-fail t (frame m ! x) pe ⟩ ⟩ ⟩ ⟩)) ⟩ ⟩ ⟩
    where
    u∈ = gN N ⊑-refl _ (here refl)
    ω-put : ∀ {n ψ τ ψ'} (d : Dst n ψ τ ψ') {D κ ρ R F} → ω ∈ D → ω ∈ putˢᴰ {Σ} T⁺ d D κ ρ R F
    ω-put (reg r) ω∈ = inj₁ ⟨ refl , ω∈ ⟩
    ω-put (slot p _) ω∈ = inj₁ ⟨ refl , ω∈ ⟩
  final (run (retq e) bs halt η m) refl with reg-need {m = m} rax (pt (cast e (regs m ⦅ rax ⦆)) ∷ []) (uncast e (single (pt∈ _)))
  ... | ⟨ N , ⟨ fN , gN ⟩ ⟩ = inj₂ ⟨ cast e (regs m ⦅ rax ⦆) , ⟨ refl , ⟨ N , ⟨ fN , gN N ⊑-refl _ (here refl) ⟩ ⟩ ⟩ ⟩
  final (run (retq e) bs (retK k bs' φ σ) η m) ()
  final (run (jmp l) bs σ η m) ()
  final (run (je l₁ l₂) bs σ η m) q with flag m
  ... | true with q
  ... | ()
  final (run (je l₁ l₂) bs σ η m) q | false with q
  ... | ()

  {- the start of the program -}
  start-⊆ : ∀ {n Bs} (k : Seq Σ n Bs (entry [])) bs → 𝒮 (run k bs halt 0 ⟨ rv tt tt tt , [] , tt , tt ⟩)
    ⊆ runᴰ T⁺ (body n bs k) (λ _ → init) (λ _ → init) init
  start-⊆ k bs d ⟨ A , ⟨ _ , d∈ ⟩ ⟩ = 𝕂-mono k bs (le (λ ()) (λ { rax () ; rdi () ; rsi () }) (λ ())) d d∈

  {- the element of a value observed as a constant is that constant -}
  pt-const : ∀ {A B} {k : base-rep B} (v : Val Σ A) → o-const B k ≡ obs v → pt v ≡ dconst k
  pt-const (dyn G v) e = pt-const v e
  pt-const (const k) refl = refl
  pt-const (code f) ()
  pt-const (pack c e) ()
  pt-const (tup ws) ()
  pt-const (inl v) ()
  pt-const (inr v) ()
