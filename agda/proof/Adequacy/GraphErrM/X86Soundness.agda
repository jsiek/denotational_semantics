{-

  Soundness of the X86 machine with respect to the graph model with
  errors (Semantics/GraphErrM/X86.agda): what the machine computes is in
  the denotation of the (well-formed) program, and when the machine stops
  with an error, ω is.

  As in Adequacy/X86Soundness.agda, each machine state denotes a set of
  values (𝒮) that every step can only shrink (step-⊆), where a location
  denotes a finite part (Ap) of the meaning 𝒱 v of the value v it holds,
  and the call stack is the continuation (𝒦): a return frame runs the
  caller's rest with %rax holding the callee's result, strictly (call).
  New here:

  * an unset location and the absent flag denote init = {ω}, and an
    unset location is approximated by a part of it;
  * every value denotes a set without ω (𝒱-clean), so that a slot can be
    bound to a finite part of it (letᵐ) and code called on finite parts
    of %rdi and %rsi (callᵐ);
  * the table of every program is consistent (X86Consistent.agda), so
    the parts bound are consistent;
  * a state that stops with an error denotes a set that holds ω
    (final-err): each check of the machine fails on an operand that is
    unset (ω), beyond the frame (init), or a value whose denotation has
    an element of the wrong kind (pt v); a missing block is init; a call
    of code with no definition is errcode; and the stack passes ω on
    (𝒦-ω).

  Labels refer to older definitions (WF): the code of a definition is
  interpreted with the table of the older ones.

-}

module proof.Adequacy.GraphErrM.X86Soundness where

open import Framework.Primitives using (Base; base-rep; Int; Nat; 𝔹; Unit; Void; Blame)
open import Language.Prim using (Out; int; bool; δ; sub; eq)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres; ■; Results)
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _~_; Con; Con⇒≈; ≈-single; _≈_)
  renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (ℬ; ℬ-consis; nthD)
open import proof.Framework.GraphModel.ErrorMonad
  hiding (K⟨_⟩; KOK; K-mono; K-≃; K-fin; K-ok; let-law; case-law) renaming (Val to Valᴰ)
open import proof.Semantics.GraphErrM.Prim using (primᵐ; primᵐ-good; primD) renaming (out to dout)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import Framework.GraphModel.Ops using (𝒯; 𝒞; car; cdr; payloadD) renaming (pair to pairD; proj to projD)
open import Language.X86
  renaming (pair to pairₛ; inl to inlₛ; inr to inrₛ; tuple to tupleₛ; fst to fstₛ; snd to sndₛ; get to getₛ)
open import Semantics.GraphErrM.X86
  renaming (Regs to SRegs; code to codeD; run to runD; put to putD; call to callD; args to argsD;
            read to readD; zeros to zerosD; _[_↦_] to _[_↦ₛ_]; flag to flagD)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates; next; stop)
open import proof.Framework.ListUtil using (_‼_; proj; has-length)
open import Semantics.CEK.Values using (obs-list)
open import Semantics.CEK.X86
  using (Val; code; pair; const; tup; obs; out; prim?; Frame; State; Stack; halt; retK; run; step; block-at; global; sem; get-field; build; is-inl; cmp; truth; bit; _[_]≔_; zeros; arg; args; test; goto; callq?; regs; upd; back; halt?)
  renaming (read to readM; put to putM; call to callM; Regs to MRegs; _[_↦_] to _[_↦ₘ_])
import Semantics.CEK.X86 as T using (inl; inr)
open import proof.Adequacy.Common using (ShapeOf; ShapeAt; has-length→length; length→has-length; δ?-inv)
open import proof.Adequacy.GraphErrM.X86WF
open import proof.Adequacy.GraphErrM.X86Consistent using (table-con)
import proof.Adequacy.GraphErrM.X86Common as Common

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using ()
open import Data.List using (List; []; _∷_; _++_; [_]; length; map; reverse; replicate)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Properties using (++-assoc; length-replicate; length-reverse)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; Pointwise-length)
open import Data.Maybe using (Maybe; just; nothing; _>>=_) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_; _<?_; _⊔_; _∸_; _+_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; n≤1+n; <⇒≢; <-≤-trans)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no; ¬_)

{- two integers in the operands of a primitive -}
prim-in : ∀ p {D E n m x} → dconst {Int} n ∈ D → dconst {Int} m ∈ E → x ≡ dout (δ p n m) → x ∈ primᵐ p ⟨ D , ⟨ E , ptt ⟩ ⟩
prim-in p n∈ m∈ e = inj₂ ⟨ ⟨ _ , ⟨ n∈ , (λ ()) ⟩ ⟩ , inj₂ ⟨ ⟨ _ , ⟨ m∈ , (λ ()) ⟩ ⟩
  , inj₂ (inj₂ ⟨ _ , ⟨ _ , ⟨ ⟨ n∈ , (λ ()) ⟩ , ⟨ ⟨ m∈ , (λ ()) ⟩ , e ⟩ ⟩ ⟩ ⟩) ⟩ ⟩


{- Registers ---------------------------------------------------------------------}

_≟R_ : (g g' : Reg) → Dec (g ≡ g')
rax ≟R rax = yes refl
rax ≟R rdi = no λ ()
rax ≟R rsi = no λ ()
rdi ≟R rax = no λ ()
rdi ≟R rdi = yes refl
rdi ≟R rsi = no λ ()
rsi ≟R rax = no λ ()
rsi ≟R rdi = no λ ()
rsi ≟R rsi = yes refl

≔-here : ∀ (ρ : SRegs) g D → (ρ [ g ≔ D ]) g ≡ D
≔-here ρ rax D = refl
≔-here ρ rdi D = refl
≔-here ρ rsi D = refl

≔-other : ∀ (ρ : SRegs) g D g' → g' ≢ g → (ρ [ g ≔ D ]) g' ≡ ρ g'
≔-other ρ rax D rax ne = ⊥-elim (ne refl)
≔-other ρ rax D rdi ne = refl
≔-other ρ rax D rsi ne = refl
≔-other ρ rdi D rax ne = refl
≔-other ρ rdi D rdi ne = ⊥-elim (ne refl)
≔-other ρ rdi D rsi ne = refl
≔-other ρ rsi D rax ne = refl
≔-other ρ rsi D rdi ne = refl
≔-other ρ rsi D rsi ne = ⊥-elim (ne refl)

{- Monotonicity of the semantics ------------------------------------------------------}

{- the semantics is monotone in the slots of the frame (of n slots), the
   registers and the flag, and in the entries of the table at the labels
   the code reads (L) -}
module Mono {T T' : Table} {L : ℕ → Set} (TT : ∀ k → L k → T k ⊆ T' k) (n : ℕ) where

  Sl : Store → Store → Set
  Sl σ σ' = ∀ x → x < n → σ x ⊆ σ' x

  Le : Store → SRegs → 𝒫 Value → Store → SRegs → 𝒫 Value → Set
  Le σ ρ F σ' ρ' F' = Sl σ σ' × (∀ g → ρ g ⊆ ρ' g) × F ⊆ F'

  MonoK : Kont → Kont → Set₁
  MonoK κ κ' = ∀ {σ ρ F σ' ρ' F'} → Le σ ρ F σ' ρ' F' → κ σ ρ F ⊆ κ' σ' ρ' F'

  MonoB : Blocks → Blocks → Set₁
  MonoB B B' = ∀ l → MonoK (B l) (B' l)

  𝒪-mono : ∀ {σ ρ σ' ρ'} a → OK L a → Sl σ σ' → (∀ g → ρ g ⊆ ρ' g) → 𝒪 T n σ ρ a ⊆ 𝒪 T' n σ' ρ' a
  𝒪-mono (loc (var x)) _ s r with x <? n
  ... | yes x< = s x x<
  ... | no _ = λ _ z → z
  𝒪-mono (loc (reg g)) _ s r = r g
  𝒪-mono (imm B k) _ s r = λ _ z → z
  𝒪-mono (label k) ok s r = TT k ok

  𝒪s-mono : ∀ {σ ρ σ' ρ'} as → All (OK L) as → Sl σ σ' → (∀ g → ρ g ⊆ ρ' g)
    → results-rel-pres _⊆_ (replicate (length as) ■) (𝒪s T n σ ρ as) (𝒪s T' n σ' ρ' as)
  𝒪s-mono [] _ s r = ptt
  𝒪s-mono (a ∷ as) (o ∷ os) s r = ⟨ lift (𝒪-mono a o s r) , 𝒪s-mono as os s r ⟩

  object-mono : ∀ {σ ρ σ' ρ'} sh as → All (OK L) as → Sl σ σ' → (∀ g → ρ g ⊆ ρ' g)
    → object T n σ ρ sh as ⊆ object T' n σ' ρ' sh as
  object-mono pairₛ [] _ s r = λ _ z → z
  object-mono pairₛ (a ∷ []) _ s r = λ _ z → z
  object-mono pairₛ (a ∷ b ∷ []) (oa ∷ ob ∷ []) s r =
    lower (mono (pairᵐ-good {⊤}) _ _ ⟨ lift (𝒪-mono a oa s r) , ⟨ lift (𝒪-mono b ob s r) , ptt ⟩ ⟩)
  object-mono pairₛ (a ∷ b ∷ c ∷ as) _ s r = λ _ z → z
  object-mono tupleₛ as os s r = lower (mono (𝒯ᵐ-good {⊤} (length as)) _ _ (𝒪s-mono as os s r))
  object-mono inlₛ [] _ s r = λ _ z → z
  object-mono inlₛ (a ∷ []) (oa ∷ []) s r = lower (mono (inlᵐ-good {⊤}) _ _ ⟨ lift (𝒪-mono a oa s r) , ptt ⟩)
  object-mono inlₛ (a ∷ b ∷ as) _ s r = λ _ z → z
  object-mono inrₛ [] _ s r = λ _ z → z
  object-mono inrₛ (a ∷ []) (oa ∷ []) s r = lower (mono (inrᵐ-good {⊤}) _ _ ⟨ lift (𝒪-mono a oa s r) , ptt ⟩)
  object-mono inrₛ (a ∷ b ∷ as) _ s r = λ _ z → z

  field-mono : ∀ f {D D'} → D ⊆ D' → field′ f D ⊆ field′ f D'
  field-mono fstₛ D⊆ = lower (mono (carᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ptt ⟩)
  field-mono sndₛ D⊆ = lower (mono (cdrᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ptt ⟩)
  field-mono (getₛ i) D⊆ = lower (mono (projᵐ-good {⊤} i) _ _ ⟨ lift D⊆ , ptt ⟩)
  field-mono payload D⊆ = payloadᵐ-mono D⊆


  ↦-le : ∀ {σ σ' : Store} {X X'} x → Sl σ σ' → X ⊆ X' → Sl (σ [ x ↦ₛ X ]) (σ' [ x ↦ₛ X' ])
  ↦-le x s X⊆ y y< with y ≟ x
  ... | yes _ = X⊆
  ... | no _ = s y y<

  ≔-le : ∀ {ρ ρ' : SRegs} {D D'} g → D ⊆ D' → (∀ g → ρ g ⊆ ρ' g) → ∀ g' → (ρ [ g ≔ D ]) g' ⊆ (ρ' [ g ≔ D' ]) g'
  ≔-le {ρ} {ρ'} {D} {D'} g D⊆ r g' with g' ≟R g
  ... | yes refl rewrite ≔-here ρ g D | ≔-here ρ' g D' = D⊆
  ... | no ne rewrite ≔-other ρ g D g' ne | ≔-other ρ' g D' g' ne = r g'

  frame-mono : ∀ x {D D' E E'} → D ⊆ D' → E ⊆ E' → frameᵐ n x D E ⊆ frameᵐ n x D' E'
  frame-mono x D⊆ E⊆ with x <? n
  ... | yes _ = E⊆
  ... | no _ = ≫=-mono D⊆ (λ _ w z → z)

  put-mono : ∀ d {D D' κ κ'} → D ⊆ D' → MonoK κ κ' → MonoK (putD n d D κ) (putD n d D' κ')
  put-mono (var x) D⊆ mκ ⟨ s , ⟨ r , f ⟩ ⟩ =
    frame-mono x D⊆ (lower (mono (letᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ⟨ (λ X X' X⊆ → lift (mκ ⟨ ↦-le x s X⊆ , ⟨ r , f ⟩ ⟩)) , ptt ⟩ ⟩))
  put-mono (reg g) D⊆ mκ ⟨ s , ⟨ r , f ⟩ ⟩ = ≫=-mono D⊆ (λ _ → mκ ⟨ s , ⟨ ≔-le g D⊆ r , f ⟩ ⟩)

  primᵐ-⊆ : ∀ p {D D' E E'} → D ⊆ D' → E ⊆ E' → primᵐ p ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ primᵐ p ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  primᵐ-⊆ p D⊆ E⊆ = lower (mono (primᵐ-good {⊤} p) _ _ ⟨ lift D⊆ , ⟨ lift E⊆ , ptt ⟩ ⟩)

  flag-mono : ∀ {F₀ F₀' κ κ' σ ρ σ' ρ'} → F₀ ⊆ F₀' → MonoK κ κ' → Sl σ σ' → (∀ g → ρ g ⊆ ρ' g)
    → flagD F₀ κ σ ρ ⊆ flagD F₀' κ' σ' ρ'
  flag-mono F⊆ mκ s r = ≫=-mono F⊆ (λ _ → mκ ⟨ s , ⟨ r , F⊆ ⟩ ⟩)

  called-le : ∀ {R R'} → R ⊆ R' → ∀ g → called R g ⊆ called R' g
  called-le R⊆ rax = R⊆
  called-le R⊆ rdi = λ _ z → z
  called-le R⊆ rsi = λ _ z → z

  call-mono : ∀ {R R' κ κ' σ σ'} → R ⊆ R' → MonoK κ κ' → Sl σ σ' → callD R κ σ ⊆ callD R' κ' σ'
  call-mono R⊆ mκ s = ≫=-mono R⊆ (λ _ → mκ ⟨ s , ⟨ called-le R⊆ , (λ _ z → z) ⟩ ⟩)

  is-mono : ∀ is {κ κ'} → Code L is → MonoK κ κ' → MonoK (⟦ is ⟧ˢ T n κ) (⟦ is ⟧ˢ T' n κ')
  is-mono [] _ mκ = mκ
  is-mono (movq a d ∷ is) ⟨ oa , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    put-mono d (𝒪-mono a oa s r) (is-mono is c mκ) le
  is-mono (subq a d ∷ is) ⟨ oa , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    put-mono d (primᵐ-⊆ sub (𝒪-mono (loc d) tt s r) (𝒪-mono a oa s r)) (is-mono is c mκ) le
  is-mono (cmpq a₂ a₁ ∷ is) ⟨ ⟨ o₂ , o₁ ⟩ , c ⟩ mκ ⟨ s , ⟨ r , _ ⟩ ⟩ =
    flag-mono (primᵐ-⊆ eq (𝒪-mono a₁ o₁ s r) (𝒪-mono a₂ o₂ s r)) (is-mono is c mκ) s r
  is-mono (sete d ∷ is) ⟨ _ , c ⟩ mκ le@(⟨ _ , ⟨ _ , f ⟩ ⟩) = put-mono d f (is-mono is c mκ) le
  is-mono (testinl a ∷ is) ⟨ oa , c ⟩ mκ ⟨ s , ⟨ r , _ ⟩ ⟩ =
    flag-mono (isinlᵐ-mono (𝒪-mono a oa s r)) (is-mono is c mκ) s r
  is-mono (alloc sh as d ∷ is) ⟨ os , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    put-mono d (object-mono sh as os s r) (is-mono is c mκ) le
  is-mono (load f a d ∷ is) ⟨ oa , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    put-mono d (field-mono f (𝒪-mono a oa s r)) (is-mono is c mκ) le
  is-mono (callq a ∷ is) ⟨ oa , c ⟩ mκ ⟨ s , ⟨ r , _ ⟩ ⟩ =
    call-mono (lower (mono (callᵐ-good {⊤}) _ _ ⟨ lift (𝒪-mono a oa s r) , ⟨ lift (r rdi) , ⟨ lift (r rsi) , ptt ⟩ ⟩ ⟩))
      (is-mono is c mκ) s

  jump-mono : ∀ j {B B'} → MonoB B B' → MonoK (⟦ j ⟧ʲ B) (⟦ j ⟧ʲ B')
  jump-mono retq mB ⟨ _ , ⟨ r , _ ⟩ ⟩ = r rax
  jump-mono (jmp l) mB = mB l
  jump-mono (je l₁ l₂) mB le@(⟨ _ , ⟨ _ , f ⟩ ⟩) =
    lower (mono (𝒞ᵐ-good {⊤}) _ _ ⟨ lift f , ⟨ (λ _ _ _ → lift (mB l₁ le)) , ⟨ (λ _ _ _ → lift (mB l₂ le)) , ptt ⟩ ⟩ ⟩)

  blocks-mono : ∀ bs → All (λ b → Code L (Block.instrs b)) bs → MonoB (blocks T n bs) (blocks T' n bs)
  blocks-mono [] _ l le = λ _ z → z
  blocks-mono (b ∷ bs) (c ∷ cs) l with l ≟ length bs
  ... | yes _ = is-mono (Block.instrs b) c (jump-mono (Block.jump b) (blocks-mono bs cs))
  ... | no _ = blocks-mono bs cs l

  body-mono : ∀ m bs b → All (λ c → Code L (Block.instrs c)) (b ∷ bs) → MonoK (runD T n (body m bs b)) (runD T' n (body m bs b))
  body-mono m bs b (c ∷ cs) = is-mono (Block.instrs b) c (jump-mono (Block.jump b) (blocks-mono bs cs))

{- any code reads what the trivial condition allows -}
ok-⊤ : ∀ a → OK (λ _ → ⊤) a
ok-⊤ (loc l) = tt
ok-⊤ (imm B k) = tt
ok-⊤ (label k) = tt

code-⊤ : ∀ is → Code (λ _ → ⊤) is
code-⊤ [] = tt
code-⊤ (movq a d ∷ is) = ⟨ ok-⊤ a , code-⊤ is ⟩
code-⊤ (subq a d ∷ is) = ⟨ ok-⊤ a , code-⊤ is ⟩
code-⊤ (cmpq a₂ a₁ ∷ is) = ⟨ ⟨ ok-⊤ a₂ , ok-⊤ a₁ ⟩ , code-⊤ is ⟩
code-⊤ (sete d ∷ is) = ⟨ tt , code-⊤ is ⟩
code-⊤ (testinl a ∷ is) = ⟨ ok-⊤ a , code-⊤ is ⟩
code-⊤ (alloc sh as d ∷ is) = ⟨ all-⊤ as , code-⊤ is ⟩
  where all-⊤ : ∀ as → All (OK (λ _ → ⊤)) as
        all-⊤ [] = []
        all-⊤ (a ∷ as) = ok-⊤ a ∷ all-⊤ as
code-⊤ (load f a d ∷ is) = ⟨ ok-⊤ a , code-⊤ is ⟩
code-⊤ (callq a ∷ is) = ⟨ ok-⊤ a , code-⊤ is ⟩

codes-⊤ : ∀ bs → All (λ b → Code (λ _ → ⊤) (Block.instrs b)) bs
codes-⊤ [] = []
codes-⊤ (b ∷ bs) = code-⊤ (Block.instrs b) ∷ codes-⊤ bs

{- Finite parts of sets --------------------------------------------------------------}

++-⊆ : ∀ {P : 𝒫 Value} A B → mem A ⊆ P → mem B ⊆ P → mem (A ++ B) ⊆ P
++-⊆ A B A⊆ B⊆ d d∈ with ∈-++⁻ A d∈
... | inj₁ a = A⊆ d a
... | inj₂ b = B⊆ d b

{- the parts f z of the elements z of V -}
pick : (Value → List Value) → List Value → List Value
pick f [] = []
pick f (z ∷ V) = f z ++ pick f V

pick-∈ : ∀ f V {z} → z ∈ mem V → mem (f z) ⊆ mem (pick f V)
pick-∈ f (z ∷ V) (here refl) d d∈ = ∈-++⁺ˡ d∈
pick-∈ f (z ∷ V) (there z∈) d d∈ = ∈-++⁺ʳ (f z) (pick-∈ f V z∈ d d∈)

pick-⊆ : ∀ {P : 𝒫 Value} f V → (∀ z → z ∈ mem V → mem (f z) ⊆ P) → mem (pick f V) ⊆ P
pick-⊆ f [] h = λ _ ()
pick-⊆ f (z ∷ V) h = ++-⊆ (f z) (pick f V) (h z (here refl)) (pick-⊆ f V (λ z' z'∈ → h z' (there z'∈)))

fstv sndv lft rgt hd tl : Value → List Value
fstv ⦅ p , q ⦆ = p ∷ []
fstv _ = []
sndv ⦅ p , q ⦆ = q ∷ []
sndv _ = []
lft (left p) = p ∷ []
lft _ = []
rgt (right p) = p ∷ []
rgt _ = []
hd (tup[ zero ] x) = x ∷ []
hd _ = []
tl (tup[ suc i ] x) = tup[ i ] x ∷ []
tl _ = []

{- Locations ---------------------------------------------------------------------}

_≟L_ : (l l' : Loc) → Dec (l ≡ l')
var x ≟L var y with x ≟ y
... | yes refl = yes refl
... | no ne = no λ { refl → ne refl }
reg g ≟L reg g' with g ≟R g'
... | yes refl = yes refl
... | no ne = no λ { refl → ne refl }
var x ≟L reg g = no λ ()
reg g ≟L var x = no λ ()

↦ₘ-other : ∀ (ρ : MRegs) g m g' → g' ≢ g → (ρ [ g ↦ₘ m ]) g' ≡ ρ g'
↦ₘ-other ρ rax m rax ne = ⊥-elim (ne refl)
↦ₘ-other ρ rax m rdi ne = refl
↦ₘ-other ρ rax m rsi ne = refl
↦ₘ-other ρ rdi m rax ne = refl
↦ₘ-other ρ rdi m rdi ne = ⊥-elim (ne refl)
↦ₘ-other ρ rdi m rsi ne = refl
↦ₘ-other ρ rsi m rax ne = refl
↦ₘ-other ρ rsi m rdi ne = refl
↦ₘ-other ρ rsi m rsi ne = ⊥-elim (ne refl)

↦ₘ-here : ∀ (ρ : MRegs) g m → (ρ [ g ↦ₘ m ]) g ≡ m
↦ₘ-here ρ rax m = refl
↦ₘ-here ρ rdi m = refl
↦ₘ-here ρ rsi m = refl

{- The machine's steps ---------------------------------------------------------------}

{- what a write of v to d does in the machine -}
record Put (d : Loc) (v : Val) (φ : Frame) (ρ : MRegs) (φ' : Frame) (ρ' : MRegs) : Set where
  field
    p-len : length φ' ≡ length φ
    p-here : readM φ' ρ' d ≡ just v
    p-other : ∀ l → l ≢ d → readM φ' ρ' l ≡ readM φ ρ l
    p-inside : ∀ {x} → d ≡ var x → x < length φ
open Put

put-inv : ∀ d m {φ ρ K s'} → putM d m φ ρ K ≡ next s'
  → Σ[ v ∈ Val ] Σ[ φ' ∈ Frame ] Σ[ ρ' ∈ MRegs ] m ≡ just v × s' ≡ K φ' ρ' × Put d v φ ρ φ' ρ'
put-inv (var x) (just v) {φ} {ρ} e with φ [ x ]≔ v in e'
put-inv (var x) (just v) {φ} {ρ} refl | just φ' =
  ⟨ v , ⟨ φ' , ⟨ ρ , ⟨ refl , ⟨ refl , record
    { p-len = Common.Assigned.len a ; p-here = Common.Assigned.here a
    ; p-other = λ { (var y) ne → Common.Assigned.other a y (λ { refl → ne refl }) ; (reg g) ne → refl }
    ; p-inside = λ { refl → Common.Assigned.inside a } } ⟩ ⟩ ⟩ ⟩ ⟩
  where a = Common.≔-inv [] φ x e'
put-inv (reg g) (just v) {φ} {ρ} refl =
  ⟨ v , ⟨ φ , ⟨ ρ [ g ↦ₘ just v ] , ⟨ refl , ⟨ refl , record
    { p-len = refl ; p-here = ↦ₘ-here ρ g (just v)
    ; p-other = λ { (var y) ne → refl ; (reg g') ne → ↦ₘ-other ρ g (just v) g' (λ { refl → ne refl }) }
    ; p-inside = λ () } ⟩ ⟩ ⟩ ⟩ ⟩

{- a write that Errs: of nothing, or beyond the frame -}
put-err : ∀ d m {φ ρ K} → putM d m φ ρ K ≡ stop o-error
  → m ≡ nothing ⊎ Σ[ v ∈ Val ] Σ[ x ∈ ℕ ] m ≡ just v × d ≡ var x × (x < length φ → ⊥)
put-err d nothing e = inj₁ refl
put-err (var x) (just v) {φ} e with φ [ x ]≔ v in e'
put-err (var x) (just v) {φ} () | just _
... | nothing = inj₂ ⟨ v , ⟨ x , ⟨ refl , ⟨ refl , outside ⟩ ⟩ ⟩ ⟩
  where
  outside : x < length φ → ⊥
  outside x< with Common.≔-ok [] φ x v x<
  ... | ⟨ φ' , e'' ⟩ with trans (sym e') e''
  ... | ()
put-err (reg g) (just v) ()

test-inv : ∀ m {K : Maybe Bool → State} {s'} → test m K ≡ next s' → Σ[ b ∈ Bool ] m ≡ just b × s' ≡ K (just b)
test-inv (just b) refl = ⟨ b , ⟨ refl , refl ⟩ ⟩

test-err : ∀ m {K : Maybe Bool → State} {o} → test m K ≡ stop o → m ≡ nothing
test-err nothing _ = refl

goto-inv : ∀ mb {σ f φ ρ s'} → goto mb σ f φ ρ ≡ next s'
  → Σ[ b ∈ Block ] Σ[ bs ∈ List Block ] mb ≡ just ⟨ b , bs ⟩ × s' ≡ run (Block.instrs b) (Block.jump b) bs σ f φ ρ
goto-inv (just ⟨ b , bs ⟩) refl = ⟨ b , ⟨ bs , ⟨ refl , refl ⟩ ⟩ ⟩

goto-err : ∀ mb {σ f φ ρ o} → goto mb σ f φ ρ ≡ stop o → mb ≡ nothing
goto-err nothing _ = refl

bind-inv : ∀ {A B : Set} (m : Maybe A) {f : A → Maybe B} {r} → (m >>= f) ≡ just r → Σ[ x ∈ A ] m ≡ just x × f x ≡ just r
bind-inv (just x) e = ⟨ x , ⟨ refl , e ⟩ ⟩

mmap-inv : ∀ {A B : Set} (f : A → B) (m : Maybe A) {y} → mmap f m ≡ just y → Σ[ x ∈ A ] m ≡ just x × y ≡ f x
mmap-inv f (just x) refl = ⟨ x , ⟨ refl , refl ⟩ ⟩

mmap-err : ∀ {A B : Set} (f : A → B) (m : Maybe A) → mmap f m ≡ nothing → m ≡ nothing
mmap-err f nothing _ = refl

truth-inv : ∀ m {b} → truth m ≡ just b → m ≡ just (bool b)
truth-inv (just (bool b)) refl = refl

{- a comparison of integers has a truth value -}
cmp-err : ∀ o₁ o₂ → truth (δ? eq o₁ o₂) ≡ nothing → δ? eq o₁ o₂ ≡ nothing
cmp-err o₁ o₂ e with δ? eq o₁ o₂ in d
... | nothing = refl
... | just r with δ?-inv eq o₁ o₂ d
cmp-err o₁ o₂ () | just r | ⟨ n , ⟨ m , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩

Evals : Frame → MRegs → List Arg → List Val → Set
Evals φ ρ = Pointwise (λ a u → arg φ ρ a ≡ just u)

args-inv : ∀ {φ ρ} acc as {k : List Val → Maybe Val} {w} → args φ ρ acc as k ≡ just w
  → Σ[ us ∈ List Val ] Evals φ ρ as us × k (reverse acc ++ us) ≡ just w
args-inv {φ} {ρ} acc [] {k} e = ⟨ [] , ⟨ [] , subst (λ vs → k vs ≡ _) (sym (++-identityʳ' (reverse acc))) e ⟩ ⟩
  where ++-identityʳ' : ∀ (xs : List Val) → xs ++ [] ≡ xs
        ++-identityʳ' [] = refl
        ++-identityʳ' (x ∷ xs) = cong (x ∷_) (++-identityʳ' xs)
args-inv {φ} {ρ} acc (a ∷ as) {k} e with arg φ ρ a in ea
... | just u with args-inv (u ∷ acc) as e
...   | ⟨ us , ⟨ es , e' ⟩ ⟩ =
  ⟨ u ∷ us , ⟨ ea ∷ es , subst (λ vs → k vs ≡ _) (++-assoc (reverse acc) [ u ] us) (subst (λ vs → k (vs ++ us) ≡ _) (Data.List.Properties.unfold-reverse u acc) e') ⟩ ⟩

{- a slot beyond the frame -}
‼-err : ∀ (φ : Frame) x → φ ‼ x ≡ nothing → x < length φ → ⊥
‼-err (u ∷ φ) zero () _
‼-err (u ∷ φ) (suc x) e (s≤s x<) = ‼-err φ x e x<

‼-nothing : ∀ {A : Set} (xs : List A) k → xs ‼ k ≡ nothing → length xs ≤ k
‼-nothing [] k _ = z≤n
‼-nothing (x ∷ xs) zero ()
‼-nothing (x ∷ xs) (suc k) e = s≤s (‼-nothing xs k e)

{- a component of a tuple of the right length -}
proj-ok : ∀ {n} (i : Fin n) (vs : List Val) → length vs ≡ n → Σ[ v ∈ Val ] proj i vs ≡ just v
proj-ok {suc n} zero (v ∷ vs) refl rewrite length→has-length n vs refl = ⟨ v , refl ⟩
proj-ok (suc i) (v ∷ vs) refl = proj-ok i vs refl

{- whether an observation is an integer -}
int? : ∀ o → (Σ[ n ∈ _ ] o ≡ o-const Int n) ⊎ (∀ n → o ≢ o-const Int n)
int? (o-const Int n) = inj₁ ⟨ n , refl ⟩
int? (o-const Nat k) = inj₂ λ n ()
int? (o-const 𝔹 k) = inj₂ λ n ()
int? (o-const Unit k) = inj₂ λ n ()
int? (o-const Void k) = inj₂ λ n ()
int? (o-const Blame k) = inj₂ λ n ()
int? o-fun = inj₂ λ n ()
int? (o-tuple os) = inj₂ λ n ()
int? (o-inl o) = inj₂ λ n ()
int? (o-inr o) = inj₂ λ n ()
int? o-error = inj₂ λ n ()

{- a primitive fails on a non-integer -}
δ?-err : ∀ p o₁ o₂ → δ? p o₁ o₂ ≡ nothing
  → (∀ n → o₁ ≢ o-const Int n) ⊎ (Σ[ n ∈ _ ] o₁ ≡ o-const Int n × (∀ m → o₂ ≢ o-const Int m))
δ?-err p o₁ o₂ e with int? o₁
... | inj₂ ne = inj₁ ne
... | inj₁ ⟨ n , refl ⟩ with int? o₂
...   | inj₂ ne = inj₂ ⟨ n , ⟨ refl , ne ⟩ ⟩
δ?-err p o₁ o₂ () | inj₁ ⟨ n , refl ⟩ | inj₁ ⟨ m , refl ⟩

length-obs-list : ∀ vs → length (obs-list vs) ≡ length vs
length-obs-list [] = refl
length-obs-list (v ∷ vs) = cong suc (length-obs-list vs)

{- Soundness, for a table ds of global definitions ---------------------------------}

module _ (ds : List Body) (wfd : DefsWF ds) where

  open Common ds

  T⁺ : Table
  T⁺ = table ds

  {- within the machine, the same table on both sides -}
  module M (n : ℕ) = Mono {T⁺} {T⁺} {λ _ → ⊤} (λ _ _ _ z → z) n

  {- Denotations of values ------------------------------------------------------}

  𝒱 : Val → 𝒫 Value
  AtV : ∀ {n} → Fin n → List Val → Value → Set

  𝒱 (code k) = T⁺ k
  𝒱 (pair v w) d = Σ[ p ∈ Value ] Σ[ q ∈ Value ] d ≡ ⦅ p , q ⦆ × p ∈ 𝒱 v × q ∈ 𝒱 w
  𝒱 (const B k) = ℬ B k ptt
  𝒱 (tup vs) d = (d ≡ ⟨⟩ × vs ≡ []) ⊎ (Σ[ m ∈ ℕ ] Σ[ i ∈ Fin m ] Σ[ e ∈ Value ] d ≡ tup[ i ] e × AtV i vs e)
  𝒱 (T.inl v) d = Σ[ p ∈ Value ] d ≡ left p × p ∈ 𝒱 v
  𝒱 (T.inr v) d = Σ[ p ∈ Value ] d ≡ right p × p ∈ 𝒱 v

  AtV i [] d = ⊥
  AtV {suc n} zero (v ∷ vs) d = length vs ≡ n × d ∈ 𝒱 v
  AtV (suc i) (v ∷ vs) d = AtV i vs d

  𝒱m : Maybe Val → 𝒫 Value
  𝒱m (just v) = 𝒱 v
  𝒱m nothing = init

  {- an element of the meaning of each value -}
  pt : Val → Value
  pt (code k) = ν
  pt (pair v w) = ⦅ pt v , pt w ⦆
  pt (const B k) = dconst k
  pt (tup []) = ⟨⟩
  pt (tup (v ∷ vs)) = tup[_]_ {suc (length vs)} zero (pt v)
  pt (T.inl v) = left (pt v)
  pt (T.inr v) = right (pt v)

  pt∈ : ∀ v → pt v ∈ 𝒱 v
  pt∈ (code k) = ν-table ds k
  pt∈ (pair v w) = ⟨ _ , ⟨ _ , ⟨ refl , ⟨ pt∈ v , pt∈ w ⟩ ⟩ ⟩ ⟩
  pt∈ (const B k) = ⟨ refl , refl ⟩
  pt∈ (tup []) = inj₁ ⟨ refl , refl ⟩
  pt∈ (tup (v ∷ vs)) = inj₂ ⟨ _ , ⟨ zero , ⟨ pt v , ⟨ refl , ⟨ refl , pt∈ v ⟩ ⟩ ⟩ ⟩ ⟩
  pt∈ (T.inl v) = ⟨ pt v , ⟨ refl , pt∈ v ⟩ ⟩
  pt∈ (T.inr v) = ⟨ pt v , ⟨ refl , pt∈ v ⟩ ⟩

  pt≢ω : ∀ v → pt v ≢ ω
  pt≢ω (code k) ()
  pt≢ω (pair v w) ()
  pt≢ω (const B k) ()
  pt≢ω (tup []) ()
  pt≢ω (tup (v ∷ vs)) ()
  pt≢ω (T.inl v) ()
  pt≢ω (T.inr v) ()

  𝒱-val : ∀ v → val∈ (𝒱 v)
  𝒱-val v = ⟨ pt v , ⟨ pt∈ v , pt≢ω v ⟩ ⟩

  pt-shape : ∀ v → ShapeOf (obs v) (pt v)
  pt-shape (code k) = tt
  pt-shape (pair v w) = tt
  pt-shape (const B k) = refl
  pt-shape (tup []) = refl
  pt-shape (tup (v ∷ vs)) = ⟨ length-obs-list vs , pt-shape v ⟩
  pt-shape (T.inl v) = pt-shape v
  pt-shape (T.inr v) = pt-shape v

  table-clean : ∀ (Ns : List Body) k → Clean (table Ns k)
  table-clean [] k = proj₁ ΛΛᵐ-val
  table-clean (N ∷ Ns) k with k ≟ length Ns
  ... | yes _ = proj₁ ΛΛᵐ-val
  ... | no _ = table-clean Ns k

  {- no value means an error -}
  𝒱-clean : ∀ v → Clean (𝒱 v)
  𝒱-clean (code k) = table-clean ds k
  𝒱-clean (pair v w) ω ⟨ _ , ⟨ _ , ⟨ () , _ ⟩ ⟩ ⟩ refl
  𝒱-clean (const B k) = λ { .ω () refl }
  𝒱-clean (tup vs) ω (inj₁ ⟨ () , _ ⟩) refl
  𝒱-clean (tup vs) ω (inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ () , _ ⟩ ⟩ ⟩ ⟩) refl
  𝒱-clean (T.inl v) ω ⟨ _ , ⟨ () , _ ⟩ ⟩ refl
  𝒱-clean (T.inr v) ω ⟨ _ , ⟨ () , _ ⟩ ⟩ refl

  {- every value means a consistent set -}
  𝒱-con : ∀ v → Con (𝒱 v)
  AtV-len : ∀ {n} (i : Fin n) vs d → AtV i vs d → length vs ≡ n
  AtV-con : ∀ {n} (i j : Fin n) vs d d' → AtV i vs d → AtV j vs d' → (¬ (i ≡ j)) ⊎ (i ≡ j × d ~ d')

  𝒱-con (code k) = table-con ds k
  𝒱-con (pair v w) _ _ ⟨ _ , ⟨ _ , ⟨ refl , ⟨ p∈ , q∈ ⟩ ⟩ ⟩ ⟩ ⟨ _ , ⟨ _ , ⟨ refl , ⟨ p∈' , q∈' ⟩ ⟩ ⟩ ⟩ =
    ⟨ 𝒱-con v _ _ p∈ p∈' , 𝒱-con w _ _ q∈ q∈' ⟩
  𝒱-con (const B k) = lower (ℬ-consis B k ptt ptt ptt)
  𝒱-con (tup vs) _ _ (inj₁ ⟨ refl , _ ⟩) (inj₁ ⟨ refl , _ ⟩) = tt
  𝒱-con (tup vs) _ _ (inj₁ ⟨ refl , refl ⟩) (inj₂ ⟨ _ , ⟨ i , ⟨ _ , ⟨ refl , () ⟩ ⟩ ⟩ ⟩)
  𝒱-con (tup vs) _ _ (inj₂ ⟨ _ , ⟨ i , ⟨ _ , ⟨ refl , () ⟩ ⟩ ⟩ ⟩) (inj₁ ⟨ refl , refl ⟩)
  𝒱-con (tup vs) _ _ (inj₂ ⟨ m , ⟨ i , ⟨ d , ⟨ refl , a ⟩ ⟩ ⟩ ⟩) (inj₂ ⟨ m' , ⟨ j , ⟨ d' , ⟨ refl , a' ⟩ ⟩ ⟩ ⟩)
      with trans (sym (AtV-len i vs d a)) (AtV-len j vs d' a')
  ... | refl = ⟨ refl , AtV-con i j vs d d' a a' ⟩
  𝒱-con (T.inl v) _ _ ⟨ _ , ⟨ refl , p∈ ⟩ ⟩ ⟨ _ , ⟨ refl , p∈' ⟩ ⟩ = 𝒱-con v _ _ p∈ p∈'
  𝒱-con (T.inr v) _ _ ⟨ _ , ⟨ refl , p∈ ⟩ ⟩ ⟨ _ , ⟨ refl , p∈' ⟩ ⟩ = 𝒱-con v _ _ p∈ p∈'

  AtV-len {suc n} zero (v ∷ vs) d ⟨ len , _ ⟩ = cong suc len
  AtV-len (suc i) (v ∷ vs) d a = cong suc (AtV-len i vs d a)

  AtV-con zero zero (v ∷ vs) d d' ⟨ _ , d∈ ⟩ ⟨ _ , d'∈ ⟩ = inj₂ ⟨ refl , 𝒱-con v d d' d∈ d'∈ ⟩
  AtV-con zero (suc j) (v ∷ vs) d d' _ _ = inj₁ λ ()
  AtV-con (suc i) zero (v ∷ vs) d d' _ _ = inj₁ λ ()
  AtV-con (suc i) (suc j) (v ∷ vs) d d' a a' with AtV-con i j vs d d' a a'
  ... | inj₁ ne = inj₁ λ { refl → ne refl }
  ... | inj₂ ⟨ refl , d~ ⟩ = inj₂ ⟨ refl , d~ ⟩

  {- a component of a tuple -}
  proj-AtV : ∀ {n} (i : Fin n) vs {v} → proj i vs ≡ just v → ∀ d → d ∈ 𝒱 v → AtV i vs d
  proj-AtV {suc n} zero (v ∷ vs) e d d∈ with has-length n vs in h
  proj-AtV {suc n} zero (v ∷ vs) refl d d∈ | true = ⟨ has-length→length n vs h , d∈ ⟩
  proj-AtV {suc n} zero (v ∷ vs) () d d∈ | false
  proj-AtV (suc i) (v ∷ vs) e d d∈ = proj-AtV i vs e d d∈

  {- primitives -}
  int-in : ∀ v {n} → obs v ≡ o-const Int n → dconst {Int} n ∈ 𝒱 v
  int-in (const B k) refl = ⟨ refl , refl ⟩

  𝒱-out : ∀ r d → d ∈ 𝒱 (out r) → d ≡ dout r
  𝒱-out (int k) (dconst k') ⟨ refl , refl ⟩ = refl
  𝒱-out (bool true) _ ⟨ _ , ⟨ refl , inj₁ ⟨ refl , _ ⟩ ⟩ ⟩ = refl
  𝒱-out (bool true) _ ⟨ _ , ⟨ refl , inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ refl , () ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  𝒱-out (bool false) _ ⟨ _ , ⟨ refl , inj₁ ⟨ refl , _ ⟩ ⟩ ⟩ = refl
  𝒱-out (bool false) _ ⟨ _ , ⟨ refl , inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ refl , () ⟩ ⟩ ⟩ ⟩ ⟩ ⟩

  {- the elements of the wrong kind -}
  notint-pt : ∀ v → (∀ n → obs v ≢ o-const Int n) → kind (pt v) ≢ base Int
  notint-pt (const Int k) ne _ = ne k refl
  notint-pt (const Nat k) ne ()
  notint-pt (const 𝔹 k) ne ()
  notint-pt (const Unit k) ne ()
  notint-pt (const Void k) ne ()
  notint-pt (const Blame k) ne ()
  notint-pt (code k) ne ()
  notint-pt (pair v w) ne ()
  notint-pt (tup []) ne ()
  notint-pt (tup (v ∷ vs)) ne ()
  notint-pt (T.inl v) ne ()
  notint-pt (T.inr v) ne ()

  notinj-pt : ∀ v → is-inl v ≡ nothing → kind (pt v) ≢ inj
  notinj-pt (code k) e ()
  notinj-pt (pair v w) e ()
  notinj-pt (const B k) e ()
  notinj-pt (tup []) e ()
  notinj-pt (tup (v ∷ vs)) e ()

  notfun-pt : ∀ v → (∀ k → v ≢ code k) → kind (pt v) ≢ fun
  notfun-pt (code k) ne _ = ne k refl
  notfun-pt (pair v w) ne ()
  notfun-pt (const B k) ne ()
  notfun-pt (tup []) ne ()
  notfun-pt (tup (v ∷ vs)) ne ()
  notfun-pt (T.inl v) ne ()
  notfun-pt (T.inr v) ne ()

  {- a field that the machine cannot take is an error -}
  field-err : ∀ fl u → get-field fl u ≡ nothing → ω ∈ field′ fl (mem (pt u ∷ []))
  field-err fstₛ (pair v w) ()
  field-err fstₛ (code k) e = bad-one _ {F = λ X → car ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err fstₛ (const B k) e = bad-one _ {F = λ X → car ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err fstₛ (tup []) e = bad-one _ {F = λ X → car ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err fstₛ (tup (v ∷ vs)) e = bad-one _ {F = λ X → car ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err fstₛ (T.inl v) e = bad-one _ {F = λ X → car ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err fstₛ (T.inr v) e = bad-one _ {F = λ X → car ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err sndₛ (pair v w) ()
  field-err sndₛ (code k) e = bad-one _ {F = λ X → cdr ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err sndₛ (const B k) e = bad-one _ {F = λ X → cdr ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err sndₛ (tup []) e = bad-one _ {F = λ X → cdr ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err sndₛ (tup (v ∷ vs)) e = bad-one _ {F = λ X → cdr ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err sndₛ (T.inl v) e = bad-one _ {F = λ X → cdr ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err sndₛ (T.inr v) e = bad-one _ {F = λ X → cdr ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err (getₛ {n} zero) (tup []) e = bad-one _ {F = λ X → projD {n} zero ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err (getₛ (suc i)) (tup []) e = bad-one _ {F = λ X → projD (suc i) ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err (getₛ {n} i) (tup (v ∷ vs)) e =
    bad-one _ {F = λ X → projD i ⟨ X , ptt ⟩} (λ ()) (λ { refl → len refl })
    where
    len : ¬ (suc (length vs) ≡ n)
    len l with proj-ok i (v ∷ vs) l
    ... | ⟨ w , e' ⟩ with trans (sym e) e'
    ... | ()
  field-err (getₛ i) (code k) e = bad-one _ {F = λ X → projD i ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err (getₛ i) (pair v w) e = bad-one _ {F = λ X → projD i ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err (getₛ i) (const B k) e = bad-one _ {F = λ X → projD i ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err (getₛ i) (T.inl v) e = bad-one _ {F = λ X → projD i ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err (getₛ i) (T.inr v) e = bad-one _ {F = λ X → projD i ⟨ X , ptt ⟩} (λ ()) (λ ())
  field-err payload (T.inl v) ()
  field-err payload (T.inr v) ()
  field-err payload (code k) e = bad-one _ {F = λ X → payloadD (X ⇂ ValPayload)} (λ ()) (λ ())
  field-err payload (pair v w) e = bad-one _ {F = λ X → payloadD (X ⇂ ValPayload)} (λ ()) (λ ())
  field-err payload (const B k) e = bad-one _ {F = λ X → payloadD (X ⇂ ValPayload)} (λ ()) (λ ())
  field-err payload (tup []) e = bad-one _ {F = λ X → payloadD (X ⇂ ValPayload)} (λ ()) (λ ())
  field-err payload (tup (v ∷ vs)) e = bad-one _ {F = λ X → payloadD (X ⇂ ValPayload)} (λ ()) (λ ())

  field-ω : ∀ fl {D} → ω ∈ D → ω ∈ field′ fl D
  field-ω fstₛ ω∈ = inj₁ ⟨ refl , ω∈ ⟩
  field-ω sndₛ ω∈ = inj₁ ⟨ refl , ω∈ ⟩
  field-ω (getₛ i) ω∈ = inj₁ ⟨ refl , ω∈ ⟩
  field-ω payload ω∈ = inj₁ ⟨ refl , ω∈ ⟩

  {- the table beyond the definitions -}
  table-out : ∀ (Ns : List Body) k → length Ns ≤ k → table Ns k ≡ errcode
  table-out [] k _ = refl
  table-out (N ∷ Ns) k le with k ≟ length Ns
  ... | yes refl = ⊥-elim (<⇒≢ le refl)
  ... | no _ = table-out Ns k (≤-trans (n≤1+n _) le)

  global-none : ∀ k → global ds k ≡ nothing → T⁺ k ≡ errcode
  global-none k e = table-out ds k (subst (_≤ k) (length-reverse ds) (‼-nothing (reverse ds) k e))

  {- Approximations ---------------------------------------------------------------}

  Apx : Set
  Apx = Loc → List Value

  {- a finite part of what a location holds -}
  Ap : List Value → Maybe Val → Set
  Ap A m = mem A ⊆ 𝒱m m

  AL : Apx → Frame → MRegs → Set
  AL A φ ρ = ∀ l → Ap (A l) (readM φ ρ l)

  σ̂ : Apx → Store
  σ̂ A x = mem (A (var x))

  ρ̂ : Apx → SRegs
  ρ̂ A g = mem (A (reg g))

  𝓕 : Maybe Bool → 𝒫 Value
  𝓕 (just b) = ⌈ dout (bool b) ⌉
  𝓕 nothing = init

  {- what runs from a point of a body on -}
  K : List Instr → Jump → List Block → ℕ → Kont
  K is j bs n = ⟦ is ⟧ˢ T⁺ n (⟦ j ⟧ʲ (blocks T⁺ n bs))

  K-mono : ∀ is j bs n → M.MonoK n (K is j bs n) (K is j bs n)
  K-mono is j bs n = M.is-mono n is (code-⊤ is) (M.jump-mono n j (M.blocks-mono n bs (codes-⊤ bs)))

  {- the call stack: a caller runs its rest with the callee's result -}
  𝒦 : Stack → 𝒫 Value → 𝒫 Value
  𝒦 halt D d = d ∈ D
  𝒦 (retK is j bs φ stk) D d =
    Σ[ A ∈ Apx ] Σ[ W ∈ List Value ] (∀ x → Ap (A (var x)) (φ ‼ x)) × mem W ⊆ D
      × d ∈ 𝒦 stk (callD (mem W) (K is j bs (length φ)) (σ̂ A))

  𝒮 : State → 𝒫 Value
  𝒮 (run is j bs stk f φ ρ) d = Σ[ A ∈ Apx ] AL A φ ρ × d ∈ 𝒦 stk (K is j bs (length φ) (σ̂ A) (ρ̂ A) (𝓕 f))

  𝒦-mono : ∀ stk {D E} → D ⊆ E → 𝒦 stk D ⊆ 𝒦 stk E
  𝒦-mono halt D⊆ = D⊆
  𝒦-mono (retK is j bs φ stk) D⊆ d ⟨ A , ⟨ W , ⟨ af , ⟨ W⊆ , r ⟩ ⟩ ⟩ ⟩ =
    ⟨ A , ⟨ W , ⟨ af , ⟨ (λ x x∈ → D⊆ x (W⊆ x x∈)) , r ⟩ ⟩ ⟩ ⟩

  ap-[] : ∀ m → Ap [] m
  ap-[] m = λ _ ()

  {- the stack passes an error on -}
  𝒦-ω : ∀ stk {D} → ω ∈ D → ω ∈ 𝒦 stk D
  𝒦-ω halt ω∈ = ω∈
  𝒦-ω (retK is j bs φ stk) ω∈ =
    ⟨ (λ _ → []) , ⟨ ω ∷ [] , ⟨ (λ x → ap-[] (φ ‼ x)) , ⟨ (λ { _ (here refl) → ω∈ }) , 𝒦-ω stk (inj₁ ⟨ refl , here refl ⟩) ⟩ ⟩ ⟩ ⟩

  Ext : Apx → Apx → Set
  Ext A B = ∀ l → mem (A l) ⊆ mem (B l)

  Ext-refl : ∀ {A} → Ext A A
  Ext-refl l d z = z

  Ext-trans : ∀ {A B C} → Ext A B → Ext B C → Ext A C
  Ext-trans E E' l d d∈ = E' l d (E l d d∈)

  Ext-le : ∀ {n A B F} → Ext A B → M.Le n (σ̂ A) (ρ̂ A) F (σ̂ B) (ρ̂ B) F
  Ext-le E = ⟨ (λ x _ → E (var x)) , ⟨ (λ g → E (reg g)) , (λ _ z → z) ⟩ ⟩

  add : Apx → Loc → List Value → Apx
  add A l V l' with l' ≟L l
  ... | yes _ = A l' ++ V
  ... | no _ = A l'

  clear : Apx → Loc → Apx
  clear A l l' with l' ≟L l
  ... | yes _ = []
  ... | no _ = A l'

  here-⊆ : ∀ {A φ ρ l v} → AL A φ ρ → readM φ ρ l ≡ just v → mem (A l) ⊆ 𝒱 v
  here-⊆ {A} {l = l} al e = subst (Ap (A l)) e (al l)

  add-AL : ∀ {A φ ρ} l V → AL A φ ρ → mem V ⊆ 𝒱m (readM φ ρ l) → AL (add A l V) φ ρ
  add-AL {A} l V al V⊆ l' with l' ≟L l
  ... | yes refl = ++-⊆ (A l) V (al l) V⊆
  ... | no _ = al l'

  add-ext : ∀ A l V → Ext A (add A l V)
  add-ext A l V l' with l' ≟L l
  ... | yes _ = λ d d∈ → ∈-++⁺ˡ d∈
  ... | no _ = λ d z → z

  add-here : ∀ A l V → mem V ⊆ mem (add A l V l)
  add-here A l V with l ≟L l
  ... | yes _ = λ d d∈ → ∈-++⁺ʳ (A l) d∈
  ... | no ne = ⊥-elim (ne refl)

  clear-AL : ∀ {A φ ρ φ' ρ'} d → AL A φ' ρ' → (∀ l → l ≢ d → readM φ' ρ' l ≡ readM φ ρ l) → AL (clear A d) φ ρ
  clear-AL {A} {φ} {ρ} d al oth l with l ≟L d
  ... | yes _ = ap-[] (readM φ ρ l)
  ... | no ne = subst (Ap (A l)) (oth l ne) (al l)

  clear-⊆ : ∀ A d l → l ≢ d → mem (A l) ⊆ mem (clear A d l)
  clear-⊆ A d l ne with l ≟L d
  ... | yes e = ⊥-elim (ne e)
  ... | no _ = λ _ z → z

  {- a part with a value -}
  ext : List Value → Val → List Value
  ext A v = A ++ pt v ∷ []

  ext-⊆ : ∀ A v → mem A ⊆ 𝒱 v → mem (ext A v) ⊆ 𝒱 v
  ext-⊆ A v A⊆ = ++-⊆ A _ A⊆ (λ { _ (here refl) → pt∈ v })

  ext-ne : ∀ A v → ext A v ≢ []
  ext-ne [] v ()
  ext-ne (x ∷ A) v ()

  ext-pt : ∀ A v → pt v ∈ mem (ext A v)
  ext-pt A v = ∈-++⁺ʳ A (here refl)

  ext-val : ∀ A v {D} → mem (ext A v) ⊆ D → val∈ D
  ext-val A v V⊆ = ⟨ pt v , ⟨ V⊆ _ (ext-pt A v) , pt≢ω v ⟩ ⟩

  noerr : ∀ v V → mem V ⊆ 𝒱 v → NoErr V
  noerr v V V⊆ ω∈ = 𝒱-clean v ω (V⊆ ω ω∈) refl

  nopt : ∀ v → NoErr (pt v ∷ [])
  nopt v = noerr v _ (λ { _ (here refl) → pt∈ v })

  dout≢ω : ∀ b → dout (bool b) ≢ ω
  dout≢ω true ()
  dout≢ω false ()

  {- a branch of the jump on a flag that holds one tag -}
  je-in : ∀ {b E F w} → w ∈ 𝒞 ⟨ ⌊ 𝓕 (just b) ⌋ ⇂ ValPayload , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩ → w ∈ 𝒞ᵐ ⟨ 𝓕 (just b) , ⟨ E , ⟨ F , ptt ⟩ ⟩ ⟩
  je-in {b} w∈ = inj₂ ⟨ ⟨ dout (bool b) , ⟨ refl , dout≢ω b ⟩ ⟩ , inj₂ w∈ ⟩

  read-in : ∀ {n σ} x → x < n → σ x ⊆ readD n σ x
  read-in {n} x x< with x <? n
  ... | yes _ = λ _ z → z
  ... | no ¬x< = ⊥-elim (¬x< x<)

  read-out : ∀ {n σ} x → (x < n → ⊥) → ω ∈ readD n σ x
  read-out {n} x ¬x< with x <? n
  ... | yes x< = ⊥-elim (¬x< x<)
  ... | no _ = refl

  checked-in : ∀ {n x D E} → x < n → E ⊆ frameᵐ n x D E
  checked-in {n} {x} x< with x <? n
  ... | yes _ = λ _ z → z
  ... | no ¬x< = ⊥-elim (¬x< x<)

  𝒪-ext : ∀ {n A B} a → Ext A B → 𝒪 T⁺ n (σ̂ A) (ρ̂ A) a ⊆ 𝒪 T⁺ n (σ̂ B) (ρ̂ B) a
  𝒪-ext {n} a E = M.𝒪-mono n a (ok-⊤ a) (λ x _ → E (var x)) (λ g → E (reg g))

  {- the operand a, which holds v, approximated by enough to hold V -}
  grow : ∀ a {φ ρ v} A V → AL A φ ρ → arg φ ρ a ≡ just v → mem V ⊆ 𝒱 v
    → Σ[ B ∈ Apx ] AL B φ ρ × Ext A B × mem V ⊆ 𝒪 T⁺ (length φ) (σ̂ B) (ρ̂ B) a
  grow (loc (var x)) {φ} A V al e V⊆ =
    ⟨ add A (var x) V , ⟨ add-AL (var x) V al (subst (λ m → mem V ⊆ 𝒱m m) (sym e) V⊆) , ⟨ add-ext A (var x) V
    , (λ d d∈ → read-in x (‼-just φ x e) d (add-here A (var x) V d d∈)) ⟩ ⟩ ⟩
  grow (loc (reg g)) A V al e V⊆ =
    ⟨ add A (reg g) V , ⟨ add-AL (reg g) V al (subst (λ m → mem V ⊆ 𝒱m m) (sym e) V⊆) , ⟨ add-ext A (reg g) V , add-here A (reg g) V ⟩ ⟩ ⟩
  grow (imm B k) A V al refl V⊆ = ⟨ A , ⟨ al , ⟨ Ext-refl , V⊆ ⟩ ⟩ ⟩
  grow (label k) A V al refl V⊆ = ⟨ A , ⟨ al , ⟨ Ext-refl , V⊆ ⟩ ⟩ ⟩

  {- the operand holds an element of its value -}
  grow-pt : ∀ a {φ ρ v} A → AL A φ ρ → arg φ ρ a ≡ just v
    → Σ[ B ∈ Apx ] AL B φ ρ × Ext A B × pt v ∈ 𝒪 T⁺ (length φ) (σ̂ B) (ρ̂ B) a
  grow-pt a {v = v} A al e with grow a A (pt v ∷ []) al e (λ { _ (here refl) → pt∈ v })
  ... | ⟨ B , ⟨ alB , ⟨ E , V⊆ ⟩ ⟩ ⟩ = ⟨ B , ⟨ alB , ⟨ E , V⊆ _ (here refl) ⟩ ⟩ ⟩

  {- an operand that the machine cannot read holds ω -}
  grow-ω : ∀ a {φ ρ} A → AL A φ ρ → arg φ ρ a ≡ nothing
    → Σ[ B ∈ Apx ] AL B φ ρ × Ext A B × ω ∈ 𝒪 T⁺ (length φ) (σ̂ B) (ρ̂ B) a
  grow-ω (loc (var x)) {φ} A al e = ⟨ A , ⟨ al , ⟨ Ext-refl , read-out x (‼-err φ x e) ⟩ ⟩ ⟩
  grow-ω (loc (reg g)) {ρ = ρ} A al e =
    ⟨ add A (reg g) (ω ∷ []) , ⟨ add-AL (reg g) (ω ∷ []) al (subst (λ m → mem (ω ∷ []) ⊆ 𝒱m m) (sym e) (λ { _ (here refl) → refl }))
    , ⟨ add-ext A (reg g) (ω ∷ []) , add-here A (reg g) (ω ∷ []) ω (here refl) ⟩ ⟩ ⟩

  grows : ∀ as {φ ρ us} A Gs → AL A φ ρ → Evals φ ρ as us → Pointwise (λ G u → mem G ⊆ 𝒱 u) Gs us
    → Σ[ B ∈ Apx ] AL B φ ρ × Ext A B × Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ (length φ) (σ̂ B) (ρ̂ B) a) as Gs
  grows [] A [] al [] [] = ⟨ A , ⟨ al , ⟨ Ext-refl , [] ⟩ ⟩ ⟩
  grows (a ∷ as) A (G ∷ Gs) al (e ∷ es) (g ∷ gs) with grow a A G al e g
  ... | ⟨ B , ⟨ alB , ⟨ E , G⊆ ⟩ ⟩ ⟩ with grows as B Gs alB es gs
  ...   | ⟨ C , ⟨ alC , ⟨ E' , ps ⟩ ⟩ ⟩ = ⟨ C , ⟨ alC , ⟨ Ext-trans E E' , (λ d d∈ → 𝒪-ext a E' d (G⊆ d d∈)) ∷ ps ⟩ ⟩ ⟩

  {- the empty approximation -}
  A∅ : Apx
  A∅ _ = []

  AL∅ : ∀ {φ ρ} → AL A∅ φ ρ
  AL∅ {φ} {ρ} l = ap-[] (readM φ ρ l)

  {- Writes ----------------------------------------------------------------------}

  {- d := D, where D holds a finite part V of v as large as what d holds
     after the step -}
  write : ∀ d {v φ ρ φ' ρ' A' A D κ F} → Put d v φ ρ φ' ρ' → AL A' φ' ρ'
    → (∀ l → l ≢ d → mem (A' l) ⊆ mem (A l)) → mem (ext (A' d) v) ⊆ D → M.MonoK (length φ) κ κ
    → κ (σ̂ A') (ρ̂ A') F ⊆ putD (length φ) d D κ (σ̂ A) (ρ̂ A) F
  write (var x) {v} {A' = A'} {A} P al' oth V⊆ mκ w w∈ =
    checked-in (p-inside P refl) w
      (letᵐ-intro (ext-ne _ v) (Con⇒≈ V (𝒱-con v) V⊆v) noe V⊆ (mκ ⟨ s , ⟨ (λ g → oth (reg g) (λ ())) , (λ _ z → z) ⟩ ⟩ w w∈))
    where
    V = ext (A' (var x)) v
    V⊆v = ext-⊆ _ v (here-⊆ al' (p-here P))
    noe = noerr v V V⊆v
    s : ∀ y → y < _ → σ̂ A' y ⊆ (σ̂ A [ x ↦ₛ mem V ]) y
    s y _ with y ≟ x
    ... | yes refl = λ d d∈ → ∈-++⁺ˡ d∈
    ... | no ne = oth (var y) (λ { refl → ne refl })
  write (reg g) {v} {A' = A'} {A} {D} P al' oth V⊆ mκ w w∈ =
    inj₂ ⟨ ext-val (A' (reg g)) v V⊆ , mκ ⟨ (λ x _ → oth (var x) (λ ())) , ⟨ r , (λ _ z → z) ⟩ ⟩ w w∈ ⟩
    where
    r : ∀ g' → ρ̂ A' g' ⊆ (ρ̂ A [ g ≔ D ]) g'
    r g' with g' ≟R g
    ... | yes refl = subst (λ X → ρ̂ A' g ⊆ X) (sym (≔-here (ρ̂ A) g D)) (λ d d∈ → V⊆ d (∈-++⁺ˡ d∈))
    ... | no ne = subst (λ X → ρ̂ A' g' ⊆ X) (sym (≔-other (ρ̂ A) g D g' ne)) (oth (reg g') (λ { refl → ne refl }))

  {- what the operands of an instruction must hold so that it writes, or
     sets the flag to, enough of the value written -}
  PutH : Frame → MRegs → Maybe Val → (Store → SRegs → 𝒫 Value) → Set
  PutH φ ρ m Dfun = ∀ {v} A₀ V → m ≡ just v → AL A₀ φ ρ → mem V ⊆ 𝒱 v
    → Σ[ A ∈ Apx ] AL A φ ρ × Ext A₀ A × mem V ⊆ Dfun (σ̂ A) (ρ̂ A)

  FlagH : Frame → MRegs → Maybe Bool → (Store → SRegs → 𝒫 Value) → Set
  FlagH φ ρ m Ffun = ∀ {b} A₀ → m ≡ just b → AL A₀ φ ρ → Σ[ A ∈ Apx ] AL A φ ρ × Ext A₀ A × 𝓕 (just b) ⊆ Ffun (σ̂ A) (ρ̂ A)

  {- and so that the error of the machine is ω -}
  ErrH : Frame → MRegs → Maybe Val → (Store → SRegs → 𝒫 Value) → Set
  ErrH φ ρ m Dfun = m ≡ nothing → Σ[ A ∈ Apx ] AL A φ ρ × ω ∈ Dfun (σ̂ A) (ρ̂ A)

  {- a step that writes d -}
  put-step : ∀ d (Dfun : Store → SRegs → 𝒫 Value) {m φ ρ stk is j bs f s'}
    → putM d m φ ρ (run is j bs stk f) ≡ next s' → PutH φ ρ m Dfun
    → 𝒮 s' ⊆ λ w → Σ[ A ∈ Apx ] AL A φ ρ
                × w ∈ 𝒦 stk (putD (length φ) d (Dfun (σ̂ A) (ρ̂ A)) (K is j bs (length φ)) (σ̂ A) (ρ̂ A) (𝓕 f))
  put-step d Dfun {m} {φ} {stk = stk} {is} {j} {bs} {f} e h w w∈ with put-inv d m e
  ... | ⟨ v , ⟨ φ' , ⟨ ρ' , ⟨ refl , ⟨ refl , P ⟩ ⟩ ⟩ ⟩ ⟩ with w∈
  ...   | ⟨ A' , ⟨ al' , w∈' ⟩ ⟩
        with h (clear A' d) (ext (A' d) v) refl (clear-AL d al' (p-other P)) (ext-⊆ _ v (here-⊆ al' (p-here P)))
  ...     | ⟨ A , ⟨ al , ⟨ E , V⊆ ⟩ ⟩ ⟩ =
    ⟨ A , ⟨ al , 𝒦-mono stk (write d P al' (λ l ne u u∈ → E l u (clear-⊆ A' d l ne u u∈)) V⊆ (K-mono is j bs (length φ))) w
                   (subst (λ n → w ∈ 𝒦 stk (K is j bs n (σ̂ A') (ρ̂ A') (𝓕 f))) (p-len P) w∈') ⟩ ⟩

  {- a step that sets the flag -}
  flag-step : ∀ (Ffun : Store → SRegs → 𝒫 Value) {m φ ρ stk is j bs s'}
    → test m (λ f' → run is j bs stk f' φ ρ) ≡ next s' → FlagH φ ρ m Ffun
    → 𝒮 s' ⊆ λ w → Σ[ A ∈ Apx ] AL A φ ρ × w ∈ 𝒦 stk (flagD (Ffun (σ̂ A) (ρ̂ A)) (K is j bs (length φ)) (σ̂ A) (ρ̂ A))
  flag-step Ffun {m} {φ} {stk = stk} {is} {j} {bs} e h w w∈ with test-inv m e
  ... | ⟨ b , ⟨ refl , refl ⟩ ⟩ with w∈
  ...   | ⟨ A' , ⟨ al' , w∈' ⟩ ⟩ with h A' refl al'
  ...     | ⟨ A , ⟨ al , ⟨ E , F⊆ ⟩ ⟩ ⟩ =
    ⟨ A , ⟨ al , 𝒦-mono stk (λ u u∈ → inj₂ ⟨ ⟨ dout (bool b) , ⟨ F⊆ (dout (bool b)) refl , dout≢ω b ⟩ ⟩
                                     , K-mono is j bs (length φ) ⟨ (λ x _ → E (var x)) , ⟨ (λ g → E (reg g)) , F⊆ ⟩ ⟩ u u∈ ⟩) w w∈' ⟩ ⟩

  {- ω written to d -}
  put-ω : ∀ n d {D κ σ ρ F} → ω ∈ D → ω ∈ putD n d D κ σ ρ F
  put-ω n (var x) ω∈ with x <? n
  ... | yes _ = letᵐ-ω ω∈
  ... | no _ = inj₁ ⟨ refl , ω∈ ⟩
  put-ω n (reg g) ω∈ = inj₁ ⟨ refl , ω∈ ⟩

  {- a write beyond the frame -}
  put-out : ∀ n x {D κ σ ρ F} → (x < n → ⊥) → nonempty D → ω ∈ putD n (var x) D κ σ ρ F
  put-out n x ¬x< ne with x <? n
  ... | yes x< = ⊥-elim (¬x< x<)
  ... | no _ with ne-has ne
  ...   | inj₁ ω∈ = inj₁ ⟨ refl , ω∈ ⟩
  ...   | inj₂ c = inj₂ ⟨ c , refl ⟩

  {- a step that Errs while writing d -}
  put-final : ∀ d (Dfun : Store → SRegs → 𝒫 Value) {m φ ρ is j bs stk f}
    → putM d m φ ρ (run is j bs stk f) ≡ stop o-error → PutH φ ρ m Dfun → ErrH φ ρ m Dfun
    → Σ[ A ∈ Apx ] AL A φ ρ × ω ∈ putD (length φ) d (Dfun (σ̂ A) (ρ̂ A)) (K is j bs (length φ)) (σ̂ A) (ρ̂ A) (𝓕 f)
  put-final d Dfun {m} {φ} {ρ} {is} {j} {bs} {stk} {f} e h eh with put-err d m e
  ... | inj₁ refl with eh refl
  ...   | ⟨ A , ⟨ al , ω∈ ⟩ ⟩ = ⟨ A , ⟨ al , put-ω (length φ) d {Dfun (σ̂ A) (ρ̂ A)} {K is j bs (length φ)} {σ̂ A} {ρ̂ A} {𝓕 f} ω∈ ⟩ ⟩
  put-final d Dfun {m} {φ} {ρ} {is} {j} {bs} {stk} {f} e h eh | inj₂ ⟨ v , ⟨ x , ⟨ refl , ⟨ refl , ¬x< ⟩ ⟩ ⟩ ⟩
      with h A∅ (pt v ∷ []) refl AL∅ (λ { _ (here refl) → pt∈ v })
  ... | ⟨ A , ⟨ al , ⟨ _ , V⊆ ⟩ ⟩ ⟩ = ⟨ A , ⟨ al , put-out (length φ) x {Dfun (σ̂ A) (ρ̂ A)} {K is j bs (length φ)} {σ̂ A} {ρ̂ A} {𝓕 f} ¬x< ⟨ pt v , V⊆ _ (here refl) ⟩ ⟩ ⟩

  {- What the instructions compute ------------------------------------------------}

  vals-cons : ∀ {n D Ds} → Conv D → (∀ i → Conv (nthD Ds i)) → ∀ i → Conv (nthD {suc n} ⟨ D , Ds ⟩ i)
  vals-cons v vs zero = v
  vals-cons v vs (suc i) = vs i

  𝒯-zero : ∀ {m len D Ds d} → m ≡ len → d ∈ D → (∀ j → nonempty (nthD {suc len} ⟨ D , Ds ⟩ j))
    → tup[_]_ {suc m} zero d ∈ 𝒯 (suc len) ⟨ D , Ds ⟩
  𝒯-zero refl d∈ vs = ⟨ refl , ⟨ d∈ , vs ⟩ ⟩

  𝒯-suc : ∀ {len m} {i : Fin m} {D Ds d} → tup[_]_ {m} i d ∈ 𝒯 len Ds → nonempty D
    → tup[_]_ {suc m} (suc i) d ∈ 𝒯 (suc len) ⟨ D , Ds ⟩
  𝒯-suc {zero} ()
  𝒯-suc {suc len} ⟨ refl , ⟨ d∈ , vs ⟩ ⟩ v = ⟨ refl , ⟨ d∈ , (λ { zero → v ; (suc j) → vs j }) ⟩ ⟩

  {- the operands of alloc tuple, approximated by Gs, each with a value -}
  vals-𝒪s : ∀ {n σ ρ} as Gs → Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ n σ ρ a) as Gs → All (λ G → val∈ (mem G)) Gs
    → ∀ i → Conv (nthD (𝒪s T⁺ n σ ρ as) i)
  vals-𝒪s (a ∷ as) (G ∷ Gs) (p ∷ ps) (v ∷ vs) =
    vals-cons {length as} (Conv-mono p v) (vals-𝒪s as Gs ps vs)

  tup-ok : ∀ us V → mem V ⊆ 𝒱 (tup us)
    → Σ[ Gs ∈ List (List Value) ] Pointwise (λ G u → mem G ⊆ 𝒱 u) Gs us × All (λ G → val∈ (mem G)) Gs
      × (∀ {n σ ρ} as → Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ n σ ρ a) as Gs → mem V ⊆ 𝒯 (length as) ⌊ 𝒪s T⁺ n σ ρ as ⌋s)
  tup-ok [] V V⊆ = ⟨ [] , ⟨ [] , ⟨ [] , G ⟩ ⟩ ⟩
    where
    G : ∀ {n σ ρ} as → Pointwise _ as [] → mem V ⊆ 𝒯 (length as) ⌊ 𝒪s T⁺ n σ ρ as ⌋s
    G [] [] z z∈ with V⊆ z z∈
    ... | inj₁ ⟨ refl , _ ⟩ = tt
    ... | inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ refl , () ⟩ ⟩ ⟩ ⟩
  tup-ok (u ∷ us) V V⊆ with tup-ok us (pick tl V) (pick-⊆ tl V tl⊆)
    where
    tl⊆ : ∀ z → z ∈ mem V → mem (tl z) ⊆ 𝒱 (tup us)
    tl⊆ z z∈ with V⊆ z z∈
    ... | inj₂ ⟨ _ , ⟨ zero , ⟨ _ , ⟨ refl , _ ⟩ ⟩ ⟩ ⟩ = λ _ ()
    ... | inj₂ ⟨ _ , ⟨ suc i , ⟨ e , ⟨ refl , a ⟩ ⟩ ⟩ ⟩ = λ { _ (here refl) → inj₂ ⟨ _ , ⟨ i , ⟨ e , ⟨ refl , a ⟩ ⟩ ⟩ ⟩ }
  ... | ⟨ Gs , ⟨ pw , ⟨ vs , T' ⟩ ⟩ ⟩ =
    ⟨ G₀ ∷ Gs , ⟨ G₀⊆ ∷ pw , ⟨ ⟨ pt u , ⟨ here refl , pt≢ω u ⟩ ⟩ ∷ vs , G ⟩ ⟩ ⟩
    where
    G₀ = pt u ∷ pick hd V
    hd⊆ : ∀ z → z ∈ mem V → mem (hd z) ⊆ 𝒱 u
    hd⊆ z z∈ with V⊆ z z∈
    ... | inj₂ ⟨ _ , ⟨ zero , ⟨ _ , ⟨ refl , ⟨ _ , e∈ ⟩ ⟩ ⟩ ⟩ ⟩ = λ { _ (here refl) → e∈ }
    ... | inj₂ ⟨ _ , ⟨ suc i , ⟨ _ , ⟨ refl , _ ⟩ ⟩ ⟩ ⟩ = λ _ ()
    G₀⊆ : mem G₀ ⊆ 𝒱 u
    G₀⊆ = ++-⊆ (pt u ∷ []) (pick hd V) (λ { _ (here refl) → pt∈ u }) (pick-⊆ hd V hd⊆)
    G : ∀ {n σ ρ} as → Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ n σ ρ a) as (G₀ ∷ Gs)
      → mem V ⊆ 𝒯 (length as) ⌊ 𝒪s T⁺ n σ ρ as ⌋s
    G {n} {σ} {ρ} (a ∷ as) (p ∷ ps) z z∈ with V⊆ z z∈
    ... | inj₂ ⟨ _ , ⟨ zero , ⟨ e , ⟨ refl , ⟨ len , _ ⟩ ⟩ ⟩ ⟩ ⟩ =
      𝒯-zero {len = length as} {Ds = ⌊ 𝒪s T⁺ n σ ρ as ⌋s} (sym (trans (Pointwise-length ps) (trans (Pointwise-length pw) len)))
        ⟨ p e (there (pick-∈ hd V z∈ e (here refl))) , 𝒱-clean u e (G₀⊆ e (there (pick-∈ hd V z∈ e (here refl)))) ⟩
        (conv-⌊⌋s (suc (length as)) {𝒪s T⁺ n σ ρ (a ∷ as)} (vals-𝒪s (a ∷ as) (G₀ ∷ Gs) (p ∷ ps) (⟨ pt u , ⟨ here refl , pt≢ω u ⟩ ⟩ ∷ vs)))
    ... | inj₂ ⟨ _ , ⟨ suc i , ⟨ e , ⟨ refl , _ ⟩ ⟩ ⟩ ⟩ =
      𝒯-suc (T' as ps (tup[ i ] e) (pick-∈ tl V z∈ _ (here refl))) (Conv-mono p ⟨ pt u , ⟨ here refl , pt≢ω u ⟩ ⟩)

  {- the operands of alloc sh, approximated by Gs, build enough of the object -}
  build-ok : ∀ sh us {v} → build sh us ≡ just v → ∀ V → mem V ⊆ 𝒱 v
    → Σ[ Gs ∈ List (List Value) ] Pointwise (λ G u → mem G ⊆ 𝒱 u) Gs us
      × (∀ {n σ ρ} as → Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ n σ ρ a) as Gs → mem V ⊆ object T⁺ n σ ρ sh as)
  build-ok pairₛ (u₁ ∷ u₂ ∷ []) refl V V⊆ =
    ⟨ pick fstv V ∷ pick sndv V ∷ [] , ⟨ pick-⊆ fstv V P⊆ ∷ pick-⊆ sndv V Q⊆ ∷ [] , G ⟩ ⟩
    where
    P⊆ : ∀ z → z ∈ mem V → mem (fstv z) ⊆ 𝒱 u₁
    P⊆ z z∈ with V⊆ z z∈
    ... | ⟨ _ , ⟨ _ , ⟨ refl , ⟨ p∈ , _ ⟩ ⟩ ⟩ ⟩ = λ { _ (here refl) → p∈ }
    Q⊆ : ∀ z → z ∈ mem V → mem (sndv z) ⊆ 𝒱 u₂
    Q⊆ z z∈ with V⊆ z z∈
    ... | ⟨ _ , ⟨ _ , ⟨ refl , ⟨ _ , q∈ ⟩ ⟩ ⟩ ⟩ = λ { _ (here refl) → q∈ }
    G : ∀ {n σ ρ} as → Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ n σ ρ a) as (pick fstv V ∷ pick sndv V ∷ [])
      → mem V ⊆ object T⁺ n σ ρ pairₛ as
    G (a ∷ b ∷ []) (pa ∷ pb ∷ []) z z∈ with V⊆ z z∈
    ... | ⟨ p , ⟨ q , ⟨ refl , ⟨ p∈ , q∈ ⟩ ⟩ ⟩ ⟩ =
      inj₂ ⟨ ⟨ p , P∈ ⟩ , inj₂ ⟨ ⟨ q , Q∈ ⟩ , ⟨ P∈ , Q∈ ⟩ ⟩ ⟩
      where P∈ = ⟨ pa p (pick-∈ fstv V z∈ p (here refl)) , 𝒱-clean u₁ p p∈ ⟩
            Q∈ = ⟨ pb q (pick-∈ sndv V z∈ q (here refl)) , 𝒱-clean u₂ q q∈ ⟩
  build-ok tupleₛ us refl V V⊆ with tup-ok us V V⊆
  ... | ⟨ Gs , ⟨ pw , ⟨ vs , G ⟩ ⟩ ⟩ = ⟨ Gs , ⟨ pw , (λ as ps z z∈ → binds-intro (length as) (vals-𝒪s as Gs ps vs) (G as ps z z∈)) ⟩ ⟩
  build-ok inlₛ (u ∷ []) refl V V⊆ = ⟨ pick lft V ∷ [] , ⟨ pick-⊆ lft V P⊆ ∷ [] , G ⟩ ⟩
    where
    P⊆ : ∀ z → z ∈ mem V → mem (lft z) ⊆ 𝒱 u
    P⊆ z z∈ with V⊆ z z∈
    ... | ⟨ _ , ⟨ refl , p∈ ⟩ ⟩ = λ { _ (here refl) → p∈ }
    G : ∀ {n σ ρ} as → Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ n σ ρ a) as (pick lft V ∷ []) → mem V ⊆ object T⁺ n σ ρ inlₛ as
    G (a ∷ []) (pa ∷ []) z z∈ with V⊆ z z∈
    ... | ⟨ p , ⟨ refl , p∈ ⟩ ⟩ = inj₂ ⟨ ⟨ p , P∈ ⟩ , P∈ ⟩
      where P∈ = ⟨ pa p (pick-∈ lft V z∈ p (here refl)) , 𝒱-clean u p p∈ ⟩
  build-ok inrₛ (u ∷ []) refl V V⊆ = ⟨ pick rgt V ∷ [] , ⟨ pick-⊆ rgt V P⊆ ∷ [] , G ⟩ ⟩
    where
    P⊆ : ∀ z → z ∈ mem V → mem (rgt z) ⊆ 𝒱 u
    P⊆ z z∈ with V⊆ z z∈
    ... | ⟨ _ , ⟨ refl , p∈ ⟩ ⟩ = λ { _ (here refl) → p∈ }
    G : ∀ {n σ ρ} as → Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ n σ ρ a) as (pick rgt V ∷ []) → mem V ⊆ object T⁺ n σ ρ inrₛ as
    G (a ∷ []) (pa ∷ []) z z∈ with V⊆ z z∈
    ... | ⟨ p , ⟨ refl , p∈ ⟩ ⟩ = inj₂ ⟨ ⟨ p , P∈ ⟩ , P∈ ⟩
      where P∈ = ⟨ pa p (pick-∈ rgt V z∈ p (here refl)) , 𝒱-clean u p p∈ ⟩

  {- V, each element wrapped by f, is in Y -}
  wrap : ∀ (f : Value → Value) V {X Y : 𝒫 Value} → (∀ x → x ∈ X → f x ∈ Y) → mem V ⊆ X → mem (map f V) ⊆ Y
  wrap f V {Y = Y} h V⊆ y y∈ = G (∈-map⁻ f y∈)
    where
    G : ∀ {y} → Σ[ x ∈ Value ] x ∈ mem V × y ≡ f x → y ∈ Y
    G ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = h x (V⊆ x x∈)

  {- the operand of load fl, approximated by G, takes enough of the field -}
  field-ok : ∀ fl u {v} → get-field fl u ≡ just v → ∀ V → mem V ⊆ 𝒱 v
    → Σ[ G ∈ List Value ] mem G ⊆ 𝒱 u × mem V ⊆ field′ fl (mem G)
  field-ok fstₛ (pair v w) refl V V⊆ =
    ⟨ _ , ⟨ wrap (λ p → ⦅ p , pt w ⦆) V (λ p p∈ → ⟨ _ , ⟨ _ , ⟨ refl , ⟨ p∈ , pt∈ w ⟩ ⟩ ⟩ ⟩) V⊆
        , (λ p p∈ → inj₂ ⟨ ⟨ _ , ⟨ ∈-map⁺ _ p∈ , (λ ()) ⟩ ⟩ , inj₂ ⟨ _ , ⟨ ∈-map⁺ _ p∈ , (λ ()) ⟩ ⟩ ⟩) ⟩ ⟩
  field-ok sndₛ (pair v w) refl V V⊆ =
    ⟨ _ , ⟨ wrap (λ q → ⦅ pt v , q ⦆) V (λ q q∈ → ⟨ _ , ⟨ _ , ⟨ refl , ⟨ pt∈ v , q∈ ⟩ ⟩ ⟩ ⟩) V⊆
        , (λ q q∈ → inj₂ ⟨ ⟨ _ , ⟨ ∈-map⁺ _ q∈ , (λ ()) ⟩ ⟩ , inj₂ ⟨ _ , ⟨ ∈-map⁺ _ q∈ , (λ ()) ⟩ ⟩ ⟩) ⟩ ⟩
  field-ok (getₛ i) (tup us) e V V⊆ =
    ⟨ _ , ⟨ wrap (tup[ i ]_) V (λ d d∈ → inj₂ ⟨ _ , ⟨ i , ⟨ d , ⟨ refl , proj-AtV i us e d d∈ ⟩ ⟩ ⟩ ⟩) V⊆
        , (λ d d∈ → inj₂ ⟨ ⟨ _ , ⟨ ∈-map⁺ _ d∈ , (λ ()) ⟩ ⟩ , inj₂ ⟨ ∈-map⁺ _ d∈ , (λ ()) ⟩ ⟩) ⟩ ⟩
  field-ok payload (T.inl v) refl V V⊆ =
    ⟨ _ , ⟨ wrap left V (λ d d∈ → ⟨ d , ⟨ refl , d∈ ⟩ ⟩) V⊆ , (λ d d∈ → inj₂ ⟨ ⟨ _ , ⟨ ∈-map⁺ left d∈ , (λ ()) ⟩ ⟩ , inj₂ (inj₁ ⟨ ⟨ ∈-map⁺ left d∈ , (λ ()) ⟩ , 𝒱-clean v d (V⊆ d d∈) ⟩) ⟩) ⟩ ⟩
  field-ok payload (T.inr v) refl V V⊆ =
    ⟨ _ , ⟨ wrap right V (λ d d∈ → ⟨ d , ⟨ refl , d∈ ⟩ ⟩) V⊆ , (λ d d∈ → inj₂ ⟨ ⟨ _ , ⟨ ∈-map⁺ right d∈ , (λ ()) ⟩ ⟩ , inj₂ (inj₂ ⟨ ⟨ ∈-map⁺ right d∈ , (λ ()) ⟩ , 𝒱-clean v d (V⊆ d d∈) ⟩) ⟩) ⟩ ⟩

  {- the two integers of a primitive -}
  prim-ok : ∀ p v w {o} → δ? p (obs v) (obs w) ≡ just o
    → Σ[ n ∈ _ ] Σ[ m ∈ _ ] dconst {Int} n ∈ 𝒱 v × dconst {Int} m ∈ 𝒱 w × o ≡ δ p n m
  prim-ok p v w e with δ?-inv p (obs v) (obs w) e
  ... | ⟨ n , ⟨ m , ⟨ ov , ⟨ ow , refl ⟩ ⟩ ⟩ ⟩ = ⟨ n , ⟨ m , ⟨ int-in v ov , ⟨ int-in w ow , refl ⟩ ⟩ ⟩ ⟩

  {- the code of the definition that a call runs, and the older ones -}
  callee : ∀ k {b} → global ds k ≡ just b
    → Σ[ Ns ∈ List Body ] table ds k ≡ codeD (table Ns) b × (∀ j → j < length Ns → table ds j ≡ table Ns j)
       × BodyOK (length Ns) b
  callee k {b} eg with global-split k eg
  ... | ⟨ xs , ⟨ Ns , ⟨ e , refl ⟩ ⟩ ⟩ =
    ⟨ Ns , ⟨ trans (cong (λ L → table L (length Ns)) e) (table-at xs b Ns)
    , ⟨ (λ j j< → trans (cong (λ L → table L j) (trans e (sym (++-assoc xs [ b ] Ns)))) (table-agree (xs ++ [ b ]) Ns j j<))
    , proj₁ (DefsWF-suffix xs (subst DefsWF e wfd)) ⟩ ⟩ ⟩

  ap-zeros : ∀ A m x → x < m → Ap A (zeros m ‼ x) → mem A ⊆ zerosD x
  ap-zeros A m x x< ap rewrite replicate-‼ m {const Int Data.Integer.0ℤ} x x< = ap

  callq-inv : ∀ m {stk ρ s'} → callq? ds m stk ρ ≡ next s'
    → Σ[ k ∈ ℕ ] Σ[ n ∈ ℕ ] Σ[ bs ∈ List Block ] Σ[ b ∈ Block ] Σ[ e₁ ∈ Val ] Σ[ e₂ ∈ Val ]
       m ≡ just (code k) × global ds k ≡ just (body n bs b) × ρ rdi ≡ just e₁ × ρ rsi ≡ just e₂
       × s' ≡ run (Block.instrs b) (Block.jump b) bs stk nothing (zeros (2 + (n ∸ 2))) (regs nothing (just e₁) (just e₂))
  callq-inv (just (code k)) {ρ = ρ} e with global ds k in eg | ρ rdi | ρ rsi
  callq-inv (just (code k)) refl | just (body n bs b) | just v₁ | just v₂ =
    ⟨ k , ⟨ n , ⟨ bs , ⟨ b , ⟨ v₁ , ⟨ v₂ , ⟨ refl , ⟨ eg , ⟨ refl , ⟨ refl , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  callq-inv (just (code k)) () | just _ | just _ | nothing
  callq-inv (just (code k)) () | just _ | nothing | _
  callq-inv (just (code k)) () | nothing | _ | _

  {- the registers a caller continues with -}
  rax-only : List Value → Apx
  rax-only W (reg rax) = W
  rax-only W _ = []

  {- callq: the callee's approximation gives the entries X ↦ (Y ↦ w) of
     its code that the caller applies -}
  call-step : ∀ a {is j bs stk f φ ρ s'} → callq? ds (arg φ ρ a) (retK is j bs φ stk) ρ ≡ next s'
    → 𝒮 s' ⊆ 𝒮 (run (callq a ∷ is) j bs stk f φ ρ)
  call-step a {is} {j} {bs} {stk} {f} {φ} {ρ} e w w∈ with callq-inv (arg φ ρ a) e
  ... | ⟨ k , ⟨ m , ⟨ bbs , ⟨ bst , ⟨ e₁ , ⟨ e₂ , ⟨ ea , ⟨ eg , ⟨ er₁ , ⟨ er₂ , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ with w∈
  ... | ⟨ A' , ⟨ al' , ⟨ A'' , ⟨ W , ⟨ af , ⟨ W⊆ , w∈' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ with callee k eg
  ... | ⟨ Ns , ⟨ et , ⟨ agree , c ∷ cs ⟩ ⟩ ⟩
      with grows (loc (reg rdi) ∷ loc (reg rsi) ∷ a ∷ []) A₀ (X ∷ Y ∷ map entry W ∷ []) al₀
                 (er₁ ∷ er₂ ∷ ea ∷ []) (X⊆ ∷ Y⊆ ∷ entries ∷ [])
    where
    A₀ : Apx
    A₀ (var x) = A'' (var x)
    A₀ (reg g) = []
    al₀ : AL A₀ φ ρ
    al₀ (var x) = af x
    al₀ (reg g) = ap-[] (ρ g)
    X = ext (A' (reg rdi)) e₁
    Y = ext (A' (reg rsi)) e₂
    X⊆ = ext-⊆ _ e₁ (here-⊆ al' refl)
    Y⊆ = ext-⊆ _ e₂ (here-⊆ al' refl)
    entry : Value → Value
    entry w = X ↦ (Y ↦ w)
    TT : ∀ k' → k' < length Ns → T⁺ k' ⊆ table Ns k'
    TT k' k'< x x∈ = subst (λ T → x ∈ T) (agree k' k'<) x∈
    regs-le : ∀ g → ρ̂ A' g ⊆ argsD (mem X) (mem Y) g
    regs-le rax = al' (reg rax)
    regs-le rdi = λ d d∈ → ∈-++⁺ˡ d∈
    regs-le rsi = λ d d∈ → ∈-++⁺ˡ d∈
    runs : ∀ w → w ∈ mem W → w ∈ runD (table Ns) (2 ⊔ m) (body m bbs bst) zerosD (argsD (mem X) (mem Y)) init
    runs w w∈W = Mono.body-mono TT (2 ⊔ m) m bbs bst (c ∷ cs)
      ⟨ (λ x x< → ap-zeros (A' (var x)) (2 + (m ∸ 2)) x (subst (x <_) (length-replicate (2 + (m ∸ 2))) (subst (x <_) (sym (frame-size m)) x<)) (al' (var x)))
      , ⟨ regs-le , (λ _ z → z) ⟩ ⟩ w
      (subst (λ n → w ∈ K (Block.instrs bst) (Block.jump bst) bbs n (σ̂ A') (ρ̂ A') init) (frame-size m) (W⊆ w w∈W))
    entries : mem (map entry W) ⊆ 𝒱 (code k)
    entries x x∈ with ∈-map⁻ entry x∈
    ... | ⟨ w , ⟨ w∈W , refl ⟩ ⟩ =
      subst (λ T → entry w ∈ T) (sym et)
        (ΛΛᵐ-entry {F = λ X Y → runD (table Ns) (2 ⊔ m) (body m bbs bst) zerosD (argsD X Y) init} (runs w w∈W) (ext-ne _ e₁) (Con⇒≈ X (𝒱-con e₁) X⊆) (noerr e₁ X X⊆)
                                (ext-ne _ e₂) (Con⇒≈ Y (𝒱-con e₂) Y⊆) (noerr e₂ Y Y⊆))
  ... | ⟨ B , ⟨ alB , ⟨ E , X⊆B ∷ Y⊆B ∷ F⊆ ∷ [] ⟩ ⟩ ⟩ =
    ⟨ B , ⟨ alB , 𝒦-mono stk (M.call-mono (length φ) W⊆R (K-mono is j bs (length φ)) (λ x _ → E (var x))) w w∈' ⟩ ⟩
    where
    W⊆R : mem W ⊆ callᵐ ⟨ 𝒪 T⁺ (length φ) (σ̂ B) (ρ̂ B) a , ⟨ ρ̂ B rdi , ⟨ ρ̂ B rsi , ptt ⟩ ⟩ ⟩
    W⊆R w w∈W = callᵐ-intro (F⊆ _ (∈-map⁺ _ w∈W)) (ext-ne _ e₁) (ext-ne _ e₂)
      (λ d d∈ → ⟨ X⊆B d d∈ , 𝒱-clean e₁ d (ext-⊆ _ e₁ (here-⊆ al' refl) d d∈) ⟩)
      (λ d d∈ → ⟨ Y⊆B d d∈ , 𝒱-clean e₂ d (ext-⊆ _ e₂ (here-⊆ al' refl) d d∈) ⟩)

  {- Steps shrink the denotation of the state ---------------------------------}

  step-⊆ : ∀ s {s'} → step ds s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
  step-⊆ (run (movq a d ∷ is) j bs stk f φ ρ) e =
    put-step d (λ σ ρ → 𝒪 T⁺ (length φ) σ ρ a) {m = arg φ ρ a} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} {f = f} e λ A₀ V ea al V⊆ → grow a A₀ V al ea V⊆
  step-⊆ (run (subq a d ∷ is) j bs stk f φ ρ) e = put-step d Df {m = Mv} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} {f = f} e h
    where
    Mv = arg φ ρ a >>= λ w → readM φ ρ d >>= λ u → prim? sub u w
    Df = λ σ ρ' → primᵐ sub ⟨ 𝒪 T⁺ (length φ) σ ρ' (loc d) , ⟨ 𝒪 T⁺ (length φ) σ ρ' a , ptt ⟩ ⟩
    h : PutH φ ρ Mv Df
    h A₀ V em al V⊆ with bind-inv (arg φ ρ a) em
    ... | ⟨ w , ⟨ ea , em' ⟩ ⟩ with bind-inv (readM φ ρ d) em'
    ... | ⟨ u , ⟨ ed , ep ⟩ ⟩ with mmap-inv out (δ? sub (obs u) (obs w)) ep
    ... | ⟨ o , ⟨ eo , refl ⟩ ⟩ with prim-ok sub u w eo
    ... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ with grow (loc d) A₀ (dconst n ∷ []) al ed (λ { _ (here refl) → n∈ })
    ... | ⟨ B , ⟨ alB , ⟨ E , n⊆ ⟩ ⟩ ⟩ with grow a B (dconst m ∷ []) alB ea (λ { _ (here refl) → m∈ })
    ... | ⟨ C , ⟨ alC , ⟨ E' , m⊆ ⟩ ⟩ ⟩ =
      ⟨ C , ⟨ alC , ⟨ Ext-trans E E'
      , (λ x x∈ → prim-in sub (𝒪-ext (loc d) E' _ (n⊆ _ (here refl))) (m⊆ _ (here refl)) (𝒱-out _ x (V⊆ x x∈))) ⟩ ⟩ ⟩
  step-⊆ (run (cmpq a₂ a₁ ∷ is) j bs stk f φ ρ) e = flag-step Ff {m = Mv} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} e h
    where
    Mv = arg φ ρ a₁ >>= λ v → arg φ ρ a₂ >>= λ w → cmp v w
    Ff = λ σ ρ' → primᵐ eq ⟨ 𝒪 T⁺ (length φ) σ ρ' a₁ , ⟨ 𝒪 T⁺ (length φ) σ ρ' a₂ , ptt ⟩ ⟩
    h : FlagH φ ρ Mv Ff
    h A₀ em al with bind-inv (arg φ ρ a₁) em
    ... | ⟨ v , ⟨ e₁ , em' ⟩ ⟩ with bind-inv (arg φ ρ a₂) em'
    ... | ⟨ w , ⟨ e₂ , ec ⟩ ⟩ with prim-ok eq v w (truth-inv _ ec)
    ... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , eo ⟩ ⟩ ⟩ ⟩ with grow a₁ A₀ (dconst n ∷ []) al e₁ (λ { _ (here refl) → n∈ })
    ... | ⟨ B , ⟨ alB , ⟨ E , n⊆ ⟩ ⟩ ⟩ with grow a₂ B (dconst m ∷ []) alB e₂ (λ { _ (here refl) → m∈ })
    ... | ⟨ C , ⟨ alC , ⟨ E' , m⊆ ⟩ ⟩ ⟩ =
      ⟨ C , ⟨ alC , ⟨ Ext-trans E E'
      , (λ { x refl → prim-in eq (𝒪-ext a₁ E' _ (n⊆ _ (here refl))) (m⊆ _ (here refl)) (cong dout eo) }) ⟩ ⟩ ⟩
  step-⊆ (run (sete d ∷ is) j bs stk (just b) φ ρ) e =
    put-step d (λ _ _ → 𝓕 (just b)) {m = just (bit b)} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} {f = just b} e
      λ { A₀ V refl al V⊆ → ⟨ A₀ , ⟨ al , ⟨ Ext-refl , (λ x x∈ → 𝒱-out (bool b) x (V⊆ x x∈)) ⟩ ⟩ ⟩ }
  step-⊆ (run (testinl a ∷ is) j bs stk f φ ρ) e = flag-step Ff {m = arg φ ρ a >>= is-inl} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} e h
    where
    Ff = λ σ ρ' → isinlᵐ (𝒪 T⁺ (length φ) σ ρ' a)
    h : FlagH φ ρ (arg φ ρ a >>= is-inl) Ff
    h A₀ em al with bind-inv (arg φ ρ a) em
    ... | ⟨ T.inl u , ⟨ ea , refl ⟩ ⟩ with grow a A₀ (left (pt u) ∷ []) al ea (λ { _ (here refl) → ⟨ _ , ⟨ refl , pt∈ u ⟩ ⟩ })
    ...   | ⟨ B , ⟨ alB , ⟨ E , l⊆ ⟩ ⟩ ⟩ = ⟨ B , ⟨ alB , ⟨ E , (λ { x refl → inj₂ ⟨ ⟨ _ , ⟨ l⊆ _ (here refl) , (λ ()) ⟩ ⟩ , inj₂ (inj₁ ⟨ _ , ⟨ ⟨ l⊆ _ (here refl) , (λ ()) ⟩ , refl ⟩ ⟩) ⟩ }) ⟩ ⟩ ⟩
    h A₀ em al | ⟨ T.inr u , ⟨ ea , refl ⟩ ⟩ with grow a A₀ (right (pt u) ∷ []) al ea (λ { _ (here refl) → ⟨ _ , ⟨ refl , pt∈ u ⟩ ⟩ })
    ...   | ⟨ B , ⟨ alB , ⟨ E , r⊆ ⟩ ⟩ ⟩ = ⟨ B , ⟨ alB , ⟨ E , (λ { x refl → inj₂ ⟨ ⟨ _ , ⟨ r⊆ _ (here refl) , (λ ()) ⟩ ⟩ , inj₂ (inj₂ ⟨ _ , ⟨ ⟨ r⊆ _ (here refl) , (λ ()) ⟩ , refl ⟩ ⟩) ⟩ }) ⟩ ⟩ ⟩
  step-⊆ (run (alloc sh as d ∷ is) j bs stk f φ ρ) e = put-step d Df {m = args φ ρ [] as (build sh)} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} {f = f} e h
    where
    Df = λ σ ρ' → object T⁺ (length φ) σ ρ' sh as
    h : PutH φ ρ (args φ ρ [] as (build sh)) Df
    h A₀ V em al V⊆ with args-inv [] as em
    ... | ⟨ us , ⟨ es , eb ⟩ ⟩ with build-ok sh us eb V V⊆
    ... | ⟨ Gs , ⟨ pw , obj ⟩ ⟩ with grows as A₀ Gs al es pw
    ... | ⟨ B , ⟨ alB , ⟨ E , ps ⟩ ⟩ ⟩ = ⟨ B , ⟨ alB , ⟨ E , obj as ps ⟩ ⟩ ⟩
  step-⊆ (run (load fl a d ∷ is) j bs stk f φ ρ) e = put-step d Df {m = arg φ ρ a >>= get-field fl} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} {f = f} e h
    where
    Df = λ σ ρ' → field′ fl (𝒪 T⁺ (length φ) σ ρ' a)
    h : PutH φ ρ (arg φ ρ a >>= get-field fl) Df
    h A₀ V em al V⊆ with bind-inv (arg φ ρ a) em
    ... | ⟨ u , ⟨ ea , eg ⟩ ⟩ with field-ok fl u eg V V⊆
    ... | ⟨ G , ⟨ G⊆ , V⊆' ⟩ ⟩ with grow a A₀ G al ea G⊆
    ... | ⟨ B , ⟨ alB , ⟨ E , G⊆' ⟩ ⟩ ⟩ = ⟨ B , ⟨ alB , ⟨ E , (λ x x∈ → M.field-mono (length φ) fl G⊆' x (V⊆' x x∈)) ⟩ ⟩ ⟩
  step-⊆ (run (callq a ∷ is) j bs stk f φ ρ) e = call-step a {is} {j} {bs} {stk} {f} {φ} {ρ} e
  step-⊆ (run [] retq bs halt f φ ρ) e with ρ rax
  step-⊆ (run [] retq bs halt f φ ρ) () | just v
  step-⊆ (run [] retq bs halt f φ ρ) () | nothing
  step-⊆ (run [] retq bs (retK is j bs' φ' stk) f φ ρ) e w w∈ with ρ rax in er
  step-⊆ (run [] retq bs (retK is j bs' φ' stk) f φ ρ) refl w ⟨ A' , ⟨ al' , w∈ ⟩ ⟩ | just v =
    ⟨ rax-only W , ⟨ al , ⟨ A' , ⟨ W , ⟨ (λ x → al' (var x)) , ⟨ (λ _ z → z)
    , 𝒦-mono stk (λ u u∈ → inj₂ ⟨ ext-val (A' (reg rax)) v (λ _ z → z)
                                 , K-mono is j bs' (length φ') ⟨ (λ _ _ _ z → z) , ⟨ r , (λ _ z → z) ⟩ ⟩ u u∈ ⟩) w w∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    W = ext (A' (reg rax)) v
    al : AL (rax-only W) φ ρ
    al (reg rax) = subst (Ap W) (sym er) (ext-⊆ _ v (here-⊆ al' refl))
    al (reg rdi) = ap-[] (ρ rdi)
    al (reg rsi) = ap-[] (ρ rsi)
    al (var x) = ap-[] (φ ‼ x)
    r : ∀ g → ρ̂ A' g ⊆ called (mem W) g
    r rax = λ d d∈ → ∈-++⁺ˡ d∈
    r rdi = al' (reg rdi)
    r rsi = al' (reg rsi)
  step-⊆ (run [] retq bs (retK is j bs' φ' stk) f φ ρ) () w w∈ | nothing
  step-⊆ (run [] (jmp l) bs stk f φ ρ) e w w∈ with goto-inv (block-at bs l) e
  ... | ⟨ b , ⟨ bs' , ⟨ eb , refl ⟩ ⟩ ⟩ with w∈
  ... | ⟨ A , ⟨ al , w∈' ⟩ ⟩ =
    ⟨ A , ⟨ al , subst (λ B → w ∈ 𝒦 stk (B (σ̂ A) (ρ̂ A) (𝓕 f))) (sym (blocks-at bs l eb)) w∈' ⟩ ⟩
  step-⊆ (run [] (je l₁ l₂) bs stk (just true) φ ρ) e w w∈ with goto-inv (block-at bs l₁) e
  ... | ⟨ b , ⟨ bs' , ⟨ eb , refl ⟩ ⟩ ⟩ with w∈
  ... | ⟨ A , ⟨ al , w∈' ⟩ ⟩ =
    ⟨ A , ⟨ al , 𝒦-mono stk (λ u u∈ → je-in {E = (λ _ → blocks T⁺ (length φ) bs l₁ (σ̂ A) (ρ̂ A) (𝓕 (just true)))} {F = (λ _ → blocks T⁺ (length φ) bs l₂ (σ̂ A) (ρ̂ A) (𝓕 (just true)))} (inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ refl , (λ ()) ⟩ , (λ ()) ⟩ })
                               , ⟨ subst (λ B → u ∈ B (σ̂ A) (ρ̂ A) (𝓕 (just true))) (sym (blocks-at bs l₁ eb)) u∈ , ≈-single ⟩ ⟩ ⟩ ⟩)) w w∈' ⟩ ⟩
  step-⊆ (run [] (je l₁ l₂) bs stk (just false) φ ρ) e w w∈ with goto-inv (block-at bs l₂) e
  ... | ⟨ b , ⟨ bs' , ⟨ eb , refl ⟩ ⟩ ⟩ with w∈
  ... | ⟨ A , ⟨ al , w∈' ⟩ ⟩ =
    ⟨ A , ⟨ al , 𝒦-mono stk (λ u u∈ → je-in {E = (λ _ → blocks T⁺ (length φ) bs l₁ (σ̂ A) (ρ̂ A) (𝓕 (just false)))} {F = (λ _ → blocks T⁺ (length φ) bs l₂ (σ̂ A) (ρ̂ A) (𝓕 (just false)))} (inj₂ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ refl , (λ ()) ⟩ , (λ ()) ⟩ })
                               , ⟨ subst (λ B → u ∈ B (σ̂ A) (ρ̂ A) (𝓕 (just false))) (sym (blocks-at bs l₂ eb)) u∈ , ≈-single ⟩ ⟩ ⟩ ⟩)) w w∈' ⟩ ⟩

  ↠-⊆ : ∀ {s t} → s ↠ t → 𝒮 t ⊆ 𝒮 s
  ↠-⊆ done d d∈ = d∈
  ↠-⊆ {s} (st ∷↠ σ) d d∈ = step-⊆ s st d (↠-⊆ σ d d∈)

  {- States that stop with an error mean ω ----------------------------------------}

  obs≢err : ∀ v → obs v ≢ o-error
  obs≢err (code k) ()
  obs≢err (pair v w) ()
  obs≢err (const B k) ()
  obs≢err (tup vs) ()
  obs≢err (T.inl v) ()
  obs≢err (T.inr v) ()

  stop-inj : ∀ {o o'} → stop {S = State} o ≡ stop o' → o ≡ o'
  stop-inj refl = refl

  {- an error of the rest of a body, in an approximation of the state -}
  ErrIn : State → Set
  ErrIn (run is j bs stk f φ ρ) = Σ[ A ∈ Apx ] AL A φ ρ × ω ∈ K is j bs (length φ) (σ̂ A) (ρ̂ A) (𝓕 f)

  err-state : ∀ s → ErrIn s → ω ∈ 𝒮 s
  err-state (run is j bs stk f φ ρ) ⟨ A , ⟨ al , ω∈ ⟩ ⟩ = ⟨ A , ⟨ al , 𝒦-ω stk ω∈ ⟩ ⟩

  {- a primitive whose operands the machine reads but cannot apply it to -}
  prim-err : ∀ p a b {φ ρ}
    → (∀ u w → arg φ ρ a ≡ just u → arg φ ρ b ≡ just w → δ? p (obs u) (obs w) ≡ nothing)
    → Σ[ A ∈ Apx ] AL A φ ρ × ω ∈ primᵐ p ⟨ 𝒪 T⁺ (length φ) (σ̂ A) (ρ̂ A) a , ⟨ 𝒪 T⁺ (length φ) (σ̂ A) (ρ̂ A) b , ptt ⟩ ⟩
  prim-err p a b {φ} {ρ} h with arg φ ρ a in ea
  ... | nothing with grow-ω a A∅ AL∅ ea
  ...   | ⟨ A , ⟨ al , ⟨ _ , ω∈ ⟩ ⟩ ⟩ = ⟨ A , ⟨ al , inj₁ ⟨ refl , ω∈ ⟩ ⟩ ⟩
  prim-err p a b {φ} {ρ} h | just u with arg φ ρ b in eb
  ... | nothing with grow-ω b A∅ AL∅ eb
  ...   | ⟨ A , ⟨ al , ⟨ _ , ω∈ ⟩ ⟩ ⟩ with grow-pt a A al ea
  ...     | ⟨ B , ⟨ alB , ⟨ E , u∈ ⟩ ⟩ ⟩ =
    ⟨ B , ⟨ alB , inj₂ ⟨ ⟨ pt u , ⟨ u∈ , pt≢ω u ⟩ ⟩ , inj₁ ⟨ refl , 𝒪-ext b E ω ω∈ ⟩ ⟩ ⟩ ⟩
  prim-err p a b {φ} {ρ} h | just u | just w with grow-pt a A∅ AL∅ ea
  ... | ⟨ A , ⟨ al , ⟨ _ , u∈ ⟩ ⟩ ⟩ with grow-pt b A al eb
  ... | ⟨ B , ⟨ alB , ⟨ E , w∈ ⟩ ⟩ ⟩ with δ?-err p (obs u) (obs w) (h u w refl refl)
  ... | inj₁ ni = ⟨ B , ⟨ alB , inj₂ ⟨ cu , inj₂ ⟨ cw , inj₁ ⟨ refl , ⟨ pt u , ⟨ proj₂ cu , notint-pt u ni ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where cu = ⟨ pt u , ⟨ 𝒪-ext a E _ u∈ , pt≢ω u ⟩ ⟩
          cw = ⟨ pt w , ⟨ w∈ , pt≢ω w ⟩ ⟩
  ... | inj₂ ⟨ _ , ⟨ _ , ni ⟩ ⟩ = ⟨ B , ⟨ alB , inj₂ ⟨ cu , inj₂ ⟨ cw , inj₂ (inj₁ ⟨ refl , ⟨ pt w , ⟨ proj₂ cw , notint-pt w ni ⟩ ⟩ ⟩) ⟩ ⟩ ⟩ ⟩
    where cu = ⟨ pt u , ⟨ 𝒪-ext a E _ u∈ , pt≢ω u ⟩ ⟩
          cw = ⟨ pt w , ⟨ w∈ , pt≢ω w ⟩ ⟩

  {- the operands of alloc, one of which the machine cannot read, or the
     values of which it cannot build an object of shape sh from -}
  args-err : ∀ {φ ρ} acc as {k : List Val → Maybe Val} → args φ ρ acc as k ≡ nothing
    → (Σ[ A ∈ Apx ] AL A φ ρ × Errs (length as) (𝒪s T⁺ (length φ) (σ̂ A) (ρ̂ A) as))
      ⊎ (Σ[ us ∈ List Val ] Evals φ ρ as us × k (reverse acc ++ us) ≡ nothing)
  args-err {φ} {ρ} acc [] {k} e = inj₂ ⟨ [] , ⟨ [] , subst (λ vs → k vs ≡ _) (sym (++-identityʳ' (reverse acc))) e ⟩ ⟩
    where ++-identityʳ' : ∀ (xs : List Val) → xs ++ [] ≡ xs
          ++-identityʳ' [] = refl
          ++-identityʳ' (x ∷ xs) = cong (x ∷_) (++-identityʳ' xs)
  args-err {φ} {ρ} acc (a ∷ as) {k} e with arg φ ρ a in ea
  ... | nothing with grow-ω a A∅ AL∅ ea
  ...   | ⟨ A , ⟨ al , ⟨ _ , ω∈ ⟩ ⟩ ⟩ = inj₁ ⟨ A , ⟨ al , inj₁ ω∈ ⟩ ⟩
  args-err {φ} {ρ} acc (a ∷ as) {k} e | just u with args-err (u ∷ acc) as e
  ... | inj₁ ⟨ A , ⟨ al , er ⟩ ⟩ with grow-pt a A al ea
  ...   | ⟨ B , ⟨ alB , ⟨ E , u∈ ⟩ ⟩ ⟩ =
    inj₁ ⟨ B , ⟨ alB , inj₂ ⟨ ⟨ pt u , ⟨ u∈ , pt≢ω u ⟩ ⟩
                         , errs-mono (length as) (M.𝒪s-mono (length φ) as (all-⊤ as) (λ x _ → E (var x)) (λ g → E (reg g))) er ⟩ ⟩ ⟩
    where all-⊤ : ∀ as → All (OK (λ _ → ⊤)) as
          all-⊤ [] = []
          all-⊤ (a ∷ as) = ok-⊤ a ∷ all-⊤ as
  args-err {φ} {ρ} acc (a ∷ as) {k} e | just u | inj₂ ⟨ us , ⟨ es , e' ⟩ ⟩ =
    inj₂ ⟨ u ∷ us , ⟨ ea ∷ es , subst (λ vs → k vs ≡ _) (++-assoc (reverse acc) [ u ] us)
                                   (subst (λ vs → k (vs ++ us) ≡ _) (Data.List.Properties.unfold-reverse u acc) e') ⟩ ⟩

  object-errs : ∀ {n σ ρ} sh as → Errs (length as) (𝒪s T⁺ n σ ρ as) → ω ∈ object T⁺ n σ ρ sh as
  object-errs pairₛ [] ()
  object-errs pairₛ (a ∷ []) er = refl
  object-errs pairₛ (a ∷ b ∷ []) er = errs-ω 2 {K = pairD} er
  object-errs pairₛ (a ∷ b ∷ c ∷ as) er = refl
  object-errs tupleₛ as er = errs-ω (length as) er
  object-errs inlₛ [] ()
  object-errs inlₛ (a ∷ []) (inj₁ ω∈) = inj₁ ⟨ refl , ω∈ ⟩
  object-errs inlₛ (a ∷ b ∷ as) er = refl
  object-errs inrₛ [] ()
  object-errs inrₛ (a ∷ []) (inj₁ ω∈) = inj₁ ⟨ refl , ω∈ ⟩
  object-errs inrₛ (a ∷ b ∷ as) er = refl

  object-build : ∀ {n σ ρ} sh as us → Pointwise (λ (_ : Arg) (_ : Val) → ⊤) as us → build sh us ≡ nothing → ω ∈ object T⁺ n σ ρ sh as
  object-build pairₛ [] [] [] e = refl
  object-build pairₛ (a ∷ []) (u ∷ []) (_ ∷ []) e = refl
  object-build pairₛ (a ∷ b ∷ []) (u ∷ w ∷ []) (_ ∷ _ ∷ []) ()
  object-build pairₛ (a ∷ b ∷ c ∷ as) _ _ e = refl
  object-build tupleₛ as us _ ()
  object-build inlₛ [] [] [] e = refl
  object-build inlₛ (a ∷ []) (u ∷ []) (_ ∷ []) ()
  object-build inlₛ (a ∷ b ∷ as) _ _ e = refl
  object-build inrₛ [] [] [] e = refl
  object-build inrₛ (a ∷ []) (u ∷ []) (_ ∷ []) ()
  object-build inrₛ (a ∷ b ∷ as) _ _ e = refl

  {- an approximation with ω in register g -}
  reg-ω : ∀ g {φ ρ} A → AL A φ ρ → ρ g ≡ nothing → Σ[ B ∈ Apx ] AL B φ ρ × Ext A B × ω ∈ mem (B (reg g))
  reg-ω g A al e = grow-ω (loc (reg g)) A al e

  final-err : ∀ s → step ds s ≡ stop o-error → ω ∈ 𝒮 s
  final-err s@(run (movq a d ∷ is) j bs stk f φ ρ) e =
    err-state s (put-final d (λ σ ρ' → 𝒪 T⁺ (length φ) σ ρ' a) {m = arg φ ρ a} {is = is} {j} {bs} {stk} {f} e
      (λ A₀ V ea al V⊆ → grow a A₀ V al ea V⊆)
      (λ ea → let r = grow-ω a A∅ AL∅ ea in ⟨ proj₁ r , ⟨ proj₁ (proj₂ r) , proj₂ (proj₂ (proj₂ r)) ⟩ ⟩))
  final-err s@(run (subq a d ∷ is) j bs stk f φ ρ) e =
    err-state s (put-final d Df {m = Mv} {is = is} {j} {bs} {stk} {f} e h eh)
    where
    Mv = arg φ ρ a >>= λ w → readM φ ρ d >>= λ u → prim? sub u w
    Df = λ σ ρ' → primᵐ sub ⟨ 𝒪 T⁺ (length φ) σ ρ' (loc d) , ⟨ 𝒪 T⁺ (length φ) σ ρ' a , ptt ⟩ ⟩
    h : PutH φ ρ Mv Df
    h A₀ V em al V⊆ with bind-inv (arg φ ρ a) em
    ... | ⟨ w , ⟨ ea , em' ⟩ ⟩ with bind-inv (readM φ ρ d) em'
    ... | ⟨ u , ⟨ ed , ep ⟩ ⟩ with mmap-inv out (δ? sub (obs u) (obs w)) ep
    ... | ⟨ o , ⟨ eo , refl ⟩ ⟩ with prim-ok sub u w eo
    ... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ with grow (loc d) A₀ (dconst n ∷ []) al ed (λ { _ (here refl) → n∈ })
    ... | ⟨ B , ⟨ alB , ⟨ E , n⊆ ⟩ ⟩ ⟩ with grow a B (dconst m ∷ []) alB ea (λ { _ (here refl) → m∈ })
    ... | ⟨ C , ⟨ alC , ⟨ E' , m⊆ ⟩ ⟩ ⟩ =
      ⟨ C , ⟨ alC , ⟨ Ext-trans E E'
      , (λ x x∈ → prim-in sub (𝒪-ext (loc d) E' _ (n⊆ _ (here refl))) (m⊆ _ (here refl)) (𝒱-out _ x (V⊆ x x∈))) ⟩ ⟩ ⟩
    eh : ErrH φ ρ Mv Df
    eh em with arg φ ρ a in ea
    ... | nothing with readM φ ρ d in ed
    ...   | nothing = let r = grow-ω (loc d) A∅ AL∅ ed in
                      ⟨ proj₁ r , ⟨ proj₁ (proj₂ r) , inj₁ ⟨ refl , proj₂ (proj₂ (proj₂ r)) ⟩ ⟩ ⟩
    ...   | just u with grow-ω a A∅ AL∅ ea
    ...     | ⟨ A , ⟨ al , ⟨ _ , ω∈ ⟩ ⟩ ⟩ with grow-pt (loc d) A al ed
    ...       | ⟨ B , ⟨ alB , ⟨ E , u∈ ⟩ ⟩ ⟩ =
      ⟨ B , ⟨ alB , inj₂ ⟨ ⟨ pt u , ⟨ u∈ , pt≢ω u ⟩ ⟩ , inj₁ ⟨ refl , 𝒪-ext a E ω ω∈ ⟩ ⟩ ⟩ ⟩
    eh em | just w = prim-err sub (loc d) a hp
      where
      hp : ∀ u w' → arg φ ρ (loc d) ≡ just u → arg φ ρ a ≡ just w' → δ? sub (obs u) (obs w') ≡ nothing
      hp u w' ed ea' with trans (sym ea) ea'
      ... | refl rewrite ed = mmap-err out _ em
  final-err s@(run (cmpq a₂ a₁ ∷ is) j bs stk f φ ρ) e with test-err (arg φ ρ a₁ >>= λ v → arg φ ρ a₂ >>= λ w → cmp v w) e
  ... | em with prim-err eq a₁ a₂ hp
    where
    hp : ∀ u w → arg φ ρ a₁ ≡ just u → arg φ ρ a₂ ≡ just w → δ? eq (obs u) (obs w) ≡ nothing
    hp u w e₁ e₂ rewrite e₁ | e₂ = cmp-err (obs u) (obs w) em
  ... | ⟨ A , ⟨ al , ω∈ ⟩ ⟩ = err-state s ⟨ A , ⟨ al , inj₁ ⟨ refl , ω∈ ⟩ ⟩ ⟩
  final-err s@(run (sete d ∷ is) j bs stk (just b) φ ρ) e =
    err-state s (put-final d (λ _ _ → 𝓕 (just b)) {m = just (bit b)} {is = is} {j} {bs} {stk} {just b} e
      (λ { A₀ V refl al V⊆ → ⟨ A₀ , ⟨ al , ⟨ Ext-refl , (λ x x∈ → 𝒱-out (bool b) x (V⊆ x x∈)) ⟩ ⟩ ⟩ })
      (λ ()))
  final-err s@(run (sete d ∷ is) j bs stk nothing φ ρ) refl =
    err-state s ⟨ A∅ , ⟨ AL∅ , put-ω (length φ) d {init} {K is j bs (length φ)} {σ̂ A∅} {ρ̂ A∅} {init} refl ⟩ ⟩
  final-err s@(run (testinl a ∷ is) j bs stk f φ ρ) e with test-err (arg φ ρ a >>= is-inl) e
  ... | em with arg φ ρ a in ea
  ...   | nothing with grow-ω a A∅ AL∅ ea
  ...     | ⟨ A , ⟨ al , ⟨ _ , ω∈ ⟩ ⟩ ⟩ = err-state s ⟨ A , ⟨ al , inj₁ ⟨ refl , inj₁ ⟨ refl , ω∈ ⟩ ⟩ ⟩ ⟩
  final-err s@(run (testinl a ∷ is) j bs stk f φ ρ) e | em | just u with grow-pt a A∅ AL∅ ea
  ... | ⟨ A , ⟨ al , ⟨ _ , u∈ ⟩ ⟩ ⟩ =
    err-state s ⟨ A , ⟨ al , inj₁ ⟨ refl , inj₂ ⟨ ⟨ pt u , ⟨ u∈ , pt≢ω u ⟩ ⟩ , inj₁ ⟨ refl , ⟨ pt u , ⟨ ⟨ u∈ , pt≢ω u ⟩ , notinj-pt u em ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  final-err s@(run (alloc sh as d ∷ is) j bs stk f φ ρ) e =
    err-state s (put-final d Df {m = args φ ρ [] as (build sh)} {is = is} {j} {bs} {stk} {f} e h eh)
    where
    Df = λ σ ρ' → object T⁺ (length φ) σ ρ' sh as
    h : PutH φ ρ (args φ ρ [] as (build sh)) Df
    h A₀ V em al V⊆ with args-inv [] as em
    ... | ⟨ us , ⟨ es , eb ⟩ ⟩ with build-ok sh us eb V V⊆
    ... | ⟨ Gs , ⟨ pw , obj ⟩ ⟩ with grows as A₀ Gs al es pw
    ... | ⟨ B , ⟨ alB , ⟨ E , ps ⟩ ⟩ ⟩ = ⟨ B , ⟨ alB , ⟨ E , obj as ps ⟩ ⟩ ⟩
    triv : ∀ {as us} → Evals φ ρ as us → Pointwise (λ _ _ → ⊤) as us
    triv [] = []
    triv (_ ∷ es) = tt ∷ triv es
    eh : ErrH φ ρ (args φ ρ [] as (build sh)) Df
    eh em with args-err [] as em
    ... | inj₁ ⟨ A , ⟨ al , er ⟩ ⟩ = ⟨ A , ⟨ al , object-errs sh as er ⟩ ⟩
    ... | inj₂ ⟨ us , ⟨ es , eb ⟩ ⟩ = ⟨ A∅ , ⟨ AL∅ , object-build sh as us (triv es) eb ⟩ ⟩
  final-err s@(run (load fl a d ∷ is) j bs stk f φ ρ) e =
    err-state s (put-final d Df {m = arg φ ρ a >>= get-field fl} {is = is} {j} {bs} {stk} {f} e h eh)
    where
    Df = λ σ ρ' → field′ fl (𝒪 T⁺ (length φ) σ ρ' a)
    h : PutH φ ρ (arg φ ρ a >>= get-field fl) Df
    h A₀ V em al V⊆ with bind-inv (arg φ ρ a) em
    ... | ⟨ u , ⟨ ea , eg ⟩ ⟩ with field-ok fl u eg V V⊆
    ... | ⟨ G , ⟨ G⊆ , V⊆' ⟩ ⟩ with grow a A₀ G al ea G⊆
    ... | ⟨ B , ⟨ alB , ⟨ E , G⊆' ⟩ ⟩ ⟩ = ⟨ B , ⟨ alB , ⟨ E , (λ x x∈ → M.field-mono (length φ) fl G⊆' x (V⊆' x x∈)) ⟩ ⟩ ⟩
    eh : ErrH φ ρ (arg φ ρ a >>= get-field fl) Df
    eh em with arg φ ρ a in ea
    ... | nothing with grow-ω a A∅ AL∅ ea
    ...   | ⟨ A , ⟨ al , ⟨ _ , ω∈ ⟩ ⟩ ⟩ = ⟨ A , ⟨ al , field-ω fl ω∈ ⟩ ⟩
    eh em | just u with grow-pt a A∅ AL∅ ea
    ... | ⟨ A , ⟨ al , ⟨ _ , u∈ ⟩ ⟩ ⟩ =
      ⟨ A , ⟨ al , M.field-mono (length φ) fl (λ { _ (here refl) → u∈ }) ω (field-err fl u em) ⟩ ⟩
  final-err s@(run (callq a ∷ is) j bs stk f φ ρ) e = err-state s ⟨ proj₁ R , ⟨ proj₁ (proj₂ R) , inj₁ ⟨ refl , proj₂ (proj₂ R) ⟩ ⟩ ⟩
    where
    n = length φ
    Call : Apx → 𝒫 Value
    Call A = callᵐ ⟨ 𝒪 T⁺ n (σ̂ A) (ρ̂ A) a , ⟨ ρ̂ A rdi , ⟨ ρ̂ A rsi , ptt ⟩ ⟩ ⟩
    {- the code is read, and then %rdi and %rsi -}
    regs-err : ∀ {v} → arg φ ρ a ≡ just v → ρ rdi ≡ nothing ⊎ (Σ[ e₁ ∈ Val ] ρ rdi ≡ just e₁ × ρ rsi ≡ nothing)
      → Σ[ A ∈ Apx ] AL A φ ρ × ω ∈ Call A
    regs-err {v} ea (inj₁ r1) with reg-ω rdi {φ} {ρ} A∅ AL∅ r1
    ... | ⟨ A , ⟨ al , ⟨ _ , ω∈ ⟩ ⟩ ⟩ with grow-pt a A al ea
    ... | ⟨ B , ⟨ alB , ⟨ E , v∈ ⟩ ⟩ ⟩ =
      ⟨ B , ⟨ alB , callᵐ-ω (inj₂ ⟨ pt v , ⟨ v∈ , pt≢ω v ⟩ ⟩) (inj₁ (E (reg rdi) ω ω∈)) ⟩ ⟩
    regs-err {v} ea (inj₂ ⟨ e₁ , ⟨ r1 , r2 ⟩ ⟩) with reg-ω rsi {φ} {ρ} A∅ AL∅ r2
    ... | ⟨ A , ⟨ al , ⟨ _ , ω∈ ⟩ ⟩ ⟩ with grow-pt (loc (reg rdi)) {φ} {ρ} A al r1
    ... | ⟨ B , ⟨ alB , ⟨ E , e₁∈ ⟩ ⟩ ⟩ with grow-pt a B alB ea
    ... | ⟨ C , ⟨ alC , ⟨ E' , v∈ ⟩ ⟩ ⟩ =
      ⟨ C , ⟨ alC , callᵐ-ω (inj₂ ⟨ pt v , ⟨ v∈ , pt≢ω v ⟩ ⟩)
                       (inj₂ ⟨ ⟨ pt e₁ , ⟨ E' (reg rdi) _ e₁∈ , pt≢ω e₁ ⟩ ⟩ , E' (reg rsi) ω (E (reg rsi) ω ω∈) ⟩) ⟩ ⟩
    {- %rdi and %rsi are set, and the code is not that of a definition -}
    call-bad : ∀ {v e₁ e₂} → arg φ ρ a ≡ just v → ρ rdi ≡ just e₁ → ρ rsi ≡ just e₂
      → (Σ[ k ∈ ℕ ] v ≡ code k × global ds k ≡ nothing) ⊎ (∀ k → v ≢ code k)
      → Σ[ A ∈ Apx ] AL A φ ρ × ω ∈ Call A
    call-bad {v} {e₁} {e₂} ea r1 r2 bad with grow-pt (loc (reg rdi)) {φ} {ρ} A∅ AL∅ r1
    ... | ⟨ A , ⟨ al , ⟨ _ , e₁∈ ⟩ ⟩ ⟩ with grow-pt (loc (reg rsi)) {φ} {ρ} A al r2
    ... | ⟨ B , ⟨ alB , ⟨ E , e₂∈ ⟩ ⟩ ⟩ with bad
    ... | inj₂ nc with grow-pt a B alB ea
    ...   | ⟨ C , ⟨ alC , ⟨ E' , v∈ ⟩ ⟩ ⟩ =
      ⟨ C , ⟨ alC , inj₂ ⟨ cv , inj₂ ⟨ ⟨ pt e₁ , ⟨ E' (reg rdi) _ (E (reg rdi) _ e₁∈) , pt≢ω e₁ ⟩ ⟩
                       , inj₂ ⟨ ⟨ pt e₂ , ⟨ E' (reg rsi) _ e₂∈ , pt≢ω e₂ ⟩ ⟩ , inj₁ ⟨ refl , ⟨ pt v , ⟨ proj₂ cv , notfun-pt v nc ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
      where cv = ⟨ pt v , ⟨ v∈ , pt≢ω v ⟩ ⟩
    call-bad {v} {e₁} {e₂} ea r1 r2 bad | ⟨ A , ⟨ al , ⟨ _ , e₁∈ ⟩ ⟩ ⟩ | ⟨ B , ⟨ alB , ⟨ E , e₂∈ ⟩ ⟩ ⟩ | inj₁ ⟨ k , ⟨ refl , eg ⟩ ⟩
        with grow a B ((pt e₁ ∷ []) ↦ ((pt e₂ ∷ []) ↦ ω) ∷ []) alB ea (λ { _ (here refl) → subst (λ D → ((pt e₁ ∷ []) ↦ ((pt e₂ ∷ []) ↦ ω)) ∈ D) (sym (global-none k eg))
               (ΛΛᵐ-entry {F = λ _ _ → ⌈ ω ⌉} refl (λ ()) ≈-single (nopt e₁) (λ ()) ≈-single (nopt e₂)) })
    ... | ⟨ C , ⟨ alC , ⟨ E' , F⊆ ⟩ ⟩ ⟩ =
      ⟨ C , ⟨ alC , callᵐ-intro (F⊆ _ (here refl)) (λ ()) (λ ())
                     (λ { _ (here refl) → ⟨ E' (reg rdi) _ (E (reg rdi) _ e₁∈) , pt≢ω e₁ ⟩ })
                     (λ { _ (here refl) → ⟨ E' (reg rsi) _ e₂∈ , pt≢ω e₂ ⟩ }) ⟩ ⟩
    R : Σ[ A ∈ Apx ] AL A φ ρ × ω ∈ Call A
    R with arg φ ρ a in ea
    ... | nothing with grow-ω a A∅ AL∅ ea
    ...   | ⟨ A , ⟨ al , ⟨ _ , ω∈ ⟩ ⟩ ⟩ = ⟨ A , ⟨ al , inj₁ ⟨ refl , ω∈ ⟩ ⟩ ⟩
    R | just v with ρ rdi in r1 | ρ rsi in r2
    ... | nothing | _ = regs-err ea (inj₁ r1)
    ... | just e₁ | nothing = regs-err ea (inj₂ ⟨ e₁ , ⟨ r1 , r2 ⟩ ⟩)
    ... | just e₁ | just e₂ = call-bad ea r1 r2 (bad v e)
      where
      bad : ∀ v → callq? ds (just v) (retK is j bs φ stk) ρ ≡ stop o-error
        → (Σ[ k ∈ ℕ ] v ≡ code k × global ds k ≡ nothing) ⊎ (∀ k → v ≢ code k)
      bad (code k) e' rewrite r1 | r2 with global ds k in eg'
      ... | nothing = inj₁ ⟨ k , ⟨ refl , eg' ⟩ ⟩
      bad (code k) () | just _
      bad (pair _ _) _ = inj₂ λ k ()
      bad (const _ _) _ = inj₂ λ k ()
      bad (tup _) _ = inj₂ λ k ()
      bad (T.inl _) _ = inj₂ λ k ()
      bad (T.inr _) _ = inj₂ λ k ()
  final-err s@(run [] retq bs halt f φ ρ) e with ρ rax in er
  ... | nothing = let R = reg-ω rax {φ} {ρ} A∅ AL∅ er in err-state s ⟨ proj₁ R , ⟨ proj₁ (proj₂ R) , proj₂ (proj₂ (proj₂ R)) ⟩ ⟩
  ... | just v = ⊥-elim (obs≢err v (stop-inj e))
  final-err s@(run [] retq bs (retK _ _ _ _ _) f φ ρ) e with ρ rax in er
  ... | nothing = let R = reg-ω rax {φ} {ρ} A∅ AL∅ er in err-state s ⟨ proj₁ R , ⟨ proj₁ (proj₂ R) , proj₂ (proj₂ (proj₂ R)) ⟩ ⟩
  final-err s@(run [] retq bs (retK _ _ _ _ _) f φ ρ) () | just v
  final-err s@(run [] (jmp l) bs stk f φ ρ) e =
    err-state s ⟨ A∅ , ⟨ AL∅ , subst (λ D → ω ∈ D) (sym (blocks-none bs l (goto-err (block-at bs l) {stk} {f} {φ} {ρ} e) _ _ _)) refl ⟩ ⟩
  final-err s@(run [] (je l₁ l₂) bs stk (just true) φ ρ) e =
    err-state s ⟨ A∅ , ⟨ AL∅ , je-in {E = (λ _ → blocks T⁺ (length φ) bs l₁ (σ̂ A∅) (ρ̂ A∅) (𝓕 (just true)))} {F = (λ _ → blocks T⁺ (length φ) bs l₂ (σ̂ A∅) (ρ̂ A∅) (𝓕 (just true)))} (inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ refl , (λ ()) ⟩ , (λ ()) ⟩ })
      , ⟨ subst (λ D → ω ∈ D) (sym (blocks-none bs l₁ (goto-err (block-at bs l₁) {stk} {just true} {φ} {ρ} e) _ _ _)) refl
        , ≈-single ⟩ ⟩ ⟩ ⟩) ⟩ ⟩
  final-err s@(run [] (je l₁ l₂) bs stk (just false) φ ρ) e =
    err-state s ⟨ A∅ , ⟨ AL∅ , je-in {E = (λ _ → blocks T⁺ (length φ) bs l₁ (σ̂ A∅) (ρ̂ A∅) (𝓕 (just false)))} {F = (λ _ → blocks T⁺ (length φ) bs l₂ (σ̂ A∅) (ρ̂ A∅) (𝓕 (just false)))} (inj₂ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → ⟨ ⟨ refl , (λ ()) ⟩ , (λ ()) ⟩ })
      , ⟨ subst (λ D → ω ∈ D) (sym (blocks-none bs l₂ (goto-err (block-at bs l₂) {stk} {just false} {φ} {ρ} e) _ _ _)) refl
        , ≈-single ⟩ ⟩ ⟩ ⟩) ⟩ ⟩
  final-err s@(run [] (je l₁ l₂) bs stk nothing φ ρ) refl =
    err-state s ⟨ A∅ , ⟨ AL∅ , inj₁ ⟨ refl , refl ⟩ ⟩ ⟩

  {- States that stop with an answer -------------------------------------------}

  private
    put-stop : ∀ d m {φ ρ K o} → putM d m φ ρ K ≡ stop o → o ≡ o-error
    put-stop d nothing refl = refl
    put-stop (var x) (just v) {φ} e with φ [ x ]≔ v
    put-stop (var x) (just v) refl | nothing = refl
    put-stop (var x) (just v) () | just _

    callq-stop : ∀ m {stk ρ o} → callq? ds m stk ρ ≡ stop o → o ≡ o-error
    callq-stop (just (code k)) {ρ = ρ} e with global ds k | ρ rdi | ρ rsi
    callq-stop (just (code k)) () | just (body _ _ _) | just _ | just _
    callq-stop (just (code k)) refl | just _ | just _ | nothing = refl
    callq-stop (just (code k)) refl | just _ | nothing | _ = refl
    callq-stop (just (code k)) refl | nothing | _ | _ = refl
    callq-stop (just (pair _ _)) refl = refl
    callq-stop (just (const _ _)) refl = refl
    callq-stop (just (tup _)) refl = refl
    callq-stop (just (T.inl _)) refl = refl
    callq-stop (just (T.inr _)) refl = refl
    callq-stop nothing refl = refl

    test-stop : ∀ m {K : Maybe Bool → State} {o} → test m K ≡ stop o → o ≡ o-error
    test-stop nothing refl = refl

    goto-stop : ∀ mb {σ f φ ρ o} → goto mb σ f φ ρ ≡ stop o → o ≡ o-error
    goto-stop nothing refl = refl

    err-ans : ∀ {o} → o ≡ o-error → Answer o → ⊥
    err-ans refl ans = ans refl

  {- a state that stops with an answer has an element of its shape -}
  final-shape : ∀ s {o} → step ds s ≡ stop o → Answer o → Σ[ d ∈ Value ] d ∈ 𝒮 s × ShapeOf o d
  final-shape (run (movq a d ∷ is) j bs stk f φ ρ) e ans = ⊥-elim (err-ans (put-stop d (arg φ ρ a) {φ = φ} {ρ = ρ} {K = run is j bs stk f} e) ans)
  final-shape (run (subq a d ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (err-ans (put-stop d (arg φ ρ a >>= λ w → readM φ ρ d >>= λ u → prim? sub u w) {φ = φ} {ρ = ρ} {K = run is j bs stk f} e) ans)
  final-shape (run (cmpq a₂ a₁ ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (err-ans (test-stop (arg φ ρ a₁ >>= λ v → arg φ ρ a₂ >>= λ w → cmp v w) {K = λ f' → run is j bs stk f' φ ρ} e) ans)
  final-shape (run (sete d ∷ is) j bs stk (just b) φ ρ) e ans =
    ⊥-elim (err-ans (put-stop d (just (bit b)) {φ = φ} {ρ = ρ} {K = run is j bs stk (just b)} e) ans)
  final-shape (run (sete d ∷ is) j bs stk nothing φ ρ) refl ans = ⊥-elim (ans refl)
  final-shape (run (testinl a ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (err-ans (test-stop (arg φ ρ a >>= is-inl) {K = λ f' → run is j bs stk f' φ ρ} e) ans)
  final-shape (run (alloc sh as d ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (err-ans (put-stop d (args φ ρ [] as (build sh)) {φ = φ} {ρ = ρ} {K = run is j bs stk f} e) ans)
  final-shape (run (load fl a d ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (err-ans (put-stop d (arg φ ρ a >>= get-field fl) {φ = φ} {ρ = ρ} {K = run is j bs stk f} e) ans)
  final-shape (run (callq a ∷ is) j bs stk f φ ρ) e ans = ⊥-elim (err-ans (callq-stop (arg φ ρ a) {retK is j bs φ stk} {ρ} e) ans)
  final-shape (run [] retq bs halt f φ ρ) e ans with ρ rax in er
  final-shape (run [] retq bs halt f φ ρ) refl ans | just v =
    ⟨ pt v , ⟨ ⟨ rax-only (pt v ∷ []) , ⟨ al , here refl ⟩ ⟩ , pt-shape v ⟩ ⟩
    where
    al : AL (rax-only (pt v ∷ [])) φ ρ
    al (reg rax) = subst (Ap (pt v ∷ [])) (sym er) (λ { _ (here refl) → pt∈ v })
    al (reg rdi) = ap-[] (ρ rdi)
    al (reg rsi) = ap-[] (ρ rsi)
    al (var x) = ap-[] (φ ‼ x)
  final-shape (run [] retq bs halt f φ ρ) refl ans | nothing = ⊥-elim (ans refl)
  final-shape (run [] retq bs (retK is j bs' φ' stk) f φ ρ) e ans with ρ rax
  final-shape (run [] retq bs (retK is j bs' φ' stk) f φ ρ) () ans | just v
  final-shape (run [] retq bs (retK is j bs' φ' stk) f φ ρ) refl ans | nothing = ⊥-elim (ans refl)
  final-shape (run [] (jmp l) bs stk f φ ρ) e ans = ⊥-elim (err-ans (goto-stop (block-at bs l) {stk} {f} {φ} {ρ} e) ans)
  final-shape (run [] (je l₁ l₂) bs stk (just true) φ ρ) e ans = ⊥-elim (err-ans (goto-stop (block-at bs l₁) {stk} {just true} {φ} {ρ} e) ans)
  final-shape (run [] (je l₁ l₂) bs stk (just false) φ ρ) e ans = ⊥-elim (err-ans (goto-stop (block-at bs l₂) {stk} {just false} {φ} {ρ} e) ans)
  final-shape (run [] (je l₁ l₂) bs stk nothing φ ρ) refl ans = ⊥-elim (ans refl)

  {- the start of main, in its approximation, is in the meaning of main -}
  start-⊆ : ∀ n bs b {d} → d ∈ 𝒮 (run (Block.instrs b) (Block.jump b) bs halt nothing (zeros n) (regs (just (const Int Data.Integer.0ℤ)) nothing nothing))
    → d ∈ ⟦ program ds (body n bs b) ⟧ₚ
  start-⊆ n bs b {d} ⟨ A , ⟨ al , d∈ ⟩ ⟩ =
    M.body-mono n n bs b (code-⊤ (Block.instrs b) ∷ codes-⊤ bs)
      ⟨ (λ x x< → ap-zeros (A (var x)) n x x< (al (var x))) , ⟨ r , (λ _ z → z) ⟩ ⟩ d
      (subst (λ m → d ∈ K (Block.instrs b) (Block.jump b) bs m _ _ init) (length-replicate n) d∈)
    where
    r : ∀ g → ρ̂ A g ⊆ called (ℬ Int Data.Integer.0ℤ ptt) g
    r rax = al (reg rax)
    r rdi = al (reg rdi)
    r rsi = al (reg rsi)

{- Soundness ------------------------------------------------------------------}

{- a well-formed program that terminates with an answer o has an element
   of the shape of o in its denotation -}
soundness : ∀ P → WF P → ∀ {o} → Terminates (sem P) o → Answer o
  → Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₚ × ShapeOf o d
soundness (program ds (body n bs b)) ⟨ wfd , _ ⟩ ⟨ s , ⟨ σ , fin ⟩ ⟩ ans
    with final-shape ds wfd s fin ans
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ d , ⟨ start-⊆ ds wfd n bs b (↠-⊆ ds wfd (Common.star→↠ ds σ) d d∈) , sh ⟩ ⟩

{- a well-formed program that stops with an error has ω in its denotation -}
sound-error : ∀ P → WF P → Terminates (sem P) o-error → ω ∈ ⟦ P ⟧ₚ
sound-error (program ds (body n bs b)) ⟨ wfd , _ ⟩ ⟨ s , ⟨ σ , fin ⟩ ⟩ =
  start-⊆ ds wfd n bs b (↠-⊆ ds wfd (Common.star→↠ ds σ) ω (final-err ds wfd s fin))
