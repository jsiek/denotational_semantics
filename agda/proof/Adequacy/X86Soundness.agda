{-

  Soundness of the X86 machine with respect to the graph model: what the
  machine computes is in the denotation of the (well-formed) program.

  As for Clos5 (Adequacy/Clos5Soundness.agda), each machine state
  denotes a set of values (𝒮) that every step can only shrink (step-⊆),
  and code pointers denote the entries of the table T⁺, with ν added.
  The state runs in continuation-passing style (Semantics/Graph/X86.agda), and the
  call stack is its continuation (𝒦): a return frame runs the caller's
  rest with %rax holding the callee's result.

  A location (a slot of the frame or a register) does not denote the
  whole meaning 𝒱 v of the value v it holds, but a finite part of it
  (Ap), as the semantics binds a slot to a finite part of a set and
  calls code on finite parts of %rdi and %rsi: a state denotes what its
  instructions mean for some such approximation of its locations. A
  step that writes v to d is matched by approximating, before the step,
  the operands it reads by enough of their values to compute the part of
  v that d holds after it (grow, write), and by the monotonicity of the
  semantics (Mono). A call makes, from the callee's approximation, the
  entries X ↦ (Y ↦ w) of the code that the caller applies.

  Labels refer to older definitions and the table is consistent (WF):
  the code of a definition is interpreted with the table of the older
  ones, and approximations must be consistent to be bound.

-}

module proof.Adequacy.X86Soundness where

open import Framework.Primitives using (Int)
open import Language.Prim using (bool; δ; sub; eq)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres)
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _~_; Con; Con⇒≈; ≈-single)
  renaming (const to dconst)
open import proof.Framework.GraphModel.Ops
  using (⋆; 𝒯; nthD; inl; inr; Λ; ⋆-mono; pair-mono; car-mono; cdr-mono; 𝒯-mono; proj-mono; 𝒞-mono; ■)
  renaming (proj to dproj; pair to dpair)
open import proof.Semantics.Graph.Prim using (primD; primD-mono) renaming (out to dout)
open import Language.X86
  renaming (pair to pairₛ; inl to inlₛ; inr to inrₛ; tuple to tupleₛ; fst to fstₛ; snd to sndₛ; get to getₛ)
open import Semantics.Graph.X86
  renaming (Regs to SRegs; code to codeD; run to runD; put to putD; call to callD; args to argsD;
            read to readD; zeros to zerosD; _[_↦_] to _[_↦ₛ_]; flag to flagD)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Terminates; next; stop)
open import proof.Framework.ListUtil using (replicate-‼-just; _‼_; proj)
open import Semantics.CEK.X86
  using (Val; code; pair; const; tup; obs; out; prim?; Frame; State; Stack; halt; retK; run; step; block-at; global; sem; get-field; build; is-inl; cmp; truth; bit; _[_]≔_; zeros; arg; args; test; goto; callq?; regs)
  renaming (read to readM; put to putM; call to callM; Regs to MRegs; _[_↦_] to _[_↦ₘ_])
import Semantics.CEK.X86 as T using (inl; inr)
open import proof.Adequacy.Common using (ShapeOf; δ?-inv)
open import proof.Adequacy.Soundness using (At; AllNE; 𝒯L; At-length; inl-⊆; inr-⊆; 𝒯L-mono; _⊆L_)
open import proof.Adequacy.Values using (module Den)
open import proof.Adequacy.X86WF
import proof.Adequacy.X86Common as Common

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using ()
open import Data.List using (List; []; _∷_; _++_; [_]; length; map; reverse; replicate)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.List.Properties using (++-assoc; length-map; length-replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_; Pointwise-length)
open import Data.Maybe using (Maybe; just; nothing; _>>=_) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_; _<?_; _⊔_; _∸_; _+_)
open import Data.Nat.Properties using ()
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

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

{- the semantics is monotone in the frame, the registers and the flag, and
   in the entries of the table at the labels the code reads (L) -}
module Mono {T T' : Table} {L : ℕ → Set} (TT : ∀ k → L k → T k ⊆ T' k) (n : ℕ) where

  Le : Store → SRegs → 𝒫 Value → Store → SRegs → 𝒫 Value → Set
  Le σ ρ F σ' ρ' F' = (∀ x → σ x ⊆ σ' x) × (∀ g → ρ g ⊆ ρ' g) × F ⊆ F'

  MonoK : Kont → Kont → Set₁
  MonoK κ κ' = ∀ {σ ρ F σ' ρ' F'} → Le σ ρ F σ' ρ' F' → κ σ ρ F ⊆ κ' σ' ρ' F'

  MonoB : Blocks → Blocks → Set₁
  MonoB B B' = ∀ l → MonoK (B l) (B' l)

  𝒪-mono : ∀ {S σ ρ σ' ρ'} a → OK L S a → (∀ x → σ x ⊆ σ' x) → (∀ g → ρ g ⊆ ρ' g)
    → 𝒪 T n σ ρ a ⊆ 𝒪 T' n σ' ρ' a
  𝒪-mono (loc (var x)) _ s r with x <? n
  ... | yes _ = s x
  ... | no _ = λ _ z → z
  𝒪-mono (loc (reg g)) _ s r = r g
  𝒪-mono (imm B k) _ s r = λ _ z → z
  𝒪-mono (label k) ok s r = TT k ok

  𝒪s-mono : ∀ {S σ ρ σ' ρ'} as → All (OK L S) as → (∀ x → σ x ⊆ σ' x) → (∀ g → ρ g ⊆ ρ' g)
    → results-rel-pres _⊆_ (replicate (length as) ■) (𝒪s T n σ ρ as) (𝒪s T' n σ' ρ' as)
  𝒪s-mono [] _ s r = ptt
  𝒪s-mono (a ∷ as) (o ∷ os) s r = ⟨ lift (𝒪-mono a o s r) , 𝒪s-mono as os s r ⟩

  object-mono : ∀ {S σ ρ σ' ρ'} sh as → All (OK L S) as → (∀ x → σ x ⊆ σ' x) → (∀ g → ρ g ⊆ ρ' g)
    → object T n σ ρ sh as ⊆ object T' n σ' ρ' sh as
  object-mono pairₛ (a ∷ b ∷ []) (oa ∷ ob ∷ []) s r =
    lower (pair-mono _ _ ⟨ lift (𝒪-mono a oa s r) , ⟨ lift (𝒪-mono b ob s r) , ptt ⟩ ⟩)
  object-mono tupleₛ as os s r = lower (𝒯-mono (length as) _ _ (𝒪s-mono as os s r))
  object-mono inlₛ (a ∷ []) (oa ∷ []) s r (left d) d∈ = 𝒪-mono a oa s r d d∈
  object-mono inrₛ (a ∷ []) (oa ∷ []) s r (right d) d∈ = 𝒪-mono a oa s r d d∈

  field-mono : ∀ f {D D'} → D ⊆ D' → field′ f D ⊆ field′ f D'
  field-mono fstₛ D⊆ = lower (car-mono _ _ ⟨ lift D⊆ , ptt ⟩)
  field-mono sndₛ D⊆ = lower (cdr-mono _ _ ⟨ lift D⊆ , ptt ⟩)
  field-mono (getₛ i) D⊆ = lower (proj-mono i _ _ ⟨ lift D⊆ , ptt ⟩)
  field-mono payload D⊆ d (inj₁ l) = inj₁ (D⊆ _ l)
  field-mono payload D⊆ d (inj₂ r) = inj₂ (D⊆ _ r)

  isinl-mono : ∀ {D D'} → D ⊆ D' → isinl D ⊆ isinl D'
  isinl-mono D⊆ w (inj₁ ⟨ u , ⟨ u∈ , e ⟩ ⟩) = inj₁ ⟨ u , ⟨ D⊆ _ u∈ , e ⟩ ⟩
  isinl-mono D⊆ w (inj₂ ⟨ u , ⟨ u∈ , e ⟩ ⟩) = inj₂ ⟨ u , ⟨ D⊆ _ u∈ , e ⟩ ⟩

  ↦-le : ∀ {σ σ' : Store} x X → (∀ y → σ y ⊆ σ' y) → ∀ y → (σ [ x ↦ₛ X ]) y ⊆ (σ' [ x ↦ₛ X ]) y
  ↦-le x X s y with y ≟ x
  ... | yes _ = λ _ z → z
  ... | no _ = s y

  ≔-le : ∀ {ρ ρ' : SRegs} {D D'} g → D ⊆ D' → (∀ g → ρ g ⊆ ρ' g) → ∀ g' → (ρ [ g ≔ D ]) g' ⊆ (ρ' [ g ≔ D' ]) g'
  ≔-le {ρ} {ρ'} {D} {D'} g D⊆ r g' with g' ≟R g
  ... | yes refl rewrite ≔-here ρ g D | ≔-here ρ' g D' = D⊆
  ... | no ne rewrite ≔-other ρ g D g' ne | ≔-other ρ' g D' g' ne = r g'

  checked-mono : ∀ x {D D'} → D ⊆ D' → checked n x D ⊆ checked n x D'
  checked-mono x D⊆ with x <? n
  ... | yes _ = D⊆
  ... | no _ = λ _ z → z

  put-mono : ∀ d {D D' κ κ'} → D ⊆ D' → MonoK κ κ' → MonoK (putD n d D κ) (putD n d D' κ')
  put-mono (var x) {D} {D'} D⊆ mκ ⟨ s , ⟨ r , f ⟩ ⟩ =
    checked-mono x λ { w ⟨ V , ⟨ ⟨ w∈ , neV ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ →
      ⟨ V , ⟨ ⟨ mκ ⟨ ↦-le x (mem V) s , ⟨ r , f ⟩ ⟩ w w∈ , neV ⟩ , ⟨ (λ d d∈ → D⊆ d (V⊆ d d∈)) , ne ⟩ ⟩ ⟩ }
  put-mono (reg g) D⊆ mκ ⟨ s , ⟨ r , f ⟩ ⟩ w ⟨ ⟨ u , u∈ ⟩ , w∈ ⟩ =
    ⟨ ⟨ u , D⊆ u u∈ ⟩ , mκ ⟨ s , ⟨ ≔-le g D⊆ r , f ⟩ ⟩ w w∈ ⟩

  primD-⊆ : ∀ p {D D' E E'} → D ⊆ D' → E ⊆ E' → primD p ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ primD p ⟨ D' , ⟨ E' , ptt ⟩ ⟩
  primD-⊆ p D⊆ E⊆ = lower (primD-mono p _ _ ⟨ lift D⊆ , ⟨ lift E⊆ , ptt ⟩ ⟩)

  flag-mono : ∀ {F₀ F₀' κ κ'} → F₀ ⊆ F₀' → MonoK κ κ' → ∀ {σ ρ F σ' ρ' F'} → Le σ ρ F σ' ρ' F'
    → flagD F₀ κ σ ρ ⊆ flagD F₀' κ' σ' ρ'
  flag-mono F⊆ mκ ⟨ s , ⟨ r , _ ⟩ ⟩ w ⟨ ⟨ u , u∈ ⟩ , w∈ ⟩ = ⟨ ⟨ u , F⊆ u u∈ ⟩ , mκ ⟨ s , ⟨ r , F⊆ ⟩ ⟩ w w∈ ⟩

  called-le : ∀ {R R'} → R ⊆ R' → ∀ g → called R g ⊆ called R' g
  called-le R⊆ rax = R⊆
  called-le R⊆ rdi = λ _ z → z
  called-le R⊆ rsi = λ _ z → z

  is-mono : ∀ {S} is {κ κ'} → Code L S is → MonoK κ κ' → MonoK (⟦ is ⟧ˢ T n κ) (⟦ is ⟧ˢ T' n κ')
  is-mono [] _ mκ = mκ
  is-mono (movq a d ∷ is) ⟨ oa , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    put-mono d (𝒪-mono a oa s r) (is-mono is c mκ) le
  is-mono (subq a d ∷ is) ⟨ ⟨ oa , od ⟩ , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    put-mono d (primD-⊆ sub (𝒪-mono (loc d) od s r) (𝒪-mono a oa s r)) (is-mono is c mκ) le
  is-mono (cmpq a₂ a₁ ∷ is) ⟨ ⟨ o₂ , o₁ ⟩ , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    flag-mono (primD-⊆ eq (𝒪-mono a₁ o₁ s r) (𝒪-mono a₂ o₂ s r)) (is-mono is c mκ) le
  is-mono (sete d ∷ is) ⟨ _ , c ⟩ mκ le@(⟨ _ , ⟨ _ , f ⟩ ⟩) = put-mono d f (is-mono is c mκ) le
  is-mono (testinl a ∷ is) ⟨ oa , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    flag-mono (isinl-mono (𝒪-mono a oa s r)) (is-mono is c mκ) le
  is-mono (alloc sh as d ∷ is) ⟨ os , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    put-mono d (object-mono sh as os s r) (is-mono is c mκ) le
  is-mono (load f a d ∷ is) ⟨ oa , c ⟩ mκ le@(⟨ s , ⟨ r , _ ⟩ ⟩) =
    put-mono d (field-mono f (𝒪-mono a oa s r)) (is-mono is c mκ) le
  is-mono (callq a ∷ is) ⟨ oa , c ⟩ mκ ⟨ s , ⟨ r , _ ⟩ ⟩ w ⟨ ⟨ u , u∈ ⟩ , w∈ ⟩ =
    ⟨ ⟨ u , R⊆ u u∈ ⟩ , is-mono is c mκ ⟨ s , ⟨ called-le R⊆ , (λ _ z → z) ⟩ ⟩ w w∈ ⟩
    where
    R⊆ = lower (⋆-mono _ _ ⟨ ⋆-mono _ _ ⟨ lift (𝒪-mono a oa s r) , ⟨ lift (r rdi) , ptt ⟩ ⟩
                           , ⟨ lift (r rsi) , ptt ⟩ ⟩)

  jump-mono : ∀ j {B B'} → MonoB B B' → MonoK (⟦ j ⟧ʲ B) (⟦ j ⟧ʲ B')
  jump-mono retq mB ⟨ _ , ⟨ r , _ ⟩ ⟩ = r rax
  jump-mono (jmp l) mB = mB l
  jump-mono (je l₁ l₂) mB le@(⟨ _ , ⟨ _ , f ⟩ ⟩) =
    lower (𝒞-mono _ _ ⟨ lift f , ⟨ (λ _ _ _ → lift (mB l₁ le)) , ⟨ (λ _ _ _ → lift (mB l₂ le)) , ptt ⟩ ⟩ ⟩)

  blocks-mono : ∀ {S} bs → All (λ b → Code L S (Block.instrs b)) bs → MonoB (blocks T n bs) (blocks T' n bs)
  blocks-mono [] _ l le = λ _ ()
  blocks-mono (b ∷ bs) (c ∷ cs) l with l ≟ length bs
  ... | yes _ = is-mono (Block.instrs b) c (jump-mono (Block.jump b) (blocks-mono bs cs))
  ... | no _ = blocks-mono bs cs l

  body-mono : ∀ {S} m bs b → All (λ c → Code L S (Block.instrs c)) (b ∷ bs) → MonoK (runD T n (body m bs b)) (runD T' n (body m bs b))
  body-mono m bs b (c ∷ cs) = is-mono (Block.instrs b) c (jump-mono (Block.jump b) (blocks-mono bs cs))

{- any code reads what the trivial conditions allow -}
ok-⊤ : ∀ a → OK (λ _ → ⊤) (λ _ → ⊤) a
ok-⊤ (loc (var x)) = tt
ok-⊤ (loc (reg g)) = tt
ok-⊤ (imm B k) = tt
ok-⊤ (label k) = tt

code-⊤ : ∀ is → Code (λ _ → ⊤) (λ _ → ⊤) is
code-⊤ [] = tt
code-⊤ (movq a d ∷ is) = ⟨ ok-⊤ a , code-⊤ is ⟩
code-⊤ (subq a d ∷ is) = ⟨ ⟨ ok-⊤ a , ok-⊤ (loc d) ⟩ , code-⊤ is ⟩
code-⊤ (cmpq a₂ a₁ ∷ is) = ⟨ ⟨ ok-⊤ a₂ , ok-⊤ a₁ ⟩ , code-⊤ is ⟩
code-⊤ (sete d ∷ is) = ⟨ tt , code-⊤ is ⟩
code-⊤ (testinl a ∷ is) = ⟨ ok-⊤ a , code-⊤ is ⟩
code-⊤ (alloc sh as d ∷ is) = ⟨ all-⊤ as , code-⊤ is ⟩
  where all-⊤ : ∀ as → All (OK (λ _ → ⊤) (λ _ → ⊤)) as
        all-⊤ [] = []
        all-⊤ (a ∷ as) = ok-⊤ a ∷ all-⊤ as
code-⊤ (load f a d ∷ is) = ⟨ ok-⊤ a , code-⊤ is ⟩
code-⊤ (callq a ∷ is) = ⟨ ok-⊤ a , code-⊤ is ⟩

codes-⊤ : ∀ bs → All (λ b → Code (λ _ → ⊤) (λ _ → ⊤) (Block.instrs b)) bs
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

{- a finite part of O X, for an operator O on one set, is in O of a finite
   part of X, picked out by f -}
split : ∀ {O : 𝒫 Value → 𝒫 Value} (Om : ∀ {D E} → D ⊆ E → O D ⊆ O E) f {X}
  → (∀ z → z ∈ O X → mem (f z) ⊆ X × z ∈ O (mem (f z)))
  → ∀ V → mem V ⊆ O X → mem (pick f V) ⊆ X × mem V ⊆ O (mem (pick f V))
split Om f h V V⊆ =
  ⟨ pick-⊆ f V (λ z z∈ → proj₁ (h z (V⊆ z z∈)))
  , (λ z z∈ → Om (pick-∈ f V z∈) z (proj₂ (h z (V⊆ z z∈)))) ⟩

fstv sndv lft rgt : Value → List Value
fstv ⦅ p , q ⦆ = p ∷ []
fstv _ = []
sndv ⦅ p , q ⦆ = q ∷ []
sndv _ = []
lft (left p) = p ∷ []
lft _ = []
rgt (right p) = p ∷ []
rgt _ = []

pair-split : ∀ {X Y} V → mem V ⊆ dpair ⟨ X , ⟨ Y , ptt ⟩ ⟩
  → mem (pick fstv V) ⊆ X × mem (pick sndv V) ⊆ Y × mem V ⊆ dpair ⟨ mem (pick fstv V) , ⟨ mem (pick sndv V) , ptt ⟩ ⟩
pair-split {X} {Y} V V⊆ =
  ⟨ pick-⊆ fstv V (λ z z∈ → proj₁ (h z (V⊆ z z∈)))
  , ⟨ pick-⊆ sndv V (λ z z∈ → proj₁ (proj₂ (h z (V⊆ z z∈))))
  , (λ z z∈ → lower (pair-mono _ _ ⟨ lift (pick-∈ fstv V z∈) , ⟨ lift (pick-∈ sndv V z∈) , ptt ⟩ ⟩) z
                 (proj₂ (proj₂ (h z (V⊆ z z∈))))) ⟩ ⟩
  where
  h : ∀ z → z ∈ dpair ⟨ X , ⟨ Y , ptt ⟩ ⟩
    → mem (fstv z) ⊆ X × mem (sndv z) ⊆ Y × z ∈ dpair ⟨ mem (fstv z) , ⟨ mem (sndv z) , ptt ⟩ ⟩
  h ⦅ p , q ⦆ ⟨ p∈ , q∈ ⟩ = ⟨ (λ { _ (here refl) → p∈ }) , ⟨ (λ { _ (here refl) → q∈ }) , ⟨ here refl , here refl ⟩ ⟩ ⟩

inl-split : ∀ {X} V → mem V ⊆ inl ⟨ X , ptt ⟩ → mem (pick lft V) ⊆ X × mem V ⊆ inl ⟨ mem (pick lft V) , ptt ⟩
inl-split = split inl-⊆ lft h
  where
  h : ∀ {X} z → z ∈ inl ⟨ X , ptt ⟩ → mem (lft z) ⊆ X × z ∈ inl ⟨ mem (lft z) , ptt ⟩
  h (left p) p∈ = ⟨ (λ { _ (here refl) → p∈ }) , here refl ⟩

inr-split : ∀ {X} V → mem V ⊆ inr ⟨ X , ptt ⟩ → mem (pick rgt V) ⊆ X × mem V ⊆ inr ⟨ mem (pick rgt V) , ptt ⟩
inr-split = split inr-⊆ rgt h
  where
  h : ∀ {X} z → z ∈ inr ⟨ X , ptt ⟩ → mem (rgt z) ⊆ X × z ∈ inr ⟨ mem (rgt z) , ptt ⟩
  h (right p) p∈ = ⟨ (λ { _ (here refl) → p∈ }) , here refl ⟩

{- the components of tuples -}
hd tl : Value → List Value
hd (tup[ zero ] x) = x ∷ []
hd _ = []
tl (tup[ suc i ] x) = tup[ i ] x ∷ []
tl _ = []

hd-tl : ∀ {D Ds} z → z ∈ 𝒯L (D ∷ Ds) → mem (hd z) ⊆ D × mem (tl z) ⊆ 𝒯L Ds
hd-tl (tup[ zero ] x) ⟨ ⟨ _ , x∈ ⟩ , _ ⟩ = ⟨ (λ { _ (here refl) → x∈ }) , (λ _ ()) ⟩
hd-tl (tup[ suc i ] x) ⟨ a , ⟨ _ , ne ⟩ ⟩ = ⟨ (λ _ ()) , (λ { _ (here refl) → ⟨ a , ne ⟩ }) ⟩

tup-split : ∀ Ds V → AllNE Ds → mem V ⊆ 𝒯L Ds
  → Σ[ Gs ∈ List (List Value) ] Pointwise (λ G D → mem G ⊆ D) Gs Ds × AllNE (map mem Gs) × mem V ⊆ 𝒯L (map mem Gs)
tup-split [] V _ V⊆ = ⟨ [] , ⟨ [] , ⟨ tt , V⊆ ⟩ ⟩ ⟩
tup-split (D ∷ Ds) V ⟨ ⟨ w , w∈ ⟩ , ne ⟩ V⊆
    with tup-split Ds (pick tl V) ne (pick-⊆ tl V λ z z∈ → proj₂ (hd-tl z (V⊆ z z∈)))
... | ⟨ Gs , ⟨ pw , ⟨ neGs , V'⊆ ⟩ ⟩ ⟩ =
  ⟨ G₀ ∷ Gs
  , ⟨ ++-⊆ (w ∷ []) (pick hd V) (λ { _ (here refl) → w∈ }) (pick-⊆ hd V λ z z∈ → proj₁ (hd-tl z (V⊆ z z∈))) ∷ pw
    , ⟨ neAll , (λ z z∈ → g z z∈ (V⊆ z z∈)) ⟩ ⟩ ⟩
  where
  G₀ = w ∷ pick hd V
  neAll : AllNE (mem G₀ ∷ map mem Gs)
  neAll = ⟨ ⟨ w , here refl ⟩ , neGs ⟩
  g : ∀ z → z ∈ mem V → z ∈ 𝒯L (D ∷ Ds) → z ∈ 𝒯L (mem G₀ ∷ map mem Gs)
  g (tup[ zero ] x) z∈ ⟨ ⟨ len , _ ⟩ , _ ⟩ =
    ⟨ ⟨ trans (length-map mem Gs) (trans (Pointwise-length pw) len) , there (pick-∈ hd V z∈ x (here refl)) ⟩ , neAll ⟩
  g (tup[ suc i ] x) z∈ _ = ⟨ proj₁ (V'⊆ (tup[ i ] x) (pick-∈ tl V z∈ _ (here refl))) , neAll ⟩

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

{- the registers other than g, after writing g -}
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

test-inv : ∀ m {K : Maybe Bool → State} {s'} → test m K ≡ next s' → Σ[ b ∈ Bool ] m ≡ just b × s' ≡ K (just b)
test-inv (just b) refl = ⟨ b , ⟨ refl , refl ⟩ ⟩

goto-inv : ∀ mb {σ f φ ρ s'} → goto mb σ f φ ρ ≡ next s'
  → Σ[ b ∈ Block ] Σ[ bs ∈ List Block ] mb ≡ just ⟨ b , bs ⟩ × s' ≡ run (Block.instrs b) (Block.jump b) bs σ f φ ρ
goto-inv (just ⟨ b , bs ⟩) refl = ⟨ b , ⟨ bs , ⟨ refl , refl ⟩ ⟩ ⟩

bind-inv : ∀ {A B : Set} (m : Maybe A) {f : A → Maybe B} {r} → (m >>= f) ≡ just r → Σ[ x ∈ A ] m ≡ just x × f x ≡ just r
bind-inv (just x) e = ⟨ x , ⟨ refl , e ⟩ ⟩

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
  ⟨ u ∷ us , ⟨ ea ∷ es , subst (λ vs → k vs ≡ _) (++-assoc (reverse acc) [ u ] us) (subst (λ vs → k (vs ++ us) ≡ _) (unfold-reverse' u acc) e') ⟩ ⟩
  where unfold-reverse' : ∀ (u : Val) acc → reverse (u ∷ acc) ≡ reverse acc ++ [ u ]
        unfold-reverse' u acc = Data.List.Properties.unfold-reverse u acc

{- Soundness, for a table ds of global definitions ---------------------------------}

module _ (ds : List Body) (wfd : DefsWF ds) (con : ∀ k → Con (table ds k)) where

  open Common ds

  {- the table, with ν added to every entry -}
  T⁺ : Table
  T⁺ k = table ds k ∪ ⌈ ν ⌉

  private
    ν~ : ∀ {f} z → z ∈ Λ ⟨ f , ptt ⟩ → ν ~ z × z ~ ν
    ν~ ν _ = ⟨ tt , tt ⟩
    ν~ (V ↦ w) _ = ⟨ tt , tt ⟩

    table-ν : ∀ Ns k z → z ∈ table Ns k → ν ~ z × z ~ ν
    table-ν (N ∷ Ns) k z z∈ with k ≟ length Ns
    ... | yes _ = ν~ z z∈
    ... | no _ = table-ν Ns k z z∈

  T⁺-con : ∀ k → Con (T⁺ k)
  T⁺-con k a b (inj₁ a∈) (inj₁ b∈) = con k a b a∈ b∈
  T⁺-con k a b (inj₁ a∈) (inj₂ refl) = proj₂ (table-ν ds k a a∈)
  T⁺-con k a b (inj₂ refl) (inj₁ b∈) = proj₁ (table-ν ds k b b∈)
  T⁺-con k a b (inj₂ refl) (inj₂ refl) = tt

  open Den T⁺ (λ k → inj₂ refl) T⁺-con

  {- within the machine, the same table on both sides -}
  module M (n : ℕ) = Mono {T⁺} {T⁺} {λ _ → ⊤} (λ _ _ _ z → z) n

  {- Approximations ---------------------------------------------------------------}

  Apx : Set
  Apx = Loc → List Value

  {- a finite part of the denotation of what a location holds -}
  Ap : List Value → Maybe Val → Set
  Ap A (just v) = mem A ⊆ 𝒱 v
  Ap A nothing = A ≡ []

  AL : Apx → Frame → MRegs → Set
  AL A φ ρ = ∀ l → Ap (A l) (readM φ ρ l)

  σ̂ : Apx → Store
  σ̂ A x = mem (A (var x))

  ρ̂ : Apx → SRegs
  ρ̂ A g = mem (A (reg g))

  𝓕 : Maybe Bool → 𝒫 Value
  𝓕 (just b) = ⌈ dout (bool b) ⌉
  𝓕 nothing = ∅

  {- what runs from a point of a body on -}
  K : List Instr → Jump → List Block → ℕ → Kont
  K is j bs n = ⟦ is ⟧ˢ T⁺ n (⟦ j ⟧ʲ (blocks T⁺ n bs))

  K-mono : ∀ is j bs n → M.MonoK n (K is j bs n) (K is j bs n)
  K-mono is j bs n = M.is-mono n is (code-⊤ is) (M.jump-mono n j (M.blocks-mono n bs (codes-⊤ bs)))

  {- the call stack: a caller runs its rest with the callee's result -}
  𝒦 : Stack → 𝒫 Value → 𝒫 Value
  𝒦 halt D d = d ∈ D
  𝒦 (retK is j bs φ stk) D d =
    Σ[ A ∈ Apx ] Σ[ W ∈ List Value ] (∀ x → Ap (A (var x)) (φ ‼ x)) × mem W ⊆ D × W ≢ []
      × d ∈ 𝒦 stk (K is j bs (length φ) (σ̂ A) (called (mem W)) ∅)

  𝒮 : State → 𝒫 Value
  𝒮 (run is j bs stk f φ ρ) d = Σ[ A ∈ Apx ] AL A φ ρ × d ∈ 𝒦 stk (K is j bs (length φ) (σ̂ A) (ρ̂ A) (𝓕 f))

  𝒦-mono : ∀ stk {D E} → D ⊆ E → 𝒦 stk D ⊆ 𝒦 stk E
  𝒦-mono halt D⊆ = D⊆
  𝒦-mono (retK is j bs φ stk) D⊆ d ⟨ A , ⟨ W , ⟨ af , ⟨ W⊆ , r ⟩ ⟩ ⟩ ⟩ =
    ⟨ A , ⟨ W , ⟨ af , ⟨ (λ x x∈ → D⊆ x (W⊆ x x∈)) , r ⟩ ⟩ ⟩ ⟩

  Ext : Apx → Apx → Set
  Ext A B = ∀ l → mem (A l) ⊆ mem (B l)

  Ext-trans : ∀ {A B C} → Ext A B → Ext B C → Ext A C
  Ext-trans E E' l d d∈ = E' l d (E l d d∈)

  Ext-le : ∀ {n A B F} → Ext A B → M.Le n (σ̂ A) (ρ̂ A) F (σ̂ B) (ρ̂ B) F
  Ext-le E = ⟨ (λ x → E (var x)) , ⟨ (λ g → E (reg g)) , (λ _ z → z) ⟩ ⟩

  add : Apx → Loc → List Value → Apx
  add A l V l' with l' ≟L l
  ... | yes _ = A l' ++ V
  ... | no _ = A l'

  clear : Apx → Loc → Apx
  clear A l l' with l' ≟L l
  ... | yes _ = []
  ... | no _ = A l'

  ap-[] : ∀ m → Ap [] m
  ap-[] (just v) = λ _ ()
  ap-[] nothing = refl

  here-⊆ : ∀ {A φ ρ l v} → AL A φ ρ → readM φ ρ l ≡ just v → mem (A l) ⊆ 𝒱 v
  here-⊆ {A} {l = l} al e = subst (Ap (A l)) e (al l)

  add-AL : ∀ {A φ ρ v} l V → AL A φ ρ → readM φ ρ l ≡ just v → mem V ⊆ 𝒱 v → AL (add A l V) φ ρ
  add-AL {A} l V al e V⊆ l' with l' ≟L l
  ... | yes refl = subst (Ap (A l ++ V)) (sym e) (++-⊆ (A l) V (here-⊆ al e) V⊆)
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

  {- a nonempty finite part -}
  ext : List Value → Val → List Value
  ext A v = A ++ proj₁ (𝒱-nonempty v) ∷ []

  ext-⊆ : ∀ A v → mem A ⊆ 𝒱 v → mem (ext A v) ⊆ 𝒱 v
  ext-⊆ A v A⊆ = ++-⊆ A _ A⊆ (λ { _ (here refl) → proj₂ (𝒱-nonempty v) })

  ext-ne : ∀ A v → ext A v ≢ []
  ext-ne [] v ()
  ext-ne (x ∷ A) v ()

  ext-pt : ∀ A v → proj₁ (𝒱-nonempty v) ∈ mem (ext A v)
  ext-pt A v = ∈-++⁺ʳ A (here refl)

  read-in : ∀ {n σ} x → x < n → σ x ⊆ readD n σ x
  read-in {n} x x< with x <? n
  ... | yes _ = λ _ z → z
  ... | no ¬x< = ⊥-elim (¬x< x<)

  checked-in : ∀ {n x D} → x < n → D ⊆ checked n x D
  checked-in {n} {x} x< with x <? n
  ... | yes _ = λ _ z → z
  ... | no ¬x< = ⊥-elim (¬x< x<)

  𝒪-ext : ∀ {n A B} a → Ext A B → 𝒪 T⁺ n (σ̂ A) (ρ̂ A) a ⊆ 𝒪 T⁺ n (σ̂ B) (ρ̂ B) a
  𝒪-ext {n} a E = M.𝒪-mono n a (ok-⊤ a) (λ x → E (var x)) (λ g → E (reg g))

  {- the operand a, which holds v, approximated by enough to hold V -}
  grow : ∀ a {φ ρ v} A V → AL A φ ρ → arg φ ρ a ≡ just v → mem V ⊆ 𝒱 v
    → Σ[ B ∈ Apx ] AL B φ ρ × Ext A B × mem V ⊆ 𝒪 T⁺ (length φ) (σ̂ B) (ρ̂ B) a
  grow (loc (var x)) {φ} A V al e V⊆ =
    ⟨ add A (var x) V , ⟨ add-AL (var x) V al e V⊆ , ⟨ add-ext A (var x) V
    , (λ d d∈ → read-in x (‼-just φ x e) d (add-here A (var x) V d d∈)) ⟩ ⟩ ⟩
  grow (loc (reg g)) A V al e V⊆ = ⟨ add A (reg g) V , ⟨ add-AL (reg g) V al e V⊆ , ⟨ add-ext A (reg g) V , add-here A (reg g) V ⟩ ⟩ ⟩
  grow (imm B k) A V al refl V⊆ = ⟨ A , ⟨ al , ⟨ (λ l d z → z) , V⊆ ⟩ ⟩ ⟩
  grow (label k) A V al refl V⊆ = ⟨ A , ⟨ al , ⟨ (λ l d z → z) , V⊆ ⟩ ⟩ ⟩

  grows : ∀ as {φ ρ us} A Gs → AL A φ ρ → Evals φ ρ as us → Pointwise (λ G u → mem G ⊆ 𝒱 u) Gs us
    → Σ[ B ∈ Apx ] AL B φ ρ × Ext A B × Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ (length φ) (σ̂ B) (ρ̂ B) a) as Gs
  grows [] A [] al [] [] = ⟨ A , ⟨ al , ⟨ (λ l d z → z) , [] ⟩ ⟩ ⟩
  grows (a ∷ as) A (G ∷ Gs) al (e ∷ es) (g ∷ gs) with grow a A G al e g
  ... | ⟨ B , ⟨ alB , ⟨ E , G⊆ ⟩ ⟩ ⟩ with grows as B Gs alB es gs
  ...   | ⟨ C , ⟨ alC , ⟨ E' , ps ⟩ ⟩ ⟩ = ⟨ C , ⟨ alC , ⟨ Ext-trans E E' , (λ d d∈ → 𝒪-ext a E' d (G⊆ d d∈)) ∷ ps ⟩ ⟩ ⟩

  {- Writes ----------------------------------------------------------------------}

  {- d := D, where D holds a finite part V of v as large as what d holds
     after the step -}
  write : ∀ d {v φ ρ φ' ρ' A' A D κ F} → Put d v φ ρ φ' ρ' → AL A' φ' ρ'
    → (∀ l → l ≢ d → mem (A' l) ⊆ mem (A l)) → mem (ext (A' d) v) ⊆ D → M.MonoK (length φ) κ κ
    → κ (σ̂ A') (ρ̂ A') F ⊆ putD (length φ) d D κ (σ̂ A) (ρ̂ A) F
  write (var x) {v} {A' = A'} {A} P al' oth V⊆ mκ w w∈ =
    checked-in (p-inside P refl) w
      ⟨ V , ⟨ ⟨ mκ ⟨ s , ⟨ (λ g → oth (reg g) (λ ())) , (λ _ z → z) ⟩ ⟩ w w∈ , ⟨ ext-ne _ v , Con⇒≈ V (𝒱-con v) V⊆v ⟩ ⟩
          , ⟨ V⊆ , ext-ne _ v ⟩ ⟩ ⟩
    where
    V = ext (A' (var x)) v
    V⊆v = ext-⊆ _ v (here-⊆ al' (p-here P))
    s : ∀ y → σ̂ A' y ⊆ (σ̂ A [ x ↦ₛ mem V ]) y
    s y with y ≟ x
    ... | yes refl = λ d d∈ → ∈-++⁺ˡ d∈
    ... | no ne = oth (var y) (λ { refl → ne refl })
  write (reg g) {v} {A' = A'} {A} {D} P al' oth V⊆ mκ w w∈ =
    ⟨ ⟨ _ , V⊆ _ (ext-pt (A' (reg g)) v) ⟩ , mκ ⟨ (λ x → oth (var x) (λ ())) , ⟨ r , (λ _ z → z) ⟩ ⟩ w w∈ ⟩
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
    ⟨ A , ⟨ al , 𝒦-mono stk (λ u u∈ → ⟨ ⟨ _ , F⊆ _ refl ⟩
                                     , K-mono is j bs (length φ) ⟨ (λ x → E (var x)) , ⟨ (λ g → E (reg g)) , F⊆ ⟩ ⟩ u u∈ ⟩) w w∈' ⟩ ⟩

  {- What the instructions compute ------------------------------------------------}

  {- the operands of alloc -}
  pw-𝒱s : ∀ Gs us → Pointwise (λ G D → mem G ⊆ D) Gs (𝒱s us) → Pointwise (λ G u → mem G ⊆ 𝒱 u) Gs us
  pw-𝒱s [] [] [] = []
  pw-𝒱s (G ∷ Gs) (u ∷ us) (g ∷ gs) = g ∷ pw-𝒱s Gs us gs

  module _ {n : ℕ} {σ : Store} {ρ : SRegs} where
    private O = 𝒪 T⁺ n σ ρ

    At-𝒪s : ∀ as (i : Fin (length as)) d → At i (map O as) d → d ∈ nthD (𝒪s T⁺ n σ ρ as) i
    At-𝒪s (a ∷ as) zero d ⟨ _ , d∈ ⟩ = d∈
    At-𝒪s (a ∷ as) (suc i) d a∈ = At-𝒪s as i d a∈

    NE-𝒪s : ∀ as → AllNE (map O as) → ∀ i → nonempty (nthD (𝒪s T⁺ n σ ρ as) i)
    NE-𝒪s (a ∷ as) ⟨ ne , _ ⟩ zero = ne
    NE-𝒪s (a ∷ as) ⟨ _ , nes ⟩ (suc i) = NE-𝒪s as nes i

    𝒯L-𝒪s : ∀ as → 𝒯L (map O as) ⊆ 𝒯 (length as) (𝒪s T⁺ n σ ρ as)
    𝒯L-𝒪s [] ⟨⟩ tt = tt
    𝒯L-𝒪s [] (tup[ zero ] d) ⟨ () , _ ⟩
    𝒯L-𝒪s [] (tup[ suc i ] d) ⟨ () , _ ⟩
    𝒯L-𝒪s (a ∷ as) (tup[_]_ {m} i d) ⟨ a∈ , ne ⟩ with trans (sym (length-map O (a ∷ as))) (At-length i _ d a∈)
    ... | refl = ⟨ refl , ⟨ At-𝒪s (a ∷ as) i d a∈ , NE-𝒪s (a ∷ as) ne ⟩ ⟩

    ⊆L-pw : ∀ as Gs → Pointwise (λ a G → mem G ⊆ O a) as Gs → map mem Gs ⊆L map O as
    ⊆L-pw [] [] [] = tt
    ⊆L-pw (a ∷ as) (G ∷ Gs) (p ∷ ps) = ⟨ p , ⊆L-pw as Gs ps ⟩

  {- the operands of alloc sh, approximated by Gs, build enough of the object -}
  build-ok : ∀ sh us {v} → build sh us ≡ just v → ∀ V → mem V ⊆ 𝒱 v
    → Σ[ Gs ∈ List (List Value) ] Pointwise (λ G u → mem G ⊆ 𝒱 u) Gs us
      × (∀ {n σ ρ} as → Pointwise (λ a G → mem G ⊆ 𝒪 T⁺ n σ ρ a) as Gs → mem V ⊆ object T⁺ n σ ρ sh as)
  build-ok pairₛ (u₁ ∷ u₂ ∷ []) refl V V⊆ with pair-split V V⊆
  ... | ⟨ P⊆ , ⟨ Q⊆ , V⊆' ⟩ ⟩ =
    ⟨ pick fstv V ∷ pick sndv V ∷ [] , ⟨ P⊆ ∷ Q⊆ ∷ []
    , (λ { (a ∷ b ∷ []) (pa ∷ pb ∷ []) x x∈ → lower (pair-mono _ _ ⟨ lift pa , ⟨ lift pb , ptt ⟩ ⟩) x (V⊆' x x∈) }) ⟩ ⟩
  build-ok tupleₛ us refl V V⊆ with tup-split (𝒱s us) V (𝒱s-nonempty us) V⊆
  ... | ⟨ Gs , ⟨ pw , ⟨ _ , V⊆' ⟩ ⟩ ⟩ =
    ⟨ Gs , ⟨ pw-𝒱s Gs us pw
    , (λ as ps x x∈ → 𝒯L-𝒪s as x (𝒯L-mono (map mem Gs) _ (⊆L-pw as Gs ps) x (V⊆' x x∈))) ⟩ ⟩
  build-ok inlₛ (u ∷ []) refl V V⊆ with inl-split V V⊆
  ... | ⟨ P⊆ , V⊆' ⟩ = ⟨ pick lft V ∷ [] , ⟨ P⊆ ∷ [] , (λ { (a ∷ []) (pa ∷ []) x x∈ → inl-⊆ pa x (V⊆' x x∈) }) ⟩ ⟩
  build-ok inrₛ (u ∷ []) refl V V⊆ with inr-split V V⊆
  ... | ⟨ P⊆ , V⊆' ⟩ = ⟨ pick rgt V ∷ [] , ⟨ P⊆ ∷ [] , (λ { (a ∷ []) (pa ∷ []) x x∈ → inr-⊆ pa x (V⊆' x x∈) }) ⟩ ⟩

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
    ⟨ _ , ⟨ wrap (λ p → ⦅ p , proj₁ (𝒱-nonempty w) ⦆) V (λ p p∈ → ⟨ p∈ , proj₂ (𝒱-nonempty w) ⟩) V⊆ , (λ p p∈ → ⟨ _ , ∈-map⁺ _ p∈ ⟩) ⟩ ⟩
  field-ok sndₛ (pair v w) refl V V⊆ =
    ⟨ _ , ⟨ wrap (λ q → ⦅ proj₁ (𝒱-nonempty v) , q ⦆) V (λ q q∈ → ⟨ proj₂ (𝒱-nonempty v) , q∈ ⟩) V⊆ , (λ q q∈ → ⟨ _ , ∈-map⁺ _ q∈ ⟩) ⟩ ⟩
  field-ok (getₛ i) (tup us) e V V⊆ =
    ⟨ _ , ⟨ wrap (tup[ i ]_) V (λ d d∈ → ⟨ proj-𝒱s i us e d d∈ , 𝒱s-nonempty us ⟩) V⊆ , (λ d d∈ → ∈-map⁺ _ d∈) ⟩ ⟩
  field-ok payload (T.inl v) refl V V⊆ = ⟨ _ , ⟨ wrap left V (λ _ z → z) V⊆ , (λ d d∈ → inj₁ (∈-map⁺ left d∈)) ⟩ ⟩
  field-ok payload (T.inr v) refl V V⊆ = ⟨ _ , ⟨ wrap right V (λ _ z → z) V⊆ , (λ d d∈ → inj₂ (∈-map⁺ right d∈)) ⟩ ⟩

  mmap-inv : ∀ {A B : Set} (f : A → B) (m : Maybe A) {y} → mmap f m ≡ just y → Σ[ x ∈ A ] m ≡ just x × y ≡ f x
  mmap-inv f (just x) refl = ⟨ x , ⟨ refl , refl ⟩ ⟩

  truth-inv : ∀ m {b} → truth m ≡ just b → m ≡ just (bool b)
  truth-inv (just (bool b)) refl = refl

  {- the two integers of a primitive -}
  prim-ok : ∀ p v w {o} → δ? p (obs v) (obs w) ≡ just o
    → Σ[ n ∈ _ ] Σ[ m ∈ _ ] dconst {Int} n ∈ 𝒱 v × dconst {Int} m ∈ 𝒱 w × o ≡ δ p n m
  prim-ok p v w e with δ?-inv p (obs v) (obs w) e
  ... | ⟨ n , ⟨ m , ⟨ ov , ⟨ ow , refl ⟩ ⟩ ⟩ ⟩ = ⟨ n , ⟨ m , ⟨ int-in v ov , ⟨ int-in w ow , refl ⟩ ⟩ ⟩ ⟩

  {- the code of the definition that a call runs, and the older ones -}
  callee : ∀ k {b} → global ds k ≡ just b
    → Σ[ Ns ∈ List Body ] table ds k ≡ codeD (table Ns) b × (∀ j → j < length Ns → table ds j ≡ table Ns j)
       × BodyOK (length Ns) (2 ⊔ Body.locals b) b
  callee k {b} eg with global-split k eg
  ... | ⟨ xs , ⟨ Ns , ⟨ e , refl ⟩ ⟩ ⟩ =
    ⟨ Ns , ⟨ trans (cong (λ L → table L (length Ns)) e) (table-at xs b Ns)
    , ⟨ (λ j j< → trans (cong (λ L → table L j) (trans e (sym (++-assoc xs [ b ] Ns)))) (table-agree (xs ++ [ b ]) Ns j j<))
    , proj₁ (DefsWF-suffix xs (subst DefsWF e wfd)) ⟩ ⟩ ⟩

  ap-zeros : ∀ A m x → Ap A (zeros m ‼ x) → mem A ⊆ zerosD x
  ap-zeros A m x ap with zeros m ‼ x in e
  ... | just w with replicate-‼-just m x e
  ...   | refl = ap
  ap-zeros A m x refl | nothing = λ _ ()

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

  {- the registers a callee starts with and a caller continues with -}
  rax-only : List Value → Apx
  rax-only W (reg rax) = W
  rax-only W _ = []

  {- callq: the callee's approximation gives the entries X ↦ (Y ↦ w) of
     its code that the caller applies -}
  call-step : ∀ a {is j bs stk f φ ρ s'} → callq? ds (arg φ ρ a) (retK is j bs φ stk) ρ ≡ next s'
    → 𝒮 s' ⊆ 𝒮 (run (callq a ∷ is) j bs stk f φ ρ)
  call-step a {is} {j} {bs} {stk} {f} {φ} {ρ} e w w∈ with callq-inv (arg φ ρ a) e
  ... | ⟨ k , ⟨ m , ⟨ bbs , ⟨ bst , ⟨ e₁ , ⟨ e₂ , ⟨ ea , ⟨ eg , ⟨ er₁ , ⟨ er₂ , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ with w∈
  ... | ⟨ A' , ⟨ al' , ⟨ A'' , ⟨ W , ⟨ af , ⟨ W⊆ , ⟨ W≢ , w∈' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ with callee k eg
  ... | ⟨ Ns , ⟨ et , ⟨ agree , c ∷ cs ⟩ ⟩ ⟩
      with grows (loc (reg rdi) ∷ loc (reg rsi) ∷ a ∷ []) A₀ (X ∷ Y ∷ map entry W ∷ []) al₀
                 (er₁ ∷ er₂ ∷ ea ∷ []) (ext-⊆ _ e₁ (here-⊆ al' refl) ∷ ext-⊆ _ e₂ (here-⊆ al' refl) ∷ entries ∷ [])
    where
    A₀ : Apx
    A₀ (var x) = A'' (var x)
    A₀ (reg g) = []
    al₀ : AL A₀ φ ρ
    al₀ (var x) = af x
    al₀ (reg g) = ap-[] (ρ g)
    X = ext (A' (reg rdi)) e₁
    Y = ext (A' (reg rsi)) e₂
    entry : Value → Value
    entry w = X ↦ (Y ↦ w)
    n' = length (zeros (2 + (m ∸ 2)))
    TT : ∀ k' → k' < length Ns → T⁺ k' ⊆ table Ns k'
    TT k' k'< x (inj₁ x∈) = subst (λ T → x ∈ T) (agree k' k'<) x∈
    TT k' k'< x (inj₂ refl) = ν-table Ns k' k'<
    regs-le : ∀ g → ρ̂ A' g ⊆ argsD (mem X) (mem Y) g
    regs-le rax = subst (λ L → mem L ⊆ ∅) (sym (al' (reg rax))) (λ _ ())
    regs-le rdi = λ d d∈ → ∈-++⁺ˡ d∈
    regs-le rsi = λ d d∈ → ∈-++⁺ˡ d∈
    runs : ∀ w → w ∈ mem W → w ∈ runD (table Ns) (2 ⊔ m) (body m bbs bst) zerosD (argsD (mem X) (mem Y)) ∅
    runs w w∈W = Mono.body-mono TT (2 ⊔ m) m bbs bst (c ∷ cs)
      ⟨ (λ x → ap-zeros (A' (var x)) (2 + (m ∸ 2)) x (al' (var x))) , ⟨ regs-le , (λ _ z → z) ⟩ ⟩ w
      (subst (λ n → w ∈ K (Block.instrs bst) (Block.jump bst) bbs n (σ̂ A') (ρ̂ A') ∅) (frame-size m) (W⊆ w w∈W))
    entries : mem (map entry W) ⊆ T⁺ k
    entries x x∈ with ∈-map⁻ entry x∈
    ... | ⟨ w , ⟨ w∈W , refl ⟩ ⟩ =
      inj₁ (subst (λ T → entry w ∈ T) (sym et)
        ⟨ ⟨ runs w w∈W , ⟨ ext-ne _ e₂ , Con⇒≈ Y (𝒱-con e₂) (ext-⊆ _ e₂ (here-⊆ al' refl)) ⟩ ⟩
        , ⟨ ext-ne _ e₁ , Con⇒≈ X (𝒱-con e₁) (ext-⊆ _ e₁ (here-⊆ al' refl)) ⟩ ⟩)
  ... | ⟨ B , ⟨ alB , ⟨ E , X⊆ ∷ Y⊆ ∷ F⊆ ∷ [] ⟩ ⟩ ⟩ =
    ⟨ B , ⟨ alB , 𝒦-mono stk (λ u u∈ → ⟨ R-ne , K-mono is j bs (length φ)
                                ⟨ (λ x → E (var x)) , ⟨ M.called-le (length φ) W⊆R , (λ _ z → z) ⟩ ⟩ u u∈ ⟩) w w∈' ⟩ ⟩
    where
    R = ⋆ ⟨ ⋆ ⟨ 𝒪 T⁺ (length φ) (σ̂ B) (ρ̂ B) a , ⟨ ρ̂ B rdi , ptt ⟩ ⟩ , ⟨ ρ̂ B rsi , ptt ⟩ ⟩
    W⊆R : mem W ⊆ R
    W⊆R w w∈W = ⟨ _ , ⟨ ⟨ _ , ⟨ F⊆ _ (∈-map⁺ _ w∈W) , ⟨ X⊆ , ext-ne _ e₁ ⟩ ⟩ ⟩ , ⟨ Y⊆ , ext-ne _ e₂ ⟩ ⟩ ⟩
    R-ne : nonempty R
    R-ne with E≢[]⇒nonempty-mem W≢
    ... | ⟨ w₀ , w₀∈ ⟩ = ⟨ w₀ , W⊆R w₀ w₀∈ ⟩

  {- Steps shrink the denotation of the state ---------------------------------}

  step-⊆ : ∀ s {s'} → step ds s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
  step-⊆ (run (movq a d ∷ is) j bs stk f φ ρ) e =
    put-step d (λ σ ρ → 𝒪 T⁺ (length φ) σ ρ a) {m = arg φ ρ a} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} {f = f} e λ A₀ V ea al V⊆ → grow a A₀ V al ea V⊆
  step-⊆ (run (subq a d ∷ is) j bs stk f φ ρ) e = put-step d Df {m = M} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} {f = f} e h
    where
    M = arg φ ρ a >>= λ w → readM φ ρ d >>= λ u → prim? sub u w
    Df = λ σ ρ' → primD sub ⟨ 𝒪 T⁺ (length φ) σ ρ' (loc d) , ⟨ 𝒪 T⁺ (length φ) σ ρ' a , ptt ⟩ ⟩
    h : PutH φ ρ M Df
    h A₀ V em al V⊆ with bind-inv (arg φ ρ a) em
    ... | ⟨ w , ⟨ ea , em' ⟩ ⟩ with bind-inv (readM φ ρ d) em'
    ... | ⟨ u , ⟨ ed , ep ⟩ ⟩ with mmap-inv out (δ? sub (obs u) (obs w)) ep
    ... | ⟨ o , ⟨ eo , refl ⟩ ⟩ with prim-ok sub u w eo
    ... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ with grow (loc d) A₀ (dconst n ∷ []) al ed (λ { _ (here refl) → n∈ })
    ... | ⟨ B , ⟨ alB , ⟨ E , n⊆ ⟩ ⟩ ⟩ with grow a B (dconst m ∷ []) alB ea (λ { _ (here refl) → m∈ })
    ... | ⟨ C , ⟨ alC , ⟨ E' , m⊆ ⟩ ⟩ ⟩ =
      ⟨ C , ⟨ alC , ⟨ Ext-trans E E'
      , (λ x x∈ → ⟨ n , ⟨ m , ⟨ 𝒪-ext (loc d) E' _ (n⊆ _ (here refl)) , ⟨ m⊆ _ (here refl) , 𝒱-out _ x (V⊆ x x∈) ⟩ ⟩ ⟩ ⟩) ⟩ ⟩ ⟩
  step-⊆ (run (cmpq a₂ a₁ ∷ is) j bs stk f φ ρ) e = flag-step Ff {m = M} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} e h
    where
    M = arg φ ρ a₁ >>= λ v → arg φ ρ a₂ >>= λ w → cmp v w
    Ff = λ σ ρ' → primD eq ⟨ 𝒪 T⁺ (length φ) σ ρ' a₁ , ⟨ 𝒪 T⁺ (length φ) σ ρ' a₂ , ptt ⟩ ⟩
    h : FlagH φ ρ M Ff
    h A₀ em al with bind-inv (arg φ ρ a₁) em
    ... | ⟨ v , ⟨ e₁ , em' ⟩ ⟩ with bind-inv (arg φ ρ a₂) em'
    ... | ⟨ w , ⟨ e₂ , ec ⟩ ⟩ with prim-ok eq v w (truth-inv _ ec)
    ... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , eo ⟩ ⟩ ⟩ ⟩ with grow a₁ A₀ (dconst n ∷ []) al e₁ (λ { _ (here refl) → n∈ })
    ... | ⟨ B , ⟨ alB , ⟨ E , n⊆ ⟩ ⟩ ⟩ with grow a₂ B (dconst m ∷ []) alB e₂ (λ { _ (here refl) → m∈ })
    ... | ⟨ C , ⟨ alC , ⟨ E' , m⊆ ⟩ ⟩ ⟩ =
      ⟨ C , ⟨ alC , ⟨ Ext-trans E E'
      , (λ { x refl → ⟨ n , ⟨ m , ⟨ 𝒪-ext a₁ E' _ (n⊆ _ (here refl)) , ⟨ m⊆ _ (here refl) , cong dout eo ⟩ ⟩ ⟩ ⟩ }) ⟩ ⟩ ⟩
  step-⊆ (run (sete d ∷ is) j bs stk (just b) φ ρ) e =
    put-step d (λ _ _ → 𝓕 (just b)) {m = just (bit b)} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} {f = just b} e λ { A₀ V refl al V⊆ → ⟨ A₀ , ⟨ al , ⟨ (λ l u z → z) , (λ x x∈ → 𝒱-out (bool b) x (V⊆ x x∈)) ⟩ ⟩ ⟩ }
  step-⊆ (run (testinl a ∷ is) j bs stk f φ ρ) e = flag-step Ff {m = arg φ ρ a >>= is-inl} {φ = φ} {ρ = ρ} {stk = stk} {is = is} {j = j} {bs = bs} e h
    where
    Ff = λ σ ρ' → isinl (𝒪 T⁺ (length φ) σ ρ' a)
    h : FlagH φ ρ (arg φ ρ a >>= is-inl) Ff
    h A₀ em al with bind-inv (arg φ ρ a) em
    ... | ⟨ T.inl u , ⟨ ea , refl ⟩ ⟩ with grow a A₀ (left (proj₁ (𝒱-nonempty u)) ∷ []) al ea (λ { _ (here refl) → proj₂ (𝒱-nonempty u) })
    ...   | ⟨ B , ⟨ alB , ⟨ E , l⊆ ⟩ ⟩ ⟩ = ⟨ B , ⟨ alB , ⟨ E , (λ { x refl → inj₁ ⟨ _ , ⟨ l⊆ _ (here refl) , refl ⟩ ⟩ }) ⟩ ⟩ ⟩
    h A₀ em al | ⟨ T.inr u , ⟨ ea , refl ⟩ ⟩ with grow a A₀ (right (proj₁ (𝒱-nonempty u)) ∷ []) al ea (λ { _ (here refl) → proj₂ (𝒱-nonempty u) })
    ...   | ⟨ B , ⟨ alB , ⟨ E , r⊆ ⟩ ⟩ ⟩ = ⟨ B , ⟨ alB , ⟨ E , (λ { x refl → inj₂ ⟨ _ , ⟨ r⊆ _ (here refl) , refl ⟩ ⟩ }) ⟩ ⟩ ⟩
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
    ⟨ rax-only W , ⟨ al , ⟨ A' , ⟨ W , ⟨ (λ x → al' (var x)) , ⟨ (λ _ z → z) , ⟨ ext-ne _ v
    , 𝒦-mono stk (K-mono is j bs' (length φ') ⟨ (λ _ _ z → z) , ⟨ r , (λ _ z → z) ⟩ ⟩) w w∈ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    where
    W = ext (A' (reg rax)) v
    al : AL (rax-only W) φ ρ
    al (reg rax) = subst (Ap W) (sym er) (ext-⊆ _ v (here-⊆ al' refl))
    al (reg rdi) = ap-[] (ρ rdi)
    al (reg rsi) = ap-[] (ρ rsi)
    al (var x) = ap-[] (φ ‼ x)
    r : ∀ g → ρ̂ A' g ⊆ called (mem W) g
    r rax = λ d d∈ → ∈-++⁺ˡ d∈
    r rdi = subst (λ L → mem L ⊆ ∅) (sym (al' (reg rdi))) (λ _ ())
    r rsi = subst (λ L → mem L ⊆ ∅) (sym (al' (reg rsi))) (λ _ ())
  step-⊆ (run [] retq bs (retK is j bs' φ' stk) f φ ρ) () w w∈ | nothing
  step-⊆ (run [] (jmp l) bs stk f φ ρ) e w w∈ with goto-inv (block-at bs l) e
  ... | ⟨ b , ⟨ bs' , ⟨ eb , refl ⟩ ⟩ ⟩ with w∈
  ... | ⟨ A , ⟨ al , w∈' ⟩ ⟩ =
    ⟨ A , ⟨ al , subst (λ B → w ∈ 𝒦 stk (B (σ̂ A) (ρ̂ A) (𝓕 f))) (sym (blocks-at bs l eb)) w∈' ⟩ ⟩
  step-⊆ (run [] (je l₁ l₂) bs stk (just true) φ ρ) e w w∈ with goto-inv (block-at bs l₁) e
  ... | ⟨ b , ⟨ bs' , ⟨ eb , refl ⟩ ⟩ ⟩ with w∈
  ... | ⟨ A , ⟨ al , w∈' ⟩ ⟩ =
    ⟨ A , ⟨ al , 𝒦-mono stk (λ u u∈ → inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → refl })
                               , ⟨ subst (λ B → u ∈ B (σ̂ A) (ρ̂ A) (𝓕 (just true))) (sym (blocks-at bs l₁ eb)) u∈ , ≈-single ⟩ ⟩ ⟩ ⟩) w w∈' ⟩ ⟩
  step-⊆ (run [] (je l₁ l₂) bs stk (just false) φ ρ) e w w∈ with goto-inv (block-at bs l₂) e
  ... | ⟨ b , ⟨ bs' , ⟨ eb , refl ⟩ ⟩ ⟩ with w∈
  ... | ⟨ A , ⟨ al , w∈' ⟩ ⟩ =
    ⟨ A , ⟨ al , 𝒦-mono stk (λ u u∈ → inj₂ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → refl })
                               , ⟨ subst (λ B → u ∈ B (σ̂ A) (ρ̂ A) (𝓕 (just false))) (sym (blocks-at bs l₂ eb)) u∈ , ≈-single ⟩ ⟩ ⟩ ⟩) w w∈' ⟩ ⟩

  ↠-⊆ : ∀ {s t} → s ↠ t → 𝒮 t ⊆ 𝒮 s
  ↠-⊆ done d d∈ = d∈
  ↠-⊆ {s} (st ∷↠ σ) d d∈ = step-⊆ s st d (↠-⊆ σ d d∈)

  {- Final states ----------------------------------------------------------------}

  private
    put-stop : ∀ d m {φ ρ K o} → putM d m φ ρ K ≡ stop o → o ≡ o-error
    put-stop d nothing refl = refl
    put-stop (var x) (just v) {φ} e with φ [ x ]≔ v
    put-stop (var x) (just v) refl | nothing = refl
    put-stop (var x) (just v) () | just _

    test-stop : ∀ m {K : Maybe Bool → State} {o} → test m K ≡ stop o → o ≡ o-error
    test-stop nothing refl = refl

    goto-stop : ∀ mb {σ f φ ρ o} → goto mb σ f φ ρ ≡ stop o → o ≡ o-error
    goto-stop nothing refl = refl

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

    error : ∀ {o} → o ≡ o-error → Answer o → ⊥
    error refl ans = ans refl

  {- a state that stops with an answer has an element of its shape -}
  final-shape : ∀ s {o} → step ds s ≡ stop o → Answer o → Σ[ d ∈ Value ] d ∈ 𝒮 s × ShapeOf o d
  final-shape (run (movq a d ∷ is) j bs stk f φ ρ) e ans = ⊥-elim (error (put-stop d (arg φ ρ a) {φ = φ} {ρ = ρ} {K = run is j bs stk f} e) ans)
  final-shape (run (subq a d ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (error (put-stop d (arg φ ρ a >>= λ w → readM φ ρ d >>= λ u → prim? sub u w) {φ = φ} {ρ = ρ} {K = run is j bs stk f} e) ans)
  final-shape (run (cmpq a₂ a₁ ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (error (test-stop (arg φ ρ a₁ >>= λ v → arg φ ρ a₂ >>= λ w → cmp v w) {K = λ f' → run is j bs stk f' φ ρ} e) ans)
  final-shape (run (sete d ∷ is) j bs stk (just b) φ ρ) e ans =
    ⊥-elim (error (put-stop d (just (bit b)) {φ = φ} {ρ = ρ} {K = run is j bs stk (just b)} e) ans)
  final-shape (run (sete d ∷ is) j bs stk nothing φ ρ) refl ans = ⊥-elim (ans refl)
  final-shape (run (testinl a ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (error (test-stop (arg φ ρ a >>= is-inl) {K = λ f' → run is j bs stk f' φ ρ} e) ans)
  final-shape (run (alloc sh as d ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (error (put-stop d (args φ ρ [] as (build sh)) {φ = φ} {ρ = ρ} {K = run is j bs stk f} e) ans)
  final-shape (run (load fl a d ∷ is) j bs stk f φ ρ) e ans =
    ⊥-elim (error (put-stop d (arg φ ρ a >>= get-field fl) {φ = φ} {ρ = ρ} {K = run is j bs stk f} e) ans)
  final-shape (run (callq a ∷ is) j bs stk f φ ρ) e ans = ⊥-elim (error (callq-stop (arg φ ρ a) {retK is j bs φ stk} {ρ} e) ans)
  final-shape (run [] retq bs halt f φ ρ) e ans with ρ rax in er
  final-shape (run [] retq bs halt f φ ρ) refl ans | just v with 𝒱-shape v
  ... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ d , ⟨ ⟨ rax-only (d ∷ []) , ⟨ al , here refl ⟩ ⟩ , sh ⟩ ⟩
    where
    al : AL (rax-only (d ∷ [])) φ ρ
    al (reg rax) = subst (Ap (d ∷ [])) (sym er) (λ { _ (here refl) → d∈ })
    al (reg rdi) = ap-[] (ρ rdi)
    al (reg rsi) = ap-[] (ρ rsi)
    al (var x) = ap-[] (φ ‼ x)
  final-shape (run [] retq bs halt f φ ρ) refl ans | nothing = ⊥-elim (ans refl)
  final-shape (run [] retq bs (retK is j bs' φ' stk) f φ ρ) e ans with ρ rax
  final-shape (run [] retq bs (retK is j bs' φ' stk) f φ ρ) () ans | just v
  final-shape (run [] retq bs (retK is j bs' φ' stk) f φ ρ) refl ans | nothing = ⊥-elim (ans refl)
  final-shape (run [] (jmp l) bs stk f φ ρ) e ans = ⊥-elim (error (goto-stop (block-at bs l) {stk} {f} {φ} {ρ} e) ans)
  final-shape (run [] (je l₁ l₂) bs stk (just true) φ ρ) e ans = ⊥-elim (error (goto-stop (block-at bs l₁) {stk} {just true} {φ} {ρ} e) ans)
  final-shape (run [] (je l₁ l₂) bs stk (just false) φ ρ) e ans = ⊥-elim (error (goto-stop (block-at bs l₂) {stk} {just false} {φ} {ρ} e) ans)
  final-shape (run [] (je l₁ l₂) bs stk nothing φ ρ) refl ans = ⊥-elim (ans refl)

{- Soundness ------------------------------------------------------------------}

{- a well-formed program that terminates with an answer o has an element
   of the shape of o in its denotation -}
soundness : ∀ P → WF P → ∀ {o} → Terminates (sem P) o → Answer o
  → Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₚ × ShapeOf o d
soundness (program ds (body n bs b)) ⟨ wfd , ⟨ cs , con ⟩ ⟩ ⟨ s , ⟨ σ , fin ⟩ ⟩ ans
    with final-shape ds wfd con s fin ans
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ with ↠-⊆ ds wfd con (Common.star→↠ ds σ) d d∈
... | ⟨ A , ⟨ al , d∈₀ ⟩ ⟩ =
  ⟨ d , ⟨ Mono.body-mono TT n n bs b cs ⟨ (λ x → ap-zeros ds wfd con (A (var x)) n x (al (var x))) , ⟨ r , (λ _ z → z) ⟩ ⟩ d
            (subst (λ m → d ∈ K ds wfd con (Block.instrs b) (Block.jump b) bs m _ _ ∅) (length-replicate n) d∈₀)
        , sh ⟩ ⟩
  where
  TT : ∀ k → k < length ds → T⁺ ds wfd con k ⊆ table ds k
  TT k k< x (inj₁ x∈) = x∈
  TT k k< x (inj₂ refl) = Common.ν-table ds ds k k<
  r : ∀ g → ρ̂ ds wfd con A g ⊆ called (zerosD 0) g
  r rax = al (reg rax)
  r rdi = subst (λ L → mem L ⊆ ∅) (sym (al (reg rdi))) (λ _ ())
  r rsi = subst (λ L → mem L ⊆ ∅) (sym (al (reg rsi))) (λ _ ())
