{-

  Correctness of select instructions (CFG → X86, Compiler/Select.agda):
  the meaning of the X86 program (Untyped/Semantics/Graph/X86.agda) is that of the CFG
  program (Semantics/Graph/CFG.agda), given that each global definition has at least
  2 slots, its parameters (Defs); the programs that compile-cfg produces
  do (defs-2).

    select-correct : Defs ds → ⟦ select P ⟧ₚ ≃ ⟦ P ⟧ₚ

  The X86 state is the CFG store, with any registers and flag. The
  instructions of x := r, then κ, mean x := r; K in CFG when κ means K
  with any registers and flag (sel, Fits); those of return r leave the
  value of r in %rax. Each case is a congruence: the instructions compute
  r through registers, and only the final move to x binds, as CFG does.
  The writes to registers and the flag before it are strict, but the
  value of r is nonempty only when theirs are, so they change nothing
  (strict-≃). The blocks map one to one (tail, blocks-≃).

  case a x l₁ l₂ tests the tag of a, binds the payload and branches on
  the flag; this is 𝒞 on a when a slot never holds both an inl and an
  inr (Tagged, Inv), which holds since the binders bind only consistent
  sets (case-core).

  The start of a global definition moves %rdi and %rsi to slots 0 and 1,
  strictly; this binds finite parts of the parameters, where CFG runs the
  body with them whole, so it needs that the meaning of a CFG tail is
  monotone in the store (Mono, frame-≃).

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (Results; results-rel-pres)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim using (primD; primD-mono; primD-≃)
open import Untyped.Language.Imp as I using (var; lit; fun-ref; atm; app; fst; snd; tuple; get; prim)
import Language.Prim as P
import Untyped.Language.CFG as C
open import Language.X86 hiding (fst; snd; get)
open import Untyped.Compiler.Select
open import Untyped.Compiler.Explicate using (explicate-body)
open import Untyped.Compiler.LiftLocals using (lift-defs)
open import Untyped.Compiler.Pipeline using (compile-x86; compile-cfg)
open import Untyped.Semantics.Graph.Imp using (Table; Store; _[_↦_]; checked; 𝒜; 𝒜s; 𝒮; zeros; frame)
open import Untyped.Semantics.Graph.CFG
  using () renaming (⟦_⟧[_] to ⟪_⟫[_]; Blocks to Blocksₜ; blocks to blocksₜ; table to tableₜ; ⟦_⟧ₚ to ⟪_⟫ₚ)
open import Untyped.Semantics.Graph.X86
open import Untyped.proof.Semantics.Graph.X86 using (Tagged; Inv; tagged-≈; inv-↦; case-core)
open import Untyped.proof.Correctness.Graph.ExplicateCommon using (module Agreeing; checked-≃)
open import Untyped.proof.Correctness.Graph.ExplicateCorrectK using (compile-cfg-same)
open import Untyped.proof.Correctness.Graph.CompilerCorrect using (Same; Same-trans; ≃→Same)
open import Untyped.proof.Correctness.Graph.DelayFiniteCommon using (ρ₀)
open import proof.Semantics.Graph.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵢ)
import Language.ISWIM as ISWIM
open import Framework.Primitives using (base-rep)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.List.Properties using (++-identityʳ; length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc; _≤_; _≟_; _<?_; s≤s; z≤n)
open import Data.Nat.Properties using (m≤n⇒m⊔n≡n; m≤m+n; ≤-trans)
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (yes; no)

module Untyped.proof.Correctness.Graph.SelectCorrect where

open import proof.Framework.GraphModel.Laws using (strict-≃; strict-≃₂; strict-≃₃; ⋆-ne)

{- No slot holds both an inl and an inr ------------------------------------------------}

tagged-table : ∀ ds k → Tagged (table ds k)
tagged-table [] k ()
tagged-table (b ∷ bs) k with k ≟ length bs
... | yes _ = λ ()
... | no _ = tagged-table bs k

{- The meaning of a CFG tail is monotone in the store ------------------------------------}

infix 4 _⊆ₛ_
_⊆ₛ_ : Store → Store → Set
σ ⊆ₛ σ' = ∀ y → σ y ⊆ σ' y

module Mono (T : Table) (n : ℕ) where

  ↦-mono : ∀ {σ σ' x X Y} → σ ⊆ₛ σ' → X ⊆ Y → σ [ x ↦ X ] ⊆ₛ σ' [ x ↦ Y ]
  ↦-mono {x = x} s X⊆ y with y ≟ x
  ... | yes _ = X⊆
  ... | no _ = s y

  𝒜-mono : ∀ a {σ σ'} → σ ⊆ₛ σ' → 𝒜 T n σ a ⊆ 𝒜 T n σ' a
  𝒜-mono (var x) s with x <? n
  ... | yes _ = s x
  ... | no _ = λ _ z → z
  𝒜-mono (lit B k) s = λ _ z → z
  𝒜-mono (fun-ref k) s = λ _ z → z

  𝒜s-mono : ∀ as {σ σ'} → σ ⊆ₛ σ' → results-rel-pres _⊆_ (replicate (length as) ■) (𝒜s T n σ as) (𝒜s T n σ' as)
  𝒜s-mono [] s = ptt
  𝒜s-mono (a ∷ as) s = ⟨ lift (𝒜-mono a s) , 𝒜s-mono as s ⟩

  𝒮-mono : ∀ r {σ σ'} → σ ⊆ₛ σ' → 𝒮 T n σ r ⊆ 𝒮 T n σ' r
  𝒮-mono (atm a) s = 𝒜-mono a s
  𝒮-mono (app f e a) s = lower (⋆-mono _ _ ⟨ ⋆-mono _ _ ⟨ lift (𝒜-mono f s) , ⟨ lift (𝒜-mono e s) , ptt ⟩ ⟩
                                           , ⟨ lift (𝒜-mono a s) , ptt ⟩ ⟩)
  𝒮-mono (I.pair a b) s = lower (pair-mono _ _ ⟨ lift (𝒜-mono a s) , ⟨ lift (𝒜-mono b s) , ptt ⟩ ⟩)
  𝒮-mono (fst a) s = lower (car-mono _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (snd a) s = lower (cdr-mono _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (tuple as) s = lower (𝒯-mono (length as) _ _ (𝒜s-mono as s))
  𝒮-mono (get i a) s = lower (proj-mono i _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (I.inl a) s = lower (inl-mono _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (I.inr a) s = lower (inr-mono _ _ ⟨ lift (𝒜-mono a s) , ptt ⟩)
  𝒮-mono (prim p a b) s = lower (primD-mono p _ _ ⟨ lift (𝒜-mono a s) , ⟨ lift (𝒜-mono b s) , ptt ⟩ ⟩)

  checked-mono : ∀ x {D D'} → D ⊆ D' → checked n x D ⊆ checked n x D'
  checked-mono x D⊆ with x <? n
  ... | yes _ = D⊆
  ... | no _ = λ _ z → z

  MonoB : Blocksₜ → Set₁
  MonoB B = ∀ l {σ σ'} → σ ⊆ₛ σ' → B l σ ⊆ B l σ'

  tail-mono : ∀ t {B} → MonoB B → ∀ {σ σ'} → σ ⊆ₛ σ' → ⟪ t ⟫[ T ] n B σ ⊆ ⟪ t ⟫[ T ] n B σ'
  tail-mono (C.return r) mB s = 𝒮-mono r s
  tail-mono (C.seq x r t) mB s = checked-mono x (lower (⋆-mono _ _
    ⟨ Λ-mono _ _ ⟨ (λ X Y X⊆ → lift (tail-mono t mB (↦-mono s X⊆))) , ptt ⟩ , ⟨ lift (𝒮-mono r s) , ptt ⟩ ⟩))
  tail-mono (C.goto l) mB s = mB l s
  tail-mono (C.case a x l₁ l₂) mB s = checked-mono x (lower (𝒞-mono _ _
    ⟨ lift (𝒜-mono a s) , ⟨ (λ X Y X⊆ → lift (mB l₁ (↦-mono s X⊆))) , ⟨ (λ X Y X⊆ → lift (mB l₂ (↦-mono s X⊆))) , ptt ⟩ ⟩ ⟩))

  blocks-mono : ∀ bs → MonoB (blocksₜ T n bs)
  blocks-mono [] l s = λ _ ()
  blocks-mono (t ∷ bs) l s with l ≟ length bs
  ... | yes _ = tail-mono t (blocks-mono bs) s
  ... | no _ = blocks-mono bs l s

prim-ne : ∀ p {D E} → nonempty (primD p ⟨ D , ⟨ E , ptt ⟩ ⟩) → nonempty D
prim-ne p ⟨ w , ⟨ k , ⟨ m , ⟨ k∈ , _ ⟩ ⟩ ⟩ ⟩ = ⟨ _ , k∈ ⟩

checked-⊆ : ∀ n x {D} → checked n x D ⊆ D
checked-⊆ n x with x <? n
... | yes _ = λ _ z → z
... | no _ = λ _ ()

{- The pass preserves meanings ---------------------------------------------------------}

{- for tables T (of X86) and T' (of CFG) that agree -}
module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TL : ∀ k → Tagged (T k)) (n : ℕ) where

  open Agreeing TT n using (𝒜-≃; 𝒮-≃)

  atm-≡ : ∀ a {σ ρ} → 𝒪 T n σ ρ (select-atm a) ≡ 𝒜 T n σ a
  atm-≡ (var x) = refl
  atm-≡ (lit B k) = refl
  atm-≡ (fun-ref k) = refl

  atm-≃ : ∀ a {σ ρ} → 𝒪 T n σ ρ (select-atm a) ≃ 𝒜 T' n σ a
  atm-≃ a {σ} = ≃-trans (≃-reflexive (atm-≡ a)) (𝒜-≃ a σ)

  tagged-atm : ∀ a {σ ρ} → Inv σ → Tagged (𝒪 T n σ ρ (select-atm a))
  tagged-atm (var x) i with x <? n
  ... | yes _ = i x
  ... | no _ = λ ()
  tagged-atm (lit B k) i = λ ()
  tagged-atm (fun-ref k) i = TL k

  𝒪s-≡ : ∀ as {σ ρ} → _≡_ {A = Σ ℕ λ m → Results (𝒫 Value) (replicate m ■)}
    ⟨ length (map select-atm as) , 𝒪s T n σ ρ (map select-atm as) ⟩ ⟨ length as , 𝒜s T n σ as ⟩
  𝒪s-≡ [] = refl
  𝒪s-≡ (a ∷ as) = cong₂ (λ D p → ⟨ suc (proj₁ p) , ⟨ D , proj₂ p ⟩ ⟩) (atm-≡ a) (𝒪s-≡ as)

  {- κ, what runs after d is assigned, means K with any registers and flag; or
     returns d -}
  Fits : Loc → Kont → (Store → 𝒫 Value) → Set₁
  Fits (var x) κ K = ∀ σ → Inv σ → ∀ ρ φ → κ σ ρ φ ≃ K σ
  Fits (reg g) κ K = ∀ σ ρ φ → κ σ ρ φ ≃ ρ g

  {- d := D; K, in CFG -}
  after : Loc → (Store → 𝒫 Value) → Store → 𝒫 Value → 𝒫 Value
  after (var x) K σ D = checked n x (⋆ ⟨ Λ ⟨ (λ X → K (σ [ x ↦ X ])) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
  after (reg g) K σ D = D

  ≔-same : ∀ g {ρ D} → (ρ [ g ≔ D ]) g ≡ D
  ≔-same rax = refl
  ≔-same rdi = refl
  ≔-same rsi = refl

  put-≃ : ∀ d {κ K D D' σ ρ φ} → Fits d κ K → Inv σ → D ≃ D' → put n d D κ σ ρ φ ≃ after d K σ D'
  put-≃ (var x) {κ} {K} {σ = σ} {ρ} {φ} fits i D≃ =
    checked-≃ n {x} (⋆-≃ (Λ-≃ {λ X → κ (σ [ x ↦ X ]) ρ φ} {λ X → K (σ [ x ↦ X ])}
                            λ V _ c → fits _ (inv-↦ i (tagged-≈ c)) ρ φ) D≃)
  put-≃ (reg g) {D = D} {σ = σ} {ρ} {φ} fits i D≃ = strict-≃ (≃-trans e D≃) (λ w w∈ → ⟨ w , proj₁ e w w∈ ⟩)
    where e = ≃-trans (fits σ (ρ [ g ≔ D ]) φ) (≃-reflexive (≔-same g))

  put-ne : ∀ d {D κ σ ρ φ} w → w ∈ put n d D κ σ ρ φ → nonempty D
  put-ne (var x) w w∈ with checked-⊆ n x w w∈
  ... | ⟨ V , ⟨ _ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ne-mem ne V⊆
  put-ne (reg g) w w∈ = proj₁ w∈

  case-ne : ∀ x {I P : 𝒫 Value} {F₁ F₂ : 𝒫 Value → 𝒫 Value} w
    → w ∈ checked n x (⋆ ⟨ Λ ⟨ (λ X → 𝒞 ⟨ I , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩) , ptt ⟩ , ⟨ P , ptt ⟩ ⟩)
    → nonempty I
  case-ne x w w∈ with checked-⊆ n x w w∈
  ... | ⟨ V , ⟨ ⟨ inj₁ ⟨ v , ⟨ _ , ⟨ l , _ ⟩ ⟩ ⟩ , _ ⟩ , _ ⟩ ⟩ = ⟨ _ , l v (here refl) ⟩
  ... | ⟨ V , ⟨ ⟨ inj₂ ⟨ v , ⟨ _ , ⟨ r , _ ⟩ ⟩ ⟩ , _ ⟩ , _ ⟩ ⟩ = ⟨ _ , r v (here refl) ⟩

  case-≃ : ∀ x {A A' : 𝒫 Value} {F₁ F₂ G₁ G₂ : 𝒫 Value → 𝒫 Value} → A ≃ A' → Tagged A
    → (∀ V → V ≈ V → F₁ (mem V) ≃ G₁ (mem V)) → (∀ V → V ≈ V → F₂ (mem V) ≃ G₂ (mem V))
    → strict (isinl A) (checked n x (⋆ ⟨ Λ ⟨ (λ X → 𝒞 ⟨ isinl A , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩) , ptt ⟩
                                      , ⟨ payloadD A , ptt ⟩ ⟩))
      ≃ checked n x (𝒞 ⟨ A' , ⟨ G₁ , ⟨ G₂ , ptt ⟩ ⟩ ⟩)
  case-≃ x {A} {A'} {F₁} {F₂} {G₁} {G₂} A≃ tg F₁≃ F₂≃ =
    strict-≃ (checked-≃ n {x} (case-core {A} {A'} {F₁} {F₂} {G₁} {G₂} A≃ tg F₁≃ F₂≃)) (case-ne x {F₁ = F₁} {F₂})

  {- the instructions of r into d, then is -}
  sel : ∀ r d is {κ K} → Fits d (⟦ is ⟧ˢ T n κ) K → ∀ σ → Inv σ → ∀ ρ φ
    → ⟦ select-simple r d ++ is ⟧ˢ T n κ σ ρ φ ≃ after d K σ (𝒮 T' n σ r)
  sel (atm a) d is f σ i ρ φ = put-≃ d f i (atm-≃ a)
  sel (app g e a) d is f σ i ρ φ =
    strict-≃₃ {D₃ = ⋆ ⟨ ⋆ ⟨ G , ⟨ E , ptt ⟩ ⟩ , ⟨ A , ptt ⟩ ⟩} (put-≃ d f i (⋆-≃ (⋆-≃ (atm-≃ g) (atm-≃ e)) (atm-≃ a)))
      (put-ne d) (λ r → proj₂ (⋆-ne {⋆ ⟨ G , ⟨ E , ptt ⟩ ⟩} r)) (λ r → proj₂ (⋆-ne {G} (proj₁ (⋆-ne r))))
    where E = 𝒪 T n σ ρ (select-atm e)
          A = 𝒪 T n σ (ρ [ rdi ≔ E ]) (select-atm a)
          G = 𝒪 T n σ (ρ [ rdi ≔ E ] [ rsi ≔ A ]) (select-atm g)
  sel (I.pair a b) d is f σ i ρ φ = put-≃ d f i (mono-≃ pair-mono ⟨ lift (atm-≃ a) , ⟨ lift (atm-≃ b) , ptt ⟩ ⟩)
  sel (fst a) d is f σ i ρ φ = put-≃ d f i (mono-≃ car-mono ⟨ lift (atm-≃ a) , ptt ⟩)
  sel (snd a) d is f σ i ρ φ = put-≃ d f i (mono-≃ cdr-mono ⟨ lift (atm-≃ a) , ptt ⟩)
  sel (tuple as) d is f σ i ρ φ =
    put-≃ d f i (≃-trans (≃-reflexive (cong (λ p → 𝒯 (proj₁ p) (proj₂ p)) (𝒪s-≡ as))) (𝒮-≃ (tuple as) σ))
  sel (get j a) d is f σ i ρ φ = put-≃ d f i (proj-≃ j (atm-≃ a))
  sel (I.inl a) d is f σ i ρ φ = put-≃ d f i (inl-≃ (atm-≃ a))
  sel (I.inr a) d is f σ i ρ φ = put-≃ d f i (inr-≃ (atm-≃ a))
  sel (prim P.sub a b) d is f σ i ρ φ =
    strict-≃₂ (put-≃ d f i (primD-≃ P.sub (atm-≃ a) (atm-≃ b))) (put-ne d)
      (prim-ne P.sub {E = 𝒪 T n σ (ρ [ rax ≔ 𝒪 T n σ ρ (select-atm a) ]) (select-atm b)})
  sel (prim P.eq a b) d is f σ i ρ φ =
    strict-≃ (put-≃ d f i (primD-≃ P.eq (atm-≃ a) (atm-≃ b))) (put-ne d)

  {- the blocks B (of X86) and B' (of CFG) agree -}
  BR : Blocks → Blocksₜ → Set₁
  BR B B' = ∀ l σ → Inv σ → ∀ ρ φ → B l σ ρ φ ≃ B' l σ

  tail : ∀ t {B B'} → BR B B' → ∀ σ → Inv σ → ∀ ρ φ → ⟦ select-tail t ⟧ᵇ T n B σ ρ φ ≃ ⟪ t ⟫[ T' ] n B' σ
  tail (C.return r) {B} br σ i ρ φ =
    ≃-trans (≃-reflexive (cong (λ is → ⟦ is ⟧ˢ T n (⟦ retq ⟧ʲ B) σ ρ φ) (sym (++-identityʳ (select-simple r (reg rax))))))
            (sel r (reg rax) [] {K = λ _ → ∅} (λ σ ρ φ → ≃-refl) σ i ρ φ)
  tail (C.seq x r t) br σ i ρ φ = sel r (var x) _ (λ σ' i' ρ' φ' → tail t br σ' i' ρ' φ') σ i ρ φ
  tail (C.goto l) br σ i ρ φ = br l σ i ρ φ
  tail (C.case a x l₁ l₂) {B} {B'} br σ i ρ φ =
    case-≃ x {F₁ = λ X → B l₁ (σ [ x ↦ X ]) ρ (isinl A)} {λ X → B l₂ (σ [ x ↦ X ]) ρ (isinl A)}
                               {λ X → B' l₁ (σ [ x ↦ X ])} {λ X → B' l₂ (σ [ x ↦ X ])}
      (atm-≃ a) (tagged-atm a i)
      (λ V c → br l₁ _ (inv-↦ i (tagged-≈ c)) ρ _) (λ V c → br l₂ _ (inv-↦ i (tagged-≈ c)) ρ _)
    where A = 𝒪 T n σ ρ (select-atm a)

  blocks-≃ : ∀ bs → BR (blocks T n (map select-tail bs)) (blocksₜ T' n bs)
  blocks-≃ [] l σ i ρ φ = ≃-refl
  blocks-≃ (t ∷ bs) l σ i ρ φ with l ≟ length (map select-tail bs) | l ≟ length bs
  ... | yes _ | yes _ = tail t (blocks-≃ bs) σ i ρ φ
  ... | no _ | no _ = blocks-≃ bs l σ i ρ φ
  ... | yes l≡ | no l≢ = ⊥-elim (l≢ (trans l≡ (length-map select-tail bs)))
  ... | no l≢ | yes l≡ = ⊥-elim (l≢ (trans l≡ (sym (length-map select-tail bs))))

  {- the prologue binds parts of the parameters; F is the rest of the start -}
  frame-≃ : ∀ {F G : Store → 𝒫 Value} → (∀ σ → Inv σ → F σ ≃ G σ) → (∀ {σ σ'} → σ ⊆ₛ σ' → G σ ⊆ G σ')
    → 2 ≤ n → ∀ {V U} → V ≈ V → U ≈ U → V ≢ [] → U ≢ []
    → checked n 0 (⋆ ⟨ Λ ⟨ (λ X → checked n 1 (⋆ ⟨ Λ ⟨ (λ Y → F (zeros [ 0 ↦ X ] [ 1 ↦ Y ])) , ptt ⟩ , ⟨ mem U , ptt ⟩ ⟩)) , ptt ⟩
                         , ⟨ mem V , ptt ⟩ ⟩)
      ≃ G (frame (mem V) (mem U))
  frame-≃ {F} {G} FG mono le {V} {U} cV cU neV neU with 0 <? n | 1 <? n
  ... | no ¬p | _ = ⊥-elim (¬p (≤-trans (s≤s z≤n) le))
  ... | yes _ | no ¬p = ⊥-elim (¬p le)
  ... | yes _ | yes _ = ⟨ to , from ⟩
    where
    to : _
    to w ⟨ V' , ⟨ ⟨ ⟨ U' , ⟨ ⟨ w∈ , ⟨ _ , cU' ⟩ ⟩ , ⟨ U'⊆ , _ ⟩ ⟩ ⟩ , ⟨ _ , cV' ⟩ ⟩ , ⟨ V'⊆ , _ ⟩ ⟩ ⟩ =
      mono s w (proj₁ (FG _ i) w w∈)
      where
      s : zeros [ 0 ↦ mem V' ] [ 1 ↦ mem U' ] ⊆ₛ frame (mem V) (mem U)
      s 0 = V'⊆
      s 1 = U'⊆
      s (suc (suc y)) = λ _ z → z
      i : Inv (zeros [ 0 ↦ mem V' ] [ 1 ↦ mem U' ])
      i 0 = tagged-≈ cV'
      i 1 = tagged-≈ cU'
      i (suc (suc y)) = λ ()
    from : _
    from w w∈ = ⟨ V , ⟨ ⟨ ⟨ U , ⟨ ⟨ proj₂ (FG _ i) w (mono s w w∈) , ⟨ neU , cU ⟩ ⟩ , ⟨ (λ _ z → z) , neU ⟩ ⟩ ⟩
                         , ⟨ neV , cV ⟩ ⟩ , ⟨ (λ _ z → z) , neV ⟩ ⟩ ⟩
      where
      s : frame (mem V) (mem U) ⊆ₛ zeros [ 0 ↦ mem V ] [ 1 ↦ mem U ]
      s 0 = λ _ z → z
      s 1 = λ _ z → z
      s (suc (suc y)) = λ _ z → z
      i : Inv (zeros [ 0 ↦ mem V ] [ 1 ↦ mem U ])
      i 0 = tagged-≈ cV
      i 1 = tagged-≈ cU
      i (suc (suc y)) = λ ()

  {- the code of a global definition of at least 2 slots -}
  start-≃ : ∀ {m} → m ≡ n → 2 ≤ n → ∀ bs t {V U} → V ≈ V → U ≈ U → V ≢ [] → U ≢ []
    → run T m (select-body prologue (C.body n bs t)) zeros (args (mem V) (mem U)) ∅
      ≃ ⟪ t ⟫[ T' ] n (blocksₜ T' n bs) (frame (mem V) (mem U))
  start-≃ refl le bs t {V} {U} =
    frame-≃ {λ σ → ⟦ select-tail t ⟧ᵇ T n (blocks T n (map select-tail bs)) σ (args (mem V) (mem U)) ∅}
      {⟪ t ⟫[ T' ] n (blocksₜ T' n bs)} (λ σ i → tail t (blocks-≃ bs) σ i _ ∅)
    (Mono.tail-mono T' n t (Mono.blocks-mono T' n bs)) le

  code-≃ : ∀ bs t → 2 ≤ n → code T (select-body prologue (C.body n bs t)) ≃ Untyped.Semantics.Graph.CFG.code T' (C.body n bs t)
  code-≃ bs t le = Λ-≃ λ V neV cV → Λ-≃ λ U neU cU → start-≃ (m≤n⇒m⊔n≡n le) le bs t cV cU neV neU

{- Programs -----------------------------------------------------------------------------}

{- each global definition has at least 2 slots, for its parameters -}
Defs : List C.Body → Set
Defs = All (λ b → 2 ≤ C.Body.locals b)

table-≃ : ∀ ds → Defs ds → ∀ k → table (map (select-body prologue) ds) k ≃ tableₜ ds k
table-≃ [] _ k = ≃-refl
table-≃ (C.body n bs t ∷ ds) (le ∷ les) k with k ≟ length (map (select-body prologue) ds) | k ≟ length ds
... | yes _ | yes _ = code-≃ (table-≃ ds les) (tagged-table (map (select-body prologue) ds)) n bs t le
... | no _ | no _ = table-≃ ds les k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-map (select-body prologue) ds)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-map (select-body prologue) ds))))

select-correct : ∀ P → Defs (C.Program.defs P) → ⟦ select P ⟧ₚ ≃ ⟪ P ⟫ₚ
select-correct (C.program ds (C.body n bs t)) les =
  tail TT TL n t (blocks-≃ TT TL n bs) zeros (λ _ ()) (called (zeros 0)) ∅
  where
  TT = table-≃ ds les
  TL = tagged-table (map (select-body prologue) ds)

{- The whole compiler, into X86 ----------------------------------------------------------}

{- lift locals gives each global definition 2 + height slots -}
defs-2 : ∀ {ds} ms → Defs (map explicate-body (lift-defs {ds} ms))
defs-2 [] = []
defs-2 (m ∷ ms) = m≤m+n 2 _ ∷ defs-2 ms

compile-x86-same : ∀ (M : ISWIM.AST) → Same (⟦ M ⟧ᵢ ρ₀) ⟦ compile-x86 M ⟧ₚ
compile-x86-same M = Same-trans (compile-cfg-same M) (≃→Same (≃-sym (select-correct (compile-cfg M) (defs-2 _))))

compile-x86-correct-const : ∀ (M : ISWIM.AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ᵢ ρ₀ → const c ∈ ⟦ compile-x86 M ⟧ₚ)
  × (const c ∈ ⟦ compile-x86 M ⟧ₚ → const c ∈ ⟦ M ⟧ᵢ ρ₀)
compile-x86-correct-const M = proj₁ (compile-x86-same M)

compile-x86-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ᵢ ρ₀) → nonempty ⟦ compile-x86 M ⟧ₚ)
  × (nonempty ⟦ compile-x86 M ⟧ₚ → nonempty (⟦ M ⟧ᵢ ρ₀))
compile-x86-correct-nonempty M = proj₂ (compile-x86-same M)
