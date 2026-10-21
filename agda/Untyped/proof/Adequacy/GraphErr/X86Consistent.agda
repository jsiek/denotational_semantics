{-

  The table of every X86 program is consistent in the graph model with
  errors (Untyped/Semantics/GraphErr/X86.agda): table-con. Soundness
  (GraphErr/X86Soundness.agda) binds finite parts of the denotations of
  machine values, and code pointers denote entries of the table, so these
  must be consistent.

  A continuation is consistent (ConK) when it maps consistent stores,
  registers and flags to consistent sets; each instruction, jump and
  block preserves this, by the consistency of the error-propagating
  operators (proof/Framework/GraphModel/ErrorMonad.agda), and so the code
  of a definition, run in consistent frames and registers, is
  consistent when the table of the older definitions is.

-}

module Untyped.proof.Adequacy.GraphErr.X86Consistent where

open import Framework.Primitives using (Int)
open import Language.Prim using (sub; eq)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; _~_; Con; Con-⌈⌉; left; right; ⟨⟩)
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres; ■)
open import proof.Framework.GraphModel.OpsBase using (ℬ; ℬ-consis)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Semantics.GraphErr.Prim using (primᵐ-good)
open import proof.Framework.GraphModel.ContinuityBase using (consis)
open import Framework.GraphModel.Ops using (payloadD)
open import proof.Framework.GraphModel.Domain using (~-refl)
open import Language.X86
  renaming (pair to pairₛ; inl to inlₛ; inr to inrₛ; tuple to tupleₛ; fst to fstₛ; snd to sndₛ; get to getₛ)
open import Untyped.Semantics.GraphErr.X86

open import Data.Empty using (⊥-elim)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Nat using (ℕ; _≟_; _<?_; _⊔_)
open import Data.Product using (_×_; proj₁) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

_~ₛ_ : Store → Store → Set
σ ~ₛ σ' = ∀ x → Every _~_ (σ x) (σ' x)

_~ᵣ_ : Regs → Regs → Set
ρ ~ᵣ ρ' = ∀ g → Every _~_ (ρ g) (ρ' g)

ConK : Kont → Set₁
ConK κ = ∀ {σ σ' ρ ρ' F F'} → σ ~ₛ σ' → ρ ~ᵣ ρ' → Every _~_ F F' → Every _~_ (κ σ ρ F) (κ σ' ρ' F')

init~ : Every _~_ init init
init~ = Con-⌈⌉ ω

ℬ~ : ∀ B k → Every _~_ (ℬ B k ptt) (ℬ B k ptt)
ℬ~ B k = lower (ℬ-consis B k ptt ptt ptt)

↦~ : ∀ {σ σ' X X'} x → σ ~ₛ σ' → Every _~_ X X' → (σ [ x ↦ X ]) ~ₛ (σ' [ x ↦ X' ])
↦~ x σ~ X~ y with y ≟ x
... | yes _ = X~
... | no _ = σ~ y

≔~ : ∀ {ρ ρ' D D'} g → ρ ~ᵣ ρ' → Every _~_ D D' → (ρ [ g ≔ D ]) ~ᵣ (ρ' [ g ≔ D' ])
≔~ rax ρ~ D~ rax = D~
≔~ rax ρ~ D~ rdi = ρ~ rdi
≔~ rax ρ~ D~ rsi = ρ~ rsi
≔~ rdi ρ~ D~ rax = ρ~ rax
≔~ rdi ρ~ D~ rdi = D~
≔~ rdi ρ~ D~ rsi = ρ~ rsi
≔~ rsi ρ~ D~ rax = ρ~ rax
≔~ rsi ρ~ D~ rdi = ρ~ rdi
≔~ rsi ρ~ D~ rsi = D~

called~ : ∀ {R R'} → Every _~_ R R' → called R ~ᵣ called R'
called~ R~ rax = R~
called~ R~ rdi = init~
called~ R~ rsi = init~

args~ : ∀ {X X' Y Y'} → Every _~_ X X' → Every _~_ Y Y' → args X Y ~ᵣ args X' Y'
args~ X~ Y~ rax = init~
args~ X~ Y~ rdi = X~
args~ X~ Y~ rsi = Y~

zeros~ : zeros ~ₛ zeros
zeros~ x = ℬ~ Int (+ 0)

field~ : ∀ f {D D'} → Every _~_ D D' → Every _~_ (field′ f D) (field′ f D')
field~ fstₛ D~ = lower (consis (carᵐ-good {⊤}) tt _ _ ⟨ lift D~ , ptt ⟩)
field~ sndₛ D~ = lower (consis (cdrᵐ-good {⊤}) tt _ _ ⟨ lift D~ , ptt ⟩)
field~ (getₛ i) D~ = lower (consis (projᵐ-good {⊤} i) tt _ _ ⟨ lift D~ , ptt ⟩)
field~ payload D~ = payloadᵐ-consis D~

module _ (T : Table) (TC : ∀ k → Con (T k)) (n : ℕ) where

  read~ : ∀ {σ σ'} x → σ ~ₛ σ' → Every _~_ (read n σ x) (read n σ' x)
  read~ x σ~ with x <? n
  ... | yes _ = σ~ x
  ... | no _ = init~

  𝒪~ : ∀ {σ σ' ρ ρ'} a → σ ~ₛ σ' → ρ ~ᵣ ρ' → Every _~_ (𝒪 T n σ ρ a) (𝒪 T n σ' ρ' a)
  𝒪~ (loc (var x)) σ~ ρ~ = read~ x σ~
  𝒪~ (loc (reg g)) σ~ ρ~ = ρ~ g
  𝒪~ (imm B k) σ~ ρ~ = ℬ~ B k
  𝒪~ (label k) σ~ ρ~ = TC k

  𝒪s~ : ∀ {σ σ' ρ ρ'} as → σ ~ₛ σ' → ρ ~ᵣ ρ'
    → results-rel-pres (Every _~_) (replicate (length as) ■) (𝒪s T n σ ρ as) (𝒪s T n σ' ρ' as)
  𝒪s~ [] σ~ ρ~ = ptt
  𝒪s~ (a ∷ as) σ~ ρ~ = ⟨ lift (𝒪~ a σ~ ρ~) , 𝒪s~ as σ~ ρ~ ⟩

  object~ : ∀ {σ σ' ρ ρ'} sh as → σ ~ₛ σ' → ρ ~ᵣ ρ' → Every _~_ (object T n σ ρ sh as) (object T n σ' ρ' sh as)
  object~ pairₛ [] σ~ ρ~ = init~
  object~ pairₛ (a ∷ []) σ~ ρ~ = init~
  object~ pairₛ (a ∷ b ∷ []) σ~ ρ~ = lower (consis (pairᵐ-good {⊤}) tt _ _ ⟨ lift (𝒪~ a σ~ ρ~) , ⟨ lift (𝒪~ b σ~ ρ~) , ptt ⟩ ⟩)
  object~ pairₛ (a ∷ b ∷ c ∷ as) σ~ ρ~ = init~
  object~ tupleₛ as σ~ ρ~ = lower (consis (𝒯ᵐ-good {⊤} (length as)) tt _ _ (𝒪s~ as σ~ ρ~))
  object~ inlₛ [] σ~ ρ~ = init~
  object~ inlₛ (a ∷ []) σ~ ρ~ = lower (consis (inlᵐ-good {⊤}) tt _ _ ⟨ lift (𝒪~ a σ~ ρ~) , ptt ⟩)
  object~ inlₛ (a ∷ b ∷ as) σ~ ρ~ = init~
  object~ inrₛ [] σ~ ρ~ = init~
  object~ inrₛ (a ∷ []) σ~ ρ~ = lower (consis (inrᵐ-good {⊤}) tt _ _ ⟨ lift (𝒪~ a σ~ ρ~) , ptt ⟩)
  object~ inrₛ (a ∷ b ∷ as) σ~ ρ~ = init~

  checked~ : ∀ x {D D' E E'} → Every _~_ D D' → Every _~_ E E' → Every _~_ (frameᵐ n x D E) (frameᵐ n x D' E')
  checked~ x D~ E~ with x <? n
  ... | yes _ = E~
  ... | no _ = ≫=-consis D~ (λ _ → init~)

  put~ : ∀ d {D D' κ σ σ' ρ ρ' F F'} → Every _~_ D D' → ConK κ → σ ~ₛ σ' → ρ ~ᵣ ρ' → Every _~_ F F'
    → Every _~_ (put n d D κ σ ρ F) (put n d D' κ σ' ρ' F')
  put~ (var x) D~ κ~ σ~ ρ~ F~ =
    checked~ x D~ (lower (consis (letᵐ-good {⊤}) tt _ _ ⟨ lift D~ , ⟨ (λ X X' X~ → lift (κ~ (↦~ x σ~ X~) ρ~ F~)) , ptt ⟩ ⟩))
  put~ (reg g) D~ κ~ σ~ ρ~ F~ = ≫=-consis D~ (λ _ → κ~ σ~ (≔~ g ρ~ D~) F~)

  flag~ : ∀ {F₀ F₀' κ σ σ' ρ ρ'} → Every _~_ F₀ F₀' → ConK κ → σ ~ₛ σ' → ρ ~ᵣ ρ'
    → Every _~_ (flag F₀ κ σ ρ) (flag F₀' κ σ' ρ')
  flag~ F~ κ~ σ~ ρ~ = ≫=-consis F~ (λ _ → κ~ σ~ ρ~ F~)

  is~ : ∀ is {κ} → ConK κ → ConK (⟦ is ⟧ˢ T n κ)
  is~ [] κ~ = κ~
  is~ (movq a d ∷ is) κ~ σ~ ρ~ F~ = put~ d (𝒪~ a σ~ ρ~) (is~ is κ~) σ~ ρ~ F~
  is~ (subq a d ∷ is) κ~ σ~ ρ~ F~ =
    put~ d (lower (consis (primᵐ-good {⊤} sub) tt _ _ ⟨ lift (𝒪~ (loc d) σ~ ρ~) , ⟨ lift (𝒪~ a σ~ ρ~) , ptt ⟩ ⟩)) (is~ is κ~) σ~ ρ~ F~
  is~ (cmpq a₂ a₁ ∷ is) κ~ σ~ ρ~ F~ =
    flag~ (lower (consis (primᵐ-good {⊤} eq) tt _ _ ⟨ lift (𝒪~ a₁ σ~ ρ~) , ⟨ lift (𝒪~ a₂ σ~ ρ~) , ptt ⟩ ⟩)) (is~ is κ~) σ~ ρ~
  is~ (sete d ∷ is) κ~ σ~ ρ~ F~ = put~ d F~ (is~ is κ~) σ~ ρ~ F~
  is~ (testinl a ∷ is) κ~ σ~ ρ~ F~ = flag~ (isinlᵐ-consis (𝒪~ a σ~ ρ~)) (is~ is κ~) σ~ ρ~
  is~ (alloc sh as d ∷ is) κ~ σ~ ρ~ F~ = put~ d (object~ sh as σ~ ρ~) (is~ is κ~) σ~ ρ~ F~
  is~ (load f a d ∷ is) κ~ σ~ ρ~ F~ = put~ d (field~ f (𝒪~ a σ~ ρ~)) (is~ is κ~) σ~ ρ~ F~
  is~ (callq a ∷ is) κ~ σ~ ρ~ F~ = ≫=-consis R~ (λ _ → is~ is κ~ σ~ (called~ R~) init~)
    where R~ = lower (consis (callᵐ-good {⊤}) tt _ _ ⟨ lift (𝒪~ a σ~ ρ~) , ⟨ lift (ρ~ rdi) , ⟨ lift (ρ~ rsi) , ptt ⟩ ⟩ ⟩)

  jump~ : ∀ j {B} → (∀ l → ConK (B l)) → ConK (⟦ j ⟧ʲ B)
  jump~ retq B~ σ~ ρ~ F~ = ρ~ rax
  jump~ (jmp l) B~ = B~ l
  jump~ (je l₁ l₂) B~ σ~ ρ~ F~ =
    lower (consis (𝒞ᵐ-good {⊤}) tt _ _ ⟨ lift F~ , ⟨ (λ _ _ _ → lift (B~ l₁ σ~ ρ~ F~)) , ⟨ (λ _ _ _ → lift (B~ l₂ σ~ ρ~ F~)) , ptt ⟩ ⟩ ⟩)

  blocks~ : ∀ bs l → ConK (blocks T n bs l)
  blocks~ [] l σ~ ρ~ F~ = init~
  blocks~ (b ∷ bs) l with l ≟ length bs
  ... | yes _ = is~ (Block.instrs b) (jump~ (Block.jump b) (blocks~ bs))
  ... | no _ = blocks~ bs l

  run~ : ∀ b → ConK (run T n b)
  run~ (body _ bs b) = is~ (Block.instrs b) (jump~ (Block.jump b) (blocks~ bs))

code-con : ∀ T → (∀ k → Con (T k)) → ∀ b → Con (code T b)
code-con T TC b = ΛΛᵐ-con (λ X X' Y Y' X~ Y~ → run~ T TC (2 ⊔ Body.locals b) b zeros~ (args~ X~ Y~) init~)

{- the table of every program is consistent -}
table-con : ∀ ds k → Con (table ds k)
table-con [] k = errcode-con
table-con (b ∷ bs) k with k ≟ length bs
... | yes _ = code-con (table bs) (table-con bs) b
... | no _ = table-con bs k
