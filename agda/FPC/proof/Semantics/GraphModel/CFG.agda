{-

  Lemmas about the semantics of CFGμ in the graph model
  (FPC/Semantics/GraphModel/CFG.agda), and about the simple expressions it
  shares with Impμ, as for CFGᵀ: a simple expression is monotone in its
  atoms (𝒮-⊆, hence a congruence in the table, 𝒮-≃), and a tail and the
  blocks are monotone in the frame (tail-mono, blocks-mono).

  A tail reads only the slots that are initialized where it starts, so
  it means the same in two frames that agree on those slots (Agree,
  tail-agree), given blocks that mean the same in frames that agree on
  the slots initialized at their entries (RespB, blocks-agree). A write
  to a slot keeps frames in agreement (agree-≔), and a write to a slot
  that is not initialized changes no initialized slot (agree-fresh).

-}

module FPC.proof.Semantics.GraphModel.CFG where

open import FPC.Semantics.GraphModel.CFG public
open import FPC.Semantics.GraphModel.Imp using (𝒜s)
open import FPC.proof.Semantics.GraphModel.Ops using (Table; _[_≔_]; ≔-~)

open import proof.Framework.GraphModel.Prelude
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres)
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.Env using (_⊆ₑ_)
open import proof.Semantics.Graph.Prim using (primD-mono)
open import FPC.proof.Semantics.GraphModel.Binders using (let-≃; case-≃)
open import FPC.Language.Type
open import FPC.Language.CFG hiding (_⊆_)
open import FPC.Language.Imp using (Atm; var; lit; ref; atm; pair; callc; tuple;
  get; inl; inr; prim; fold; unfold; _∉_; ∈-⊆; ∈∉-idx; ⊆-refl)
  renaming (_∈_ to _∈ᴵ_; _⊆_ to _⊆ᴵ_)
open import FPC.Framework.AllUtil using (All; []; _∷_; pos)

open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Nat using (suc; _≟_)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym;
  cong)
open import Relation.Nullary using (yes; no)

module _ {Σ Δ I} {T T' : Table Σ} {σ σ'}
  (h : ∀ {A} (a : Atm Σ Δ I A) → 𝒜 a T σ ⊆ 𝒜 a T' σ') where

  𝒜s-⊆ : ∀ {Δs} (as : All (Atm Σ Δ I) Δs)
    → results-rel-pres _⊆_ (replicate (length Δs) ■) (𝒜s as T σ) (𝒜s as T' σ')
  𝒜s-⊆ [] = ptt
  𝒜s-⊆ (a ∷ as) = ⟨ lift (h a) , 𝒜s-⊆ as ⟩

  𝒮-⊆ : ∀ {A} (s : Simple Σ Δ I A) → 𝒮 s T σ ⊆ 𝒮 s T' σ'
  𝒮-⊆ (atm a) = h a
  𝒮-⊆ (pair a b) = lower (pair-mono _ _ ⟨ lift (h a) , ⟨ lift (h b) , ptt ⟩ ⟩)
  𝒮-⊆ (callc f a) = lower (⋆-mono _ _
    ⟨ ⋆-mono _ _
        ⟨ car-mono _ _ ⟨ lift (h f) , ptt ⟩
          , ⟨ cdr-mono _ _ ⟨ lift (h f) , ptt ⟩ , ptt ⟩ ⟩
            , ⟨ lift (h a) , ptt ⟩ ⟩)
  𝒮-⊆ (tuple as) = lower (𝒯-mono _ _ _ (𝒜s-⊆ as))
  𝒮-⊆ (get i a) = lower (proj-mono (pos i) _ _ ⟨ lift (h a) , ptt ⟩)
  𝒮-⊆ (inl a) = lower (inl-mono _ _ ⟨ lift (h a) , ptt ⟩)
  𝒮-⊆ (inr a) = lower (inr-mono _ _ ⟨ lift (h a) , ptt ⟩)
  𝒮-⊆ (prim p a b) =
    lower (primD-mono p _ _ ⟨ lift (h a) , ⟨ lift (h b) , ptt ⟩ ⟩)
  𝒮-⊆ (fold a) = h a
  𝒮-⊆ (unfold a) = h a

{- an atom, in the table and the frame -}
𝒜-⊆ : ∀ {Σ Δ I A} {T T' : Table Σ} {σ σ'}
  → (∀ {s} (f : Σ ∋ s) → T f ⊆ T' f)
  → σ ⊆ₑ σ'
  → ∀ (a : Atm Σ Δ I A)
  → 𝒜 a T σ ⊆ 𝒜 a T' σ'
𝒜-⊆ h s (var x _) = s (idx x)
𝒜-⊆ h s (lit B c) = λ _ z → z
𝒜-⊆ h s (ref f) = h f

𝒮-≃ : ∀ {Σ Δ I A} {T T' : Table Σ}
  → (∀ {s} (f : Σ ∋ s) → T f ≃ T' f)
  → ∀ (s : Simple Σ Δ I A) σ
  → 𝒮 s T σ ≃ 𝒮 s T' σ
𝒮-≃ TT s σ =
  ⟨ 𝒮-⊆ (𝒜-⊆ (λ f → proj₁ (TT f)) (λ _ _ z → z)) s
    , 𝒮-⊆ (𝒜-⊆ (λ f → proj₂ (TT f)) (λ _ _ z → z)) s ⟩

𝒜-mono : ∀ {Σ Δ I A} {T : Table Σ} {σ σ'}
  → σ ⊆ₑ σ'
  → ∀ (a : Atm Σ Δ I A)
  → 𝒜 a T σ ⊆ 𝒜 a T σ'
𝒜-mono = 𝒜-⊆ (λ _ _ z → z)

≔-mono : ∀ {σ σ' : Env Value} {X X'} i
  → σ ⊆ₑ σ'
  → X ⊆ X'
  → σ [ i ≔ X ] ⊆ₑ σ' [ i ≔ X' ]
≔-mono i = ≔-~ _⊆_ i

module _ {Σ} {T : Table Σ} where

  MonoB : ∀ {Δ} {Bs : List (Inits Δ)} → Meanings Bs → Set₁
  MonoB B = ∀ {I} (l : _ ∋ I) {σ σ'} → σ ⊆ₑ σ' → B l σ ⊆ B l σ'

  tail-mono : ∀ {R Δ Bs I} (t : Tail Σ R Δ Bs I) {B : Meanings Bs}
    → MonoB B
    → ∀ {σ σ'}
    → σ ⊆ₑ σ'
    → ⟦ t ⟧ᵗ T B σ ⊆ ⟦ t ⟧ᵗ T B σ'
  tail-mono (return s) mB σ⊆ = 𝒮-⊆ (𝒜-mono σ⊆) s
  tail-mono (seq x s p t) mB σ⊆ = lower (⋆-mono _ _
    ⟨ Λ-mono _ _
        ⟨ (λ X Y X⊆ → lift (tail-mono t mB (≔-mono (idx x) σ⊆ X⊆)))
          , ptt ⟩
    , ⟨ lift (𝒮-⊆ (𝒜-mono σ⊆) s) , ptt ⟩ ⟩)
  tail-mono (goto l) mB σ⊆ = mB l σ⊆
  tail-mono (case a x y l₁ l₂) mB σ⊆ = lower (𝒞-mono _ _
    ⟨ lift (𝒜-mono σ⊆ a)
        , ⟨ (λ X Y X⊆ → lift (mB l₁ (≔-mono (idx x) σ⊆ X⊆)))
    , ⟨ (λ X Y X⊆ → lift (mB l₂ (≔-mono (idx y) σ⊆ X⊆))) , ptt ⟩ ⟩ ⟩)

  blocks-mono : ∀ {R Δ Bs} (bs : Blocks Σ R Δ Bs) → MonoB (blocks bs T)
  blocks-mono (bs ▷ t) Z = tail-mono t (blocks-mono bs)
  blocks-mono (bs ▷ t) (S l) = blocks-mono bs l

{- Agreement --------------------------------------------------------------}

{- frames that agree on the initialized slots I -}
Agree : ∀ {Δ} → Inits Δ → Env Value → Env Value → Set₁
Agree {Δ} I σ σ' = ∀ {A} (z : Δ ∋ A) → .(z ∈ᴵ I) → σ (idx z) ≡ σ' (idx z)

{- a slot initialized after a write to x, at another position than x,
   was initialized before -}
∈-⊕⁻ : ∀ {Δ A B} {I : Inits Δ} (x : Δ ∋ A) (z : Δ ∋ B)
  → z ∈ᴵ I ⊕ x
  → idx x ≢ idx z
  → z ∈ᴵ I
∈-⊕⁻ {I = b ∷ I} Z Z t n = ⊥-elim (n refl)
∈-⊕⁻ {I = b ∷ I} Z (S z) t n = t
∈-⊕⁻ {I = b ∷ I} (S x) Z t n = t
∈-⊕⁻ {I = b ∷ I} (S x) (S z) t n = ∈-⊕⁻ {I = I} x z t (λ e → n (cong suc e))

agree-⊆ : ∀ {Δ} {I J : Inits Δ} {σ σ'}
  → .(J ⊆ᴵ I)
  → Agree I σ σ'
  → Agree J σ σ'
agree-⊆ {I = I} {J} p a z i = a z (∈-⊆ {I = I} {J} z i p)

{- a write to slot x, in frames that agree on I, gives frames that agree
   on the slots J initialized after it -}
agree-≔ : ∀ {Δ A} {I J : Inits Δ} {σ σ'} (x : Δ ∋ A) {X}
  → .(J ⊆ᴵ I ⊕ x)
  → Agree I σ σ'
  → Agree J (σ [ idx x ≔ X ]) (σ' [ idx x ≔ X ])
agree-≔ {I = I} {J} x p a z i with idx x ≟ idx z
... | yes _ = refl
... | no n = a z (∈-⊕⁻ {I = I} x z (∈-⊆ {I = I ⊕ x} {J} z i p) n)

{- a write to a slot y that is not initialized changes no initialized
   slot -}
agree-fresh : ∀ {Δ A} {I : Inits Δ} {σ} (y : Δ ∋ A) {Y}
  → .(y ∉ I)
  → Agree I σ (σ [ idx y ≔ Y ])
agree-fresh {I = I} y n z i with idx y ≟ idx z
... | yes e = ⊥-elim (∈∉-idx {I = I} z y i n (sym e))
... | no _ = refl

module _ {Σ Δ I} {T T' : Table Σ} {σ σ'}
  (TT : ∀ {s} (f : Σ ∋ s) → T f ≃ T' f) (ag : Agree I σ σ') where

  𝒜-agree : ∀ {A} (a : Atm Σ Δ I A) → 𝒜 a T σ ≃ 𝒜 a T' σ'
  𝒜-agree (var x i) rewrite ag x i = ≃-refl
  𝒜-agree (lit B c) = ≃-refl
  𝒜-agree (ref f) = TT f

  𝒮-agree : ∀ {A} (s : Simple Σ Δ I A) → 𝒮 s T σ ≃ 𝒮 s T' σ'
  𝒮-agree s =
    ⟨ 𝒮-⊆ (λ a → proj₁ (𝒜-agree a)) s
    , 𝒮-⊆ {T = T'} {T} {σ'} {σ} (λ a → proj₂ (𝒜-agree a)) s ⟩

module _ {Σ} {T T' : Table Σ} (TT : ∀ {s} (f : Σ ∋ s) → T f ≃ T' f) where

  {- the blocks B and B' mean the same in frames that agree on the slots
     initialized at their entries -}
  RespB : ∀ {Δ} {Bs : List (Inits Δ)} → Meanings Bs → Meanings Bs → Set₁
  RespB {Bs = Bs} B B' =
    ∀ {I} (l : Bs ∋ I) {σ σ'} → Agree I σ σ' → B l σ ≃ B' l σ'

  tail-agree : ∀ {R Δ Bs I} (t : Tail Σ R Δ Bs I) {B B' : Meanings Bs}
    → RespB B B'
    → ∀ {σ σ'}
    → Agree I σ σ'
    → ⟦ t ⟧ᵗ T B σ ≃ ⟦ t ⟧ᵗ T' B' σ'
  tail-agree (return s) rB ag = 𝒮-agree TT ag s
  tail-agree {I = I} (seq x s p t) rB {σ} {σ'} ag =
    let-≃ (𝒮-agree TT ag s) λ X _ _ →
      tail-agree t rB {σ [ idx x ≔ X ]} {σ' [ idx x ≔ X ]}
        (agree-≔ {I = I} {σ = σ} {σ'} x p ag)
  tail-agree (goto l) rB ag = rB l ag
  tail-agree {I = I} (case a x y l₁ l₂) rB {σ} {σ'} ag =
    case-≃ (𝒜-agree TT ag a)
      (λ X _ _ → rB l₁ {σ [ idx x ≔ X ]} {σ' [ idx x ≔ X ]}
        (agree-≔ {I = I} {σ = σ} {σ'} x (⊆-refl {I = I ⊕ x}) ag))
      (λ X _ _ → rB l₂ {σ [ idx y ≔ X ]} {σ' [ idx y ≔ X ]}
        (agree-≔ {I = I} {σ = σ} {σ'} y (⊆-refl {I = I ⊕ y}) ag))

  blocks-agree : ∀ {R Δ Bs} (bs : Blocks Σ R Δ Bs)
    → RespB (blocks bs T) (blocks bs T')
  blocks-agree (bs ▷ t) Z = tail-agree t (blocks-agree bs)
  blocks-agree (bs ▷ t) (S l) = blocks-agree bs l
