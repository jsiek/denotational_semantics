{-

  Correctness of typed select instructions (CFGᵀ → X86,
  Compiler/Select.agda) in the graph model: the X86 program
  (Semantics/Graph/X86.agda, unchanged) means what the CFGᵀ program does
  (Semantics/Graph/Typed/CFG.agda), for every CFGᵀ program.

  The X86 store holds the slots of the CFGᵀ frame at their levels (Rel):
  slot x is X86 variable lvl x. A tail runs within the frame, since its
  depth is at most the frame's (depth-≥, Compiler/SelectFacts).
  The instructions of s into d, then κ, mean d := s; K in CFGᵀ when κ
  means K with any registers and flag (sel, Fits, after); the writes to
  registers before the last move are strict, but the value of s is
  nonempty only when theirs are (strict-≃). A project's test instruction
  has a value exactly when the slot holds a value its tag accepts, and
  then the guard keeps the whole slot (guard-≃). A case tests the tag,
  binds the payload and branches on the flag: 𝒞 on a slot that never
  holds both an inl and an inr (Tagged, Inv; case-core). The start of a
  definition moves %rdi and %rsi to slots 0 and 1, which binds finite
  parts of the arguments, so it needs that a CFGᵀ tail is monotone in its
  frame (tail-mono). Blocks and definitions map one to one, by level.

-}

module proof.Correctness.Graph.SelectCorrect where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Framework.GraphModel.Laws using (strict-≃; strict-≃₂; ⋆-ne)
open import proof.Semantics.Graph.Prim using (primD; primD-mono; primD-≃)
open import proof.Framework.GraphModel.Env using (Env; _⊆ₑ_)
open import Framework.Primitives using (Int)
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋)
open import proof.Framework.Lookup using (lvl-<; lvl-⊑)
import Language.Prim as P
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.Imp using (Atm; var; lit; ref; atm; pack; callc; tuple; get; inl; inr; prim; inject; project)
import Language.Typed.CFG as C
open C using (Tail; return; seq; goto; case; Blocks; _▷_)
import Language.X86 as L
open L using (Loc; reg; rax; rdi; rsi; Instr; Block; block; jmp; je; retq)
open import Compiler.Select
open import proof.Compiler.SelectFacts using (depth-≥; len-defs; len-blocks)
import Semantics.Graph.X86 as X
open X using (Store; read; _[_↦_]; checked; zeros; _[_≔_]; isinl; called; args)
open import proof.Semantics.Graph.Typed.Ops using (Table; tables; accepts; guardᵖ; fun₄; init)
open import proof.Semantics.Graph.Typed.CFG using (⟦_⟧ᵗ; Meanings; blocks; drop; 𝒜; 𝒮; tail-mono; blocks-mono)
  renaming (code′ to codeᶜ; table to tableᶜ; ⟦_⟧ₚ to ⟦_⟧ᶜ; run to runᶜ)
open import Semantics.Graph.Typed.Imp using (𝒜s)
open import proof.Framework.GraphModel.DOpSig using (Results; RRs; mono-≃)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin)
open import Data.Integer using (0ℤ)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; suc; _≤_; _<_; _≟_; _<?_; _⊔_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; <-≤-trans; m≤m⊔n; m≤n⊔m; <⇒≢; ≤-refl; n≤1+n)
open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_; toList; map)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

{- Stores ------------------------------------------------------------------------------}

read-in : ∀ {n σ x} → x < n → read n σ x ≡ σ x
read-in {n} {σ} {x} lt with x <? n
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p lt)

checked-in : ∀ {n x D} → x < n → checked n x D ≡ D
checked-in {n} {x} lt with x <? n
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p lt)

↦-same : ∀ {σ : Store} {x D} → (σ [ x ↦ D ]) x ≡ D
↦-same {x = x} with x ≟ x
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)

↦-other : ∀ {σ : Store} {x y D} → y ≢ x → (σ [ x ↦ D ]) y ≡ σ y
↦-other {x = x} {y} ne with y ≟ x
... | yes e = ⊥-elim (ne e)
... | no _ = refl

≔-same : ∀ g {ρ : X.Regs} {D} → (ρ [ g ≔ D ]) g ≡ D
≔-same rax = refl
≔-same rdi = refl
≔-same rsi = refl

drop-idx : ∀ {Δ' Δ A} (p : Δ' ⊑ Δ) (σ : Env Value) (y : Δ' ∋ A) → drop p σ (idx y) ≡ σ (idx (⊑-∋ p y))
drop-idx here⊑ σ y = refl
drop-idx (there⊑ p) σ y = drop-idx p (λ i → σ (suc i)) y

ˢ-++ : ∀ xs {ys T n κ} → X.⟦ xs ++ ys ⟧ˢ T n κ ≡ X.⟦ xs ⟧ˢ T n (X.⟦ ys ⟧ˢ T n κ)
ˢ-++ [] = refl
ˢ-++ (i ∷ xs) {T = T} {n} = cong (X.⟦ i ⟧ⁱ T n) (ˢ-++ xs)

{- No slot holds both an inl and an inr -}
Tagged : 𝒫 Value → Set
Tagged D = ∀ {u v} → left u ∈ D → right v ∈ D → ⊥

Inv : Store → Set
Inv σ = ∀ y → Tagged (σ y)

tagged-≈ : ∀ {V} → V ≈ V → Tagged (mem V)
tagged-≈ {V} c l r = ≈⇒Every V V c _ _ l r

inv-↦ : ∀ {σ x X} → Inv σ → Tagged X → Inv (σ [ x ↦ X ])
inv-↦ {x = x} i t y with y ≟ x
... | yes _ = t
... | no _ = i y

{- case: test, bind the payload, and branch on the flag (as in the untyped proof) -}
case-core : ∀ {A A' : 𝒫 Value} {F₁ F₂ G₁ G₂ : 𝒫 Value → 𝒫 Value} → A ≃ A' → Tagged A
  → (∀ V → V ≈ V → F₁ (mem V) ≃ G₁ (mem V)) → (∀ V → V ≈ V → F₂ (mem V) ≃ G₂ (mem V))
  → ⋆ ⟨ Λ ⟨ (λ X → 𝒞 ⟨ isinl A , ⟨ (λ _ → F₁ X) , ⟨ (λ _ → F₂ X) , ptt ⟩ ⟩ ⟩) , ptt ⟩ , ⟨ payloadD A , ptt ⟩ ⟩
    ≃ 𝒞 ⟨ A' , ⟨ G₁ , ⟨ G₂ , ptt ⟩ ⟩ ⟩
case-core {A} {A'} ⟨ A⊆ , A⊇ ⟩ tg F₁≃ F₂≃ = ⟨ G , H ⟩
  where
  G : _
  G w ⟨ [] , ⟨ ⟨ _ , ⟨ ne , _ ⟩ ⟩ , _ ⟩ ⟩ = ⊥-elim (ne refl)
  G w ⟨ v ∷ V , ⟨ ⟨ inj₁ ⟨ f , ⟨ _ , ⟨ fl , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩ , ⟨ _ , c ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with fl f (here refl)
  ... | inj₁ ⟨ u , ⟨ l∈ , _ ⟩ ⟩ =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ _ (lefts (V⊆ d d∈))) , ⟨ proj₁ (F₁≃ (v ∷ V) c) w w∈ , c ⟩ ⟩ ⟩ ⟩
    where
    lefts : ∀ {d} → payloadD A d → left d ∈ A
    lefts (inj₁ l) = l
    lefts (inj₂ r) = ⊥-elim (tg l∈ r)
  ... | inj₂ ⟨ _ , ⟨ _ , () ⟩ ⟩
  G w ⟨ v ∷ V , ⟨ ⟨ inj₂ ⟨ f , ⟨ _ , ⟨ fr , ⟨ w∈ , _ ⟩ ⟩ ⟩ ⟩ , ⟨ _ , c ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩
    with fr f (here refl)
  ... | inj₂ ⟨ u , ⟨ r∈ , _ ⟩ ⟩ =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ d d∈ → A⊆ _ (rights (V⊆ d d∈))) , ⟨ proj₁ (F₂≃ (v ∷ V) c) w w∈ , c ⟩ ⟩ ⟩ ⟩
    where
    rights : ∀ {d} → payloadD A d → right d ∈ A
    rights (inj₁ l) = ⊥-elim (tg l r∈)
    rights (inj₂ r) = r
  ... | inj₁ ⟨ _ , ⟨ _ , () ⟩ ⟩
  H : _
  H w (inj₁ ⟨ v , ⟨ V , ⟨ l∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ v ∷ V , ⟨ ⟨ inj₁ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → inj₁ ⟨ v , ⟨ A⊇ _ (l∈ v (here refl)) , refl ⟩ ⟩ })
                                      , ⟨ proj₂ (F₁≃ (v ∷ V) c) w w∈ , ⟨ tt ∷ [] , tt ⟩ ⟩ ⟩ ⟩ ⟩
                , ⟨ (λ ()) , c ⟩ ⟩
              , ⟨ (λ d d∈ → inj₁ (A⊇ _ (l∈ d d∈))) , (λ ()) ⟩ ⟩ ⟩
  H w (inj₂ ⟨ v , ⟨ V , ⟨ r∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ v ∷ V , ⟨ ⟨ inj₂ ⟨ ⟨⟩ , ⟨ [] , ⟨ (λ { _ (here refl) → inj₂ ⟨ v , ⟨ A⊇ _ (r∈ v (here refl)) , refl ⟩ ⟩ })
                                      , ⟨ proj₂ (F₂≃ (v ∷ V) c) w w∈ , ⟨ tt ∷ [] , tt ⟩ ⟩ ⟩ ⟩ ⟩
                , ⟨ (λ ()) , c ⟩ ⟩
              , ⟨ (λ d d∈ → inj₂ (A⊇ _ (r∈ d d∈))) , (λ ()) ⟩ ⟩ ⟩

{- The pass preserves meanings -----------------------------------------------------------}

{- for tables T (of X86, by level) and T' (of CFGᵀ) that agree, in a frame of n slots -}
module _ {Σ} {T : X.Table} {T' : Table Σ} (TT : ∀ {m} (f : Σ ∋ m) → T (lvl f) ≃ T' f) (n : ℕ) where

  {- the X86 store holds the slots of the frame at their levels -}
  Rel : Ctx → Store → Env Value → Set
  Rel Δ s σ = ∀ {A} (x : Δ ∋ A) → s (lvl x) ≃ σ (idx x)

  rel-↦ : ∀ {Δ Δ' A s σ X} (p : Δ' ⊑ Δ) → Rel Δ s σ → Rel (A ∷ Δ') (s [ length Δ' ↦ X ]) (X • drop p σ)
  rel-↦ {Δ' = Δ'} {s = s} p r Z = ≃-reflexive (↦-same {s} {length Δ'})
  rel-↦ {s = s} {σ} p r (S y) =
    ≃-trans (≃-reflexive (↦-other (<⇒≢ (lvl-< y))))
      (≃-trans (≃-trans (≃-reflexive (cong s (sym (lvl-⊑ p y)))) (r (⊑-∋ p y))) (≃-reflexive (sym (drop-idx p σ y))))

  atm-≃ : ∀ {Δ A s σ} → length Δ ≤ n → Rel Δ s σ → (a : Atm Σ Δ A) → ∀ {ρ} → X.𝒪 T n s ρ (select-atm a) ≃ 𝒜 a T' σ
  atm-≃ le r (var x) = ≃-trans (≃-reflexive (read-in (<-≤-trans (lvl-< x) le))) (r x)
  atm-≃ le r (lit B c) = ≃-refl
  atm-≃ le r (ref f) = TT f

  {- d is a slot of the frame, or a register -}
  OkD : Loc → Set
  OkD (L.var x) = x < n
  OkD (reg g) = ⊤

  {- κ, what runs after d is assigned, means K of its value with any
     registers and flag; or returns d -}
  Fits : Loc → X.Kont → (𝒫 Value → 𝒫 Value) → Store → Set₁
  Fits (L.var x) κ K s = ∀ X → Tagged X → ∀ ρ φ → κ (s [ x ↦ X ]) ρ φ ≃ K X
  Fits (reg g) κ K s = ∀ s' ρ φ → κ s' ρ φ ≃ ρ g

  {- d := D, then K, in CFGᵀ -}
  after : Loc → (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
  after (L.var x) K D = ⋆ ⟨ Λ ⟨ K , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
  after (reg g) K D = D

  after-≃ : ∀ d {K D D'} → D ≃ D' → after d K D ≃ after d K D'
  after-≃ (L.var x) {K} D≃ = ⋆-≃ (≃-refl {D = Λ ⟨ K , ptt ⟩}) D≃
  after-≃ (reg g) D≃ = D≃

  after-ne : ∀ d {K D} w → w ∈ after d K D → nonempty D
  after-ne (L.var x) w ⟨ V , ⟨ _ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ne-mem ne V⊆
  after-ne (reg g) w w∈ = ⟨ w , w∈ ⟩

  put-≃ : ∀ d {κ K s D D' ρ φ} → OkD d → Fits d κ K s → D ≃ D' → X.put n d D κ s ρ φ ≃ after d K D'
  put-≃ (L.var x) {κ} {K} {s} {ρ = ρ} {φ} lt f D≃ =
    ≃-trans (≃-reflexive (checked-in lt)) (⋆-≃ (Λ-≃ {λ X → κ (s [ x ↦ X ]) ρ φ} {K} λ V _ c → f _ (tagged-≈ c) ρ φ) D≃)
  put-≃ (reg g) {s = s} {D} {ρ = ρ} {φ} _ f D≃ = strict-≃ (≃-trans e D≃) (λ w w∈ → ⟨ w , proj₁ e w w∈ ⟩)
    where e = ≃-trans (f s (ρ [ g ≔ D ]) φ) (≃-reflexive (≔-same g))

  put-ne : ∀ d {κ K s D ρ φ} → OkD d → Fits d κ K s → ∀ w → w ∈ X.put n d D κ s ρ φ → nonempty D
  put-ne d ok f w w∈ = after-ne d w (proj₁ (put-≃ d ok f ≃-refl) w w∈)

  {- a project: E, the value of the test, has a value exactly when the slot A' does that P accepts -}
  guard-≃ : ∀ d {K E X A'} {P : Value → Set} → (nonempty E → Σ[ a ∈ Value ] a ∈ A' × P a)
    → (∀ {a} → a ∈ A' → P a → nonempty E) → X ≃ after d K A' → strict E X ≃ after d K (guardᵖ P A')
  guard-≃ d {K} {E} {X} {A'} {P} to from X≃ = ⟨ ⊆→ , ⊇ ⟩
    where
    full : Σ[ a ∈ Value ] a ∈ A' × P a → guardᵖ P A' ≃ A'
    full wt = ⟨ (λ _ → proj₂) , (λ w w∈ → ⟨ wt , w∈ ⟩) ⟩
    ⊆→ : strict E X ⊆ after d K (guardᵖ P A')
    ⊆→ w ⟨ ne , w∈ ⟩ = proj₂ (after-≃ d (full (to ne))) w (proj₁ X≃ w w∈)
    ⊇ : after d K (guardᵖ P A') ⊆ strict E X
    ⊇ w w∈ with after-ne d w w∈
    ... | ⟨ _ , ⟨ ⟨ a , ⟨ a∈ , pa ⟩ ⟩ , _ ⟩ ⟩ =
      ⟨ from a∈ pa , proj₂ X≃ w (proj₁ (after-≃ d (full ⟨ a , ⟨ a∈ , pa ⟩ ⟩)) w w∈) ⟩

  {- the components of a tuple -}
  𝒪v : ∀ {Δ m} → Store → X.Regs → Vec (Atm Σ Δ Any) m → Results (𝒫 Value) (replicate m ■)
  𝒪v s ρ [] = ptt
  𝒪v s ρ (a ∷ as) = ⟨ X.𝒪 T n s ρ (select-atm a) , 𝒪v s ρ as ⟩

  𝒪v-≡ : ∀ {Δ m s ρ} (as : Vec (Atm Σ Δ Any) m) → _≡_ {A = Σ[ k ∈ ℕ ] Results (𝒫 Value) (replicate k ■)}
    ⟨ length (toList (map select-atm as)) , X.𝒪s T n s ρ (toList (map select-atm as)) ⟩ ⟨ m , 𝒪v s ρ as ⟩
  𝒪v-≡ [] = refl
  𝒪v-≡ (a ∷ as) = cong (λ p → ⟨ suc (proj₁ p) , ⟨ _ , proj₂ p ⟩ ⟩) (𝒪v-≡ as)

  𝒪v-≃ : ∀ {Δ m s σ ρ} → length Δ ≤ n → Rel Δ s σ → (as : Vec (Atm Σ Δ Any) m)
    → RRs (replicate m ■) (𝒪v s ρ as) (𝒜s as T' σ)
  𝒪v-≃ le r [] = ptt
  𝒪v-≃ le r (a ∷ as) = ⟨ lift (atm-≃ le r a) , 𝒪v-≃ le r as ⟩

  {- the instructions of s into d, then κ -}
  sel : ∀ {Δ A} (s : C.Simple Σ Δ A) d {κ K st σ} → OkD d → Fits d κ K st → length Δ ≤ n → Rel Δ st σ
    → ∀ ρ φ → X.⟦ select-simple s d ⟧ˢ T n κ st ρ φ ≃ after d K (𝒮 s T' σ)
  sel (atm a) d ok f le r ρ φ = put-≃ d ok f (atm-≃ le r a)
  sel (pack a b) d ok f le r ρ φ = put-≃ d ok f (mono-≃ pair-mono ⟨ lift (atm-≃ le r a) , ⟨ lift (atm-≃ le r b) , ptt ⟩ ⟩)
  sel (callc g a) d {st = st} {σ} ok f le r ρ φ =
    strict-≃ (strict-≃ (strict-≃ (strict-≃ (put-≃ d ok f R≃) (put-ne d ok f))
      (λ w w∈ → proj₂ (⋆-ne {P₁} {A₃} (proj₁ w∈))))
      (λ w w∈ → proj₂ (⋆-ne {C₁} {C₂} (proj₁ (⋆-ne {P₁} {A₃} (proj₁ (proj₂ w∈)))))))
      (λ w w∈ → proj₁ (⋆-ne {C₁} {C₂} (proj₁ (⋆-ne {P₁} {A₃} (proj₁ (proj₂ (proj₂ w∈)))))))
    where
    G₁ = X.𝒪 T n st ρ (select-atm g)
    G₂ = X.𝒪 T n st (ρ [ rax ≔ car ⟨ G₁ , ptt ⟩ ]) (select-atm g)
    A₃ = X.𝒪 T n st (ρ [ rax ≔ car ⟨ G₁ , ptt ⟩ ] [ rdi ≔ cdr ⟨ G₂ , ptt ⟩ ]) (select-atm a)
    C₁ = car ⟨ G₁ , ptt ⟩
    C₂ = cdr ⟨ G₂ , ptt ⟩
    P₁ = ⋆ ⟨ C₁ , ⟨ C₂ , ptt ⟩ ⟩
    R≃ : ⋆ ⟨ ⋆ ⟨ car ⟨ G₁ , ptt ⟩ , ⟨ cdr ⟨ G₂ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ A₃ , ptt ⟩ ⟩
       ≃ ⋆ ⟨ ⋆ ⟨ car ⟨ 𝒜 g T' σ , ptt ⟩ , ⟨ cdr ⟨ 𝒜 g T' σ , ptt ⟩ , ptt ⟩ ⟩ , ⟨ 𝒜 a T' σ , ptt ⟩ ⟩
    R≃ = ⋆-≃ (⋆-≃ (mono-≃ {f = car} car-mono ⟨ lift (atm-≃ le r g) , ptt ⟩) (mono-≃ {f = cdr} cdr-mono ⟨ lift (atm-≃ le r g) , ptt ⟩)) (atm-≃ le r a)
  sel (tuple {n = m} as) d {st = st} {σ} ok f le r ρ φ =
    put-≃ d ok f (≃-trans (≃-reflexive (cong (λ p → 𝒯 (proj₁ p) (proj₂ p)) (𝒪v-≡ as))) (mono-≃ (𝒯-mono m) (𝒪v-≃ le r as)))
  sel (get i a) d ok f le r ρ φ = put-≃ d ok f (proj-≃ i (atm-≃ le r a))
  sel (inl a) d ok f le r ρ φ = put-≃ d ok f (inl-≃ (atm-≃ le r a))
  sel (inr a) d ok f le r ρ φ = put-≃ d ok f (inr-≃ (atm-≃ le r a))
  sel (prim P.sub a b) d ok f le r ρ φ =
    strict-≃₂ (put-≃ d ok f (primD-≃ P.sub (atm-≃ le r a) (atm-≃ le r b))) (put-ne d ok f)
      λ { ⟨ _ , ⟨ k , ⟨ _ , ⟨ k∈ , _ ⟩ ⟩ ⟩ ⟩ → ⟨ _ , k∈ ⟩ }
  sel (prim P.eq a b) d ok f le r ρ φ = strict-≃ (put-≃ d ok f (primD-≃ P.eq (atm-≃ le r a) (atm-≃ le r b))) (put-ne d ok f)
  sel (inject G a) d ok f le r ρ φ = put-≃ d ok f (atm-≃ le r a)
  sel (project tint a) d ok f le r ρ φ =
    strict-≃ (guard-≃ d (λ { ⟨ _ , ⟨ k , ⟨ m , ⟨ k∈ , _ ⟩ ⟩ ⟩ ⟩ → ⟨ _ , ⟨ proj₁ A≃ _ k∈ , ⟨ k , refl ⟩ ⟩ ⟩ })
                          (λ { a∈ ⟨ k , refl ⟩ → ⟨ _ , ⟨ k , ⟨ 0ℤ , ⟨ proj₂ A≃ _ a∈ , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩ ⟩ ⟩ ⟩ })
                          (put-≃ d ok f A≃))
      (λ { w ⟨ ⟨ _ , ⟨ k , ⟨ _ , ⟨ k∈ , _ ⟩ ⟩ ⟩ ⟩ , _ ⟩ → ⟨ _ , k∈ ⟩ })
    where A≃ = atm-≃ le r a
  sel (project tsum a) d ok f le r ρ φ =
    guard-≃ d (λ { ⟨ _ , inj₁ ⟨ u , ⟨ u∈ , refl ⟩ ⟩ ⟩ → ⟨ _ , ⟨ proj₁ A≃ _ u∈ , inj₁ ⟨ u , refl ⟩ ⟩ ⟩
                 ; ⟨ _ , inj₂ ⟨ u , ⟨ u∈ , refl ⟩ ⟩ ⟩ → ⟨ _ , ⟨ proj₁ A≃ _ u∈ , inj₂ ⟨ u , refl ⟩ ⟩ ⟩ })
              (λ { a∈ (inj₁ ⟨ u , refl ⟩) → ⟨ _ , inj₁ ⟨ u , ⟨ proj₂ A≃ _ a∈ , refl ⟩ ⟩ ⟩
                 ; a∈ (inj₂ ⟨ u , refl ⟩) → ⟨ _ , inj₂ ⟨ u , ⟨ proj₂ A≃ _ a∈ , refl ⟩ ⟩ ⟩ })
              (put-≃ d ok f A≃)
    where A≃ = atm-≃ le r a
  sel (project tfun a) d ok f le r ρ φ =
    guard-≃ d (λ { ⟨ _ , ⟨ v , uv∈ ⟩ ⟩ → ⟨ _ , ⟨ proj₁ A≃ _ uv∈ , tt ⟩ ⟩ })
              (λ { {⦅ u , v ⦆} a∈ _ → ⟨ u , ⟨ v , proj₂ A≃ _ a∈ ⟩ ⟩ ; {const _} _ () ; {_ ↦ _} _ () ; {ν} _ () ; {ω} _ ()
                 ; {tup[ _ ] _} _ () ; {left _} _ () ; {right _} _ () ; {⟨⟩} _ () })
              (put-≃ d ok f A≃)
    where A≃ = atm-≃ le r a
  sel (project (ttup m i) a) d ok f le r ρ φ =
    guard-≃ d (λ { ⟨ u , u∈ ⟩ → ⟨ _ , ⟨ proj₁ A≃ _ u∈ , ⟨ u , refl ⟩ ⟩ ⟩ })
              (λ { a∈ ⟨ u , refl ⟩ → ⟨ u , proj₂ A≃ _ a∈ ⟩ })
              (put-≃ d ok f A≃)
    where A≃ = atm-≃ le r a

  {- the blocks B (of X86, by level) and B' (of CFGᵀ) agree -}
  BR : ∀ {Bs} → X.Blocks → Meanings Bs → Set₁
  BR {Bs} B B' = ∀ {Δ} (l : Bs ∋ Δ) s σ → Rel Δ s σ → Inv s → ∀ ρ φ → B (lvl l) s ρ φ ≃ B' l σ

  tail : ∀ {Bs Δ} (t : Tail Σ Bs Δ) {B : X.Blocks} {B' : Meanings Bs} → BR B B' → depth t ≤ n
    → ∀ s σ → Rel Δ s σ → Inv s → ∀ ρ φ → X.⟦ select-tail t ⟧ᵇ T n B s ρ φ ≃ ⟦ t ⟧ᵗ T' B' σ
  tail (return r) br le s σ rl i ρ φ = sel r (reg rax) {K = λ _ → ∅} tt (λ _ _ _ → ≃-refl) le rl ρ φ
  tail (seq {Δ'} p r t) {B} {B'} br le s σ rl i ρ φ =
    ≃-trans (≃-reflexive (cong (λ κ → κ s ρ φ) (ˢ-++ (select-simple r (L.var (length Δ'))))))
      (sel r (L.var (length Δ')) {K = λ X → ⟦ t ⟧ᵗ T' B' (X • drop p σ)} (<-≤-trans (depth-≥ t) le′)
        (λ X tX ρ' φ' → tail t br le′ (s [ length Δ' ↦ X ]) (X • drop p σ) (rel-↦ p rl) (inv-↦ i tX) ρ' φ') (≤-trans (depth-≥ (seq p r t)) le) rl ρ φ)
    where le′ = ≤-trans (m≤n⊔m _ (depth t)) le
  tail (goto l) br le s σ rl i ρ φ = br l s σ rl i ρ φ
  tail (case {Δ'} a p l₁ l₂) {B} {B'} br le s σ rl i ρ φ = strict-≃ eq λ w w∈ → ne′ {λ X → B' l₁ (X • drop p σ)} {λ X → B' l₂ (X • drop p σ)} (proj₁ eq w w∈)
    where
    k = length Δ'
    leΔ = ≤-trans (depth-≥ (case a p l₁ l₂)) le
    A = X.𝒪 T n s ρ (select-atm a)
    A≃ = atm-≃ leΔ rl a
    tagged : (a : Atm Σ _ ⟪ sum ⟫) → Tagged (X.𝒪 T n s ρ (select-atm a))
    tagged (var x) = subst Tagged (sym (read-in (<-≤-trans (lvl-< x) leΔ))) (i (lvl x))
    eq = ≃-trans (≃-reflexive (checked-in (≤-trans (m≤n⊔m _ _) le)))
      (case-core {F₁ = λ X → B (lvl l₁) (s [ k ↦ X ]) ρ (isinl A)} {λ X → B (lvl l₂) (s [ k ↦ X ]) ρ (isinl A)}
                 {λ X → B' l₁ (X • drop p σ)} {λ X → B' l₂ (X • drop p σ)}
        A≃ (tagged a) (λ V c → br l₁ _ _ (rel-↦ p rl) (inv-↦ i (tagged-≈ c)) ρ _)
        (λ V c → br l₂ _ _ (rel-↦ p rl) (inv-↦ i (tagged-≈ c)) ρ _))
    ne′ : ∀ {F G : 𝒫 Value → 𝒫 Value} {w} → w ∈ 𝒞 ⟨ 𝒜 a T' σ , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩ → nonempty (isinl A)
    ne′ (inj₁ ⟨ v , ⟨ V , ⟨ l , _ ⟩ ⟩ ⟩) = ⟨ left ⟨⟩ , inj₁ ⟨ v , ⟨ proj₂ A≃ _ (l v (here refl)) , refl ⟩ ⟩ ⟩
    ne′ (inj₂ ⟨ v , ⟨ V , ⟨ l , _ ⟩ ⟩ ⟩) = ⟨ right ⟨⟩ , inj₂ ⟨ v , ⟨ proj₂ A≃ _ (l v (here refl)) , refl ⟩ ⟩ ⟩

  blocks-≃ : ∀ {Bs} (bs : Blocks Σ Bs) → blocks-depth bs ≤ n → BR (X.blocks T n (select-blocks bs)) (blocks bs T')
  blocks-≃ {_ ∷ Bs} (bs ▷ t) le Z s σ rl i ρ φ with length Bs ≟ length (select-blocks bs)
  ... | yes _ = tail t (blocks-≃ bs (≤-trans (m≤n⊔m _ _) le)) (≤-trans (m≤m⊔n _ _) le) s σ rl i ρ φ
  ... | no ne = ⊥-elim (ne (sym (len-blocks bs)))
  blocks-≃ (bs ▷ t) le (S l) s σ rl i ρ φ with lvl l ≟ length (select-blocks bs)
  ... | yes e = ⊥-elim (<⇒≢ (lvl-< l) (trans e (len-blocks bs)))
  ... | no _ = blocks-≃ bs (≤-trans (m≤n⊔m _ _) le) l s σ rl i ρ φ

{- the code of a definition: its start moves its arguments to slots 0 and 1 -}
code-≃ : ∀ {Σ} {T : X.Table} {T' : Table Σ} (TT : ∀ {m} (f : Σ ∋ m) → T (lvl f) ≃ T' f)
  → ∀ {m} (b : C.Body Σ (Any ∷ ⟪ tup m ⟫ ∷ [])) → X.code T (select-body prologue b) ≃ codeᶜ T' b
code-≃ {T = T} {T'} TT (C.body bs t) = Λ-≃ λ V neV cV → Λ-≃ λ U neU cU → start cV cU neV neU
  where
  n = 2 ⊔ (blocks-depth bs ⊔ depth t)
  L = blocks-depth bs ⊔ depth t
  le₁ = ≤-trans (m≤m⊔n (blocks-depth bs) (depth t)) (m≤n⊔m 2 L)
  le₂ = ≤-trans (m≤n⊔m (blocks-depth bs) (depth t)) (m≤n⊔m 2 L)
  start : ∀ {V U} → V ≈ V → U ≈ U → V ≢ [] → U ≢ []
    → X.run T n (select-body prologue (C.body bs t)) zeros (args (mem V) (mem U)) ∅ ≃ runᶜ (C.body bs t) T' (mem U • mem V • λ _ → init)
  start {V} {U} cV cU neV neU with 0 <? n | 1 <? n
  ... | no ¬p | _ = ⊥-elim (¬p (≤-trans (s≤s z≤n) (m≤m⊔n 2 L)))
  ... | yes _ | no ¬p = ⊥-elim (¬p (m≤m⊔n 2 L))
  ... | yes _ | yes _ = ⟨ to , from ⟩
    where
    sim : ∀ {X Y} → X ≈ X → Y ≈ Y → ∀ ρ → X.⟦ select-tail t ⟧ᵇ T n (X.blocks T n (select-blocks bs)) (zeros [ 0 ↦ mem X ] [ 1 ↦ mem Y ]) ρ ∅
      ≃ ⟦ t ⟧ᵗ T' (blocks bs T') (mem Y • mem X • λ _ → init)
    sim {X} {Y} cX cY ρ = tail TT n t (blocks-≃ TT n bs le₁) le₂ _ _ (λ { Z → ≃-refl ; (S Z) → ≃-refl }) inv ρ ∅
      where
      inv : Inv (zeros [ 0 ↦ mem X ] [ 1 ↦ mem Y ])
      inv 0 = tagged-≈ cX
      inv 1 = tagged-≈ cY
      inv (suc (suc y)) = λ ()
    to : _
    to w ⟨ V' , ⟨ ⟨ ⟨ U' , ⟨ ⟨ w∈ , ⟨ _ , cU' ⟩ ⟩ , ⟨ U'⊆ , _ ⟩ ⟩ ⟩ , ⟨ _ , cV' ⟩ ⟩ , ⟨ V'⊆ , _ ⟩ ⟩ ⟩ =
      tail-mono {T = T'} t (blocks-mono bs) s w (proj₁ (sim cV' cU' _) w w∈)
      where
      s : (mem U' • mem V' • λ _ → init) ⊆ₑ (mem U • mem V • λ _ → init)
      s 0 = U'⊆
      s 1 = V'⊆
      s (suc (suc y)) = λ _ z → z
    from : _
    from w w∈ = ⟨ V , ⟨ ⟨ ⟨ U , ⟨ ⟨ proj₂ (sim cV cU _) w w∈ , ⟨ neU , cU ⟩ ⟩ , ⟨ (λ _ z → z) , neU ⟩ ⟩ ⟩
                       , ⟨ neV , cV ⟩ ⟩ , ⟨ (λ _ z → z) , neV ⟩ ⟩ ⟩

{- Programs ------------------------------------------------------------------------------}

{- the X86 table at the level of f is the CFGᵀ table at f -}
table-select : ∀ {Σ ns} (ds : All (λ n → C.Body Σ (Any ∷ ⟪ tup n ⟫ ∷ [])) ns) {m} (f : Σ ∋ m)
  → X.table (select-defs ds) (lvl f) ≃ tables codeᶜ ds f
table-select [] f = ≃-refl
table-select {ns = _ ∷ ns} (d ∷ ds) f with lvl f ≟ length (select-defs ds) | lvl f ≟ length ns
... | yes _ | yes _ = code-≃ (table-select ds) d
... | no _ | no _ = table-select ds f
... | yes e | no ne = ⊥-elim (ne (trans e (len-defs ds)))
... | no ne | yes e = ⊥-elim (ne (trans e (sym (len-defs ds))))

{- and empty at any number not below its length -}
table-beyond : ∀ (bs : List L.Body) k → length bs ≤ k → X.table bs k ≡ ∅
table-beyond [] k le = refl
table-beyond (b ∷ bs) k le with k ≟ length bs
... | yes refl = ⊥-elim (<⇒≢ le refl)
... | no _ = table-beyond bs k (≤-trans (n≤1+n _) le)

select-correct : ∀ (P : C.Program) → X.⟦ select P ⟧ₚ ≃ ⟦ P ⟧ᶜ
select-correct (C.program ds (C.body bs t)) =
  tail (table-select ds) n t (blocks-≃ (table-select ds) n bs (m≤m⊔n _ _)) (m≤n⊔m _ _) zeros (λ _ → init) (λ ()) (λ _ ())
    (called (zeros 0)) ∅
  where n = blocks-depth bs ⊔ depth t
