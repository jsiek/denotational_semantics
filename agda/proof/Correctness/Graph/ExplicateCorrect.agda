{-

  Correctness of explicate control (Imp → CFG, Compiler/Explicate.agda)
  against the direct semantics of Imp (proof/Semantics/Graph/ImpDirect.agda), an
  alternative to the main proof against the continuation-passing
  semantics (ExplicateCorrectK.agda): the meaning of the CFG program
  (Semantics/Graph/CFG.agda) is that of the Imp program.

    explicate-correct : ⟦ explicate P ⟧ₚ ≃ ⟦ P ⟧ₚ

  The pass is a commuting conversion. In Imp, x := e; k binds x to the
  value of e and runs k in the store that e leaves; that store, like the
  value, collects the runs of e (the runs of the branches of a case, or
  of the body of a nested assignment, for each part of what they bind).
  In CFG, k runs after each run of e on its own: explicate-assign e x k
  is, for every tail k (cps),

    ⟪ explicate-assign e x k ⟫ ≃ letK x (ℐ⟦ e ⟧) ⟪ k ⟫

  where letK x r K binds x to the value of r and runs K in its store.
  Each step is a law: let-assoc for a nested assignment, let-case for a
  case, the join point of the case being the block that holds k. One
  direction of each law is monotonicity; in the other, k has run on the
  collected store, and the finitely many elements it used come from
  finitely many runs (Dir, DC: CFG tails preserve directed unions of
  stores), whose bound parts can be joined into one run (merge). That
  join needs the bound sets to be consistent: the scrutinee of a case
  has only left or only right elements, and the parts of a value are
  consistent with each other. So the stores are consistent (I-con).

  explicate-tail e then means the value of e (tail). A tail made at the
  blocks bs runs with any newer blocks (ExplicateCommon.agda), so the
  meaning of a continuation does not depend on the blocks added after it
  (Stable).

  In a domain where Λ binds any finite set, the pass does not preserve
  meanings: for the Clos5 code λ fv. λ Y. let y = case Y of inl _ ⇒
  ⟨1,1⟩ | inr _ ⇒ ⟨2,2⟩ in ⟨fst y, snd y⟩, lifted into Imp, the
  argument Y = {left ν, right ν} makes the let bind y to a mix of the
  two branches, so ⟨1,2⟩ is a result in Imp but not in CFG, where each
  branch reaches the join point on its own.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (results-rel-pres)
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Language.Imp as I
  using (var; lit; fun-ref; atm; app; fst; snd; tuple; get; prim; simple; case; assign; body; program)
import Language.CFG as C
open import Compiler.Explicate
open import proof.Semantics.Graph.ImpDirect
  using (Store; _[_↦_]; 𝒜; 𝒜s; 𝒮; Table; zeros; frame; caseₛ; letₛ; _↓_)
  renaming (⟦_⟧[_] to ℐ⟦_⟧[_]; checked to checkedᵢ; table to tableᵢ; code to codeᵢ; ⟦_⟧ₚ to ℐ⟦_⟧ₚ)
open import Semantics.Graph.CFG
  using (blocks; checked; ⟦_⟧ₚ)
  renaming (⟦_⟧[_] to ⟪_⟫[_]; table to tableₜ; code to codeₜ)
open import proof.Semantics.Graph.Clos5IswimContinuous using (ΛΛ-con)
open import proof.Correctness.Graph.ConcretizeCorrect
  using (⋆-≃; 𝒞-≃)
open import proof.Correctness.Graph.RCOCorrect using (Λ-≃)
open import proof.Correctness.Graph.LiftLocalsCorrect using (compile-imp-same)
open import proof.Correctness.Graph.ExplicateCommon
open import proof.Correctness.Graph.DelayFiniteCommon using (ne-mem)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length; replicate; map)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Nat using (ℕ; zero; suc; _≟_; _<?_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

module proof.Correctness.Graph.ExplicateCorrect where

{- Stores ----------------------------------------------------------------------}

infix 4 _⊆ₛ_ _~ₛ_
_⊆ₛ_ : Store → Store → Set
σ ⊆ₛ σ' = ∀ z → σ z ⊆ σ' z

_~ₛ_ : Store → Store → Set
σ ~ₛ σ' = ∀ z → Every _~_ (σ z) (σ' z)

upd-⊆ : ∀ {σ σ' X X'} x → σ ⊆ₛ σ' → X ⊆ X' → σ [ x ↦ X ] ⊆ₛ σ' [ x ↦ X' ]
upd-⊆ x s X⊆ z with z ≟ x
... | yes _ = X⊆
... | no _ = s z

upd-~ : ∀ {σ σ' X X'} x → σ ~ₛ σ' → Every _~_ X X' → σ [ x ↦ X ] ~ₛ σ' [ x ↦ X' ]
upd-~ x c X~ z with z ≟ x
... | yes _ = X~
... | no _ = c z

⊆-refl : ∀ {D : 𝒫 Value} → D ⊆ D
⊆-refl d d∈ = d∈

{- Directed unions of stores ------------------------------------------------------}

{- a family of stores in which any two have an upper bound -}
record Dir : Set₁ where
  field
    I : Set
    at : I → Store
    i₀ : I
    ub : I → I → I
    ub₁ : ∀ i j → at i ⊆ₛ at (ub i j)
    ub₂ : ∀ i j → at j ⊆ₛ at (ub i j)
open Dir

⋃ : Dir → Store
⋃ d z w = Σ[ i ∈ I d ] w ∈ at d i z

Mono : (Store → 𝒫 Value) → Set₁
Mono F = ∀ {σ σ'} → σ ⊆ₛ σ' → F σ ⊆ F σ'

{- F preserves directed unions -}
DC : (Store → 𝒫 Value) → Set₁
DC F = ∀ d w → w ∈ F (⋃ d) → Σ[ i ∈ I d ] w ∈ F (at d i)

Good : (Store → 𝒫 Value) → Set₁
Good F = Mono F × DC F

{- finitely many elements, each in some member, are all in one -}
dir-list : ∀ d (G : I d → 𝒫 Value) → (∀ i j → G i ⊆ G (ub d i j) × G j ⊆ G (ub d i j))
  → ∀ V → (∀ u → u ∈ mem V → Σ[ i ∈ I d ] u ∈ G i) → Σ[ i ∈ I d ] mem V ⊆ G i
dir-list d G up [] _ = ⟨ i₀ d , (λ _ ()) ⟩
dir-list d G up (v ∷ V) h with h v (here refl) | dir-list d G up V (λ u u∈ → h u (there u∈))
... | ⟨ i , v∈ ⟩ | ⟨ j , V⊆ ⟩ =
  ⟨ ub d i j , (λ { _ (here refl) → proj₁ (up i j) _ v∈ ; u (there u∈) → proj₂ (up i j) u (V⊆ u u∈) }) ⟩

dc-list : ∀ {F} (f : Value → Value) → Good F → ∀ d V → (∀ u → u ∈ mem V → f u ∈ F (⋃ d))
  → Σ[ i ∈ I d ] (∀ u → u ∈ mem V → f u ∈ F (at d i))
dc-list {F} f ⟨ m , c ⟩ d V h =
  dir-list d (λ i u → f u ∈ F (at d i)) (λ i j → ⟨ (λ u → m (ub₁ d i j) (f u)) , (λ u → m (ub₂ d i j) (f u)) ⟩)
    V (λ u u∈ → c d (f u) (h u u∈))

_[_↦_]ᵈ : Dir → ℕ → 𝒫 Value → Dir
d [ x ↦ X ]ᵈ = record { I = I d ; at = λ i → at d i [ x ↦ X ] ; i₀ = i₀ d ; ub = ub d
  ; ub₁ = λ i j → upd-⊆ x (ub₁ d i j) ⊆-refl ; ub₂ = λ i j → upd-⊆ x (ub₂ d i j) ⊆-refl }

⋃-upd : ∀ d x X → ⋃ d [ x ↦ X ] ⊆ₛ ⋃ (d [ x ↦ X ]ᵈ)
⋃-upd d x X z with z ≟ x
... | yes _ = λ w w∈ → ⟨ i₀ d , w∈ ⟩
... | no _ = λ w w∈ → w∈

{- The operators preserve directed unions -------------------------------------------}

const-good : ∀ {D} → Good (λ _ → D)
const-good = ⟨ (λ _ → ⊆-refl) , (λ d w w∈ → ⟨ i₀ d , w∈ ⟩) ⟩

⋆-good : ∀ {F G} → Good F → Good G → Good (λ σ → ⋆ ⟨ F σ , ⟨ G σ , ptt ⟩ ⟩)
⋆-good {F} {G} ⟨ mF , cF ⟩ gG@(⟨ mG , cG ⟩) = ⟨ m , c ⟩
  where
  m : Mono (λ σ → ⋆ ⟨ F σ , ⟨ G σ , ptt ⟩ ⟩)
  m s w ⟨ V , ⟨ f∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ⟨ V , ⟨ mF s _ f∈ , ⟨ (λ u u∈ → mG s u (V⊆ u u∈)) , ne ⟩ ⟩ ⟩
  c : DC (λ σ → ⋆ ⟨ F σ , ⟨ G σ , ptt ⟩ ⟩)
  c d w ⟨ V , ⟨ f∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ with cF d _ f∈ | dc-list (λ u → u) gG d V V⊆
  ... | ⟨ i , f∈′ ⟩ | ⟨ j , V⊆′ ⟩ =
    ⟨ ub d i j , ⟨ V , ⟨ mF (ub₁ d i j) _ f∈′ , ⟨ (λ u u∈ → mG (ub₂ d i j) u (V⊆′ u u∈)) , ne ⟩ ⟩ ⟩ ⟩

Λ-good : ∀ x {F} → Good F → Good (λ σ → Λ ⟨ (λ X → F (σ [ x ↦ X ])) , ptt ⟩)
Λ-good x {F} ⟨ mF , cF ⟩ = ⟨ m , c ⟩
  where
  m : Mono (λ σ → Λ ⟨ (λ X → F (σ [ x ↦ X ])) , ptt ⟩)
  m s ν _ = tt
  m s (V ↦ w) ⟨ w∈ , ok ⟩ = ⟨ mF (upd-⊆ x s ⊆-refl) w w∈ , ok ⟩
  c : DC (λ σ → Λ ⟨ (λ X → F (σ [ x ↦ X ])) , ptt ⟩)
  c d ν _ = ⟨ i₀ d , tt ⟩
  c d (V ↦ w) ⟨ w∈ , ok ⟩ with cF (d [ x ↦ mem V ]ᵈ) w (mF (⋃-upd d x (mem V)) w w∈)
  ... | ⟨ i , w∈′ ⟩ = ⟨ i , ⟨ w∈′ , ok ⟩ ⟩

𝒞-good : ∀ x {A F₁ F₂} → Good A → Good F₁ → Good F₂
  → Good (λ σ → 𝒞 ⟨ A σ , ⟨ (λ X → F₁ (σ [ x ↦ X ])) , ⟨ (λ X → F₂ (σ [ x ↦ X ])) , ptt ⟩ ⟩ ⟩)
𝒞-good x {A} {F₁} {F₂} gA@(⟨ mA , cA ⟩) ⟨ m₁ , c₁ ⟩ ⟨ m₂ , c₂ ⟩ = ⟨ m , c ⟩
  where
  H = λ σ → 𝒞 ⟨ A σ , ⟨ (λ X → F₁ (σ [ x ↦ X ])) , ⟨ (λ X → F₂ (σ [ x ↦ X ])) , ptt ⟩ ⟩ ⟩
  m : Mono H
  m s w (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , ok ⟩ ⟩ ⟩ ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ (λ u u∈ → mA s _ (all u u∈)) , ⟨ m₁ (upd-⊆ x s ⊆-refl) w w∈ , ok ⟩ ⟩ ⟩ ⟩
  m s w (inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , ok ⟩ ⟩ ⟩ ⟩) =
    inj₂ ⟨ v , ⟨ V , ⟨ (λ u u∈ → mA s _ (all u u∈)) , ⟨ m₂ (upd-⊆ x s ⊆-refl) w w∈ , ok ⟩ ⟩ ⟩ ⟩
  c : DC H
  c d w (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , ok ⟩ ⟩ ⟩ ⟩)
      with c₁ (d [ x ↦ mem (v ∷ V) ]ᵈ) w (m₁ (⋃-upd d x _) w w∈) | dc-list left gA d (v ∷ V) all
  ... | ⟨ i , w∈′ ⟩ | ⟨ j , all′ ⟩ = ⟨ ub d i j , inj₁ ⟨ v , ⟨ V ,
          ⟨ (λ u u∈ → mA (ub₂ d i j) _ (all′ u u∈)) , ⟨ m₁ (upd-⊆ x (ub₁ d i j) ⊆-refl) w w∈′ , ok ⟩ ⟩ ⟩ ⟩ ⟩
  c d w (inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ w∈ , ok ⟩ ⟩ ⟩ ⟩)
      with c₂ (d [ x ↦ mem (v ∷ V) ]ᵈ) w (m₂ (⋃-upd d x _) w w∈) | dc-list right gA d (v ∷ V) all
  ... | ⟨ i , w∈′ ⟩ | ⟨ j , all′ ⟩ = ⟨ ub d i j , inj₂ ⟨ v , ⟨ V ,
          ⟨ (λ u u∈ → mA (ub₂ d i j) _ (all′ u u∈)) , ⟨ m₂ (upd-⊆ x (ub₁ d i j) ⊆-refl) w w∈′ , ok ⟩ ⟩ ⟩ ⟩ ⟩

pair-good : ∀ {F G} → Good F → Good G → Good (λ σ → pair ⟨ F σ , ⟨ G σ , ptt ⟩ ⟩)
pair-good {F} {G} ⟨ mF , cF ⟩ ⟨ mG , cG ⟩ = ⟨ (λ { s ⦅ u , v ⦆ ⟨ u∈ , v∈ ⟩ → ⟨ mF s u u∈ , mG s v v∈ ⟩ }) , c ⟩
  where
  c : DC (λ σ → pair ⟨ F σ , ⟨ G σ , ptt ⟩ ⟩)
  c d ⦅ u , v ⦆ ⟨ u∈ , v∈ ⟩ with cF d u u∈ | cG d v v∈
  ... | ⟨ i , u∈′ ⟩ | ⟨ j , v∈′ ⟩ = ⟨ ub d i j , ⟨ mF (ub₁ d i j) u u∈′ , mG (ub₂ d i j) v v∈′ ⟩ ⟩

prim-good : ∀ p {F G} → Good F → Good G → Good (λ σ → primD p ⟨ F σ , ⟨ G σ , ptt ⟩ ⟩)
prim-good p {F} {G} ⟨ mF , cF ⟩ ⟨ mG , cG ⟩ =
  ⟨ (λ { s v ⟨ k , ⟨ l , ⟨ k∈ , ⟨ l∈ , eq ⟩ ⟩ ⟩ ⟩ → ⟨ k , ⟨ l , ⟨ mF s _ k∈ , ⟨ mG s _ l∈ , eq ⟩ ⟩ ⟩ ⟩ }) , c ⟩
  where
  c : DC (λ σ → primD p ⟨ F σ , ⟨ G σ , ptt ⟩ ⟩)
  c d v ⟨ k , ⟨ l , ⟨ k∈ , ⟨ l∈ , eq ⟩ ⟩ ⟩ ⟩ with cF d _ k∈ | cG d _ l∈
  ... | ⟨ i , k∈′ ⟩ | ⟨ j , l∈′ ⟩ =
    ⟨ ub d i j , ⟨ k , ⟨ l , ⟨ mF (ub₁ d i j) _ k∈′ , ⟨ mG (ub₂ d i j) _ l∈′ , eq ⟩ ⟩ ⟩ ⟩ ⟩

car-good : ∀ {F} → Good F → Good (λ σ → car ⟨ F σ , ptt ⟩)
car-good ⟨ m , c ⟩ = ⟨ (λ { s u ⟨ v , ∈ ⟩ → ⟨ v , m s _ ∈ ⟩ })
                     , (λ { d u ⟨ v , ∈ ⟩ → let ⟨ i , ∈′ ⟩ = c d _ ∈ in ⟨ i , ⟨ v , ∈′ ⟩ ⟩ }) ⟩

cdr-good : ∀ {F} → Good F → Good (λ σ → cdr ⟨ F σ , ptt ⟩)
cdr-good ⟨ m , c ⟩ = ⟨ (λ { s v ⟨ u , ∈ ⟩ → ⟨ u , m s _ ∈ ⟩ })
                     , (λ { d v ⟨ u , ∈ ⟩ → let ⟨ i , ∈′ ⟩ = c d _ ∈ in ⟨ i , ⟨ u , ∈′ ⟩ ⟩ }) ⟩

proj-good : ∀ {k} (i : Fin k) {F} → Good F → Good (λ σ → proj i ⟨ F σ , ptt ⟩)
proj-good i ⟨ m , c ⟩ = ⟨ (λ s w → m s (tup[ i ] w)) , (λ d w → c d (tup[ i ] w)) ⟩

inl-good : ∀ {F} → Good F → Good (λ σ → inl ⟨ F σ , ptt ⟩)
inl-good ⟨ m , c ⟩ = ⟨ (λ { s (left v) ∈ → m s v ∈ }) , (λ { d (left v) ∈ → c d v ∈ }) ⟩

inr-good : ∀ {F} → Good F → Good (λ σ → inr ⟨ F σ , ptt ⟩)
inr-good ⟨ m , c ⟩ = ⟨ (λ { s (right v) ∈ → m s v ∈ }) , (λ { d (right v) ∈ → c d v ∈ }) ⟩

{- one member that has an element of each of k sets -}
cover : ∀ k (F : Fin k → Store → 𝒫 Value) → (∀ j → Good (F j)) → ∀ d
  → (∀ j → nonempty (F j (⋃ d))) → Σ[ i ∈ I d ] (∀ j → nonempty (F j (at d i)))
cover zero F g d ne = ⟨ i₀ d , (λ ()) ⟩
cover (suc k) F g d ne
    with proj₂ (g zero) d _ (proj₂ (ne zero)) | cover k (λ j → F (suc j)) (λ j → g (suc j)) d (λ j → ne (suc j))
... | ⟨ i , ∈ ⟩ | ⟨ j , ne′ ⟩ = ⟨ ub d i j , (λ { zero → ⟨ _ , proj₁ (g zero) (ub₁ d i j) _ ∈ ⟩
                                              ; (suc l) → ⟨ _ , proj₁ (g (suc l)) (ub₂ d i j) _ (proj₂ (ne′ l)) ⟩ }) ⟩

{- CFG tails preserve directed unions -----------------------------------------------}

module _ (T : Table) (n : ℕ) where

  𝒜-good : ∀ a → Good (λ σ → 𝒜 T n σ a)
  𝒜-good (var x) with x <? n
  ... | yes _ = ⟨ (λ s → s x) , (λ d w w∈ → w∈) ⟩
  ... | no _ = const-good
  𝒜-good (lit B k) = const-good
  𝒜-good (fun-ref k) = const-good

  nth-good : ∀ as (j : Fin (length as)) → Good (λ σ → nthD (𝒜s T n σ as) j)
  nth-good (a ∷ as) zero = 𝒜-good a
  nth-good (a ∷ as) (suc j) = nth-good as j

  𝒯-good : ∀ as → Good (λ σ → 𝒯 (length as) (𝒜s T n σ as))
  𝒯-good [] = const-good
  𝒯-good (a ∷ as) = ⟨ m , c ⟩
    where
    g = nth-good (a ∷ as)
    m : Mono (λ σ → 𝒯 (length (a ∷ as)) (𝒜s T n σ (a ∷ as)))
    m s (tup[ i ] w) ⟨ refl , ⟨ w∈ , ne ⟩ ⟩ =
      ⟨ refl , ⟨ proj₁ (g i) s w w∈ , (λ j → ⟨ _ , proj₁ (g j) s _ (proj₂ (ne j)) ⟩) ⟩ ⟩
    c : DC (λ σ → 𝒯 (length (a ∷ as)) (𝒜s T n σ (a ∷ as)))
    c d (tup[ i ] w) ⟨ refl , ⟨ w∈ , ne ⟩ ⟩ with proj₂ (g i) d w w∈ | cover _ _ g d ne
    ... | ⟨ k , w∈′ ⟩ | ⟨ l , ne′ ⟩ = ⟨ ub d k l , ⟨ refl , ⟨ proj₁ (g i) (ub₁ d k l) w w∈′
        , (λ j → ⟨ _ , proj₁ (g j) (ub₂ d k l) _ (proj₂ (ne′ j)) ⟩) ⟩ ⟩ ⟩

  𝒮-good : ∀ s → Good (λ σ → 𝒮 T n σ s)
  𝒮-good (atm a) = 𝒜-good a
  𝒮-good (app f e a) = ⋆-good (⋆-good (𝒜-good f) (𝒜-good e)) (𝒜-good a)
  𝒮-good (I.pair a b) = pair-good (𝒜-good a) (𝒜-good b)
  𝒮-good (fst a) = car-good (𝒜-good a)
  𝒮-good (snd a) = cdr-good (𝒜-good a)
  𝒮-good (tuple as) = 𝒯-good as
  𝒮-good (get i a) = proj-good i (𝒜-good a)
  𝒮-good (I.inl a) = inl-good (𝒜-good a)
  𝒮-good (I.inr a) = inr-good (𝒜-good a)
  𝒮-good (prim p a b) = prim-good p (𝒜-good a) (𝒜-good b)

  ∅-good : Good (λ _ → ∅)
  ∅-good = ⟨ (λ _ _ ()) , (λ _ _ ()) ⟩

  tail-good : ∀ B → (∀ l → Good (B l)) → ∀ t → Good (⟪ t ⟫[ T ] n B)
  tail-good B g (C.return s) = 𝒮-good s
  tail-good B g (C.seq x s t) with x <? n
  ... | yes _ = ⋆-good (Λ-good x (tail-good B g t)) (𝒮-good s)
  ... | no _ = ∅-good
  tail-good B g (C.goto l) = g l
  tail-good B g (C.case a x l₁ l₂) with x <? n
  ... | yes _ = 𝒞-good x (𝒜-good a) (g l₁) (g l₂)
  ... | no _ = ∅-good

  blocks-good : ∀ bs l → Good (blocks T n bs l)
  blocks-good [] l = ∅-good
  blocks-good (t ∷ bs) l with l ≟ length bs
  ... | yes _ = tail-good (blocks T n bs) (blocks-good bs) t
  ... | no _ = blocks-good bs l

{- Imp is monotone, and consistent ----------------------------------------------------}

{- the value and the store of a run grow with the store it starts in -}
Grows : (𝒫 Value × Store) → (𝒫 Value × Store) → Set
Grows r r' = proj₁ r ⊆ proj₁ r' × proj₂ r ⊆ₛ proj₂ r'

↓-mono : ∀ {r r'} → Grows r r' → ∀ z → r ↓ z ⊆ r' ↓ z
↓-mono ⟨ v⊆ , s⊆ ⟩ z w ⟨ w∈ , ⟨ u , u∈ ⟩ ⟩ = ⟨ s⊆ z w w∈ , ⟨ u , v⊆ u u∈ ⟩ ⟩

↓-con : ∀ {r r'} → proj₂ r ~ₛ proj₂ r' → ∀ z → Every _~_ (r ↓ z) (r' ↓ z)
↓-con c z a b ⟨ a∈ , _ ⟩ ⟨ b∈ , _ ⟩ = c z a b a∈ b∈

module _ (T : Table) (n : ℕ) where

  I-mono : ∀ e {σ σ'} → σ ⊆ₛ σ' → Grows (ℐ⟦ e ⟧[ T ] n σ) (ℐ⟦ e ⟧[ T ] n σ')
  I-mono (simple s) s⊆ = ⟨ proj₁ (𝒮-good T n s) s⊆ , s⊆ ⟩
  I-mono (case a x e₁ e₂) {σ} {σ'} s⊆ with x <? n
  ... | no _ = ⟨ (λ _ ()) , s⊆ ⟩
  ... | yes _ =
    ⟨ lower (𝒞-mono _ _ ⟨ A⊆ , ⟨ (λ X X' X⊆ → lift (proj₁ (IH e₁ X⊆))) , ⟨ (λ X X' X⊆ → lift (proj₁ (IH e₂ X⊆))) , ptt ⟩ ⟩ ⟩)
    , (λ z → lower (𝒞-mono _ _ ⟨ A⊆ , ⟨ (λ X X' X⊆ → lift (↓IH e₁ X⊆ z)) , ⟨ (λ X X' X⊆ → lift (↓IH e₂ X⊆ z)) , ptt ⟩ ⟩ ⟩)) ⟩
    where
    A⊆ = lift (proj₁ (𝒜-good T n a) s⊆)
    IH = λ e {X X'} (X⊆ : X ⊆ X') → I-mono e (upd-⊆ x s⊆ X⊆)
    ↓IH : ∀ e {X X'} → X ⊆ X' → ∀ z → ℐ⟦ e ⟧[ T ] n (σ [ x ↦ X ]) ↓ z ⊆ ℐ⟦ e ⟧[ T ] n (σ' [ x ↦ X' ]) ↓ z
    ↓IH e {X} {X'} X⊆ = ↓-mono {ℐ⟦ e ⟧[ T ] n (σ [ x ↦ X ])} {ℐ⟦ e ⟧[ T ] n (σ' [ x ↦ X' ])} (IH e X⊆)
  I-mono (assign x e₁ e₂) {σ} {σ'} s⊆ with x <? n
  ... | no _ = ⟨ (λ _ ()) , s⊆ ⟩
  ... | yes _ =
    ⟨ lower (⋆-mono _ _ ⟨ Λ-mono _ _ ⟨ (λ X X' X⊆ → lift (proj₁ (IH X⊆))) , ptt ⟩ , ⟨ lift (proj₁ IH₁) , ptt ⟩ ⟩)
    , (λ z → lower (⋆-mono _ _ ⟨ Λ-mono _ _ ⟨ (λ X X' X⊆ → lift (↓IH X⊆ z)) , ptt ⟩
                              , ⟨ lift (proj₁ IH₁) , ptt ⟩ ⟩)) ⟩
    where
    IH₁ = I-mono e₁ s⊆
    σ₁ = proj₂ (ℐ⟦ e₁ ⟧[ T ] n σ)
    σ₁' = proj₂ (ℐ⟦ e₁ ⟧[ T ] n σ')
    IH = λ {X X'} (X⊆ : X ⊆ X') → I-mono e₂ (upd-⊆ x (proj₂ IH₁) X⊆)
    ↓IH : ∀ {X X'} → X ⊆ X' → ∀ z → ℐ⟦ e₂ ⟧[ T ] n (σ₁ [ x ↦ X ]) ↓ z ⊆ ℐ⟦ e₂ ⟧[ T ] n (σ₁' [ x ↦ X' ]) ↓ z
    ↓IH {X} {X'} X⊆ = ↓-mono {ℐ⟦ e₂ ⟧[ T ] n (σ₁ [ x ↦ X ])} {ℐ⟦ e₂ ⟧[ T ] n (σ₁' [ x ↦ X' ])} (IH X⊆)

module _ (T : Table) (TC : ∀ k → Con (T k)) (n : ℕ) where

  𝒜-con : ∀ a {σ σ'} → σ ~ₛ σ' → Every _~_ (𝒜 T n σ a) (𝒜 T n σ' a)
  𝒜-con (var x) c with x <? n
  ... | yes _ = c x
  ... | no _ = Con-⌈⌉ ω
  𝒜-con (lit B k) c = lower (ℬ-consis B k ptt ptt ptt)
  𝒜-con (fun-ref k) c = TC k

  𝒜s-con : ∀ as {σ σ'} → σ ~ₛ σ'
    → results-rel-pres (Every _~_) (replicate (length as) ■) (𝒜s T n σ as) (𝒜s T n σ' as)
  𝒜s-con [] c = ptt
  𝒜s-con (a ∷ as) c = ⟨ lift (𝒜-con a c) , 𝒜s-con as c ⟩

  𝒮-con : ∀ s {σ σ'} → σ ~ₛ σ' → Every _~_ (𝒮 T n σ s) (𝒮 T n σ' s)
  𝒮-con (atm a) c = 𝒜-con a c
  𝒮-con (app f e a) c =
    lower (⋆-consis _ _ ⟨ ⋆-consis _ _ ⟨ lift (𝒜-con f c) , ⟨ lift (𝒜-con e c) , ptt ⟩ ⟩ , ⟨ lift (𝒜-con a c) , ptt ⟩ ⟩)
  𝒮-con (I.pair a b) c = lower (pair-consis _ _ ⟨ lift (𝒜-con a c) , ⟨ lift (𝒜-con b c) , ptt ⟩ ⟩)
  𝒮-con (fst a) c = lower (car-consis _ _ ⟨ lift (𝒜-con a c) , ptt ⟩)
  𝒮-con (snd a) c = lower (cdr-consis _ _ ⟨ lift (𝒜-con a c) , ptt ⟩)
  𝒮-con (tuple as) c = lower (𝒯-consis (length as) _ _ (𝒜s-con as c))
  𝒮-con (get i a) c = lower (proj-consis i _ _ ⟨ lift (𝒜-con a c) , ptt ⟩)
  𝒮-con (I.inl a) c = lower (inl-consis _ _ ⟨ lift (𝒜-con a c) , ptt ⟩)
  𝒮-con (I.inr a) c = lower (inr-consis _ _ ⟨ lift (𝒜-con a c) , ptt ⟩)
  𝒮-con (prim p a b) c = lower (primD-consis p _ _ ⟨ lift (𝒜-con a c) , ⟨ lift (𝒜-con b c) , ptt ⟩ ⟩)

  {- consistent stores give consistent values and stores -}
  I-con : ∀ e {σ σ'} → σ ~ₛ σ'
    → Every _~_ (proj₁ (ℐ⟦ e ⟧[ T ] n σ)) (proj₁ (ℐ⟦ e ⟧[ T ] n σ')) × proj₂ (ℐ⟦ e ⟧[ T ] n σ) ~ₛ proj₂ (ℐ⟦ e ⟧[ T ] n σ')
  I-con (simple s) c = ⟨ 𝒮-con s c , c ⟩
  I-con (case a x e₁ e₂) {σ} {σ'} c with x <? n
  ... | no _ = ⟨ (λ _ _ ()) , c ⟩
  ... | yes _ =
    ⟨ lower (𝒞-consis _ _ ⟨ A~ , ⟨ (λ X X' X~ → lift (proj₁ (IH e₁ X~))) , ⟨ (λ X X' X~ → lift (proj₁ (IH e₂ X~))) , ptt ⟩ ⟩ ⟩)
    , (λ z → lower (𝒞-consis _ _ ⟨ A~ , ⟨ (λ X X' X~ → lift (↓IH e₁ X~ z)) , ⟨ (λ X X' X~ → lift (↓IH e₂ X~ z)) , ptt ⟩ ⟩ ⟩)) ⟩
    where
    A~ = lift (𝒜-con a c)
    IH = λ e {X X'} (X~ : Every _~_ X X') → I-con e (upd-~ x c X~)
    ↓IH : ∀ e {X X'} → Every _~_ X X' → ∀ z
      → Every _~_ (ℐ⟦ e ⟧[ T ] n (σ [ x ↦ X ]) ↓ z) (ℐ⟦ e ⟧[ T ] n (σ' [ x ↦ X' ]) ↓ z)
    ↓IH e {X} {X'} X~ = ↓-con {ℐ⟦ e ⟧[ T ] n (σ [ x ↦ X ])} {ℐ⟦ e ⟧[ T ] n (σ' [ x ↦ X' ])} (proj₂ (IH e X~))
  I-con (assign x e₁ e₂) {σ} {σ'} c with x <? n
  ... | no _ = ⟨ (λ _ _ ()) , c ⟩
  ... | yes _ =
    ⟨ lower (⋆-consis _ _ ⟨ Λ-consis _ _ ⟨ (λ X X' X~ → lift (proj₁ (IH X~))) , ptt ⟩ , ⟨ lift (proj₁ IH₁) , ptt ⟩ ⟩)
    , (λ z → lower (⋆-consis _ _ ⟨ Λ-consis _ _ ⟨ (λ X X' X~ → lift (↓IH X~ z)) , ptt ⟩
                                 , ⟨ lift (proj₁ IH₁) , ptt ⟩ ⟩)) ⟩
    where
    IH₁ = I-con e₁ c
    σ₁ = proj₂ (ℐ⟦ e₁ ⟧[ T ] n σ)
    σ₁' = proj₂ (ℐ⟦ e₁ ⟧[ T ] n σ')
    IH = λ {X X'} (X~ : Every _~_ X X') → I-con e₂ (upd-~ x (proj₂ IH₁) X~)
    ↓IH : ∀ {X X'} → Every _~_ X X' → ∀ z
      → Every _~_ (ℐ⟦ e₂ ⟧[ T ] n (σ₁ [ x ↦ X ]) ↓ z) (ℐ⟦ e₂ ⟧[ T ] n (σ₁' [ x ↦ X' ]) ↓ z)
    ↓IH {X} {X'} X~ = ↓-con {ℐ⟦ e₂ ⟧[ T ] n (σ₁ [ x ↦ X ])} {ℐ⟦ e₂ ⟧[ T ] n (σ₁' [ x ↦ X' ])} (proj₂ (IH X~))

zeros-con : Con-env zeros
zeros-con _ = lower (ℬ-consis _ _ ptt ptt ptt)

frame-~ : ∀ {X X' Y Y'} → Every _~_ X X' → Every _~_ Y Y' → frame X Y ~ₛ frame X' Y'
frame-~ X~ Y~ zero = X~
frame-~ X~ Y~ (suc zero) = Y~
frame-~ X~ Y~ (suc (suc y)) = zeros-con y

{- the tables of programs are consistent -}
tableᵢ-con : ∀ ds k → Con (tableᵢ ds k)
tableᵢ-con [] k = λ _ _ ()
tableᵢ-con (body m e ∷ bs) k with k ≟ length bs
... | yes _ = ΛΛ-con (λ X X' Y Y' X~ Y~ → proj₁ (I-con (tableᵢ bs) (tableᵢ-con bs) m e (frame-~ X~ Y~)))
... | no _ = tableᵢ-con bs k

{- Binding the value of a run ---------------------------------------------------------}

module _ (n : ℕ) where

  {- x := the value of r, then K in the store of r -}
  letK⁰ : ℕ → 𝒫 Value × Store → (Store → 𝒫 Value) → 𝒫 Value
  letK⁰ x r K = ⋆ ⟨ Λ ⟨ (λ X → K (proj₂ r [ x ↦ X ])) , ptt ⟩ , ⟨ proj₁ r , ptt ⟩ ⟩

  letK : ℕ → 𝒫 Value × Store → (Store → 𝒫 Value) → 𝒫 Value
  letK x r K = checked n x (letK⁰ x r K)

  letK-≃ : ∀ {x r D' K K'} → Con-env (proj₂ r) → proj₁ r ≃ D'
    → (∀ σ' → Con-env σ' → K σ' ≃ K' σ') → letK x r K ≃ letK x ⟨ D' , proj₂ r ⟩ K'
  letK-≃ {x} {r} {D'} {K} {K'} c D≃ K≃ =
    checked-≃ n {x} (⋆-≃ (Λ-≃ {λ X → K (proj₂ r [ x ↦ X ])} {λ X → K' (proj₂ r [ x ↦ X ])}
                              (λ X _ cX → K≃ _ (upd-~ x c (≈⇒Con cX)))) D≃)

  {- a construct that assigns slot y: nothing, if y is beyond the frame -}
  letK-checked : ∀ {x y σ r K} → letK x (checkedᵢ n y σ r) K ≃ checked n y (letK x r K)
  letK-checked {x} {y} {σ} {r} {K} with y <? n
  ... | yes _ = ≃-refl
  ... | no _ = ⟨ G , (λ _ ()) ⟩
    where
    G : letK x ⟨ ∅ , σ ⟩ K ⊆ ∅
    G w w∈ with x <? n
    G w ⟨ V , ⟨ _ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ | yes _ = proj₂ (ne-mem ne V⊆)
    G w () | no _

  {- the value of a construct that assigns slot x -}
  checked-val : ∀ {x σ r} → checked n x (proj₁ r) ≃ proj₁ (checkedᵢ n x σ r)
  checked-val {x} with x <? n
  ... | yes _ = ≃-refl
  ... | no _ = ⟨ (λ _ ()) , (λ _ ()) ⟩

  checked-⋆Λ : ∀ {x F D} → ⋆ ⟨ Λ ⟨ (λ Y → checked n x (F Y)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ≃ checked n x (⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
  checked-⋆Λ {x} with x <? n
  ... | yes _ = ≃-refl
  ... | no _ = ⟨ (λ { w ⟨ V , ⟨ ⟨ () , _ ⟩ , _ ⟩ ⟩ }) , (λ _ ()) ⟩

  checked-𝒞 : ∀ {x A F G} → 𝒞 ⟨ A , ⟨ (λ Y → checked n x (F Y)) , ⟨ (λ Y → checked n x (G Y)) , ptt ⟩ ⟩ ⟩
    ≃ checked n x (𝒞 ⟨ A , ⟨ F , ⟨ G , ptt ⟩ ⟩ ⟩)
  checked-𝒞 {x} with x <? n
  ... | yes _ = ≃-refl
  ... | no _ = ⟨ (λ { w (inj₁ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ () , _ ⟩ ⟩ ⟩ ⟩) ; w (inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ () , _ ⟩ ⟩ ⟩ ⟩) }) , (λ _ ()) ⟩

{- Collecting the runs ------------------------------------------------------------------}

{- E Y runs a construct with the set Y bound; its value and store grow with Y -}
EMono : (𝒫 Value → 𝒫 Value × Store) → Set₁
EMono E = ∀ {Y Y'} → Y ⊆ Y' → Grows (E Y) (E Y')

Part : 𝒫 Value → List Value → Set
Part P Y = Y ≢ [] × mem Y ⊆ P

++-part : ∀ {P Y Y'} → Part P Y → Part P Y' → Part P (Y ++ Y')
++-part {Y = []} ⟨ ne , _ ⟩ _ = ⊥-elim (ne refl)
++-part {P} {v ∷ Y} {Y'} ⟨ _ , Y⊆ ⟩ ⟨ _ , Y'⊆ ⟩ = ⟨ (λ ()) , G ⟩
  where
  G : mem (v ∷ Y ++ Y') ⊆ P
  G u u∈ with ∈-++⁻ (v ∷ Y) u∈
  ... | inj₁ i = Y⊆ u i
  ... | inj₂ i = Y'⊆ u i

{- an element of K on a directed union, and finitely many elements of
   the G i, are all in one member -}
one-member : ∀ {K} d (G : I d → 𝒫 Value) → Good K → (∀ i j → G i ⊆ G (ub d i j) × G j ⊆ G (ub d i j))
  → ∀ {w} X → w ∈ K (⋃ d) → (∀ u → u ∈ mem X → Σ[ i ∈ I d ] u ∈ G i)
  → Σ[ i ∈ I d ] w ∈ K (at d i) × mem X ⊆ G i
one-member d G ⟨ mK , cK ⟩ up X w∈ h with cK d _ w∈ | dir-list d G up X h
... | ⟨ i , w∈′ ⟩ | ⟨ j , X⊆ ⟩ = ⟨ ub d i j , ⟨ mK (ub₁ d i j) _ w∈′ , (λ u u∈ → proj₂ (up i j) u (X⊆ u u∈)) ⟩ ⟩

{- K ran on the store that collects the runs of E on the finite parts
   of P, with x bound to X, which collects their values: then one run
   of E, on a consistent finite part of P, gives X and what K needs -}
merge : ∀ {P E K x X σm w} → Con P → EMono E → Good K → X ≢ []
  → (∀ u → u ∈ mem X → Σ[ Y ∈ List Value ] Part P Y × u ∈ proj₁ (E (mem Y)))
  → (∀ z u → u ∈ σm z → Σ[ Y ∈ List Value ] Part P Y × u ∈ (E (mem Y) ↓ z))
  → w ∈ K (σm [ x ↦ mem X ])
  → Σ[ Y ∈ List Value ] Part P Y × Y ≈ Y × mem X ⊆ proj₁ (E (mem Y)) × w ∈ K (proj₂ (E (mem Y)) [ x ↦ mem X ])
merge {P} {E} {K} {x} {X} {σm} {w} cP mE gK neX inX inσ w∈
    with one-member d G gK up X (proj₁ gK σ⊆ w w∈) got
  where
  Run = Σ[ Y ∈ List Value ] Part P Y × nonempty (proj₁ (E (mem Y)))
  G : Run → 𝒫 Value
  G i = proj₁ (E (mem (proj₁ i)))
  first = inX _ (proj₂ (E≢[]⇒nonempty-mem neX))
  ub′ : Run → Run → Run
  ub′ ⟨ Y , ⟨ p , ⟨ u , u∈ ⟩ ⟩ ⟩ ⟨ Y' , ⟨ p' , _ ⟩ ⟩ =
    ⟨ Y ++ Y' , ⟨ ++-part p p' , ⟨ u , proj₁ (mE (λ v → ∈-++⁺ˡ)) u u∈ ⟩ ⟩ ⟩
  up : ∀ i j → G i ⊆ G (ub′ i j) × G j ⊆ G (ub′ i j)
  up i j = ⟨ proj₁ (mE (λ v → ∈-++⁺ˡ)) , proj₁ (mE (λ v → ∈-++⁺ʳ (proj₁ i))) ⟩
  d : Dir
  d = record { I = Run ; at = λ i → proj₂ (E (mem (proj₁ i))) [ x ↦ mem X ]
             ; i₀ = ⟨ proj₁ first , ⟨ proj₁ (proj₂ first) , ⟨ _ , proj₂ (proj₂ first) ⟩ ⟩ ⟩
             ; ub = ub′
             ; ub₁ = λ i j → upd-⊆ x (proj₂ (mE (λ v → ∈-++⁺ˡ))) ⊆-refl
             ; ub₂ = λ i j → upd-⊆ x (proj₂ (mE (λ v → ∈-++⁺ʳ (proj₁ i)))) ⊆-refl }
  σ⊆ : σm [ x ↦ mem X ] ⊆ₛ ⋃ d
  σ⊆ z with z ≟ x
  ... | yes _ = λ u u∈ → ⟨ i₀ d , u∈ ⟩
  ... | no _ = λ u u∈ → let ⟨ Y , ⟨ p , ⟨ u∈′ , ne ⟩ ⟩ ⟩ = inσ z u u∈ in ⟨ ⟨ Y , ⟨ p , ne ⟩ ⟩ , u∈′ ⟩
  got : ∀ u → u ∈ mem X → Σ[ i ∈ Run ] u ∈ G i
  got u u∈ = let ⟨ Y , ⟨ p , u∈′ ⟩ ⟩ = inX u u∈ in ⟨ ⟨ Y , ⟨ p , ⟨ u , u∈′ ⟩ ⟩ ⟩ , u∈′ ⟩
... | ⟨ ⟨ Y , ⟨ p , _ ⟩ ⟩ , ⟨ w∈′ , X⊆ ⟩ ⟩ = ⟨ Y , ⟨ p , ⟨ Con⇒≈ Y cP (proj₂ p) , ⟨ X⊆ , w∈′ ⟩ ⟩ ⟩ ⟩

{- The laws of the commuting conversion -----------------------------------------------}

module _ (n : ℕ) where

  {- a nested assignment: K after y := D; E y, or after each run of E -}
  let-assoc⁰ : ∀ {D E K x} → Con D → EMono E → Good K
    → ⋆ ⟨ Λ ⟨ (λ Y → letK⁰ n x (E Y) K) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ≃ letK⁰ n x (letₛ D E) K
  let-assoc⁰ {D} {E} {K} {x} cD mE gK = ⟨ G , H ⟩
    where
    G : ⋆ ⟨ Λ ⟨ (λ Y → letK⁰ n x (E Y) K) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⊆ letK⁰ n x (letₛ D E) K
    G w ⟨ Y , ⟨ ⟨ ⟨ X , ⟨ ⟨ w∈ , ⟨ neX , cX ⟩ ⟩ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ , ⟨ neY , cY ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ =
      ⟨ X , ⟨ ⟨ proj₁ gK (upd-⊆ x σ⊆ ⊆-refl) w w∈ , ⟨ neX , cX ⟩ ⟩
          , ⟨ (λ u u∈ → ⟨ Y , ⟨ ⟨ X⊆ u u∈ , ⟨ neY , cY ⟩ ⟩ , ⟨ Y⊆ , neY ⟩ ⟩ ⟩) , neX ⟩ ⟩ ⟩
      where σ⊆ = λ z u u∈ → ⟨ Y , ⟨ ⟨ ⟨ u∈ , ne-mem neX X⊆ ⟩ , ⟨ neY , cY ⟩ ⟩ , ⟨ Y⊆ , neY ⟩ ⟩ ⟩
    H : letK⁰ n x (letₛ D E) K ⊆ ⋆ ⟨ Λ ⟨ (λ Y → letK⁰ n x (E Y) K) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
    H w ⟨ X , ⟨ ⟨ w∈ , ⟨ neX , cX ⟩ ⟩ , ⟨ X⊆ , _ ⟩ ⟩ ⟩
        with merge {D} {E} {K} {x} {X} {proj₂ (letₛ D E)} cD mE gK neX inX inσ w∈
      where
      inX : ∀ u → u ∈ mem X → Σ[ Y ∈ List Value ] Part D Y × u ∈ proj₁ (E (mem Y))
      inX u u∈ with X⊆ u u∈
      ... | ⟨ Y , ⟨ ⟨ u∈′ , ⟨ neY , _ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ = ⟨ Y , ⟨ ⟨ neY , Y⊆ ⟩ , u∈′ ⟩ ⟩
      inσ : ∀ z u → u ∈ proj₂ (letₛ D E) z → Σ[ Y ∈ List Value ] Part D Y × u ∈ (E (mem Y) ↓ z)
      inσ z u ⟨ Y , ⟨ ⟨ u∈ , ⟨ neY , _ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ = ⟨ Y , ⟨ ⟨ neY , Y⊆ ⟩ , u∈ ⟩ ⟩
    ... | ⟨ Y , ⟨ ⟨ neY , Y⊆ ⟩ , ⟨ cY , ⟨ X⊆′ , w∈′ ⟩ ⟩ ⟩ ⟩ =
      ⟨ Y , ⟨ ⟨ ⟨ X , ⟨ ⟨ w∈′ , ⟨ neX , cX ⟩ ⟩ , ⟨ X⊆′ , neX ⟩ ⟩ ⟩ , ⟨ neY , cY ⟩ ⟩ , ⟨ Y⊆ , neY ⟩ ⟩ ⟩

  let-assoc : ∀ {D E K x} → Con D → EMono E → Good K
    → ⋆ ⟨ Λ ⟨ (λ Y → letK n x (E Y) K) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ≃ letK n x (letₛ D E) K
  let-assoc {D} {E} {K} {x} cD mE gK =
    ≃-trans (checked-⋆Λ n {x} {λ Y → letK⁰ n x (E Y) K} {D}) (checked-≃ n {x} (let-assoc⁰ cD mE gK))

  {- the bound parts of one run, as a branch of 𝒞 -}
  pack : ∀ {P} {E : 𝒫 Value → 𝒫 Value × Store} {K x X w} → X ≢ [] → X ≈ X
    → Σ[ Y ∈ List Value ] Part P Y × Y ≈ Y × mem X ⊆ proj₁ (E (mem Y)) × w ∈ K (proj₂ (E (mem Y)) [ x ↦ mem X ])
    → Σ[ v ∈ Value ] Σ[ V ∈ List Value ] (∀ d → d ∈ mem (v ∷ V) → d ∈ P)
        × w ∈ letK⁰ n x (E (mem (v ∷ V))) K × (v ∷ V) ≈ (v ∷ V)
  pack neX cX ⟨ [] , ⟨ ⟨ ne , _ ⟩ , _ ⟩ ⟩ = ⊥-elim (ne refl)
  pack {X = X} neX cX ⟨ v ∷ V , ⟨ ⟨ _ , Y⊆ ⟩ , ⟨ cY , ⟨ X⊆ , w∈ ⟩ ⟩ ⟩ ⟩ =
    ⟨ v , ⟨ V , ⟨ Y⊆ , ⟨ ⟨ X , ⟨ ⟨ w∈ , ⟨ neX , cX ⟩ ⟩ , ⟨ X⊆ , neX ⟩ ⟩ ⟩ , cY ⟩ ⟩ ⟩ ⟩

  {- a case: K after a case on A, or after each run of a branch; by the
     consistency of A, all the runs are of the same branch -}
  let-case⁰ : ∀ {A E₁ E₂ K x} → Con A → EMono E₁ → EMono E₂ → Good K
    → 𝒞 ⟨ A , ⟨ (λ Y → letK⁰ n x (E₁ Y) K) , ⟨ (λ Y → letK⁰ n x (E₂ Y) K) , ptt ⟩ ⟩ ⟩
      ≃ letK⁰ n x (caseₛ A E₁ E₂) K
  let-case⁰ {A} {E₁} {E₂} {K} {x} cA m₁ m₂ gK = ⟨ G , H ⟩
    where
    G : 𝒞 ⟨ A , ⟨ (λ Y → letK⁰ n x (E₁ Y) K) , ⟨ (λ Y → letK⁰ n x (E₂ Y) K) , ptt ⟩ ⟩ ⟩
        ⊆ letK⁰ n x (caseₛ A E₁ E₂) K
    G w (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ ⟨ X , ⟨ ⟨ w∈ , ⟨ neX , cX ⟩ ⟩ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ , cV ⟩ ⟩ ⟩ ⟩) =
      ⟨ X , ⟨ ⟨ proj₁ gK (upd-⊆ x σ⊆ ⊆-refl) w w∈ , ⟨ neX , cX ⟩ ⟩
          , ⟨ (λ u u∈ → inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ X⊆ u u∈ , cV ⟩ ⟩ ⟩ ⟩) , neX ⟩ ⟩ ⟩
      where σ⊆ = λ z u u∈ → inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ ⟨ u∈ , ne-mem neX X⊆ ⟩ , cV ⟩ ⟩ ⟩ ⟩
    G w (inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ ⟨ X , ⟨ ⟨ w∈ , ⟨ neX , cX ⟩ ⟩ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ , cV ⟩ ⟩ ⟩ ⟩) =
      ⟨ X , ⟨ ⟨ proj₁ gK (upd-⊆ x σ⊆ ⊆-refl) w w∈ , ⟨ neX , cX ⟩ ⟩
          , ⟨ (λ u u∈ → inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ X⊆ u u∈ , cV ⟩ ⟩ ⟩ ⟩) , neX ⟩ ⟩ ⟩
      where σ⊆ = λ z u u∈ → inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ ⟨ u∈ , ne-mem neX X⊆ ⟩ , cV ⟩ ⟩ ⟩ ⟩
    H : letK⁰ n x (caseₛ A E₁ E₂) K
        ⊆ 𝒞 ⟨ A , ⟨ (λ Y → letK⁰ n x (E₁ Y) K) , ⟨ (λ Y → letK⁰ n x (E₂ Y) K) , ptt ⟩ ⟩ ⟩
    H w ⟨ [] , ⟨ _ , ⟨ _ , ne ⟩ ⟩ ⟩ = ⊥-elim (ne refl)
    H w ⟨ u₀ ∷ X , ⟨ ⟨ w∈ , ⟨ neX , cX ⟩ ⟩ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ with X⊆ u₀ (here refl)
    ... | inj₁ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩ =
      inj₁ (pack {E = E₁} {K} {x} neX cX (merge {E = E₁} {K} {x} {σm = proj₂ (caseₛ A E₁ E₂)} (λ a b → cA _ _) m₁ gK neX inX inσ w∈))
      where
      other : ∀ {v} → right v ∈ A → ∀ {B : Set} → B
      other r∈ = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) r∈)
      inX : ∀ u → u ∈ mem (u₀ ∷ X) → Σ[ Y ∈ List Value ] Part (λ d → left d ∈ A) Y × u ∈ proj₁ (E₁ (mem Y))
      inX u u∈ with X⊆ u u∈
      ... | inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ u∈′ , _ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V , ⟨ ⟨ (λ ()) , all ⟩ , u∈′ ⟩ ⟩
      ... | inj₂ ⟨ v , ⟨ V , ⟨ all , _ ⟩ ⟩ ⟩ = other (all v (here refl))
      inσ : ∀ z u → u ∈ proj₂ (caseₛ A E₁ E₂) z → Σ[ Y ∈ List Value ] Part (λ d → left d ∈ A) Y × u ∈ (E₁ (mem Y) ↓ z)
      inσ z u (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩) = ⟨ v ∷ V , ⟨ ⟨ (λ ()) , all ⟩ , u∈ ⟩ ⟩
      inσ z u (inj₂ ⟨ v , ⟨ V , ⟨ all , _ ⟩ ⟩ ⟩) = other (all v (here refl))
    ... | inj₂ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩ =
      inj₂ (pack {E = E₂} {K} {x} neX cX (merge {E = E₂} {K} {x} {σm = proj₂ (caseₛ A E₁ E₂)} (λ a b → cA _ _) m₂ gK neX inX inσ w∈))
      where
      other : ∀ {v} → left v ∈ A → ∀ {B : Set} → B
      other l∈ = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) l∈)
      inX : ∀ u → u ∈ mem (u₀ ∷ X) → Σ[ Y ∈ List Value ] Part (λ d → right d ∈ A) Y × u ∈ proj₁ (E₂ (mem Y))
      inX u u∈ with X⊆ u u∈
      ... | inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ u∈′ , _ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V , ⟨ ⟨ (λ ()) , all ⟩ , u∈′ ⟩ ⟩
      ... | inj₁ ⟨ v , ⟨ V , ⟨ all , _ ⟩ ⟩ ⟩ = other (all v (here refl))
      inσ : ∀ z u → u ∈ proj₂ (caseₛ A E₁ E₂) z → Σ[ Y ∈ List Value ] Part (λ d → right d ∈ A) Y × u ∈ (E₂ (mem Y) ↓ z)
      inσ z u (inj₂ ⟨ v , ⟨ V , ⟨ all , ⟨ u∈ , _ ⟩ ⟩ ⟩ ⟩) = ⟨ v ∷ V , ⟨ ⟨ (λ ()) , all ⟩ , u∈ ⟩ ⟩
      inσ z u (inj₁ ⟨ v , ⟨ V , ⟨ all , _ ⟩ ⟩ ⟩) = other (all v (here refl))

  let-case : ∀ {A E₁ E₂ K x} → Con A → EMono E₁ → EMono E₂ → Good K
    → 𝒞 ⟨ A , ⟨ (λ Y → letK n x (E₁ Y) K) , ⟨ (λ Y → letK n x (E₂ Y) K) , ptt ⟩ ⟩ ⟩ ≃ letK n x (caseₛ A E₁ E₂) K
  let-case {A} {E₁} {E₂} {K} {x} cA m₁ m₂ gK =
    ≃-trans (checked-𝒞 n {x} {A} {λ Y → letK⁰ n x (E₁ Y) K} {λ Y → letK⁰ n x (E₂ Y) K})
            (checked-≃ n {x} (let-case⁰ cA m₁ m₂ gK))

{- The pass preserves meanings ----------------------------------------------------------}

{- for tables T (of CFG) and T' (of Imp) that agree, T' consistent -}
module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TC : ∀ k → Con (T' k)) (n : ℕ) where

  open Agreeing TT n

  {- k means the same with newer blocks -}
  Stable : List C.Tail → C.Tail → Set₁
  Stable bs k = ∀ bs'' → bs ≼ bs'' → ∀ σ → Con-env σ → ⟪ k ⟫[ T ] n (B bs'') σ ≃ ⟪ k ⟫[ T ] n (B bs) σ

  {- a jump to the block that holds k -}
  goto-stable : ∀ {k bs bs₁} → k ∷ bs ≼ bs₁ → Stable bs₁ (C.goto (length bs))
  goto-stable e₁ bs'' e σ c = goto-≃ e₁ e σ

  {- explicate-assign e x k: run e, assign x, then k -}
  cps : ∀ e x k bs → Stable bs k → ∀ bs'' → proj₂ (explicate-assign e x k bs) ≼ bs'' → ∀ σ → Con-env σ
    → ⟪ proj₁ (explicate-assign e x k bs) ⟫[ T ] n (B bs'') σ ≃ letK n x (ℐ⟦ e ⟧[ T' ] n σ) (⟪ k ⟫[ T ] n (B bs))
  cps (simple s) x k bs st bs'' ext σ c =
    letK-≃ n {x} {⟨ 𝒮 T n σ s , σ ⟩} c (𝒮-≃ s σ) (st bs'' ext)
  cps (assign y e₁ e₂) x k bs st bs'' ext σ c =
    ≃-trans (cps e₁ y t' bs₁ st' bs'' ext σ c)
    (≃-trans (letK-≃ n {y} {ℐ⟦ e₁ ⟧[ T' ] n σ} (proj₂ IC) ≃-refl (cps e₂ x k bs st bs₁ ≼-refl))
    (≃-sym (≃-trans (letK-checked n {x} {y} {K = K}) (checked-≃ n {y} (≃-sym (let-assoc n {K = K} {x} (proj₁ IC) mE gK))))))
    where
    t' = proj₁ (explicate-assign e₂ x k bs)
    bs₁ = proj₂ (explicate-assign e₂ x k bs)
    st' : Stable bs₁ t'
    st' bs₂ e σ' c' = ≃-trans (cps e₂ x k bs st bs₂ e σ' c') (≃-sym (cps e₂ x k bs st bs₁ ≼-refl σ' c'))
    K = ⟪ k ⟫[ T ] n (B bs)
    IC = I-con T' TC n e₁ c
    mE = λ {Y Y'} (Y⊆ : Y ⊆ Y') → I-mono T' n e₂ (upd-⊆ y (λ z → ⊆-refl) Y⊆)
    gK = tail-good T n (B bs) (blocks-good T n bs) k
  cps (case a y e₁ e₂) x k bs st bs'' ext σ c =
    ≃-trans (checked-≃ n {y} (𝒞-≃ {F = λ Y → B bs'' (length bs₂) (σ [ y ↦ Y ])}
                                  {λ Y → letK n x (ℐ⟦ e₁ ⟧[ T' ] n (σ [ y ↦ Y ])) K}
                                  {λ Y → B bs'' (length bs₄) (σ [ y ↦ Y ])}
                                  {λ Y → letK n x (ℐ⟦ e₂ ⟧[ T' ] n (σ [ y ↦ Y ])) K}
               (𝒜-≃ a σ) (λ v V cV → br₁ _ (upd-~ y c (≈⇒Con cV))) (λ v V cV → br₂ _ (upd-~ y c (≈⇒Con cV)))))
    (≃-sym (≃-trans (letK-checked n {x} {y} {K = K}) (checked-≃ n {y} (≃-sym (let-case n {K = K} {x} (𝒜-con T' TC n a c) m₁ m₂ gK)))))
    where
    l = length bs
    K = ⟪ k ⟫[ T ] n (B bs)
    bs₁ = k ∷ bs
    t₁ = proj₁ (explicate-assign e₁ x (C.goto l) bs₁)
    bs₂ = proj₂ (explicate-assign e₁ x (C.goto l) bs₁)
    bs₃ = t₁ ∷ bs₂
    bs₄ = proj₂ (explicate-assign e₂ x (C.goto l) bs₃)
    e₁₃ : bs₁ ≼ bs₃
    e₁₃ = ≼-trans (grows-assign e₁ x (C.goto l) bs₁) ≼-∷
    br₁ : ∀ σ' → Con-env σ' → B bs'' (length bs₂) σ' ≃ letK n x (ℐ⟦ e₁ ⟧[ T' ] n σ') K
    br₁ σ' c' =
      ≃-trans (at-σ (blocks-at T n (≼-trans (grows-assign e₂ x (C.goto l) bs₃) (≼-trans ≼-∷ ext))) σ')
      (≃-trans (cps e₁ x (C.goto l) bs₁ (goto-stable ≼-refl) bs₂ ≼-refl σ' c')
               (≃-reflexive (cong (letK n x (ℐ⟦ e₁ ⟧[ T' ] n σ')) (blocks-at T n {k} {bs} ≼-refl))))
    br₂ : ∀ σ' → Con-env σ' → B bs'' (length bs₄) σ' ≃ letK n x (ℐ⟦ e₂ ⟧[ T' ] n σ') K
    br₂ σ' c' =
      ≃-trans (at-σ (blocks-at T n ext) σ')
      (≃-trans (cps e₂ x (C.goto l) bs₃ (goto-stable e₁₃) bs₄ ≼-refl σ' c')
               (≃-reflexive (cong (letK n x (ℐ⟦ e₂ ⟧[ T' ] n σ')) (blocks-at T n e₁₃))))
    m₁ = λ {Y Y'} (Y⊆ : Y ⊆ Y') → I-mono T' n e₁ (upd-⊆ y (λ z → ⊆-refl) Y⊆)
    m₂ = λ {Y Y'} (Y⊆ : Y ⊆ Y') → I-mono T' n e₂ (upd-⊆ y (λ z → ⊆-refl) Y⊆)
    gK = tail-good T n (B bs) (blocks-good T n bs) k

  {- explicate-tail e: the value of e -}
  tail : ∀ e bs bs'' → proj₂ (explicate-tail e bs) ≼ bs'' → ∀ σ → Con-env σ
    → ⟪ proj₁ (explicate-tail e bs) ⟫[ T ] n (B bs'') σ ≃ proj₁ (ℐ⟦ e ⟧[ T' ] n σ)
  tail (simple s) bs bs'' ext σ c = 𝒮-≃ s σ
  tail (assign x e₁ e₂) bs bs'' ext σ c =
    ≃-trans (cps e₁ x t₂ bs₁ st bs'' ext σ c)
    (≃-trans (letK-≃ n {x} {ℐ⟦ e₁ ⟧[ T' ] n σ} (proj₂ (I-con T' TC n e₁ c)) ≃-refl (tail e₂ bs bs₁ ≼-refl))
             (checked-val n {x}))
    where
    t₂ = proj₁ (explicate-tail e₂ bs)
    bs₁ = proj₂ (explicate-tail e₂ bs)
    st : Stable bs₁ t₂
    st bs₂ e σ' c' = ≃-trans (tail e₂ bs bs₂ e σ' c') (≃-sym (tail e₂ bs bs₁ ≼-refl σ' c'))
  tail (case a x e₁ e₂) bs bs'' ext σ c =
    ≃-trans (checked-≃ n {x} (𝒞-≃ {F = λ Y → B bs'' (length bs₁) (σ [ x ↦ Y ])}
                                  {λ Y → proj₁ (ℐ⟦ e₁ ⟧[ T' ] n (σ [ x ↦ Y ]))}
                                  {λ Y → B bs'' (length bs₃) (σ [ x ↦ Y ])}
                                  {λ Y → proj₁ (ℐ⟦ e₂ ⟧[ T' ] n (σ [ x ↦ Y ]))}
               (𝒜-≃ a σ) (λ v V cV → br₁ _ (upd-~ x c (≈⇒Con cV))) (λ v V cV → br₂ _ (upd-~ x c (≈⇒Con cV)))))
    (checked-val n {x})
    where
    t₁ = proj₁ (explicate-tail e₁ bs)
    bs₁ = proj₂ (explicate-tail e₁ bs)
    bs₂ = t₁ ∷ bs₁
    bs₃ = proj₂ (explicate-tail e₂ bs₂)
    br₁ : ∀ σ' → Con-env σ' → B bs'' (length bs₁) σ' ≃ proj₁ (ℐ⟦ e₁ ⟧[ T' ] n σ')
    br₁ σ' c' = ≃-trans (at-σ (blocks-at T n (≼-trans (grows-tail e₂ bs₂) (≼-trans ≼-∷ ext))) σ')
                        (tail e₁ bs bs₁ ≼-refl σ' c')
    br₂ : ∀ σ' → Con-env σ' → B bs'' (length bs₃) σ' ≃ proj₁ (ℐ⟦ e₂ ⟧[ T' ] n σ')
    br₂ σ' c' = ≃-trans (at-σ (blocks-at T n ext) σ') (tail e₂ bs₂ bs₃ ≼-refl σ' c')

{- Programs -----------------------------------------------------------------------------}

code-≃ : ∀ {T T'} → (∀ k → T k ≃ T' k) → (∀ k → Con (T' k)) → ∀ b → codeₜ T (explicate-body b) ≃ codeᵢ T' b
code-≃ TT TC (body n e) = Λ-≃ λ X _ cX → Λ-≃ λ Y _ cY →
  tail TT TC n e [] _ ≼-refl (frame (mem X) (mem Y)) (frame-~ (≈⇒Con cX) (≈⇒Con cY))

table-≃ : ∀ ds k → tableₜ (map explicate-body ds) k ≃ tableᵢ ds k
table-≃ [] k = ≃-refl
table-≃ (b ∷ bs) k with k ≟ length (map explicate-body bs) | k ≟ length bs
... | yes _ | yes _ = code-≃ (table-≃ bs) (tableᵢ-con bs) b
... | no _ | no _ = table-≃ bs k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-map explicate-body bs)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-map explicate-body bs))))

explicate-correct : ∀ P → ⟦ explicate P ⟧ₚ ≃ ℐ⟦ P ⟧ₚ
explicate-correct (program ds (body n e)) =
  tail (table-≃ ds) (tableᵢ-con ds) n e [] _ ≼-refl zeros zeros-con

{- the whole compiler, into CFG -}
open Into ℐ⟦_⟧ₚ compile-imp-same explicate-correct public
