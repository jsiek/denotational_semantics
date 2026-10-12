{-

  Correctness of lift locals (monadic Clos5 → Imp,
  Compile/LiftLocals.agda) against the continuation-passing semantics of
  Imp (Sem/ImpK.agda): the meaning of the Imp program is that of the
  Clos5 program.

    lift-program-correct : ⟦ lift-program P mp ⟧ᴷₚ ≃ ⟦ P ⟧ₚ

  The invariant at depth d is as for the direct semantics
  (Correctness/LiftLocalsCorrect.agda): the store agrees with the
  environment, slot d ∸ (x + 1) meaning variable x for x < d (Agree), and
  the variables from d on are out of scope (Scope). Running lift n d m
  with a continuation κ that means K D, given the value D and any store
  that agrees with the environment, means K applied to the meaning of m
  (lift-sem). So the store that m leaves is not described: κ is only
  ever given stores that agree.

  K is what the enclosing lets make of the value: nothing at the end of
  a body (K D = D), and ⋆ ⟨ Λ G , D ⟩ for the right-hand side of a let
  whose body and continuation mean G. The commuting conversion is now on
  the Clos5 side: K commutes with let and with case (let-law,
  case-law). Each needs the bound sets to be consistent, so that the
  finitely many runs that ⋆ ⟨ Λ G , - ⟩ uses can be joined into one
  (join): the meaning of the right-hand side of a let, and the
  scrutinee of a case, which has only left or only right elements.

-}

open import SetsAsPredicates
open import NewDOpSig using (Results)
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos5 using (program; Args)
open import Compiler.Lang.Mon
open import Compiler.Compile.LiftLocals using (lift-atom; lift-atoms; lift; height; lift-defs; lift-program)
open import Compiler.Model.Graph.Sem.Clos5Iswim using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; table; ⟦_⟧ₚ; init)
open import Compiler.Model.Graph.Sem.Clos5IswimContinuous using (⟦⟧[]-monotone; Clos5-con; table-con)
open import Compiler.Model.Graph.Sem.Imp using (read; 𝒜s)
open import Compiler.Model.Graph.Sem.ImpK
  using (Store; _[_↦_]; 𝒜; 𝒮; frame; checked; Kont; halt; ⟦_⟧ᴷ[_]; ⟦_⟧ᴷₚ)
  renaming (table to tableᴷ)
open import Compiler.Model.Graph.Correctness.GlobalizeCorrect
  using (RRs; nthD-≃; app-≃; pair-≃; car-≃; cdr-≃; prim-≃)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (⋆-≃; 𝒯-≃; proj-≃; inl-≃; inr-≃; 𝒞-≃)
open import Compiler.Model.Graph.Correctness.RCOCorrect using (Λ-≃; RRs-refl; compile-mon-same)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import Compiler.Model.Graph.Correctness.CompilerCorrect using (Same; Same-trans; ≃→Same)
open import Compiler.Compile.Pipeline using (compile; compile-imp)
open import Compiler.Compile.RCO using (rco-program-mon)
open import Compiler.Model.Graph.Sem.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵢ)
import Compiler.Lang.ISWIM as ISWIM
open import NewEnv using (Env)
open import Primitives using (base-rep)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; _≟_; _<?_; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-mono-≤; +-suc; m≤m⊔n; m≤n⊔m; m≤m+n; m∸n≤m; ≮⇒≥; <-irrefl; <-≤-trans)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using () renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

module Compiler.Model.Graph.Correctness.LiftLocalsCorrectK where

{- Slots and stores ----------------------------------------------------------------}

read-at : ∀ {n σ y} → y < n → read n σ y ≡ σ y
read-at {n} {σ} {y} y<n with y <? n
... | yes _ = refl
... | no y≮n = ⊥-elim (y≮n y<n)

read-out : ∀ n σ → read n σ n ≡ init
read-out n σ with n <? n
... | yes n<n = ⊥-elim (<-irrefl refl n<n)
... | no _ = refl

upd-at : ∀ σ {X} x → (σ [ x ↦ X ]) x ≡ X
upd-at σ x with x ≟ x
... | yes _ = refl
... | no x≢x = ⊥-elim (x≢x refl)

upd-< : ∀ {σ X y d} → y < d → (σ [ d ↦ X ]) y ≃ σ y
upd-< {σ} {X} {y} {d} y<d with y ≟ d
... | yes refl = ⊥-elim (<-irrefl refl y<d)
... | no _ = ≃-refl

slot-< : ∀ {x d} → x < d → d ∸ suc x < d
slot-< {x} {suc d} _ = s≤s (m∸n≤m d x)

checked-at : ∀ {n x D} → x < n → checked n x D ≃ D
checked-at {n} {x} x<n with x <? n
... | yes _ = ≃-refl
... | no x≮n = ⊥-elim (x≮n x<n)

{- the frame is large enough for what lift assigns at depth d -}
fits : ∀ {d n} k → d + suc k ≤ n → suc d + k ≤ n
fits {d} {n} k H = subst (_≤ n) (+-suc d k) H

fits-< : ∀ {d n} k → suc d + k ≤ n → d < n
fits-< {d} k H = ≤-trans (s≤s (m≤m+n d k)) H

⊔ˡ : ∀ {d n} a b → d + (a ⊔ b) ≤ n → d + a ≤ n
⊔ˡ {d} a b H = ≤-trans (+-mono-≤ (≤-refl {d}) (m≤m⊔n a b)) H

⊔ʳ : ∀ {d n} a b → d + (a ⊔ b) ≤ n → d + b ≤ n
⊔ʳ {d} a b H = ≤-trans (+-mono-≤ (≤-refl {d}) (m≤n⊔m a b)) H

{- The invariant ---------------------------------------------------------------------}

{- at depth d, σ agrees with ρ: slot d ∸ (x + 1) means variable x -}
record Agree (d : ℕ) (σ : Store) (ρ : Env Value) : Set where
  constructor agree
  field at : ∀ x → x < d → σ (d ∸ suc x) ≃ ρ x
open Agree

{- the variables from d on are out of scope -}
Scope : ℕ → Env Value → Set
Scope d ρ = ∀ x → d ≤ x → ρ x ≃ init

{- under a binder: its value in slot d -}
agree-ext : ∀ {d σ ρ X} → Agree d σ ρ → Agree (suc d) (σ [ d ↦ X ]) (X • ρ)
agree-ext {d} {σ} A = agree λ { zero _ → ≃-reflexive (upd-at σ d)
  ; (suc x) (s≤s x<d) → ≃-trans (upd-< (slot-< x<d)) (at A x x<d) }

scope-ext : ∀ {d ρ X} → Scope d ρ → Scope (suc d) (X • ρ)
scope-ext O (suc x) (s≤s d≤x) = O x d≤x

{- back from under a binder: drop its slot -}
weak : ∀ {d σ ρ X} → Agree (suc d) σ (X • ρ) → Agree d σ ρ
weak A = agree λ x x<d → at A (suc x) (s≤s x<d)

{- Commuting with let and case --------------------------------------------------------}

MonoF : (𝒫 Value → 𝒫 Value) → Set₁
MonoF F = ∀ {X X'} → X ⊆ X' → F X ⊆ F X'

{- u is in F on a finite, nonempty part of P -}
Run : 𝒫 Value → (𝒫 Value → 𝒫 Value) → 𝒫 Value
Run P F u = Σ[ Y ∈ List Value ] Y ≢ [] × (mem Y ⊆ P × u ∈ F (mem Y))

{- finitely many such elements are all in F on one finite part of P -}
gather : ∀ {P F} → MonoF F → ∀ V → mem V ⊆ Run P F → V ≢ [] → Σ[ Y ∈ List Value ] Y ≢ [] × (mem Y ⊆ P × mem V ⊆ F (mem Y))
gather mF [] h ne = ⊥-elim (ne refl)
gather mF (v ∷ []) h _ with h v (here refl)
... | ⟨ Y , ⟨ neY , ⟨ Y⊆ , v∈ ⟩ ⟩ ⟩ = ⟨ Y , ⟨ neY , ⟨ Y⊆ , (λ { _ (here refl) → v∈ }) ⟩ ⟩ ⟩
gather {P} mF (v ∷ v' ∷ V) h _ with h v (here refl) | gather mF (v' ∷ V) (λ u u∈ → h u (there u∈)) (λ ())
... | ⟨ [] , ⟨ neY , _ ⟩ ⟩ | _ = ⊥-elim (neY refl)
... | ⟨ y ∷ Y , ⟨ _ , ⟨ Y⊆ , v∈ ⟩ ⟩ ⟩ | ⟨ Y' , ⟨ _ , ⟨ Y'⊆ , V⊆ ⟩ ⟩ ⟩ =
  ⟨ y ∷ Y ++ Y' , ⟨ (λ ()) , ⟨ P⊆ , (λ { _ (here refl) → mF (λ _ → ∈-++⁺ˡ) _ v∈
                                       ; u (there u∈) → mF (λ _ → ∈-++⁺ʳ (y ∷ Y)) u (V⊆ u u∈) }) ⟩ ⟩ ⟩
  where
  P⊆ : mem (y ∷ Y ++ Y') ⊆ P
  P⊆ u u∈ with ∈-++⁻ (y ∷ Y) u∈
  ... | inj₁ i = Y⊆ u i
  ... | inj₂ i = Y'⊆ u i

{- ⋆ ⟨ Λ G , - ⟩ of such elements, for a consistent P: they come from F
   on one consistent finite part of P -}
join : ∀ {P F G w} → Con P → MonoF F → w ∈ ⋆ ⟨ Λ ⟨ G , ptt ⟩ , ⟨ Run P F , ptt ⟩ ⟩
  → Σ[ y ∈ Value ] Σ[ Y ∈ List Value ]
      mem (y ∷ Y) ⊆ P × (w ∈ ⋆ ⟨ Λ ⟨ G , ptt ⟩ , ⟨ F (mem (y ∷ Y)) , ptt ⟩ ⟩ × (y ∷ Y) ≈ (y ∷ Y))
join {P} cP mF ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ with gather mF V V⊆ neV
... | ⟨ [] , ⟨ neY , _ ⟩ ⟩ = ⊥-elim (neY refl)
... | ⟨ y ∷ Y , ⟨ _ , ⟨ Y⊆ , V⊆' ⟩ ⟩ ⟩ =
  ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ ⟨ V , ⟨ w∈ , ⟨ V⊆' , neV ⟩ ⟩ ⟩ , Con⇒≈ (y ∷ Y) cP Y⊆ ⟩ ⟩ ⟩ ⟩

{- the meaning of the enclosing lets, given the value -}
K⟨_⟩ : Maybe (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
K⟨ nothing ⟩ D = D
K⟨ just G ⟩ D = ⋆ ⟨ Λ ⟨ G , ptt ⟩ , ⟨ D , ptt ⟩ ⟩

K-≃ : ∀ k {D D'} → D ≃ D' → K⟨ k ⟩ D ≃ K⟨ k ⟩ D'
K-≃ nothing eq = eq
K-≃ (just G) eq = ⋆-≃ {Λ ⟨ G , ptt ⟩} {Λ ⟨ G , ptt ⟩} ≃-refl eq

let-law : ∀ k {D F} → Con D → MonoF F
  → K⟨ k ⟩ (⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩) ≃ ⋆ ⟨ Λ ⟨ (λ X → K⟨ k ⟩ (F X)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
let-law nothing cD mF = ≃-refl
let-law (just G) {D} {F} cD mF = ⟨ L , R ⟩
  where
  L : K⟨ just G ⟩ (⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩) ⊆ ⋆ ⟨ Λ ⟨ (λ X → K⟨ just G ⟩ (F X)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
  L w ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ with join {D} {F} {G} cD mF ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → run (V⊆ u u∈)) , neV ⟩ ⟩ ⟩
    where
    run : ∀ {u} → u ∈ ⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ → u ∈ Run D F
    run ⟨ Y , ⟨ ⟨ u∈ , ⟨ neY , _ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ = ⟨ Y , ⟨ neY , ⟨ Y⊆ , u∈ ⟩ ⟩ ⟩
  ... | ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , cY ⟩ ⟩ ⟩ ⟩ = ⟨ y ∷ Y , ⟨ ⟨ w∈' , ⟨ (λ ()) , cY ⟩ ⟩ , ⟨ Y⊆ , (λ ()) ⟩ ⟩ ⟩
  R : ⋆ ⟨ Λ ⟨ (λ X → K⟨ just G ⟩ (F X)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩ ⊆ K⟨ just G ⟩ (⋆ ⟨ Λ ⟨ F , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
  R w ⟨ Y , ⟨ ⟨ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , ⟨ neY , cY ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ =
    ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → ⟨ Y , ⟨ ⟨ V⊆ u u∈ , ⟨ neY , cY ⟩ ⟩ , ⟨ Y⊆ , neY ⟩ ⟩ ⟩) , neV ⟩ ⟩ ⟩

case-law : ∀ k {A F₁ F₂} → Con A → MonoF F₁ → MonoF F₂
  → K⟨ k ⟩ (𝒞 ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) ≃ 𝒞 ⟨ A , ⟨ (λ X → K⟨ k ⟩ (F₁ X)) , ⟨ (λ X → K⟨ k ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩
case-law nothing cA m₁ m₂ = ≃-refl
case-law (just G) {A} {F₁} {F₂} cA m₁ m₂ = ⟨ L , R ⟩
  where
  L : K⟨ just G ⟩ (𝒞 ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) ⊆ 𝒞 ⟨ A , ⟨ (λ X → K⟨ just G ⟩ (F₁ X)) , ⟨ (λ X → K⟨ just G ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩
  L w ⟨ [] , ⟨ _ , ⟨ _ , neV ⟩ ⟩ ⟩ = ⊥-elim (neV refl)
  L w ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ with V⊆ u₀ (here refl)
  ... | inj₁ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩ =
    inj₁ (join {F = F₁} {G} (λ a b → cA _ _) m₁ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ lefts , neV ⟩ ⟩ ⟩)
    where
    lefts : mem (u₀ ∷ V) ⊆ Run (λ d → left d ∈ A) F₁
    lefts u u∈ with V⊆ u u∈
    ... | inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ u∈' , _ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V' , ⟨ (λ ()) , ⟨ all , u∈' ⟩ ⟩ ⟩
    ... | inj₂ ⟨ v , ⟨ V' , ⟨ all , _ ⟩ ⟩ ⟩ = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) (all v (here refl)))
  ... | inj₂ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩ =
    inj₂ (join {F = F₂} {G} (λ a b → cA _ _) m₂ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ rights , neV ⟩ ⟩ ⟩)
    where
    rights : mem (u₀ ∷ V) ⊆ Run (λ d → right d ∈ A) F₂
    rights u u∈ with V⊆ u u∈
    ... | inj₂ ⟨ v , ⟨ V' , ⟨ all , ⟨ u∈' , _ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V' , ⟨ (λ ()) , ⟨ all , u∈' ⟩ ⟩ ⟩
    ... | inj₁ ⟨ v , ⟨ V' , ⟨ all , _ ⟩ ⟩ ⟩ = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) (all v (here refl)))
  R : 𝒞 ⟨ A , ⟨ (λ X → K⟨ just G ⟩ (F₁ X)) , ⟨ (λ X → K⟨ just G ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩ ⊆ K⟨ just G ⟩ (𝒞 ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ V⊆ u u∈ , c ⟩ ⟩ ⟩ ⟩) , neV ⟩ ⟩ ⟩
  R w (inj₂ ⟨ v , ⟨ V' , ⟨ all , ⟨ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₂ ⟨ v , ⟨ V' , ⟨ all , ⟨ V⊆ u u∈ , c ⟩ ⟩ ⟩ ⟩) , neV ⟩ ⟩ ⟩

{- The pass preserves meanings ----------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TC : ∀ k → Con (T' k)) where

  atom-≃ : ∀ {n d h σ ρ M} (a : Atom M) → d + h ≤ n → Scope d ρ → Agree d σ ρ
    → 𝒜 T n σ (lift-atom n d a) ≃ ⟦ M ⟧[ T' ] ρ
  atom-≃ {n} {d} {h} {σ} (var x) H O A with x <? d
  ... | yes x<d = ≃-trans (≃-reflexive (read-at (<-≤-trans (slot-< x<d) (≤-trans (m≤m+n d h) H)))) (at A x x<d)
  ... | no x≮d = ≃-trans (≃-reflexive (read-out n σ)) (≃-sym (O x (≮⇒≥ x≮d)))
  atom-≃ (lit B k) _ _ _ = ≃-refl
  atom-≃ (ref k) _ _ _ = TT k

  {- the atoms of a tuple: what holds of their meanings in Clos5 holds in Imp -}
  atoms-≃ : ∀ {n d h σ ρ k} {Ms : Args (replicate k ■)} (as : Atoms Ms) → d + h ≤ n → Scope d ρ → Agree d σ ρ
    → (Q : ∀ m → Results (𝒫 Value) (replicate m ■) → Set)
    → (∀ {m Ds Es} → RRs _ Ds Es → Q m Es → Q m Ds)
    → Q k (⟦ Ms ⟧₊[ T' ] ρ) → Q (length (lift-atoms n d as)) (𝒜s T n σ (lift-atoms n d as))
  atoms-≃ [] H O A Q resp q = q
  atoms-≃ (a ∷ as) H O A Q resp q =
    atoms-≃ as H O A (λ m Ds → Q (suc m) ⟨ _ , Ds ⟩) (λ eq → resp ⟨ up ≃-refl , eq ⟩)
      (resp ⟨ up (atom-≃ a H O A) , RRs-refl _ ⟩ q)

  mono-• : ∀ {ρ} M → MonoF (λ X → ⟦ M ⟧[ T' ] (X • ρ))
  mono-• M X⊆ = ⟦⟧[]-monotone T' M λ { zero → X⊆ ; (suc x) → λ _ w∈ → w∈ }

  {- lift at depth d, then a continuation that means K, given a store
     that agrees with ρ -}
  lift-sem : ∀ {M} (m : Mon M) {n d σ ρ} k {κ : Kont} → d + height m ≤ n → Scope d ρ → Agree d σ ρ → Con-env ρ
    → (∀ D σ' → Agree d σ' ρ → κ D σ' ≃ K⟨ k ⟩ D)
    → ⟦ lift n d m ⟧ᴷ[ T ] n σ κ ≃ K⟨ k ⟩ (⟦ M ⟧[ T' ] ρ)
  lift-sem (atom a) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (atom-≃ a H O A))
  lift-sem (app (a ∷ b ∷ c ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (app-≃ ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ⟨ up (atom-≃ c H O A) , ptt ⟩ ⟩ ⟩))
  lift-sem (pair (a ∷ b ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (pair-≃ ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ptt ⟩ ⟩))
  lift-sem (fst (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (car-≃ ⟨ up (atom-≃ a H O A) , ptt ⟩))
  lift-sem (snd (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (cdr-≃ ⟨ up (atom-≃ a H O A) , ptt ⟩))
  lift-sem (tuple {k'} {Ms} as) {ρ = ρ} k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (atoms-≃ as H O A (λ m Ds → 𝒯 m Ds ≃ 𝒯 k' (⟦ Ms ⟧₊[ T' ] ρ))
                 (λ {m} eq q → ≃-trans (𝒯-≃ m (nthD-≃ _ _ eq)) q) ≃-refl))
  lift-sem (get {i = i} (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (proj-≃ i (atom-≃ a H O A)))
  lift-sem (inl (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (inl-≃ (atom-≃ a H O A)))
  lift-sem (inr (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (inr-≃ (atom-≃ a H O A)))
  lift-sem (prim {p} (a ∷ b ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (prim-≃ p ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ptt ⟩ ⟩))
  lift-sem (case {L} {M₁} {M₂} a m₁ m₂) {n} {d} {σ} {ρ} k {κ} H O A cρ κ≃ =
    ≃-trans (checked-at (fits-< _ (fits {d} _ H)))
    (≃-trans (𝒞-≃ {F = λ X → ⟦ lift n (suc d) m₁ ⟧ᴷ[ T ] n (σ [ d ↦ X ]) κ} {λ X → K⟨ k ⟩ (⟦ M₁ ⟧[ T' ] (X • ρ))}
                   {λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ [ d ↦ X ]) κ} {λ X → K⟨ k ⟩ (⟦ M₂ ⟧[ T' ] (X • ρ))}
                   (atom-≃ a H O A)
                   (λ v V cV → lift-sem m₁ k (⊔ˡ (height m₁) _ H') (scope-ext O) (agree-ext A)
                                 (Con-• (≈⇒Con cV) cρ) (λ D σ' A' → κ≃ D σ' (weak A')))
                   (λ v V cV → lift-sem m₂ k (⊔ʳ _ (height m₂) H') (scope-ext O) (agree-ext A)
                                 (Con-• (≈⇒Con cV) cρ) (λ D σ' A' → κ≃ D σ' (weak A'))))
             (≃-sym (case-law k {F₁ = λ X → ⟦ M₁ ⟧[ T' ] (X • ρ)} {λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)}
                       (Clos5-con T' TC L cρ) (mono-• M₁) (mono-• M₂))))
    where H' = fits {d} (height m₁ ⊔ height m₂) H
  lift-sem (let′ {M₁} {M₂} m₁ m₂) {n} {d} {σ} {ρ} k {κ} H O A cρ κ≃ =
    ≃-trans (lift-sem m₁ (just G) (⊔ˡ {d} (height m₁) _ H) O A cρ κ₁≃)
            (≃-sym (let-law k {F = λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)} (Clos5-con T' TC M₁ cρ) (mono-• M₂)))
    where
    H₂ = fits {d} _ (⊔ʳ (height m₁) _ H)
    G = λ X → K⟨ k ⟩ (⟦ M₂ ⟧[ T' ] (X • ρ))
    κ₁≃ : ∀ D σ' → Agree d σ' ρ
      → checked n d (⋆ ⟨ Λ ⟨ (λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ' [ d ↦ X ]) κ) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
        ≃ K⟨ just G ⟩ D
    κ₁≃ D σ' A' = ≃-trans (checked-at (fits-< _ H₂))
      (⋆-≃ (Λ-≃ {λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ' [ d ↦ X ]) κ} {G} λ V _ cV → lift-sem m₂ k H₂ (scope-ext O) (agree-ext A') (Con-• (≈⇒Con cV) cρ)
                              (λ D' σ'' A'' → κ≃ D' σ'' (weak A''))) ≃-refl)

{- Programs ---------------------------------------------------------------------}

{- a function body: the free variables in slot 0, the argument in slot 1 -}
agree-frame : ∀ X Y → Agree 2 (frame X Y) (Y • X • (λ _ → init))
agree-frame X Y = agree λ { zero _ → ≃-refl ; (suc zero) _ → ≃-refl ; (suc (suc x)) (s≤s (s≤s ())) }

scope-frame : ∀ X Y → Scope 2 (Y • X • (λ _ → init))
scope-frame X Y = λ { (suc zero) (s≤s ()) ; (suc (suc x)) _ → ≃-refl }

length-lift-defs : ∀ {ds} (ms : All Mon ds) → length (lift-defs ms) ≡ length ds
length-lift-defs [] = refl
length-lift-defs (m ∷ ms) rewrite length-lift-defs ms = refl

table-lift : ∀ {ds} (ms : All Mon ds) k → tableᴷ (lift-defs ms) k ≃ table ds k
table-lift [] k = ≃-refl
table-lift {N ∷ Ns} (m ∷ ms) k with k ≟ length (lift-defs ms) | k ≟ length Ns
... | yes _ | yes _ =
  Λ-≃ λ X _ cX → Λ-≃ λ Y _ cY → lift-sem (table-lift ms) (table-con Ns) m nothing ≤-refl
    (scope-frame (mem X) (mem Y)) (agree-frame (mem X) (mem Y))
    (Con-• (≈⇒Con cY) (Con-• (≈⇒Con cX) (λ _ → Con-⌈⌉ ω))) (λ _ _ _ → ≃-refl)
... | no _ | no _ = table-lift ms k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-lift-defs ms)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-lift-defs ms))))

lift-program-correct : ∀ P (mp : MonProgram P) → ⟦ lift-program P mp ⟧ᴷₚ ≃ ⟦ P ⟧ₚ
lift-program-correct (program ds M) ⟨ ms , m ⟩ =
  lift-sem (table-lift ms) (table-con ds) m nothing ≤-refl (λ x _ → ≃-refl) (agree λ x ())
    (λ _ → Con-⌈⌉ ω) (λ _ _ _ → ≃-refl)

{- The whole compiler, into Imp ------------------------------------------------

  compile-imp = lift-program ∘ compile-mon (Compile/Pipeline.agda): the
  result produces the same constants as the ISWIM program, and produces
  something exactly when it does. -}

compile-imp-same : ∀ (M : ISWIM.AST) → Same (⟦ M ⟧ᵢ ρ₀) ⟦ compile-imp M ⟧ᴷₚ
compile-imp-same M = Same-trans (compile-mon-same M)
  (≃→Same (≃-sym (lift-program-correct _ (rco-program-mon (compile M)))))

compile-imp-correct-const : ∀ (M : ISWIM.AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ᵢ ρ₀ → const c ∈ ⟦ compile-imp M ⟧ᴷₚ)
  × (const c ∈ ⟦ compile-imp M ⟧ᴷₚ → const c ∈ ⟦ M ⟧ᵢ ρ₀)
compile-imp-correct-const M = proj₁ (compile-imp-same M)

compile-imp-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ᵢ ρ₀) → nonempty ⟦ compile-imp M ⟧ᴷₚ)
  × (nonempty ⟦ compile-imp M ⟧ᴷₚ → nonempty (⟦ M ⟧ᵢ ρ₀))
compile-imp-correct-nonempty M = proj₂ (compile-imp-same M)
