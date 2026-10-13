{-

  Correctness of lift locals (monadic Clos5 → Imp,
  Compiler/LiftLocals.agda) in the graph model with errors, against the
  continuation-passing semantics of Imp (Semantics/GraphErr/ImpK.agda):

    lift-locals-correct : ⟦ lift-program P mp ⟧ᴷₚ ≃ ⟦ P ⟧₅

  The proof is that of the graph model
  (proof/Correctness/Graph/{LiftLocalsCommon,LiftLocalsCorrectK}.agda):
  at depth d the store agrees with the environment (Agree), the variables
  from d on are out of scope (Scope), and lift n d m run with a
  continuation that means K, given a store that agrees, means K of the
  meaning of m (lift-sem). What changes with errors:

  * K is a strict let (letᵉ), and it commutes with letᵉ and 𝒞ᵉ
    (let-law, case-law) also on errors: an error of the right-hand side
    of a let, or of the scrutinee of a case, is passed on by both sides,
    and an error of a body or branch is a result of both. The finite
    parts that a let or case binds hold no ω, and their join holds none
    (gather).
  * Every assignment that lift makes is within the frame, so the frame
    checks (checkedᵉ) never err; a variable out of scope is a slot beyond
    the frame, which errs (init), as it does in Clos5.
  * Code bodies run in frames of max(2, 2 + height) slots, which is
    2 + height.

  No precondition: the pass is correct for every monadic program.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig using (Results; RRs; RRs-refl)
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase using (nthD-≃)
open import proof.Framework.GraphModel.ErrorOps
open import proof.Semantics.GraphErr.Prim using (primᵉ-≃)
open import Language.Clos5 using (program; Args)
import Language.Clos5 as C5
open import Language.Mon
import Language.Imp as I
import Language.ISWIM as ISWIM
open import Compiler.LiftLocals using (lift; height; lift-atom; lift-atoms; lift-defs; lift-program)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Pipeline using (compile; compile-mon; compile-imp)
open import Compiler.RCO using (rco-program-mon)
open import proof.Semantics.GraphErr.Clos5
  using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; table; ⟦_⟧ₚ; ⟦⟧[]-monotone; Clos5ᵉ-con; table-con)
  renaming (init to init₅)
open import Semantics.GraphErr.ImpK
  using (Store; read; _[_↦_]; checkedᵉ; 𝒜; 𝒜s; frame; Kont; ⟦_⟧ᴷ[_]; ⟦_⟧ᴷₚ; init)
  renaming (table to tableᴷ)
open import proof.Framework.GraphModel.Env using (Env)

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
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using () renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

module proof.Correctness.GraphErr.LiftLocalsCorrect where

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

checked-at : ∀ {n x D E} → x < n → checkedᵉ n x D E ≃ E
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

record Agree (d : ℕ) (σ : Store) (ρ : Env Value) : Set where
  constructor agree
  field at : ∀ x → x < d → σ (d ∸ suc x) ≃ ρ x
open Agree public

Scope : ℕ → Env Value → Set
Scope d ρ = ∀ x → d ≤ x → ρ x ≃ init

agree-ext : ∀ {d σ ρ X} → Agree d σ ρ → Agree (suc d) (σ [ d ↦ X ]) (X • ρ)
agree-ext {d} {σ} A = agree λ { zero _ → ≃-reflexive (upd-at σ d)
  ; (suc x) (s≤s x<d) → ≃-trans (upd-< (slot-< x<d)) (at A x x<d) }

scope-ext : ∀ {d ρ X} → Scope d ρ → Scope (suc d) (X • ρ)
scope-ext O (suc x) (s≤s d≤x) = O x d≤x

weak : ∀ {d σ ρ X} → Agree (suc d) σ (X • ρ) → Agree d σ ρ
weak A = agree λ x x<d → at A (suc x) (s≤s x<d)

agree-frame : ∀ X Y → Agree 2 (frame X Y) (Y • X • (λ _ → init))
agree-frame X Y = agree λ { zero _ → ≃-refl ; (suc zero) _ → ≃-refl ; (suc (suc x)) (s≤s (s≤s ())) }

scope-frame : ∀ X Y → Scope 2 (Y • X • (λ _ → init))
scope-frame X Y = λ { (suc zero) (s≤s ()) ; (suc (suc x)) _ → ≃-refl }

length-lift-defs : ∀ {ds} (ms : All Mon ds) → length (lift-defs ms) ≡ length ds
length-lift-defs [] = refl
length-lift-defs (m ∷ ms) rewrite length-lift-defs ms = refl

{- Atoms ----------------------------------------------------------------------------}

module AtomsSame {T T' : Table} (TT : ∀ k → T k ≃ T' k) where

  atom-≃ : ∀ {n d h σ ρ M} (a : Atom M) → d + h ≤ n → Scope d ρ → Agree d σ ρ
    → 𝒜 T n σ (lift-atom n d a) ≃ ⟦ M ⟧[ T' ] ρ
  atom-≃ {n} {d} {h} {σ} (var x) H O A with x <? d
  ... | yes x<d = ≃-trans (≃-reflexive (read-at (<-≤-trans (slot-< x<d) (≤-trans (m≤m+n d h) H)))) (at A x x<d)
  ... | no x≮d = ≃-trans (≃-reflexive (read-out n σ)) (≃-sym (O x (≮⇒≥ x≮d)))
  atom-≃ (lit B k) _ _ _ = ≃-refl
  atom-≃ (ref k) _ _ _ = TT k

  atoms-≃ : ∀ {n d h σ ρ k} {Ms : Args (replicate k ■)} (as : Atoms Ms) → d + h ≤ n → Scope d ρ → Agree d σ ρ
    → (Q : ∀ m → Results (𝒫 Value) (replicate m ■) → Set)
    → (∀ {m Ds Es} → RRs _ Ds Es → Q m Es → Q m Ds)
    → Q k (⟦ Ms ⟧₊[ T' ] ρ) → Q (length (lift-atoms n d as)) (𝒜s T n σ (lift-atoms n d as))
  atoms-≃ [] H O A Q resp q = q
  atoms-≃ (a ∷ as) H O A Q resp q =
    atoms-≃ as H O A (λ m Ds → Q (suc m) ⟨ _ , Ds ⟩) (λ eq → resp ⟨ up ≃-refl , eq ⟩)
      (resp ⟨ up (atom-≃ a H O A) , RRs-refl _ ⟩ q)

{- Commuting with let and case --------------------------------------------------------}

{- GENERIC (laws of letᵉ and 𝒞ᵉ) -}

MonoF : (𝒫 Value → 𝒫 Value) → Set₁
MonoF F = ∀ {X X'} → X ⊆ X' → F X ⊆ F X'

{- u is in F on a finite, nonempty part of P without ω -}
Run : 𝒫 Value → (𝒫 Value → 𝒫 Value) → 𝒫 Value
Run P F u = Σ[ Y ∈ List Value ] Y ≢ [] × NoErr Y × (mem Y ⊆ P × u ∈ F (mem Y))

NoErr-++ : ∀ Y Y' → NoErr Y → NoErr Y' → NoErr (Y ++ Y')
NoErr-++ Y Y' n n' ω∈ with ∈-++⁻ Y ω∈
... | inj₁ i = n i
... | inj₂ i = n' i

{- finitely many such elements are all in F on one finite part of P -}
gather : ∀ {P F} → MonoF F → ∀ V → mem V ⊆ Run P F → V ≢ []
  → Σ[ Y ∈ List Value ] Y ≢ [] × NoErr Y × (mem Y ⊆ P × mem V ⊆ F (mem Y))
gather mF [] h ne = ⊥-elim (ne refl)
gather mF (v ∷ []) h _ with h v (here refl)
... | ⟨ Y , ⟨ neY , ⟨ nY , ⟨ Y⊆ , v∈ ⟩ ⟩ ⟩ ⟩ = ⟨ Y , ⟨ neY , ⟨ nY , ⟨ Y⊆ , (λ { _ (here refl) → v∈ }) ⟩ ⟩ ⟩ ⟩
gather {P} mF (v ∷ v' ∷ V) h _ with h v (here refl) | gather mF (v' ∷ V) (λ u u∈ → h u (there u∈)) (λ ())
... | ⟨ [] , ⟨ neY , _ ⟩ ⟩ | _ = ⊥-elim (neY refl)
... | ⟨ y ∷ Y , ⟨ _ , ⟨ nY , ⟨ Y⊆ , v∈ ⟩ ⟩ ⟩ ⟩ | ⟨ Y' , ⟨ _ , ⟨ nY' , ⟨ Y'⊆ , V⊆ ⟩ ⟩ ⟩ ⟩ =
  ⟨ y ∷ Y ++ Y' , ⟨ (λ ()) , ⟨ NoErr-++ (y ∷ Y) Y' nY nY'
  , ⟨ P⊆ , (λ { _ (here refl) → mF (λ _ → ∈-++⁺ˡ) _ v∈
              ; u (there u∈) → mF (λ _ → ∈-++⁺ʳ (y ∷ Y)) u (V⊆ u u∈) }) ⟩ ⟩ ⟩ ⟩
  where
  P⊆ : mem (y ∷ Y ++ Y') ⊆ P
  P⊆ u u∈ with ∈-++⁻ (y ∷ Y) u∈
  ... | inj₁ i = Y⊆ u i
  ... | inj₂ i = Y'⊆ u i

{- letᵉ ⟨ -, G ⟩ of such elements, for a consistent P: they come from F
   on one consistent finite part of P without ω -}
join : ∀ {P F G w} → Con P → MonoF F
  → (Σ[ V ∈ List Value ] (V ↦ w ∈ Λᵉ ⟨ G , ptt ⟩) × mem V ⊆ Run P F × V ≢ [] × NoErr V)
  → Σ[ y ∈ Value ] Σ[ Y ∈ List Value ]
      mem (y ∷ Y) ⊆ P × (w ∈ letᵉ ⟨ F (mem (y ∷ Y)) , ⟨ G , ptt ⟩ ⟩ × (y ∷ Y) ≈ (y ∷ Y) × NoErr (y ∷ Y))
join {P} cP mF ⟨ V , ⟨ w∈ , ⟨ V⊆ , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩ with gather mF V V⊆ neV
... | ⟨ [] , ⟨ neY , _ ⟩ ⟩ = ⊥-elim (neY refl)
... | ⟨ y ∷ Y , ⟨ _ , ⟨ nY , ⟨ Y⊆ , V⊆' ⟩ ⟩ ⟩ ⟩ =
  ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆' , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩ , ⟨ Con⇒≈ (y ∷ Y) cP Y⊆ , nY ⟩ ⟩ ⟩ ⟩ ⟩

{- the meaning of the enclosing lets, given the value -}
K⟨_⟩ : Maybe (𝒫 Value → 𝒫 Value) → 𝒫 Value → 𝒫 Value
K⟨ nothing ⟩ D = D
K⟨ just G ⟩ D = letᵉ ⟨ D , ⟨ G , ptt ⟩ ⟩

K-≃ : ∀ k {D D'} → D ≃ D' → K⟨ k ⟩ D ≃ K⟨ k ⟩ D'
K-≃ nothing eq = eq
K-≃ (just G) eq = ⋆ᵉ-≃ {Λᵉ ⟨ G , ptt ⟩} {Λᵉ ⟨ G , ptt ⟩} ≃-refl eq

{- an error of the operand of a let -}
let-err : ∀ {D G} → ω ∈ D → ω ∈ letᵉ ⟨ D , ⟨ G , ptt ⟩ ⟩
let-err ω∈ = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , ω∈ ⟩) ⟩

let-law : ∀ k {D F} → Con D → MonoF F
  → K⟨ k ⟩ (letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩) ≃ letᵉ ⟨ D , ⟨ (λ X → K⟨ k ⟩ (F X)) , ptt ⟩ ⟩
let-law nothing cD mF = ≃-refl
let-law (just G) {D} {F} cD mF = ⟨ L , R ⟩
  where
  run : ∀ {u} → u ∈ letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩ → u ≢ ω → u ∈ Run D F
  run (inj₁ ⟨ Y , ⟨ ⟨ u∈ , ⟨ neY , ⟨ _ , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩) _ = ⟨ Y , ⟨ neY , ⟨ nY , ⟨ Y⊆ , u∈ ⟩ ⟩ ⟩ ⟩
  run (inj₂ ⟨ refl , _ ⟩) u≢ = ⊥-elim (u≢ refl)
  L : K⟨ just G ⟩ (letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩) ⊆ letᵉ ⟨ D , ⟨ (λ X → K⟨ just G ⟩ (F X)) , ptt ⟩ ⟩
  L w (inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆ , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩)
      with join {D} {F} {G} cD mF ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → run (V⊆ u u∈) (λ { refl → nV u∈ })) , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩
  ... | ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩ =
    inj₁ ⟨ y ∷ Y , ⟨ ⟨ w∈' , ⟨ (λ ()) , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , ⟨ (λ ()) , nY ⟩ ⟩ ⟩ ⟩
  L w (inj₂ ⟨ refl , inj₁ () ⟩)
  L w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈D ⟩) ⟩ ⟩) ⟩) = let-err ω∈D
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ ⟨ refl , inj₁ () ⟩ ⟩) ⟩)
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ ⟩) ⟩) =
    ⊥-elim (nf (Λᵉ-fun d d∈))
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₁ ⟨ Y , ⟨ ⟨ ω∈F , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩ ⟩) ⟩) =
    inj₁ ⟨ Y , ⟨ ⟨ let-err ω∈F , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , ⟨ neY , nY ⟩ ⟩ ⟩ ⟩
  R : letᵉ ⟨ D , ⟨ (λ X → K⟨ just G ⟩ (F X)) , ptt ⟩ ⟩ ⊆ K⟨ just G ⟩ (letᵉ ⟨ D , ⟨ F , ptt ⟩ ⟩)
  R w (inj₁ ⟨ Y , ⟨ ⟨ inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neVn ⟩ ⟩ ⟩ , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩) =
    inj₁ ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₁ ⟨ Y , ⟨ ⟨ V⊆ u u∈ , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , ⟨ neY , nY ⟩ ⟩ ⟩ ⟩) , neVn ⟩ ⟩ ⟩
  R w (inj₁ ⟨ Y , ⟨ ⟨ inj₂ ⟨ refl , inj₁ () ⟩ , _ ⟩ , _ ⟩ ⟩)
  R w (inj₁ ⟨ Y , ⟨ ⟨ inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ , _ ⟩ , _ ⟩ ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  R w (inj₁ ⟨ Y , ⟨ ⟨ inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈F ⟩) ⟩ , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , _ ⟩ ⟩ ⟩) =
    let-err (inj₁ ⟨ Y , ⟨ ⟨ ω∈F , ⟨ neY , ⟨ cY , nY ⟩ ⟩ ⟩ , ⟨ Y⊆ , ⟨ neY , nY ⟩ ⟩ ⟩ ⟩)
  R w (inj₂ ⟨ refl , inj₁ () ⟩)
  R w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  R w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈D ⟩) ⟩) = let-err (let-err ω∈D)

case-law : ∀ k {A F₁ F₂} → Con A → MonoF F₁ → MonoF F₂
  → K⟨ k ⟩ (𝒞ᵉ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) ≃ 𝒞ᵉ ⟨ A , ⟨ (λ X → K⟨ k ⟩ (F₁ X)) , ⟨ (λ X → K⟨ k ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩
case-law nothing cA m₁ m₂ = ≃-refl
case-law (just G) {A} {F₁} {F₂} cA m₁ m₂ = ⟨ L , R ⟩
  where
  C = 𝒞ᵉ ⟨ A , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩
  C' = 𝒞ᵉ ⟨ A , ⟨ (λ X → K⟨ just G ⟩ (F₁ X)) , ⟨ (λ X → K⟨ just G ⟩ (F₂ X)) , ptt ⟩ ⟩ ⟩
  L : K⟨ just G ⟩ C ⊆ C'
  L w (inj₁ ⟨ [] , ⟨ _ , ⟨ _ , ⟨ neV , _ ⟩ ⟩ ⟩ ⟩) = ⊥-elim (neV refl)
  L w (inj₁ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ V⊆ , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩) with V⊆ u₀ (here refl)
  ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim (nV (here refl))
  ... | inj₁ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩ with join {F = F₁} {G} (λ a b → cA _ _) m₁ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ lefts , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩
    where
    lefts : mem (u₀ ∷ V) ⊆ Run (λ d → left d ∈ A) F₁
    lefts u u∈ with V⊆ u u∈
    ... | inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ u∈' , ⟨ _ , n ⟩ ⟩ ⟩ ⟩ ⟩ = ⟨ v ∷ V' , ⟨ (λ ()) , ⟨ n , ⟨ all , u∈' ⟩ ⟩ ⟩ ⟩
    ... | inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , _ ⟩ ⟩ ⟩) = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) (all v (here refl)))
    ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim (nV u∈)
  ... | ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩ = inj₁ ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩
  L w (inj₁ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ V⊆ , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩) | inj₂ (inj₁ ⟨ v₀ , ⟨ _ , ⟨ all₀ , _ ⟩ ⟩ ⟩)
      with join {F = F₂} {G} (λ a b → cA _ _) m₂ ⟨ u₀ ∷ V , ⟨ w∈ , ⟨ rights , ⟨ neV , nV ⟩ ⟩ ⟩ ⟩
    where
    rights : mem (u₀ ∷ V) ⊆ Run (λ d → right d ∈ A) F₂
    rights u u∈ with V⊆ u u∈
    ... | inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ u∈' , ⟨ _ , n ⟩ ⟩ ⟩ ⟩ ⟩) = ⟨ v ∷ V' , ⟨ (λ ()) , ⟨ n , ⟨ all , u∈' ⟩ ⟩ ⟩ ⟩
    ... | inj₁ ⟨ v , ⟨ V' , ⟨ all , _ ⟩ ⟩ ⟩ = ⊥-elim (cA _ _ (all₀ v₀ (here refl)) (all v (here refl)))
    ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = ⊥-elim (nV u∈)
  ... | ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩ = inj₂ (inj₁ ⟨ y , ⟨ Y , ⟨ Y⊆ , ⟨ w∈' , ⟨ cY , nY ⟩ ⟩ ⟩ ⟩ ⟩)
  L w (inj₂ ⟨ refl , inj₁ () ⟩)
  L w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ ω∈ , cn ⟩ ⟩ ⟩ ⟩ ⟩) ⟩) =
    inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ let-err ω∈ , cn ⟩ ⟩ ⟩ ⟩
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ ω∈ , cn ⟩ ⟩ ⟩ ⟩) ⟩) ⟩) =
    inj₂ (inj₁ ⟨ v , ⟨ V , ⟨ all , ⟨ let-err ω∈ , cn ⟩ ⟩ ⟩ ⟩)
  L w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , inj₂ (inj₂ ⟨ refl , e ⟩) ⟩) ⟩) = inj₂ (inj₂ ⟨ refl , e ⟩)
  R : C' ⊆ K⟨ just G ⟩ C
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neVn ⟩ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    inj₁ ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ V⊆ u u∈ , c ⟩ ⟩ ⟩ ⟩) , neVn ⟩ ⟩ ⟩
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₁ () ⟩ , c ⟩ ⟩ ⟩ ⟩)
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    ⊥-elim (nf (Λᵉ-fun d d∈))
  R w (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩ , c ⟩ ⟩ ⟩ ⟩) =
    let-err (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ ω∈ , c ⟩ ⟩ ⟩ ⟩)
  R w (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₁ ⟨ V , ⟨ w∈ , ⟨ V⊆ , neVn ⟩ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩)) =
    inj₁ ⟨ V , ⟨ w∈ , ⟨ (λ u u∈ → inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ V⊆ u u∈ , c ⟩ ⟩ ⟩ ⟩)) , neVn ⟩ ⟩ ⟩
  R w (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₁ () ⟩ , c ⟩ ⟩ ⟩ ⟩))
  R w (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ , c ⟩ ⟩ ⟩ ⟩)) =
    ⊥-elim (nf (Λᵉ-fun d d∈))
  R w (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩ , c ⟩ ⟩ ⟩ ⟩)) =
    let-err (inj₂ (inj₁ ⟨ v , ⟨ V' , ⟨ all , ⟨ ω∈ , c ⟩ ⟩ ⟩ ⟩))
  R w (inj₂ (inj₂ ⟨ refl , e ⟩)) = let-err (inj₂ (inj₂ ⟨ refl , e ⟩))

{- The pass preserves meanings ----------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) (TC : ∀ k → Con (T' k)) where

  open AtomsSame TT

  mono-• : ∀ {ρ} M → MonoF (λ X → ⟦ M ⟧[ T' ] (X • ρ))
  mono-• M X⊆ = ⟦⟧[]-monotone T' M λ { zero → X⊆ ; (suc x) → λ _ w∈ → w∈ }

  lift-sem : ∀ {M} (m : Mon M) {n d σ ρ} k {κ : Kont} → d + height m ≤ n → Scope d ρ → Agree d σ ρ → Con-env ρ
    → (∀ D σ' → Agree d σ' ρ → κ D σ' ≃ K⟨ k ⟩ D)
    → ⟦ lift n d m ⟧ᴷ[ T ] n σ κ ≃ K⟨ k ⟩ (⟦ M ⟧[ T' ] ρ)
  lift-sem (atom a) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (atom-≃ a H O A))
  lift-sem (app (a ∷ b ∷ c ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (callᵉ-≃ (atom-≃ a H O A) (atom-≃ b H O A) (atom-≃ c H O A)))
  lift-sem (pair (a ∷ b ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (pairᵉ-≃ (atom-≃ a H O A) (atom-≃ b H O A)))
  lift-sem (fst (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (carᵉ-≃ (atom-≃ a H O A)))
  lift-sem (snd (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (cdrᵉ-≃ (atom-≃ a H O A)))
  lift-sem (tuple {k'} {Ms} as) {ρ = ρ} k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (atoms-≃ as H O A (λ m Ds → 𝒯ᵉ m Ds ≃ 𝒯ᵉ k' (⟦ Ms ⟧₊[ T' ] ρ))
                 (λ {m} eq q → ≃-trans (𝒯ᵉ-≃ m (nthD-≃ _ _ eq)) q) ≃-refl))
  lift-sem (get {i = i} (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (projᵉ-≃ i (atom-≃ a H O A)))
  lift-sem (inl (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (inlᵉ-≃ (atom-≃ a H O A)))
  lift-sem (inr (a ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k (inrᵉ-≃ (atom-≃ a H O A)))
  lift-sem (prim {p} (a ∷ b ∷ [])) k H O A cρ κ≃ = ≃-trans (κ≃ _ _ A) (K-≃ k
    (primᵉ-≃ p (atom-≃ a H O A) (atom-≃ b H O A)))
  lift-sem (case {L} {M₁} {M₂} a m₁ m₂) {n} {d} {σ} {ρ} k {κ} H O A cρ κ≃ =
    ≃-trans (checked-at (fits-< _ (fits {d} _ H)))
    (≃-trans (𝒞ᵉ-≃ {F = λ X → ⟦ lift n (suc d) m₁ ⟧ᴷ[ T ] n (σ [ d ↦ X ]) κ} {λ X → K⟨ k ⟩ (⟦ M₁ ⟧[ T' ] (X • ρ))}
                   {λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ [ d ↦ X ]) κ} {λ X → K⟨ k ⟩ (⟦ M₂ ⟧[ T' ] (X • ρ))}
                   (atom-≃ a H O A)
                   (λ v V cV _ → lift-sem m₁ k (⊔ˡ (height m₁) _ H') (scope-ext O) (agree-ext A)
                                 (Con-• (≈⇒Con cV) cρ) (λ D σ' A' → κ≃ D σ' (weak A')))
                   (λ v V cV _ → lift-sem m₂ k (⊔ʳ _ (height m₂) H') (scope-ext O) (agree-ext A)
                                 (Con-• (≈⇒Con cV) cρ) (λ D σ' A' → κ≃ D σ' (weak A'))))
             (≃-sym (case-law k {F₁ = λ X → ⟦ M₁ ⟧[ T' ] (X • ρ)} {λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)}
                       (Clos5ᵉ-con T' TC L cρ) (mono-• M₁) (mono-• M₂))))
    where H' = fits {d} (height m₁ ⊔ height m₂) H
  lift-sem (let′ {M₁} {M₂} m₁ m₂) {n} {d} {σ} {ρ} k {κ} H O A cρ κ≃ =
    ≃-trans (lift-sem m₁ (just G) (⊔ˡ {d} (height m₁) _ H) O A cρ κ₁≃)
            (≃-sym (let-law k {F = λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)} (Clos5ᵉ-con T' TC M₁ cρ) (mono-• M₂)))
    where
    H₂ = fits {d} _ (⊔ʳ (height m₁) _ H)
    G = λ X → K⟨ k ⟩ (⟦ M₂ ⟧[ T' ] (X • ρ))
    κ₁≃ : ∀ D σ' → Agree d σ' ρ
      → checkedᵉ n d D (letᵉ ⟨ D , ⟨ (λ X → ⟦ lift n (suc d) m₂ ⟧ᴷ[ T ] n (σ' [ d ↦ X ]) κ) , ptt ⟩ ⟩)
        ≃ K⟨ just G ⟩ D
    κ₁≃ D σ' A' = ≃-trans (checked-at (fits-< _ H₂))
      (letᵉ-≃ ≃-refl λ V _ cV _ → lift-sem m₂ k H₂ (scope-ext O) (agree-ext A') (Con-• (≈⇒Con cV) cρ)
                              (λ D' σ'' A'' → κ≃ D' σ'' (weak A'')))

{- Programs ---------------------------------------------------------------------}

table-lift : ∀ {ds} (ms : All Mon ds) k → tableᴷ (lift-defs ms) k ≃ table ds k
table-lift [] k = ≃-refl
table-lift {N ∷ Ns} (m ∷ ms) k with k ≟ length (lift-defs ms) | k ≟ length Ns
... | yes _ | yes _ =
  Λᵉ-≃ λ X _ cX _ → Λᵉ-≃ λ Y _ cY _ → lift-sem (table-lift ms) (table-con Ns) m nothing ≤-refl
    (scope-frame (mem X) (mem Y)) (agree-frame (mem X) (mem Y))
    (Con-• (≈⇒Con cY) (Con-• (≈⇒Con cX) (λ _ → Con-⌈⌉ ω))) (λ _ _ _ → ≃-refl)
... | no _ | no _ = table-lift ms k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-lift-defs ms)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-lift-defs ms))))

lift-locals-correct : ∀ (P : C5.Program) (mp : MonProgram P) → ⟦ lift-program P mp ⟧ᴷₚ ≃ ⟦ P ⟧ₚ
lift-locals-correct (program ds M) ⟨ ms , m ⟩ =
  lift-sem (table-lift ms) (table-con ds) m nothing ≤-refl (λ x _ → ≃-refl) (agree λ x ())
    (λ _ → Con-⌈⌉ ω) (λ _ _ _ → ≃-refl)

{- the compiler's programs -}
lift-correct-compile : ∀ (M : ISWIM.AST) → Closed M → ⟦ compile-imp M ⟧ᴷₚ ≃ ⟦ compile-mon M ⟧ₚ
lift-correct-compile M _ = lift-locals-correct (compile-mon M) (rco-program-mon (compile M))
