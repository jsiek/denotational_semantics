{-

  What the two proofs of lift locals (monadic Clos5 → Imp,
  Compile/LiftLocals.agda) have in common: the proof against the
  continuation-passing semantics of Imp (LiftLocalsCorrectK.agda, the
  main one) and the proof against the direct semantics
  (LiftLocalsCorrect.agda, an alternative).

  The invariant, at depth d: the store agrees with the environment,
  slot d ∸ (x + 1) meaning variable x for x < d (Agree), and the
  variables from d on are out of scope, meaning init as the slot beyond
  the frame does (Scope). Atoms then mean the same (atom-≃, atoms-≃).
  The frame is large enough, d + height m ≤ n, so every assignment is
  within it (fits, ⊔ˡ, ⊔ʳ).

  Given the correctness of lift-program for either semantics ℐ of Imp
  programs, the whole compiler into Imp is correct (Into).

-}

open import Framework.GraphModel.SetsAsPredicates
open import Framework.GraphModel.DOpSig using (Results)
open import Framework.GraphModel.Domain
open import Compiler.Lang.Clos5 using (Args)
open import Compiler.Lang.Mon
import Compiler.Lang.Imp as I
open import Compiler.Compile.LiftLocals using (lift-atom; lift-atoms; lift-defs; lift-program)
open import Compiler.Model.Graph.Sem.Clos5Iswim using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; ⟦_⟧ₚ; init)
open import Compiler.Model.Graph.Sem.Imp using (Store; read; _[_↦_]; 𝒜; 𝒜s; frame)
open import proof.Compiler.Model.Graph.Correctness.GlobalizeCorrect using (RRs)
open import proof.Compiler.Model.Graph.Correctness.RCOCorrect using (RRs-refl; compile-mon-same)
open import proof.Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀)
open import proof.Compiler.Model.Graph.Correctness.CompilerCorrect using (Same; Same-trans; ≃→Same)
open import Compiler.Compile.Pipeline using (compile; compile-imp)
open import Compiler.Compile.RCO using (rco-program-mon)
open import Compiler.Model.Graph.Sem.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵢ)
import Compiler.Lang.ISWIM as ISWIM
open import Framework.GraphModel.Env using (Env)
open import Framework.Primitives using (base-rep)

open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _⊔_; _<_; _≤_; _≟_; _<?_; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; +-mono-≤; +-suc; m≤m⊔n; m≤n⊔m; m≤m+n; m∸n≤m; ≮⇒≥; <-irrefl; <-≤-trans)
open import Data.List using (length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim)
open import Level using () renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (yes; no)

module proof.Compiler.Model.Graph.Correctness.LiftLocalsCommon where

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
open Agree public

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

{- Atoms ----------------------------------------------------------------------------}

module AtomsSame {T T' : Table} (TT : ∀ k → T k ≃ T' k) where

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

{- Programs ---------------------------------------------------------------------}

{- a function body: the free variables in slot 0, the argument in slot 1 -}
agree-frame : ∀ X Y → Agree 2 (frame X Y) (Y • X • (λ _ → init))
agree-frame X Y = agree λ { zero _ → ≃-refl ; (suc zero) _ → ≃-refl ; (suc (suc x)) (s≤s (s≤s ())) }

scope-frame : ∀ X Y → Scope 2 (Y • X • (λ _ → init))
scope-frame X Y = λ { (suc zero) (s≤s ()) ; (suc (suc x)) _ → ≃-refl }

length-lift-defs : ∀ {ds} (ms : All Mon ds) → length (lift-defs ms) ≡ length ds
length-lift-defs [] = refl
length-lift-defs (m ∷ ms) rewrite length-lift-defs ms = refl

{- The whole compiler, into Imp ------------------------------------------------

  compile-imp = lift-program ∘ compile-mon (Compile/Pipeline.agda): given
  that lift-program preserves meanings, for a semantics ℐ of Imp
  programs, the result produces the same constants as the ISWIM program,
  and produces something exactly when it does. -}

module Into (ℐ : I.Program → 𝒫 Value)
  (lift-program-correct : ∀ P (mp : MonProgram P) → ℐ (lift-program P mp) ≃ ⟦ P ⟧ₚ) where

  compile-imp-same : ∀ (M : ISWIM.AST) → Same (⟦ M ⟧ᵢ ρ₀) (ℐ (compile-imp M))
  compile-imp-same M = Same-trans (compile-mon-same M)
    (≃→Same (≃-sym (lift-program-correct _ (rco-program-mon (compile M)))))

  compile-imp-correct-const : ∀ (M : ISWIM.AST) → ∀ {B} (c : base-rep B)
    → (const c ∈ ⟦ M ⟧ᵢ ρ₀ → const c ∈ ℐ (compile-imp M))
    × (const c ∈ ℐ (compile-imp M) → const c ∈ ⟦ M ⟧ᵢ ρ₀)
  compile-imp-correct-const M = proj₁ (compile-imp-same M)

  compile-imp-correct-nonempty : ∀ (M : ISWIM.AST)
    → (nonempty (⟦ M ⟧ᵢ ρ₀) → nonempty (ℐ (compile-imp M)))
    × (nonempty (ℐ (compile-imp M)) → nonempty (⟦ M ⟧ᵢ ρ₀))
  compile-imp-correct-nonempty M = proj₂ (compile-imp-same M)
