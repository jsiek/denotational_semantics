{-

  Correctness of lift locals (monadic Clos5 → Imp,
  Compile/LiftLocals.agda): the meaning of the Imp program (Sem/Imp.agda)
  is that of the Clos5 program.

    lift-program-correct : ⟦ lift-program P mp ⟧ₚ ≃ ⟦ P ⟧ₚ

  The invariant, at depth d: the store agrees with the environment,
  slot d ∸ (x + 1) meaning variable x for x < d (Agree), and the
  variables from d on are out of scope, meaning init as the slot beyond
  the frame does (Scope). Running lift n d m then

  - gives the meaning of m (lift-sem), and
  - leaves a store that still agrees with the environment at depth d,
    when m has a value (Out). As in the operational proofs, this is
    stated relative to the environment, not to the store m started
    with, so coming back from under a binder only forgets the top slot
    (weak): whatever the body wrote at depth d + 1 or deeper is no
    longer looked at. The condition that m has a value is inherent: the
    slots after a case are empty when the scrutinee is not an
    injection, and those after a let when its right-hand side has no
    value; and the store of a let or case collects the slots from the
    runs of its body that have a value (Sem/Imp.agda).

  The frame is large enough, d + height m ≤ n, so every assignment is
  within it. No continuity is needed: the operators of let and case on
  both sides are related by congruence.

-}

open import SetsAsPredicates
open import NewDOpSig using (Results)
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos5 using (program; Args)
open import Compiler.Lang.Mon
open import Compiler.Compile.LiftLocals using (lift-atom; lift-atoms; lift; height; lift-defs; lift-program)
open import Compiler.Model.Graph.Sem.Clos5Iswim using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; table; ⟦_⟧ₚ; init)
open import Compiler.Model.Graph.Sem.Imp
  using (Store; read; _[_↦_]; 𝒜; 𝒜s; caseₛ; letₛ; frame)
  renaming (⟦_⟧[_] to ℐ⟦_⟧[_]; table to tableᵢ; ⟦_⟧ₚ to ℐ⟦_⟧ₚ)
open import Compiler.Model.Graph.Correctness.GlobalizeCorrect
  using (RRs; nthD-≃; app-≃; pair-≃; car-≃; cdr-≃; prim-≃; ΛΛ-≃)
open import Compiler.Model.Graph.Correctness.ConcretizeCorrect
  using (⋆-≃; 𝒯-≃; proj-≃; inl-≃; inr-≃; 𝒞-≃)
open import Compiler.Model.Graph.Correctness.RCOCorrect
  using (strict-≃; Λ-≃; ne-mem; RRs-refl; compile-mon-same)
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
open import Data.List using ([]; _∷_; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using () renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

module Compiler.Model.Graph.Correctness.LiftLocalsCorrect where

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

{- the store that r leaves agrees with ρ, if r has a value -}
Out : ℕ → Env Value → 𝒫 Value × Store → Set
Out d ρ r = nonempty (proj₁ r) → Agree d (proj₂ r) ρ

out-case : ∀ {d ρ A E₁ E₂} → (∀ X → Out d ρ (E₁ X)) → (∀ X → Out d ρ (E₂ X))
  → Out d ρ (caseₛ A E₁ E₂)
out-case R₁ R₂ ne = agree λ x x<d → ⟨
    (λ { u (inj₁ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ ⟨ u∈ , ne' ⟩ , _ ⟩ ⟩ ⟩ ⟩) → proj₁ (at (R₁ _ ne') x x<d) u u∈
          ; u (inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ ⟨ u∈ , ne' ⟩ , _ ⟩ ⟩ ⟩ ⟩) → proj₁ (at (R₂ _ ne') x x<d) u u∈ })
  , (case ne of λ { ⟨ w , inj₁ ⟨ v , ⟨ V , ⟨ l∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩ ⟩ u u∈ →
            inj₁ ⟨ v , ⟨ V , ⟨ l∈ , ⟨ ⟨ proj₂ (at (R₁ _ ⟨ w , w∈ ⟩) x x<d) u u∈ , ⟨ w , w∈ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩
          ; ⟨ w , inj₂ ⟨ v , ⟨ V , ⟨ r∈ , ⟨ w∈ , c ⟩ ⟩ ⟩ ⟩ ⟩ u u∈ →
            inj₂ ⟨ v , ⟨ V , ⟨ r∈ , ⟨ ⟨ proj₂ (at (R₂ _ ⟨ w , w∈ ⟩) x x<d) u u∈ , ⟨ w , w∈ ⟩ ⟩ , c ⟩ ⟩ ⟩ ⟩ }) ⟩

out-let : ∀ {d ρ D E} → (nonempty D → ∀ X → Out d ρ (E X)) → Out d ρ (letₛ D E)
out-let R ⟨ w , ⟨ V , ⟨ ⟨ w∈ , V≢ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ ⟩ = agree λ x x<d →
  ⟨ (λ { u ⟨ U , ⟨ ⟨ ⟨ u∈ , ne' ⟩ , _ ⟩ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ →
         proj₁ (at (R (ne-mem neU U⊆) (mem U) ne') x x<d) u u∈ })
  , (λ u u∈ → ⟨ V , ⟨ ⟨ ⟨ proj₂ (at (R (ne-mem ne V⊆) (mem V) ⟨ w , w∈ ⟩) x x<d) u u∈ , ⟨ w , w∈ ⟩ ⟩ , V≢ ⟩
                    , ⟨ V⊆ , ne ⟩ ⟩ ⟩) ⟩

{- ⋆ ⟨ F , D ⟩ has a value only if D does -}
⋆-strict : ∀ {F D E} → D ⊆ E → ∀ w → w ∈ ⋆ ⟨ F , ⟨ D , ptt ⟩ ⟩ → nonempty E
⋆-strict D⊆ w ⟨ V , ⟨ _ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ne-mem ne (λ u u∈ → D⊆ u (V⊆ u u∈))

{- The pass preserves meanings ----------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) where

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

  {- lift at depth d: the meaning, and a store that still agrees with ρ -}
  lift-sem : ∀ {M} (m : Mon M) {n d σ ρ} → d + height m ≤ n → Scope d ρ → Agree d σ ρ
    → proj₁ (ℐ⟦ lift n d m ⟧[ T ] n σ) ≃ ⟦ M ⟧[ T' ] ρ × Out d ρ (ℐ⟦ lift n d m ⟧[ T ] n σ)
  lift-sem (atom a) H O A = ⟨ atom-≃ a H O A , (λ _ → A) ⟩
  lift-sem (app (a ∷ b ∷ c ∷ [])) H O A =
    ⟨ app-≃ ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ⟨ up (atom-≃ c H O A) , ptt ⟩ ⟩ ⟩ , (λ _ → A) ⟩
  lift-sem (pair (a ∷ b ∷ [])) H O A =
    ⟨ pair-≃ ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ptt ⟩ ⟩ , (λ _ → A) ⟩
  lift-sem (fst (a ∷ [])) H O A = ⟨ car-≃ ⟨ up (atom-≃ a H O A) , ptt ⟩ , (λ _ → A) ⟩
  lift-sem (snd (a ∷ [])) H O A = ⟨ cdr-≃ ⟨ up (atom-≃ a H O A) , ptt ⟩ , (λ _ → A) ⟩
  lift-sem (tuple {k} {Ms} as) {ρ = ρ} H O A =
    ⟨ atoms-≃ as H O A (λ m Ds → 𝒯 m Ds ≃ 𝒯 k (⟦ Ms ⟧₊[ T' ] ρ))
                 (λ {m} eq q → ≃-trans (𝒯-≃ m (nthD-≃ _ _ eq)) q) ≃-refl
    , (λ _ → A) ⟩
  lift-sem (get {i = i} (a ∷ [])) H O A = ⟨ proj-≃ i (atom-≃ a H O A) , (λ _ → A) ⟩
  lift-sem (inl (a ∷ [])) H O A = ⟨ inl-≃ (atom-≃ a H O A) , (λ _ → A) ⟩
  lift-sem (inr (a ∷ [])) H O A = ⟨ inr-≃ (atom-≃ a H O A) , (λ _ → A) ⟩
  lift-sem (prim {p} (a ∷ b ∷ [])) H O A =
    ⟨ prim-≃ p ⟨ up (atom-≃ a H O A) , ⟨ up (atom-≃ b H O A) , ptt ⟩ ⟩ , (λ _ → A) ⟩
  lift-sem (case {M = M₁} {M₂} a m₁ m₂) {n} {d} {σ} {ρ} H O A with d <? n
  ... | no d≮n = ⊥-elim (d≮n (fits-< _ (fits {d} _ H)))
  ... | yes d<n =
    ⟨ 𝒞-≃ {F = B m₁} {λ X → ⟦ M₁ ⟧[ T' ] (X • ρ)} {B m₂} {λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)}
          (atom-≃ a H O A) (λ v V _ → proj₁ (IH₁ (mem (v ∷ V)))) (λ v V _ → proj₁ (IH₂ (mem (v ∷ V))))
    , out-case {A = 𝒜 T n σ (lift-atom n d a)}
               (λ X ne → weak (proj₂ (IH₁ X) ne)) (λ X ne → weak (proj₂ (IH₂ X) ne)) ⟩
    where
    B = λ {N} (m : Mon N) X → proj₁ (ℐ⟦ lift n (suc d) m ⟧[ T ] n (σ [ d ↦ X ]))
    H' = fits {d} (height m₁ ⊔ height m₂) H
    IH₁ = λ X → lift-sem m₁ (⊔ˡ (height m₁) _ H') (scope-ext O) (agree-ext {X = X} A)
    IH₂ = λ X → lift-sem m₂ (⊔ʳ _ (height m₂) H') (scope-ext O) (agree-ext {X = X} A)
  lift-sem (let′ {M₁} {M₂} m₁ m₂) {n} {d} {σ} {ρ} H O A with d <? n
  ... | no d≮n = ⊥-elim (d≮n (fits-< _ (fits {d} (height m₂) (⊔ʳ (height m₁) _ H))))
  ... | yes d<n =
    ⟨ strict-≃ (⋆-strict {Λ ⟨ F , ptt ⟩} (λ _ w∈ → w∈))
               (⋆-strict {Λ ⟨ F' , ptt ⟩} (proj₂ (proj₁ IH₁)))
        (λ ne → ⋆-≃ (Λ-≃ {F} {F'} λ V _ _ → proj₁ (IH₂ ne (mem V))) (proj₁ IH₁))
    , out-let (λ ne X ne' → weak (proj₂ (IH₂ ne X) ne')) ⟩
    where
    IH₁ = lift-sem m₁ (⊔ˡ {d} (height m₁) _ H) O A
    σ₁ = proj₂ (ℐ⟦ lift n d m₁ ⟧[ T ] n σ)
    F = λ X → proj₁ (ℐ⟦ lift n (suc d) m₂ ⟧[ T ] n (σ₁ [ d ↦ X ]))
    F' = λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)
    IH₂ = λ ne X → lift-sem m₂ (fits {d} _ (⊔ʳ (height m₁) _ H)) (scope-ext O)
      (agree-ext {X = X} (proj₂ IH₁ ne))

{- Programs ---------------------------------------------------------------------}

{- a function body: the free variables in slot 0, the argument in slot 1 -}
agree-frame : ∀ X Y → Agree 2 (frame X Y) (Y • X • (λ _ → init))
agree-frame X Y = agree λ { zero _ → ≃-refl ; (suc zero) _ → ≃-refl ; (suc (suc x)) (s≤s (s≤s ())) }

scope-frame : ∀ X Y → Scope 2 (Y • X • (λ _ → init))
scope-frame X Y = λ { (suc zero) (s≤s ()) ; (suc (suc x)) _ → ≃-refl }

length-lift-defs : ∀ {ds} (ms : All Mon ds) → length (lift-defs ms) ≡ length ds
length-lift-defs [] = refl
length-lift-defs (m ∷ ms) rewrite length-lift-defs ms = refl

table-lift : ∀ {ds} (ms : All Mon ds) k → tableᵢ (lift-defs ms) k ≃ table ds k
table-lift [] k = ≃-refl
table-lift {N ∷ Ns} (m ∷ ms) k with k ≟ length (lift-defs ms) | k ≟ length Ns
... | yes _ | yes _ =
  ΛΛ-≃ λ X Y → proj₁ (lift-sem (table-lift ms) m ≤-refl (scope-frame X Y) (agree-frame X Y))
... | no _ | no _ = table-lift ms k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-lift-defs ms)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-lift-defs ms))))

lift-program-correct : ∀ P (mp : MonProgram P) → ℐ⟦ lift-program P mp ⟧ₚ ≃ ⟦ P ⟧ₚ
lift-program-correct (program ds M) ⟨ ms , m ⟩ =
  proj₁ (lift-sem (table-lift ms) m ≤-refl (λ x _ → ≃-refl) (agree λ x ()))

{- The whole compiler, into Imp ------------------------------------------------

  compile-imp = lift-program ∘ compile-mon (Compile/Pipeline.agda): the
  result produces the same constants as the ISWIM program, and produces
  something exactly when it does. -}

compile-imp-same : ∀ (M : ISWIM.AST) → Same (⟦ M ⟧ᵢ ρ₀) ℐ⟦ compile-imp M ⟧ₚ
compile-imp-same M = Same-trans (compile-mon-same M)
  (≃→Same (≃-sym (lift-program-correct _ (rco-program-mon (compile M)))))

compile-imp-correct-const : ∀ (M : ISWIM.AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ᵢ ρ₀ → const c ∈ ℐ⟦ compile-imp M ⟧ₚ)
  × (const c ∈ ℐ⟦ compile-imp M ⟧ₚ → const c ∈ ⟦ M ⟧ᵢ ρ₀)
compile-imp-correct-const M = proj₁ (compile-imp-same M)

compile-imp-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ᵢ ρ₀) → nonempty ℐ⟦ compile-imp M ⟧ₚ)
  × (nonempty ℐ⟦ compile-imp M ⟧ₚ → nonempty (⟦ M ⟧ᵢ ρ₀))
compile-imp-correct-nonempty M = proj₂ (compile-imp-same M)
