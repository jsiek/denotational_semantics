{-

  Correctness of lift locals (monadic Clos5 → Imp,
  Compile/LiftLocals.agda): the meaning of the Imp program (Sem/Imp.agda)
  is that of the Clos5 program.

    lift-program-correct : ⟦ lift-program P mp ⟧ₚ ≃ ⟦ P ⟧ₚ

  The invariant, at depth d in a frame of n slots: the store agrees with
  the environment, slot d ∸ (x + 1) meaning variable x for x < d, and
  the variables out of scope meaning init, as the slot beyond the frame
  does (Agree). Running lift n d m then

  - gives the meaning of m (lift-sem), and
  - leaves the slots below d as they were (Pres): an assignment at depth
    d' ≥ d writes slot d'. Pres is two inclusions, the second only when
    m has a value: the slots after a case are empty when the scrutinee
    is not an injection, and those after a let when its right-hand side
    has no value, like the value itself.

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
  using (Store; read; _[_↦_]; 𝒜; 𝒜s; caseₛ; letₛ; frame; zeros)
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
  using (≤-refl; ≤-trans; +-mono-≤; +-suc; m≤m⊔n; m≤n⊔m; m≤m+n; m∸n≤m; ≮⇒≥; <-irrefl; m<n⇒m<1+n)
open import Data.List using ([]; _∷_; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
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

read-≃ : ∀ n {σ σ'} y → σ y ≃ σ' y → read n σ y ≃ read n σ' y
read-≃ n y eq with y <? n
... | yes _ = eq
... | no _ = ≃-refl

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

{- at depth d in a frame of n slots, σ agrees with ρ -}
record Agree (n d : ℕ) (σ : Store) (ρ : Env Value) : Set where
  constructor agree
  field
    in-scope : ∀ x → x < d → read n σ (d ∸ suc x) ≃ ρ x
    out-of-scope : ∀ x → d ≤ x → ρ x ≃ init

{- under a binder: its value in slot d -}
agree-ext : ∀ {n d σ ρ X} → d < n → Agree n d σ ρ → Agree n (suc d) (σ [ d ↦ X ]) (X • ρ)
agree-ext {n} {d} {σ} {ρ} {X} d<n (agree A O) = agree G H
  where
  G : ∀ x → x < suc d → read n (σ [ d ↦ X ]) (suc d ∸ suc x) ≃ (X • ρ) x
  G zero _ = ≃-reflexive (trans (read-at d<n) (upd-at σ d))
  G (suc x) (s≤s x<d) = ≃-trans (read-≃ n _ (upd-< (slot-< x<d))) (A x x<d)
  H : ∀ x → suc d ≤ x → (X • ρ) x ≃ init
  H (suc x) (s≤s d≤x) = O x d≤x

agree-pres : ∀ {n d σ σ' ρ} → (∀ y → y < d → σ' y ≃ σ y) → Agree n d σ ρ → Agree n d σ' ρ
agree-pres {n} eq (agree A O) =
  agree (λ x x<d → ≃-trans (read-≃ n _ (eq _ (slot-< x<d))) (A x x<d)) O

{- the slots below d of the store that r leaves are those of σ, if r has a value -}
record Pres (d : ℕ) (σ : Store) (r : 𝒫 Value × Store) : Set where
  constructor pres
  field
    ⊆σ : ∀ y → y < d → proj₂ r y ⊆ σ y
    σ⊆ : nonempty (proj₁ r) → ∀ y → y < d → σ y ⊆ proj₂ r y
open Pres

pres-refl : ∀ {d σ D} → Pres d σ ⟨ D , σ ⟩
pres-refl = pres (λ _ _ _ w∈ → w∈) (λ _ _ _ _ w∈ → w∈)

{- the slot of a binder at depth d is above those that Pres d keeps -}
pres-ext : ∀ {d σ X r} → Pres (suc d) (σ [ d ↦ X ]) r → Pres d σ r
pres-ext (pres P Q) =
  pres (λ y y<d w w∈ → proj₁ (upd-< y<d) w (P y (m<n⇒m<1+n y<d) w w∈))
       (λ ne y y<d w w∈ → Q ne y (m<n⇒m<1+n y<d) w (proj₂ (upd-< y<d) w w∈))

pres-case : ∀ {d σ A E₁ E₂} → (∀ X → Pres d σ (E₁ X)) → (∀ X → Pres d σ (E₂ X))
  → Pres d σ (caseₛ A E₁ E₂)
pres-case P₁ P₂ =
  pres (λ { y y<d w (inj₁ ⟨ v , ⟨ V , ⟨ _ , w∈ ⟩ ⟩ ⟩) → ⊆σ (P₁ _) y y<d w w∈
       ; y y<d w (inj₂ ⟨ v , ⟨ V , ⟨ _ , w∈ ⟩ ⟩ ⟩) → ⊆σ (P₂ _) y y<d w w∈ })
       (λ { ⟨ w , inj₁ ⟨ v , ⟨ V , ⟨ l∈ , w∈ ⟩ ⟩ ⟩ ⟩ y y<d u u∈ →
           inj₁ ⟨ v , ⟨ V , ⟨ l∈ , σ⊆ (P₁ _) ⟨ w , w∈ ⟩ y y<d u u∈ ⟩ ⟩ ⟩
       ; ⟨ w , inj₂ ⟨ v , ⟨ V , ⟨ r∈ , w∈ ⟩ ⟩ ⟩ ⟩ y y<d u u∈ →
           inj₂ ⟨ v , ⟨ V , ⟨ r∈ , σ⊆ (P₂ _) ⟨ w , w∈ ⟩ y y<d u u∈ ⟩ ⟩ ⟩ })

pres-let : ∀ {d σ D σ₁ E} → Pres d σ ⟨ D , σ₁ ⟩ → (nonempty D → ∀ X → Pres d σ₁ (E X))
  → Pres d σ (letₛ D E)
pres-let (pres P Q) PE =
  pres (λ { y y<d w ⟨ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ →
           P y y<d w (⊆σ (PE (ne-mem ne V⊆) (mem V)) y y<d w w∈) })
       (λ { ⟨ w , ⟨ V , ⟨ ⟨ w∈ , _ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ ⟩ y y<d u u∈ →
           ⟨ V , ⟨ ⟨ σ⊆ (PE (ne-mem ne V⊆) (mem V)) ⟨ w , w∈ ⟩ y y<d u
                      (Q (ne-mem ne V⊆) y y<d u u∈) , ne ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ })

{- ⋆ ⟨ F , D ⟩ has a value only if D does -}
⋆-strict : ∀ {F D E} → D ⊆ E → ∀ w → w ∈ ⋆ ⟨ F , ⟨ D , ptt ⟩ ⟩ → nonempty E
⋆-strict D⊆ w ⟨ V , ⟨ _ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ne-mem ne (λ u u∈ → D⊆ u (V⊆ u u∈))

{- The pass preserves meanings ----------------------------------------------------}

module _ {T T' : Table} (TT : ∀ k → T k ≃ T' k) where

  atom-≃ : ∀ {n d σ ρ M} (a : Atom M) → Agree n d σ ρ → 𝒜 T n σ (lift-atom n d a) ≃ ⟦ M ⟧[ T' ] ρ
  atom-≃ {n} {d} {σ} (var x) (agree A O) with x <? d
  ... | yes x<d = A x x<d
  ... | no x≮d = ≃-trans (≃-reflexive (read-out n σ)) (≃-sym (O x (≮⇒≥ x≮d)))
  atom-≃ (lit B k) _ = ≃-refl
  atom-≃ (ref k) _ = TT k

  {- the atoms of a tuple: what holds of their meanings in Clos5 holds in Imp -}
  atoms-≃ : ∀ {n d σ ρ k} {Ms : Args (replicate k ■)} (as : Atoms Ms) → Agree n d σ ρ
    → (Q : ∀ m → Results (𝒫 Value) (replicate m ■) → Set)
    → (∀ {m Ds Es} → RRs _ Ds Es → Q m Es → Q m Ds)
    → Q k (⟦ Ms ⟧₊[ T' ] ρ) → Q (length (lift-atoms n d as)) (𝒜s T n σ (lift-atoms n d as))
  atoms-≃ [] Ag Q resp q = q
  atoms-≃ (a ∷ as) Ag Q resp q =
    atoms-≃ as Ag (λ m Ds → Q (suc m) ⟨ _ , Ds ⟩) (λ eq → resp ⟨ up ≃-refl , eq ⟩)
      (resp ⟨ up (atom-≃ a Ag) , RRs-refl _ ⟩ q)

  {- lift at depth d: the meaning, and the slots below d kept -}
  lift-sem : ∀ {M} (m : Mon M) {n d σ ρ} → d + height m ≤ n → Agree n d σ ρ
    → proj₁ (ℐ⟦ lift n d m ⟧[ T ] n σ) ≃ ⟦ M ⟧[ T' ] ρ × Pres d σ (ℐ⟦ lift n d m ⟧[ T ] n σ)
  lift-sem (atom a) H Ag = ⟨ atom-≃ a Ag , pres-refl ⟩
  lift-sem (app (a ∷ b ∷ c ∷ [])) H Ag =
    ⟨ app-≃ ⟨ up (atom-≃ a Ag) , ⟨ up (atom-≃ b Ag) , ⟨ up (atom-≃ c Ag) , ptt ⟩ ⟩ ⟩ , pres-refl ⟩
  lift-sem (pair (a ∷ b ∷ [])) H Ag =
    ⟨ pair-≃ ⟨ up (atom-≃ a Ag) , ⟨ up (atom-≃ b Ag) , ptt ⟩ ⟩ , pres-refl ⟩
  lift-sem (fst (a ∷ [])) H Ag = ⟨ car-≃ ⟨ up (atom-≃ a Ag) , ptt ⟩ , pres-refl ⟩
  lift-sem (snd (a ∷ [])) H Ag = ⟨ cdr-≃ ⟨ up (atom-≃ a Ag) , ptt ⟩ , pres-refl ⟩
  lift-sem (tuple {k} {Ms} as) {ρ = ρ} H Ag =
    ⟨ atoms-≃ as Ag (λ m Ds → 𝒯 m Ds ≃ 𝒯 k (⟦ Ms ⟧₊[ T' ] ρ))
                 (λ {m} eq q → ≃-trans (𝒯-≃ m (nthD-≃ _ _ eq)) q) ≃-refl
    , pres-refl ⟩
  lift-sem (get {i = i} (a ∷ [])) H Ag = ⟨ proj-≃ i (atom-≃ a Ag) , pres-refl ⟩
  lift-sem (inl (a ∷ [])) H Ag = ⟨ inl-≃ (atom-≃ a Ag) , pres-refl ⟩
  lift-sem (inr (a ∷ [])) H Ag = ⟨ inr-≃ (atom-≃ a Ag) , pres-refl ⟩
  lift-sem (prim {p} (a ∷ b ∷ [])) H Ag =
    ⟨ prim-≃ p ⟨ up (atom-≃ a Ag) , ⟨ up (atom-≃ b Ag) , ptt ⟩ ⟩ , pres-refl ⟩
  lift-sem (case {M = M₁} {M₂} a m₁ m₂) {n} {d} {σ} {ρ} H Ag with d <? n
  ... | no d≮n = ⊥-elim (d≮n (fits-< _ (fits {d} _ H)))
  ... | yes d<n =
    ⟨ 𝒞-≃ {F = B m₁} {λ X → ⟦ M₁ ⟧[ T' ] (X • ρ)} {B m₂} {λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)}
          (atom-≃ a Ag) (λ v V → proj₁ (IH₁ (mem (v ∷ V)))) (λ v V → proj₁ (IH₂ (mem (v ∷ V))))
    , pres-case {A = 𝒜 T n σ (lift-atom n d a)}
                (λ X → pres-ext (proj₂ (IH₁ X))) (λ X → pres-ext (proj₂ (IH₂ X))) ⟩
    where
    B = λ {N} (m : Mon N) X → proj₁ (ℐ⟦ lift n (suc d) m ⟧[ T ] n (σ [ d ↦ X ]))
    H' = fits {d} (height m₁ ⊔ height m₂) H
    IH₁ = λ X → lift-sem m₁ (⊔ˡ (height m₁) _ H') (agree-ext {X = X} d<n Ag)
    IH₂ = λ X → lift-sem m₂ (⊔ʳ _ (height m₂) H') (agree-ext {X = X} d<n Ag)
  lift-sem (let′ {M₁} {M₂} m₁ m₂) {n} {d} {σ} {ρ} H Ag with d <? n
  ... | no d≮n = ⊥-elim (d≮n (fits-< _ (fits {d} (height m₂) (⊔ʳ (height m₁) _ H))))
  ... | yes d<n =
    ⟨ strict-≃ (⋆-strict {Λ ⟨ F , ptt ⟩} (λ _ w∈ → w∈))
               (⋆-strict {Λ ⟨ F' , ptt ⟩} (proj₂ (proj₁ IH₁)))
        (λ ne → ⋆-≃ (Λ-≃ {F} {F'} λ V _ → proj₁ (IH₂ ne (mem V))) (proj₁ IH₁))
    , pres-let (proj₂ IH₁) (λ ne X → pres-ext (proj₂ (IH₂ ne X))) ⟩
    where
    IH₁ = lift-sem m₁ (⊔ˡ {d} (height m₁) _ H) Ag
    σ₁ = proj₂ (ℐ⟦ lift n d m₁ ⟧[ T ] n σ)
    F = λ X → proj₁ (ℐ⟦ lift n (suc d) m₂ ⟧[ T ] n (σ₁ [ d ↦ X ]))
    F' = λ X → ⟦ M₂ ⟧[ T' ] (X • ρ)
    IH₂ = λ ne X → lift-sem m₂ (fits {d} _ (⊔ʳ (height m₁) _ H))
      (agree-ext {X = X} d<n (agree-pres {σ' = σ₁}
        (λ y y<d → ⟨ ⊆σ (proj₂ IH₁) y y<d , σ⊆ (proj₂ IH₁) ne y y<d ⟩) Ag))

{- Programs ---------------------------------------------------------------------}

{- a function body: the free variables in slot 0, the argument in slot 1 -}
agree-frame : ∀ {h} X Y → Agree (2 + h) 2 (frame X Y) (Y • X • (λ _ → init))
agree-frame X Y =
  agree (λ { zero _ → ≃-refl ; (suc zero) _ → ≃-refl ; (suc (suc x)) (s≤s (s≤s ())) })
        (λ { (suc zero) (s≤s ()) ; (suc (suc x)) _ → ≃-refl })

length-lift-defs : ∀ {ds} (ms : All Mon ds) → length (lift-defs ms) ≡ length ds
length-lift-defs [] = refl
length-lift-defs (m ∷ ms) rewrite length-lift-defs ms = refl

table-lift : ∀ {ds} (ms : All Mon ds) k → tableᵢ (lift-defs ms) k ≃ table ds k
table-lift [] k = ≃-refl
table-lift {N ∷ Ns} (m ∷ ms) k with k ≟ length (lift-defs ms) | k ≟ length Ns
... | yes _ | yes _ =
  ΛΛ-≃ λ X Y → proj₁ (lift-sem (table-lift ms) m ≤-refl (agree-frame X Y))
... | no _ | no _ = table-lift ms k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-lift-defs ms)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-lift-defs ms))))

lift-program-correct : ∀ P (mp : MonProgram P) → ℐ⟦ lift-program P mp ⟧ₚ ≃ ⟦ P ⟧ₚ
lift-program-correct (program ds M) ⟨ ms , m ⟩ =
  proj₁ (lift-sem (table-lift ms) m ≤-refl (agree (λ x ()) (λ x _ → ≃-refl)))

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
