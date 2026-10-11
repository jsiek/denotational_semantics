{-

  Backward (reflect) direction of the correctness of the delay pass
  (Clos3 → Clos4), using the logical relation of DelayFiniteRel, indexed
  by *finite lists of target observations* (see issue #1).

  The function clause (app-obs) is the only place where the car and cdr
  halves of target closures meet, and they meet inside the finite list V',
  so junk entries and mixed closures never produce a target-only result.

  The proof uses two properties of the semantics:
  - target denotations are consistent (⟦⟧'-consis), which follows from the
    consistency of the target operators (𝕆-Clos4-consis);
  - source denotations are continuous (C3.term-continuous).
-}

open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import Primitives
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos3 as L3
open import Compiler.Lang.Clos4 as L4
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import Compiler.Model.Graph.Sem.Clos3Iswim as S3
open import Compiler.Model.Graph.Sem.Clos4Iswim as S4 renaming
  (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
open import Compiler.Compile.Delay using (delay; del-map-args)
open import NewEnv using (nonempty-env; •-~)
open import NewDenotProperties using (Every)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon
open import Compiler.Model.Graph.Correctness.DelayFiniteRel
open import Compiler.Model.Graph.Correctness.DelayApp using (let-app-≃)
import Compiler.Model.Graph.Sem.Clos3IswimContinuous as C3

open import Data.Nat using (ℕ; zero; suc; s≤s)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Level using (lift; lower)

module Compiler.Model.Graph.Correctness.DelayReflectFinite where

{- Properties of the semantics ------------------------------------------------}

{- target denotations are consistent, by induction on the term -}
⟦⟧'-consis-env : ∀ (M' : AST') {ρ₁ ρ₂ : Env} → (∀ x → Every _~_ (ρ₁ x) (ρ₂ x))
  → Every _~_ (⟦ M' ⟧' ρ₁) (⟦ M' ⟧' ρ₂)
⟦⟧'-consis-arg : ∀ {b} (arg : Arg' b) {ρ₁ ρ₂ : Env} → (∀ x → Every _~_ (ρ₁ x) (ρ₂ x))
  → result-rel-pres (Every _~_) b (⟦ arg ⟧ₐ' ρ₁) (⟦ arg ⟧ₐ' ρ₂)
⟦⟧'-consis-args : ∀ {bs} (args : Args' bs) {ρ₁ ρ₂ : Env} → (∀ x → Every _~_ (ρ₁ x) (ρ₂ x))
  → results-rel-pres (Every _~_) bs (⟦ args ⟧₊' ρ₁) (⟦ args ⟧₊' ρ₂)

⟦⟧'-consis-env (# x) ρ~ = ρ~ x
⟦⟧'-consis-env (op ⦅ args ⦆') {ρ₁}{ρ₂} ρ~ =
  lower (𝕆-Clos4-consis op (⟦ args ⟧₊' ρ₁) (⟦ args ⟧₊' ρ₂) (⟦⟧'-consis-args args ρ~))
⟦⟧'-consis-arg (ast' M') ρ~ = lift (⟦⟧'-consis-env M' ρ~)
⟦⟧'-consis-arg (bind' arg) ρ~ = λ X Y X~Y → ⟦⟧'-consis-arg arg (•-~ (Every _~_) ρ~ X~Y)
⟦⟧'-consis-arg (clear' arg) ρ~ = ⟦⟧'-consis-arg arg (λ x → Init-consis)
⟦⟧'-consis-args nil ρ~ = ptt
⟦⟧'-consis-args (cons arg args) ρ~ = ⟨ ⟦⟧'-consis-arg arg ρ~ , ⟦⟧'-consis-args args ρ~ ⟩

⟦⟧'-consis : ∀ (M' : AST') (ρ' : Env) → (∀ x → consis (ρ' x)) → consis (⟦ M' ⟧' ρ')
⟦⟧'-consis M' ρ' ρ'~ = ⟦⟧'-consis-env M' ρ'~

{- one finite part of the bound variable suffices -}
cont-0 : ∀ (M : AST) {X ρ} → nonempty-env ρ → nonempty X → ∀ y → y ∈ ⟦ M ⟧ (X • ρ)
  → Σ[ u ∈ Value ] Σ[ U ∈ List Value ] mem (u ∷ U) ⊆ X × y ∈ ⟦ M ⟧ (mem (u ∷ U) • ρ)
cont-0 M {X}{ρ} NE NE-X y y∈ with C3.term-continuous M (X • ρ) NE' y y∈
  where NE' : nonempty-env (X • ρ)
        NE' zero = NE-X
        NE' (suc x) = NE x
... | ⟨ Vs , ⟨ ok , y∈fin ⟩ ⟩ with Vs 0 | proj₁ (ok 0) | proj₂ (ok 0)
     | S3.⟦⟧-monotone {ρ = λ z → mem (Vs z)} {ρ′ = mem (Vs 0) • ρ} M env⊆ y y∈fin
  where env⊆ : ∀ z → mem (Vs z) ⊆ (mem (Vs 0) • ρ) z
        env⊆ zero = λ d d∈ → d∈
        env⊆ (suc z) = proj₂ (ok (suc z))
... | [] | ne | _ | _ = ⊥-elim (ne refl)
... | u ∷ U | _ | U⊆ | y∈' = ⟨ u , ⟨ U , ⟨ U⊆ , y∈' ⟩ ⟩ ⟩

{- the beta rule for source closures: applied to E, a closure with
   environment T behaves like its body (using continuity) -}
clos-β : ∀ (N : AST) {T E} → nonempty T → nonempty E
  → ⟦ N ⟧ (E • T • (λ _ → Init))
    ⊆ (⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ (λ Y → ⟦ N ⟧ (Y • X • (λ _ → Init))) , ptt ⟩) , ptt ⟩
         , ⟨ T , ptt ⟩ ⟩ ● E)
clos-β N {T}{E} NE-T NE-E x x∈ with C3.term-continuous N _ NE x x∈
  where NE : nonempty-env (E • T • (λ _ → Init))
        NE zero = NE-E
        NE (suc zero) = NE-T
        NE (suc (suc y)) = ⟨ ω , refl ⟩
... | ⟨ Vs , ⟨ ok , x∈fin ⟩ ⟩ =
  ⟨ Vs 0 , ⟨ ⟨ Vs 1 , ⟨ ⟨ ⟨ x∈' , proj₁ (ok 0) ⟩ , proj₁ (ok 1) ⟩
                      , ⟨ proj₂ (ok 1) , proj₁ (ok 1) ⟩ ⟩ ⟩
           , ⟨ proj₂ (ok 0) , proj₁ (ok 0) ⟩ ⟩ ⟩
  where
  env⊆ : ∀ y → mem (Vs y) ⊆ (mem (Vs 0) • mem (Vs 1) • (λ _ → Init)) y
  env⊆ zero = λ d z → z
  env⊆ (suc zero) = λ d z → z
  env⊆ (suc (suc y)) = proj₂ (ok (suc (suc y)))
  x∈' = S3.⟦⟧-monotone {ρ = λ y → mem (Vs y)} N env⊆ x x∈fin

{- Collecting the finite witnesses of a target application -------------------}

{- a target application V' ⊆ (car L' ● cdr L') ● N' is a batch of calls of
   a finite W ⊆ L' on a finite U ⊆ N' -}
collect : ∀ (L' N' : 𝒫 Value) V' → mem V' ⊆ (L' ⊙ N')
  → Σ[ W ∈ List Value ] Σ[ U ∈ List Value ]
      mem W ⊆ L' × mem U ⊆ N' × Calls W U V'
collect L' N' [] _ = ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , [] ⟩ ⟩ ⟩ ⟩
collect L' N' (w ∷ V') V'⊆
    with V'⊆ w (here refl) | collect L' N' V' (λ d d∈ → V'⊆ d (there d∈))
... | ⟨ U₀ , ⟨ ⟨ FV , ⟨ e∈L' , ⟨ FV⊆Cdr , neFV ⟩ ⟩ ⟩ , ⟨ U₀⊆N' , neU₀ ⟩ ⟩ ⟩
    | ⟨ W , ⟨ U , ⟨ W⊆ , ⟨ U⊆ , cs ⟩ ⟩ ⟩ ⟩ =
  ⟨ e ∷ (C ++ W) , ⟨ U₀ ++ U , ⟨ W⊆' , ⟨ U⊆' , ⟨ ent , neU₀ ⟩ ∷ Calls-⊆ inW cs ⟩ ⟩ ⟩ ⟩
  where
  e = ⦅ FV ↦ (U₀ ↦ w) ∣
  C = lmap ∣_⦆ FV
  inW : mem W ⊆ mem (e ∷ (C ++ W))
  inW d d∈ = there (∈-++⁺ʳ C d∈)

  W⊆' : mem (e ∷ (C ++ W)) ⊆ L'
  W⊆' _ (here refl) = e∈L'
  W⊆' d (there d∈) with ∈-++⁻ C d∈
  ... | inj₂ d∈W = W⊆ d d∈W
  ... | inj₁ d∈C with ∈-map⁻ ∣_⦆ d∈C
  ... | ⟨ fv , ⟨ fv∈ , refl ⟩ ⟩ = FV⊆Cdr fv fv∈

  U⊆' : mem (U₀ ++ U) ⊆ N'
  U⊆' d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = U₀⊆N' d d∈U₀
  ... | inj₂ d∈U = U⊆ d d∈U

  ent : CarEntry (e ∷ (C ++ W)) U₀ w
  ent = car-entry FV (here refl) neFV (λ d d∈ → there (∈-++⁺ˡ (∈-map⁺ ∣_⦆ d∈)))

{- The fundamental lemma ------------------------------------------------------}

{- the hypotheses on the environments -}
record Envs (ρ' ρ : Env) : Set₁ where
  constructor envs
  field
    NE : nonempty-env ρ
    ρ'~ : ∀ x → consis (ρ' x)
    ρ⊳ : ρ' ⊳ₑ ρ

delay-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ
  → ∀ V' k → mem V' ⊆ ⟦ delay M ⟧' ρ' → Bnd k V' → R k V' (⟦ M ⟧ ρ)

reflect-nth : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → (i : Fin n) → ∀ V' k → mem V' ⊆ nthD (⟦ del-map-args args ⟧₊' ρ') i → Bnd k V'
  → R k V' (nthD (⟦ args ⟧₊ ρ) i)

reflect-𝒯 : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → ∀ V' k → mem V' ⊆ 𝒯 n (⟦ del-map-args args ⟧₊' ρ') → Bnd k V'
  → R k V' (𝒯 n (⟦ args ⟧₊ ρ))

{- a nonempty target set yields a nonempty source set -}
ne-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → nonempty (⟦ delay M ⟧' ρ') → nonempty (⟦ M ⟧ ρ)
ne-reflect M E ⟨ v , v∈ ⟩ =
  Obs.nonempty-obs (delay-reflect M E (v ∷ []) (suc (depth v)) (single⊆ v∈) (Bnd-single v)) (λ ())

{- the tagged parts of a reflected set are related -}
tag-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → ∀ t W j → mem W ⊆ Untag t (⟦ delay M ⟧' ρ')
  → Bnd j W → R j W (Untag t (⟦ M ⟧ ρ))
tag-reflect M E t W j W⊆ bW =
  Obs.tag-obs (delay-reflect M E (lmap (tag t) W) (suc j) mW bm) t W (λ d d∈ → ∈-map⁺ (tag t) d∈)
  where
  mW : mem (lmap (tag t) W) ⊆ _
  mW d d∈ with ∈-map⁻ (tag t) d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = W⊆ x x∈
  bm : Bnd (suc j) (lmap (tag t) W)
  bm d d∈ with ∈-map⁻ (tag t) d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = Bnd-tag t (bW x x∈)
    where
    Bnd-tag : ∀ t {x j} → depth x Data.Nat.< j → depth (tag t x) Data.Nat.< suc j
    Bnd-tag (tupT i) = s≤s
    Bnd-tag leftT = s≤s
    Bnd-tag rightT = s≤s

{- the cases for case-op: by consistency, all the target results come from
   the branch B on the side s of the scrutinee L -}
reflect-branch : ∀ (s : Tag) (L B : AST) {ρ' ρ C} → Envs ρ' ρ
  → ∀ v → tag s v ∈ ⟦ delay L ⟧' ρ' → (∀ {a b} → tag s a ~ tag s b → a ~ b)
  → (nonempty (Untag s (⟦ L ⟧ ρ)) → ⟦ B ⟧ (Untag s (⟦ L ⟧ ρ) • ρ) ⊆ C)
  → ∀ V' k → mem V' ⊆ ⟦ delay B ⟧' (Untag s (⟦ delay L ⟧' ρ') • ρ') → Bnd k V' → R k V' C
reflect-branch s L B {ρ'}{ρ} E v sv s~ B⊆ V' k V'⊆ bV =
  R-mono k (B⊆ NE-s) (delay-reflect B (envs NE' ρ'~' ρ⊳') V' k V'⊆ bV)
  where
  open Envs E
  NE-s = Obs.nonempty-obs (tag-reflect L E s (v ∷ []) (suc (depth v)) (single⊆ sv) (Bnd-single v))
           (λ ())
  NE' : nonempty-env (Untag s (⟦ L ⟧ ρ) • ρ)
  NE' zero = NE-s
  NE' (suc x) = NE x
  ρ'~' : ∀ x → consis ((Untag s (⟦ delay L ⟧' ρ') • ρ') x)
  ρ'~' zero a b a∈ b∈ = s~ (⟦⟧'-consis (delay L) ρ' ρ'~ _ _ a∈ b∈)
  ρ'~' (suc x) = ρ'~ x
  ρ⊳' : (Untag s (⟦ delay L ⟧' ρ') • ρ') ⊳ₑ (Untag s (⟦ L ⟧ ρ) • ρ)
  ρ⊳' zero = tag-reflect L E s
  ρ⊳' (suc x) = ρ⊳ x

ℒ-ne : ∀ {D : 𝒫 Value} v → v ∈ ℒ ⟨ D , ptt ⟩ → nonempty D
ℒ-ne (left d) d∈ = ⟨ d , d∈ ⟩

ℛ-ne : ∀ {D : 𝒫 Value} v → v ∈ ℛ ⟨ D , ptt ⟩ → nonempty D
ℛ-ne (right d) d∈ = ⟨ d , d∈ ⟩

pair-ne : ∀ {A B : 𝒫 Value} v → v ∈ pair ⟨ A , ⟨ B , ptt ⟩ ⟩ → nonempty B
pair-ne ⦅ f ∣ ⟨ v , ⟨ _ , v∈ ⟩ ⟩ = ⟨ v , v∈ ⟩
pair-ne ∣ v ⦆ ⟨ f , ⟨ _ , v∈ ⟩ ⟩ = ⟨ v , v∈ ⟩

pair-tag : ∀ {A B : 𝒫 Value} t {d} → tag t d ∈ pair ⟨ A , ⟨ B , ptt ⟩ ⟩ → Data.Empty.⊥
pair-tag (tupT i) ()
pair-tag leftT ()
pair-tag rightT ()

delay-reflect (` x) E = Envs.ρ⊳ E x

delay-reflect (app ⦅ L ,, N ,, Nil ⦆) {ρ'} E V' k V'⊆ bV
    with collect (⟦ delay L ⟧' ρ') (⟦ delay N ⟧' ρ') V'
           (λ d d∈ → proj₁ (let-app-≃ (delay L) (delay N) ρ') d (V'⊆ d d∈))
... | ⟨ W , ⟨ U , ⟨ W⊆L' , ⟨ U⊆N' , cs ⟩ ⟩ ⟩ ⟩ =
  R-irr (depths W) k (Bnd-Calls-apps (Bnd-depths W) cs) bV
    (Obs.app-obs (delay-reflect L E W (suc (depths W)) W⊆L' (Bnd-depths W))
       cs _ U~ (delay-reflect N E U (depths W) U⊆N' (Bnd-Calls-args (Bnd-depths W) cs)))
  where
  U~ : consis (mem U)
  U~ a b a∈ b∈ = ⟦⟧'-consis (delay N) ρ' (Envs.ρ'~ E) a b (U⊆N' a a∈) (U⊆N' b b∈)

delay-reflect (lit B c ⦅ Nil ⦆) E V' k V'⊆ bV = R-flat k V'⊆ (λ v v∈ → ℬ-flat v (V'⊆ v v∈))

delay-reflect (tuple n ⦅ args ⦆) = reflect-𝒯 args

delay-reflect (get i ⦅ M ,, Nil ⦆) E = tag-reflect M E (tupT i)

delay-reflect (inl-op ⦅ M ,, Nil ⦆) E V' zero V'⊆ bV = ptt
delay-reflect (inl-op ⦅ M ,, Nil ⦆) E V' (suc k) V'⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → let ⟨ v , v∈ ⟩ = ne-mem ne V'⊆
                              ⟨ m , m∈ ⟩ = ne-reflect M E (ℒ-ne v v∈) in ⟨ left m , m∈ ⟩
  ; app-obs = λ cs _ _ _ → R-∅ k (Calls-none (λ u u∈ → V'⊆ _ u∈) cs)
  ; tag-obs = λ { leftT W W⊆ →
                    delay-reflect M E W k (λ d d∈ → V'⊆ _ (W⊆ d d∈)) (Bnd-Untag leftT bV W⊆)
                ; rightT W W⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W⊆ d d∈)) }
  }

delay-reflect (inr-op ⦅ M ,, Nil ⦆) E V' zero V'⊆ bV = ptt
delay-reflect (inr-op ⦅ M ,, Nil ⦆) E V' (suc k) V'⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → let ⟨ v , v∈ ⟩ = ne-mem ne V'⊆
                              ⟨ m , m∈ ⟩ = ne-reflect M E (ℛ-ne v v∈) in ⟨ right m , m∈ ⟩
  ; app-obs = λ cs _ _ _ → R-∅ k (Calls-none (λ u u∈ → V'⊆ _ u∈) cs)
  ; tag-obs = λ { rightT W W⊆ →
                    delay-reflect M E W k (λ d d∈ → V'⊆ _ (W⊆ d d∈)) (Bnd-Untag rightT bV W⊆)
                ; leftT W W⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W⊆ d d∈)) }
  }

delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) E [] k V'⊆ bV = R-∅ k (λ _ ())
delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ'}{ρ} E (w ∷ V') k V'⊆ bV
    with V'⊆ w (here refl)
... | inj₁ ⟨ v , ⟨ _ , ⟨ allL , _ ⟩ ⟩ ⟩ =
  reflect-branch leftT L M E v lv (λ a~b → a~b) M⊆ (w ∷ V') k V'⊆F bV
  where
  lv = allL v (here refl)
  M⊆ : nonempty (Lefts (⟦ L ⟧ ρ)) → ⟦ M ⟧ (Lefts (⟦ L ⟧ ρ) • ρ) ⊆ _
  M⊆ ne x x∈ = let ⟨ u , ⟨ U , ⟨ s , x∈' ⟩ ⟩ ⟩ = cont-0 M (Envs.NE E) ne x x∈
               in inj₁ ⟨ u , ⟨ U , ⟨ s , x∈' ⟩ ⟩ ⟩
  V'⊆F : mem (w ∷ V') ⊆ ⟦ delay M ⟧' (Lefts (⟦ delay L ⟧' ρ') • ρ')
  V'⊆F x x∈ with V'⊆ x x∈
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL' , x∈F ⟩ ⟩ ⟩ =
    S4.⟦⟧-monotone (delay M) (λ { zero → allL' ; (suc y) → λ d z → z }) x x∈F
  ... | inj₂ ⟨ u , ⟨ U , ⟨ allR , _ ⟩ ⟩ ⟩ =
    ⊥-elim (⟦⟧'-consis (delay L) ρ' (Envs.ρ'~ E) _ _ lv (allR u (here refl)))
... | inj₂ ⟨ v , ⟨ _ , ⟨ allR , _ ⟩ ⟩ ⟩ =
  reflect-branch rightT L N E v rv (λ a~b → a~b) N⊆ (w ∷ V') k V'⊆G bV
  where
  rv = allR v (here refl)
  N⊆ : nonempty (Rights (⟦ L ⟧ ρ)) → ⟦ N ⟧ (Rights (⟦ L ⟧ ρ) • ρ) ⊆ _
  N⊆ ne x x∈ = let ⟨ u , ⟨ U , ⟨ s , x∈' ⟩ ⟩ ⟩ = cont-0 N (Envs.NE E) ne x x∈
               in inj₂ ⟨ u , ⟨ U , ⟨ s , x∈' ⟩ ⟩ ⟩
  V'⊆G : mem (w ∷ V') ⊆ ⟦ delay N ⟧' (Rights (⟦ delay L ⟧' ρ') • ρ')
  V'⊆G x x∈ with V'⊆ x x∈
  ... | inj₂ ⟨ u , ⟨ U , ⟨ allR' , x∈G ⟩ ⟩ ⟩ =
    S4.⟦⟧-monotone (delay N) (λ { zero → allR' ; (suc y) → λ d z → z }) x x∈G
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL , _ ⟩ ⟩ ⟩ =
    ⊥-elim (⟦⟧'-consis (delay L) ρ' (Envs.ρ'~ E) _ _ rv (allL u (here refl)))

delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) E V' zero V'⊆ bV = ptt
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) {ρ'}{ρ} E V' (suc k) V'⊆ bV =
  record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → let ⟨ t , t∈ ⟩ = T-ne (let ⟨ v , v∈ ⟩ = ne-mem ne V'⊆ in pair-ne v v∈)
                          in ⟨ ν , ⟨ t ∷ [] , ⟨ ⟨ tt , (λ ()) ⟩ , ⟨ single⊆ t∈ , (λ ()) ⟩ ⟩ ⟩ ⟩
  ; app-obs = clos-app k bV
  ; tag-obs = λ t W W⊆ → R-∅ k (λ d d∈ → pair-tag t (V'⊆ _ (W⊆ d d∈)))
  }
  where
  open Envs E
  T' = 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ')
  T = 𝒯 n (⟦ fvs ⟧₊ ρ)
  D = ⟦ clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆ ⟧ ρ

  T-ne : nonempty T' → nonempty T
  T-ne ⟨ t' , t'∈ ⟩ =
    Obs.nonempty-obs (reflect-𝒯 fvs E (t' ∷ []) (suc (depth t')) (single⊆ t'∈) (Bnd-single t')) (λ ())

  Cdrs⊆T' : Cdrs V' ⊆ T'
  Cdrs⊆T' fv e∈ = let ⟨ _ , ⟨ _ , fv∈ ⟩ ⟩ = V'⊆ _ e∈ in fv∈

  clos-app : ∀ j → Bnd (suc j) V' → ∀ {U' W'} → Calls V' U' W' → ∀ E → consis (mem U')
    → R j U' E → R j W' (D ● E)
  clos-app zero _ _ E _ _ = ptt
  clos-app (suc j) bV' [] E U'~ rU = R-∅ (suc j) (λ _ ())
  clos-app (suc j) bV' {U'} {w ∷ W'} cs Es U'~ rU =
    R-mono (suc j) (clos-β N NE-T NE-E)
      (delay-reflect N (envs NE-ρs ρ''~ ρ''⊳ρs) (w ∷ W') (suc j) W⊆B (Bnd-Calls-apps bV' cs))
    where
    wit = Calls-∈ cs (here refl)
    ent = Call.entry wit
    NE-E = Obs.nonempty-obs rU (ne-⊆ (Call.U₀⊆ wit) (Call.U₀≢[] wit))
    NE-T = T-ne (ne-mem (CarEntry.FV≢[] ent) (λ d d∈ → Cdrs⊆T' d (CarEntry.FV⊆ ent d d∈)))

    ρ'' : Env
    ρ'' = mem U' • Cdrs V' • (λ _ → Init)

    W⊆B : mem (w ∷ W') ⊆ ⟦ delay N ⟧' ρ''
    W⊆B x x∈ with Calls-∈ cs x∈
    ... | call U₀ (car-entry FV e∈ neFV FV⊆) neU U₀⊆ with V'⊆ _ e∈
    ... | ⟨ t , ⟨ ⟨ ⟨ x∈B , _ ⟩ , _ ⟩ , _ ⟩ ⟩ =
      S4.⟦⟧-monotone (delay N) (λ { zero → U₀⊆ ; (suc zero) → FV⊆ ; (suc (suc y)) → λ d z → z })
        x x∈B

    ρ''~ : ∀ y → consis (ρ'' y)
    ρ''~ zero = U'~
    ρ''~ (suc zero) a b a∈ b∈ =
      ⟦⟧'-consis (tuple n ⦅ del-map-args fvs ⦆') ρ' ρ'~ a b (Cdrs⊆T' a a∈) (Cdrs⊆T' b b∈)
    ρ''~ (suc (suc y)) = Init-consis

    NE-ρs : nonempty-env (Es • T • (λ _ → Init))
    NE-ρs zero = NE-E
    NE-ρs (suc zero) = NE-T
    NE-ρs (suc (suc y)) = ⟨ ω , refl ⟩

    ρ''⊳ρs : ρ'' ⊳ₑ (Es • T • (λ _ → Init))
    ρ''⊳ρs zero Y' i Y'⊆ bY =
      R-irr (suc j) i (Bnd-⊆ Y'⊆ (Bnd-Calls-args bV' cs)) bY (R-⊆ (suc j) Y'⊆ rU)
    ρ''⊳ρs (suc zero) Y' i Y'⊆ bY = reflect-𝒯 fvs E Y' i (λ y y∈ → Cdrs⊆T' y (Y'⊆ y y∈)) bY
    ρ''⊳ρs (suc (suc x)) Y' i Y'⊆ bY = R-flat i Y'⊆ (λ v v∈ → Init-flat (Y'⊆ v v∈))

reflect-nth (M ,, args) E zero = delay-reflect M E
reflect-nth (M ,, args) E (suc i) = reflect-nth args E i

reflect-𝒯 {zero} args E V' k V'⊆ bV =
  R-flat k (λ v v∈ → proj₁ (𝒯0-flat v (V'⊆ v v∈))) (λ v v∈ → proj₂ (𝒯0-flat v (V'⊆ v v∈)))
reflect-𝒯 {suc n} args E V' zero V'⊆ bV = ptt
reflect-𝒯 {suc n} args {ρ'}{ρ} E V' (suc k) V'⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → tup-ne (ne-mem ne V'⊆)
  ; app-obs = λ cs _ _ _ → R-∅ k (Calls-none (λ u u∈ → V'⊆ _ u∈) cs)
  ; tag-obs = λ { (tupT i) W W⊆ → nth-case i W W⊆
                ; leftT W W⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W⊆ d d∈)) }
  }
  where
  Ds' = ⟦ del-map-args args ⟧₊' ρ'
  Ds = ⟦ args ⟧₊ ρ

  comp-ne : ∀ j → nonempty (nthD Ds' j) → nonempty (nthD Ds j)
  comp-ne j ⟨ d , d∈ ⟩ =
    Obs.nonempty-obs (reflect-nth args E j (d ∷ []) (suc (depth d)) (single⊆ d∈) (Bnd-single d)) (λ ())

  tup-ne : nonempty (𝒯 (suc n) Ds') → nonempty (𝒯 (suc n) Ds)
  tup-ne ⟨ tup[ i ] d , ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ ⟩ =
    let ⟨ d₀ , d₀∈ ⟩ = comp-ne i ⟨ d , d∈ ⟩ in ⟨ tup[ i ] d₀ , ⟨ refl , ⟨ d₀∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩ ⟩

  nth-case : ∀ {m} (i : Fin m) W' → mem W' ⊆ Untag (tupT i) (mem V')
    → R k W' (Untag (tupT i) (𝒯 (suc n) Ds))
  nth-case i [] _ = R-∅ k (λ _ ())
  nth-case i (w ∷ W') W'⊆ with V'⊆ _ (W'⊆ w (here refl))
  ... | ⟨ refl , ⟨ _ , ne ⟩ ⟩ =
    R-mono k (λ d d∈ → ⟨ refl , ⟨ d∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩)
      (reflect-nth args E i (w ∷ W') k sub (Bnd-Untag (tupT i) bV W'⊆))
    where
    sub : mem (w ∷ W') ⊆ nthD Ds' i
    sub d d∈ with V'⊆ _ (W'⊆ d d∈)
    ... | ⟨ refl , ⟨ d∈' , _ ⟩ ⟩ = d∈'

{- The end theorem (backward half) --------------------------------------------}

Envs₀ : Envs ρ₀ ρ₀
Envs₀ = envs (λ _ → ⟨ ω , refl ⟩) (λ _ → Init-consis) Init⊳Init

reflect-const : ∀ (M : AST) {B} (c : base-rep B)
  → const c ∈ ⟦ delay M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀
reflect-const M c c∈ =
  Obs.const-obs (delay-reflect M Envs₀ (const c ∷ []) 1 (single⊆ c∈) (Bnd-single (const c)))
    c (here refl)

reflect-nonempty : ∀ (M : AST) → nonempty (⟦ delay M ⟧' ρ₀) → nonempty (⟦ M ⟧ ρ₀)
reflect-nonempty M = ne-reflect M Envs₀
