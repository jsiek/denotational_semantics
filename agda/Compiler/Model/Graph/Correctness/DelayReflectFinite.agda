{-

  Backward (reflect) direction of the correctness of the delay pass
  (Clos3 → Clos4), using a logical relation indexed by *finite lists of
  target observations* (see issue #1).

  The relation R k V' D (see DelayFiniteRel) relates a finite list V' of
  target values to a source set D. Here it is instantiated with target
  application on the observed side (Args-of, Apps) and source application
  (_●_) on the other side.

  The function clause (app-obs) is the only place where the car and cdr
  halves of target closures meet, and they meet inside the finite list V',
  so junk entries and mixed closures never produce a target-only result.

  The proof uses two properties of the semantics:
  - target denotations are consistent (⟦⟧'-consis), which follows from the
    consistency of the target operators (𝕆-Clos4-consis);
  - source denotations are continuous (src-continuous), from
    NewSemantics.⟦⟧-continuous and the ContinuousSemantics instance in
    Sem.Clos3IswimContinuous.
-}

open import NewSigUtil
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
open import NewEnv using (nonempty-env; extend-nonempty-env; •-~)
open import NewDenotProperties using (Every)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon
open import Compiler.Model.Graph.Correctness.DelayApp using (let-app-≃)
import Compiler.Model.Graph.Sem.Clos3IswimContinuous as C3

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Level using (lift; lower)

module Compiler.Model.Graph.Correctness.DelayReflectFinite where

{- Observations of a finite list of target values ----------------------------}

{- the free variables stored in the cdr halves of V' -}
Cdrs : List Value → 𝒫 Value
Cdrs V' fv = ∣ fv ⦆ ⋵ V'

{- the arguments that the car halves of V' are prepared to accept -}
record ArgWit (V' : List Value) (u : Value) : Set where
  constructor argwit
  field
    FV U₀ : List Value
    w : Value
    entry∈ : ⦅ FV ↦ (U₀ ↦ w) ∣ ⋵ V'
    u∈U₀ : u ⋵ U₀

Args-of : List Value → 𝒫 Value
Args-of V' = ArgWit V'

{- the results of applying the car halves of V' to the cdr halves of V'
   and to the arguments U' -}
record AppWit (V' U' : List Value) (w : Value) : Set where
  constructor appwit
  field
    FV U₀ : List Value
    entry∈ : ⦅ FV ↦ (U₀ ↦ w) ∣ ⋵ V'
    FV≢[] : FV ≢ []
    FV⊆ : mem FV ⊆ Cdrs V'
    U₀≢[] : U₀ ≢ []
    U₀⊆ : mem U₀ ⊆ mem U'

Apps : List Value → List Value → 𝒫 Value
Apps V' U' = AppWit V' U'

d-arg : ∀ {u FV U₀ w} → u ⋵ U₀ → suc (depth u) ≤ depth ⦅ FV ↦ (U₀ ↦ w) ∣
d-arg {u}{FV}{U₀}{w} u∈ =
  s≤s (≤-trans (depth-⋵ u∈) (≤-trans (m≤m⊔n (depths U₀) (depth w))
      (≤-trans (n≤1+n _) (≤-trans (m≤n⊔m (depths FV) _) (n≤1+n _)))))

d-app : ∀ {FV U₀ w} → suc (depth w) ≤ depth ⦅ FV ↦ (U₀ ↦ w) ∣
d-app {FV}{U₀}{w} =
  s≤s (≤-trans (m≤n⊔m (depths U₀) (depth w))
      (≤-trans (n≤1+n _) (≤-trans (m≤n⊔m (depths FV) _) (n≤1+n _))))


Bnd-Args : ∀ {k V' U'} → Bnd (suc k) V' → mem U' ⊆ Args-of V' → Bnd k U'
Bnd-Args bV U'⊆ u u∈ with U'⊆ u u∈
... | argwit FV U₀ w e∈ u∈U₀ = <-shrink (d-arg {FV = FV}{w = w} u∈U₀) (bV _ e∈)

Bnd-Apps : ∀ {k V' U' W'} → Bnd (suc k) V' → mem W' ⊆ Apps V' U' → Bnd k W'
Bnd-Apps bV W'⊆ w w∈ with W'⊆ w w∈
... | appwit FV U₀ e∈ _ _ _ _ = <-shrink (d-app {FV}{U₀}{w}) (bV _ e∈)


Cdrs-⊆ : ∀ {V₁ V₂} → mem V₁ ⊆ mem V₂ → Cdrs V₁ ⊆ Cdrs V₂
Cdrs-⊆ s fv e∈ = s _ e∈

Args-⊆ : ∀ {V₁ V₂} → mem V₁ ⊆ mem V₂ → Args-of V₁ ⊆ Args-of V₂
Args-⊆ s u (argwit FV U₀ w e∈ u∈) = argwit FV U₀ w (s _ e∈) u∈

Apps-⊆ : ∀ {V₁ V₂ U₁ U₂} → mem V₁ ⊆ mem V₂ → mem U₁ ⊆ mem U₂
       → Apps V₁ U₁ ⊆ Apps V₂ U₂
Apps-⊆ s t w (appwit FV U₀ e∈ neFV FV⊆ neU U₀⊆) =
  appwit FV U₀ (s _ e∈) neFV (λ d d∈ → Cdrs-⊆ s d (FV⊆ d d∈)) neU
         (λ d d∈ → t d (U₀⊆ d d∈))


Apps-flat : ∀ {V' U'} → (∀ v → v ⋵ V' → Flat v) → Apps V' U' ⊆ ∅
Apps-flat fl w (appwit FV U₀ e∈ _ _ _ _) = flat-car (fl _ e∈)

{- The relation ---------------------------------------------------------------}

open import Compiler.Model.Graph.Correctness.DelayFiniteRel
  Args-of Apps _●_ (λ U' → consis (mem U'))
  Args-⊆ (λ s → Apps-⊆ s (λ d z → z)) Apps-flat ●-mono-l Bnd-Args Bnd-Apps
  public

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

{- source denotations are continuous -}
src-continuous : ∀ (M : AST) (ρ : Env) → nonempty-env ρ → ∀ v → v ∈ ⟦ M ⟧ ρ
  → Σ[ Vs ∈ (Var → List Value) ] (∀ x → Vs x ≢ [] × mem (Vs x) ⊆ ρ x)
                                 × v ∈ ⟦ M ⟧ (λ x → mem (Vs x))
src-continuous = C3.term-continuous

cont-1 : ∀ (M : AST) (ρ : Env) (X : 𝒫 Value) → nonempty-env ρ → nonempty X
  → ∀ x → x ∈ ⟦ M ⟧ (X • ρ)
  → Σ[ u ∈ Value ] Σ[ U ∈ List Value ] mem (u ∷ U) ⊆ X × x ∈ ⟦ M ⟧ (mem (u ∷ U) • ρ)
cont-1 M ρ X NE NE-X x x∈ = go (src-continuous M (X • ρ) (extend-nonempty-env NE NE-X) x x∈)
  where
  helper : ∀ V → V ≢ [] → mem V ⊆ X → x ∈ ⟦ M ⟧ (mem V • ρ)
    → Σ[ u ∈ Value ] Σ[ U ∈ List Value ] mem (u ∷ U) ⊆ X × x ∈ ⟦ M ⟧ (mem (u ∷ U) • ρ)
  helper [] ne _ _ = ⊥-elim (ne refl)
  helper (u ∷ U) _ sub x∈' = ⟨ u , ⟨ U , ⟨ sub , x∈' ⟩ ⟩ ⟩

  env⊆ : ∀ (Vs : Var → List Value) → (∀ y → Vs y ≢ [] × mem (Vs y) ⊆ (X • ρ) y)
    → ∀ y → mem (Vs y) ⊆ (mem (Vs 0) • ρ) y
  env⊆ Vs ok zero = λ d z → z
  env⊆ Vs ok (suc y) = proj₂ (ok (suc y))

  go : (Σ[ Vs ∈ (Var → List Value) ] (∀ y → Vs y ≢ [] × mem (Vs y) ⊆ (X • ρ) y)
                                     × x ∈ ⟦ M ⟧ (λ y → mem (Vs y)))
    → Σ[ u ∈ Value ] Σ[ U ∈ List Value ] mem (u ∷ U) ⊆ X × x ∈ ⟦ M ⟧ (mem (u ∷ U) • ρ)
  go ⟨ Vs , ⟨ ok , x∈fin ⟩ ⟩ =
    helper (Vs 0) (proj₁ (ok 0)) (proj₂ (ok 0))
      (S3.⟦⟧-monotone {ρ = λ y → mem (Vs y)} {ρ′ = mem (Vs 0) • ρ} M (env⊆ Vs ok) x x∈fin)


{- Collecting the finite witnesses of a target application -------------------}

collect-cdrs : ∀ (L' : 𝒫 Value) FV → mem FV ⊆ Cdr L'
  → Σ[ C ∈ List Value ] mem C ⊆ L' × mem FV ⊆ Cdrs C
collect-cdrs L' FV FV⊆ = ⟨ lmap ∣_⦆ FV , ⟨ G , (λ fv fv∈ → ∈-map⁺ ∣_⦆ fv∈) ⟩ ⟩
  where
  G : mem (lmap ∣_⦆ FV) ⊆ L'
  G d d∈ with ∈-map⁻ ∣_⦆ d∈
  ... | ⟨ fv , ⟨ fv∈ , refl ⟩ ⟩ = FV⊆ fv fv∈

collect : ∀ (L' N' : 𝒫 Value) V' → mem V' ⊆ ((Car L' ● Cdr L') ● N')
  → Σ[ W ∈ List Value ] Σ[ U ∈ List Value ]
      mem W ⊆ L' × mem U ⊆ N' × mem V' ⊆ Apps W U × mem U ⊆ Args-of W
collect L' N' [] _ =
  ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩ ⟩ ⟩ ⟩
collect L' N' (w ∷ V') V'⊆
    with V'⊆ w (here refl) | collect L' N' V' (λ d d∈ → V'⊆ d (there d∈))
... | ⟨ U₀ , ⟨ ⟨ FV , ⟨ e∈L' , ⟨ FV⊆Cdr , neFV ⟩ ⟩ ⟩ , ⟨ U₀⊆N' , neU₀ ⟩ ⟩ ⟩
    | ⟨ W , ⟨ U , ⟨ W⊆ , ⟨ U⊆ , ⟨ V'⊆A , U⊆A ⟩ ⟩ ⟩ ⟩ ⟩
    with collect-cdrs L' FV FV⊆Cdr
... | ⟨ C , ⟨ C⊆L' , FV⊆C ⟩ ⟩ =
  ⟨ e ∷ (C ++ W) , ⟨ U₀ ++ U , ⟨ W⊆' , ⟨ U⊆' , ⟨ A' , UA' ⟩ ⟩ ⟩ ⟩ ⟩
  where
  e = ⦅ FV ↦ (U₀ ↦ w) ∣
  inC : mem C ⊆ mem (e ∷ (C ++ W))
  inC d d∈ = there (∈-++⁺ˡ d∈)
  inW : mem W ⊆ mem (e ∷ (C ++ W))
  inW d d∈ = there (∈-++⁺ʳ C d∈)
  inU : mem U ⊆ mem (U₀ ++ U)
  inU d d∈ = ∈-++⁺ʳ U₀ d∈

  W⊆' : mem (e ∷ (C ++ W)) ⊆ L'
  W⊆' _ (here refl) = e∈L'
  W⊆' d (there d∈) with ∈-++⁻ C d∈
  ... | inj₁ d∈C = C⊆L' d d∈C
  ... | inj₂ d∈W = W⊆ d d∈W

  U⊆' : mem (U₀ ++ U) ⊆ N'
  U⊆' d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = U₀⊆N' d d∈U₀
  ... | inj₂ d∈U = U⊆ d d∈U

  A' : mem (w ∷ V') ⊆ Apps (e ∷ (C ++ W)) (U₀ ++ U)
  A' _ (here refl) =
    appwit FV U₀ (here refl) neFV (λ d d∈ → Cdrs-⊆ inC d (FV⊆C d d∈)) neU₀
           (λ d d∈ → ∈-++⁺ˡ d∈)
  A' d (there d∈) = Apps-⊆ inW inU d (V'⊆A d d∈)

  UA' : mem (U₀ ++ U) ⊆ Args-of (e ∷ (C ++ W))
  UA' d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = argwit FV U₀ w (here refl) d∈U₀
  ... | inj₂ d∈U = Args-⊆ inW d (U⊆A d d∈U)

{- The fundamental lemma ------------------------------------------------------}

delay-reflect : ∀ (M : AST) (ρ' ρ : Env) → nonempty-env ρ → (∀ x → consis (ρ' x))
  → ρ' ⊳ₑ ρ
  → ∀ V' k → mem V' ⊆ ⟦ delay M ⟧' ρ' → Bnd k V' → R k V' (⟦ M ⟧ ρ)

reflect-nth : ∀ {n} (args : L3.Args (replicate n ■)) (ρ' ρ : Env) → nonempty-env ρ
  → (∀ x → consis (ρ' x)) → ρ' ⊳ₑ ρ
  → (i : Fin n) → ∀ V' k → mem V' ⊆ nthD (⟦ del-map-args args ⟧₊' ρ') i → Bnd k V'
  → R k V' (nthD (⟦ args ⟧₊ ρ) i)

reflect-𝒯 : ∀ {n} (args : L3.Args (replicate n ■)) (ρ' ρ : Env) → nonempty-env ρ
  → (∀ x → consis (ρ' x)) → ρ' ⊳ₑ ρ
  → ∀ V' k → mem V' ⊆ 𝒯 n (⟦ del-map-args args ⟧₊' ρ') → Bnd k V'
  → R k V' (𝒯 n (⟦ args ⟧₊ ρ))

reflect-clos : ∀ n (N : AST) (fvs : L3.Args (replicate n ■)) (ρ' ρ : Env)
  → nonempty-env ρ → (∀ x → consis (ρ' x)) → ρ' ⊳ₑ ρ
  → ∀ V' k → mem V' ⊆ ⟦ delay (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ⟧' ρ'
  → Bnd k V' → R k V' (⟦ clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆ ⟧ ρ)

reflect-case-left : ∀ (L M N : AST) (ρ' ρ : Env) → nonempty-env ρ
  → (∀ x → consis (ρ' x)) → ρ' ⊳ₑ ρ
  → ∀ v → left v ∈ ⟦ delay L ⟧' ρ'
  → ∀ V' k → mem V' ⊆ ⟦ delay (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ' → Bnd k V'
  → R k V' (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ)

reflect-case-right : ∀ (L M N : AST) (ρ' ρ : Env) → nonempty-env ρ
  → (∀ x → consis (ρ' x)) → ρ' ⊳ₑ ρ
  → ∀ v → right v ∈ ⟦ delay L ⟧' ρ'
  → ∀ V' k → mem V' ⊆ ⟦ delay (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ⟧' ρ' → Bnd k V'
  → R k V' (⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ)

delay-reflect (` x) ρ' ρ NE ρ'~ ρ⊳ = ρ⊳ x

delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) =
  reflect-clos n N fvs

delay-reflect (app ⦅ L ,, N ,, Nil ⦆) ρ' ρ NE ρ'~ ρ⊳ V' k V'⊆ bV
    with collect (⟦ delay L ⟧' ρ') (⟦ delay N ⟧' ρ') V'
           (λ d d∈ → proj₁ (let-app-≃ (delay L) (delay N) ρ') d (V'⊆ d d∈))
... | ⟨ W , ⟨ U , ⟨ W⊆L' , ⟨ U⊆N' , ⟨ V'⊆Apps , U⊆Args ⟩ ⟩ ⟩ ⟩ ⟩ =
  R-irr (depths W) k (Bnd-Apps (Bnd-depths W) V'⊆Apps) bV
    (Obs.app-obs (delay-reflect L ρ' ρ NE ρ'~ ρ⊳ W (suc (depths W)) W⊆L' (Bnd-depths W))
       U (⟦ N ⟧ ρ) U⊆Args U~
       (delay-reflect N ρ' ρ NE ρ'~ ρ⊳ U (depths W) U⊆N' (Bnd-Args (Bnd-depths W) U⊆Args))
       V' V'⊆Apps)
  where
  N'~ = ⟦⟧'-consis (delay N) ρ' ρ'~
  U~ : consis (mem U)
  U~ a b a∈ b∈ = N'~ a b (U⊆N' a a∈) (U⊆N' b b∈)

delay-reflect (lit B c ⦅ Nil ⦆) ρ' ρ NE ρ'~ ρ⊳ V' k V'⊆ bV =
  R-flat k V'⊆ (λ v v∈ → ℬ-flat v (V'⊆ v v∈))

delay-reflect (tuple n ⦅ args ⦆) = reflect-𝒯 args

delay-reflect (get i ⦅ M ,, Nil ⦆) ρ' ρ NE ρ'~ ρ⊳ V' k V'⊆ bV =
  Obs.nth-obs (delay-reflect M ρ' ρ NE ρ'~ ρ⊳ (lmap tupi V') (suc k) mV bm) i V'
    (λ d d∈ → ∈-map⁺ tupi d∈)
  where
  tupi = λ d → tup[ i ] d
  mV : mem (lmap tupi V') ⊆ ⟦ delay M ⟧' ρ'
  mV d d∈ with ∈-map⁻ tupi d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = V'⊆ x x∈
  bm : Bnd (suc k) (lmap tupi V')
  bm d d∈ with ∈-map⁻ tupi d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = s≤s (bV x x∈)

delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ' ρ NE ρ'~ ρ⊳ V' zero V'⊆ bV = ptt
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ' ρ NE ρ'~ ρ⊳ V' (suc k) V'⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; ω-obs = λ ω∈ → ⊥-elim (V'⊆ _ ω∈)
  ; nonempty-obs = λ ne → inl-ne (ne-head ne)
  ; app-obs = λ U' E _ _ _ W' W'⊆ →
      R-∅ k (λ w w∈ → V'⊆ _ (AppWit.entry∈ (W'⊆ w w∈)))
  ; nth-obs = λ i W' W'⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W'⊆ d d∈))
  ; left-obs = λ W' W'⊆ →
      delay-reflect M ρ' ρ NE ρ'~ ρ⊳ W' k (λ d d∈ → V'⊆ _ (W'⊆ d d∈)) (Bnd-Lefts bV W'⊆)
  ; right-obs = λ W' W'⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W'⊆ d d∈))
  }
  where
  inl-ne : Σ[ v ∈ Value ] v ⋵ V' → nonempty (ℒ ⟨ ⟦ M ⟧ ρ , ptt ⟩)
  inl-ne ⟨ v , v∈ ⟩ with ℒ-inv v (V'⊆ v v∈)
  ... | ⟨ d , ⟨ refl , d∈ ⟩ ⟩
      with Obs.nonempty-obs (delay-reflect M ρ' ρ NE ρ'~ ρ⊳ (d ∷ []) (suc (depth d))
                                (single⊆ d∈) (Bnd-single d)) (λ ())
  ... | ⟨ m , m∈ ⟩ = ⟨ left m , m∈ ⟩

delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ' ρ NE ρ'~ ρ⊳ V' zero V'⊆ bV = ptt
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ' ρ NE ρ'~ ρ⊳ V' (suc k) V'⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; ω-obs = λ ω∈ → ⊥-elim (V'⊆ _ ω∈)
  ; nonempty-obs = λ ne → inr-ne (ne-head ne)
  ; app-obs = λ U' E _ _ _ W' W'⊆ →
      R-∅ k (λ w w∈ → V'⊆ _ (AppWit.entry∈ (W'⊆ w w∈)))
  ; nth-obs = λ i W' W'⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W'⊆ d d∈))
  ; left-obs = λ W' W'⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W'⊆ d d∈))
  ; right-obs = λ W' W'⊆ →
      delay-reflect M ρ' ρ NE ρ'~ ρ⊳ W' k (λ d d∈ → V'⊆ _ (W'⊆ d d∈)) (Bnd-Rights bV W'⊆)
  }
  where
  inr-ne : Σ[ v ∈ Value ] v ⋵ V' → nonempty (ℛ ⟨ ⟦ M ⟧ ρ , ptt ⟩)
  inr-ne ⟨ v , v∈ ⟩ with ℛ-inv v (V'⊆ v v∈)
  ... | ⟨ d , ⟨ refl , d∈ ⟩ ⟩
      with Obs.nonempty-obs (delay-reflect M ρ' ρ NE ρ'~ ρ⊳ (d ∷ []) (suc (depth d))
                                (single⊆ d∈) (Bnd-single d)) (λ ())
  ... | ⟨ m , m∈ ⟩ = ⟨ right m , m∈ ⟩

delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ' ρ NE ρ'~ ρ⊳ [] k V'⊆ bV =
  R-∅ k (λ _ ())
delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ' ρ NE ρ'~ ρ⊳ (w ∷ V') k V'⊆ bV
    with V'⊆ w (here refl)
... | inj₁ ⟨ v , ⟨ V , ⟨ allL , _ ⟩ ⟩ ⟩ =
  reflect-case-left L M N ρ' ρ NE ρ'~ ρ⊳ v (allL v (here refl)) (w ∷ V') k V'⊆ bV
... | inj₂ ⟨ v , ⟨ V , ⟨ allR , _ ⟩ ⟩ ⟩ =
  reflect-case-right L M N ρ' ρ NE ρ'~ ρ⊳ v (allR v (here refl)) (w ∷ V') k V'⊆ bV

reflect-nth {suc n} (M ,, args) ρ' ρ NE ρ'~ ρ⊳ zero = delay-reflect M ρ' ρ NE ρ'~ ρ⊳
reflect-nth {suc n} (M ,, args) ρ' ρ NE ρ'~ ρ⊳ (suc i) = reflect-nth args ρ' ρ NE ρ'~ ρ⊳ i

reflect-𝒯 {zero} args ρ' ρ NE ρ'~ ρ⊳ V' k V'⊆ bV =
  R-flat k (λ v v∈ → proj₁ (𝒯0-flat v (V'⊆ v v∈))) (λ v v∈ → proj₂ (𝒯0-flat v (V'⊆ v v∈)))
reflect-𝒯 {suc n} args ρ' ρ NE ρ'~ ρ⊳ V' zero V'⊆ bV = ptt
reflect-𝒯 {suc n} args ρ' ρ NE ρ'~ ρ⊳ V' (suc k) V'⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; ω-obs = λ ω∈ → ⊥-elim (V'⊆ _ ω∈)
  ; nonempty-obs = λ ne → tup-ne (ne-head ne)
  ; app-obs = λ U' E _ _ _ W' W'⊆ →
      R-∅ k (λ w w∈ → V'⊆ _ (AppWit.entry∈ (W'⊆ w w∈)))
  ; nth-obs = nth-case
  ; left-obs = λ W' W'⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W'⊆ d d∈))
  ; right-obs = λ W' W'⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W'⊆ d d∈))
  }
  where
  Ds' = ⟦ del-map-args args ⟧₊' ρ'
  Ds = ⟦ args ⟧₊ ρ

  {- each nonempty component on one side is nonempty on the other -}
  comp-ne : ∀ j → nonempty (nthD Ds' j) → nonempty (nthD Ds j)
  comp-ne j ⟨ d , d∈ ⟩ =
    Obs.nonempty-obs (reflect-nth args ρ' ρ NE ρ'~ ρ⊳ j (d ∷ []) (suc (depth d))
                        (single⊆ d∈) (Bnd-single d)) (λ ())

  tup-ne' : ∀ v → v ∈ 𝒯 (suc n) Ds' → nonempty (𝒯 (suc n) Ds)
  tup-ne' (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ with comp-ne i ⟨ d , d∈ ⟩
  ... | ⟨ d₀ , d₀∈ ⟩ = ⟨ tup[ i ] d₀ , ⟨ refl , ⟨ d₀∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩ ⟩
  tup-ne' (const k) ()
  tup-ne' (V ↦ w) ()
  tup-ne' ν ()
  tup-ne' ω ()
  tup-ne' ⦅ u ∣ ()
  tup-ne' ∣ v ⦆ ()
  tup-ne' (left d) ()
  tup-ne' (right d) ()

  tup-ne : Σ[ v ∈ Value ] v ⋵ V' → nonempty (𝒯 (suc n) Ds)
  tup-ne ⟨ v , v∈ ⟩ = tup-ne' v (V'⊆ v v∈)

  nth-case : ∀ {m} (i : Fin m) W' → mem W' ⊆ Nths i V' → R k W' (Nth i (𝒯 (suc n) Ds))
  nth-case i [] _ = R-∅ k (λ _ ())
  nth-case i (w ∷ W') W'⊆ with V'⊆ _ (W'⊆ w (here refl))
  ... | ⟨ refl , ⟨ _ , ne ⟩ ⟩ =
    R-mono k (λ d d∈ → ⟨ refl , ⟨ d∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩)
      (reflect-nth args ρ' ρ NE ρ'~ ρ⊳ i (w ∷ W') k sub (Bnd-Nths bV W'⊆))
    where
    sub : mem (w ∷ W') ⊆ nthD Ds' i
    sub d d∈ with V'⊆ _ (W'⊆ d d∈)
    ... | ⟨ refl , ⟨ d∈' , _ ⟩ ⟩ = d∈'

reflect-clos n N fvs ρ' ρ NE ρ'~ ρ⊳ V' zero V'⊆ bV = ptt
reflect-clos n N fvs ρ' ρ NE ρ'~ ρ⊳ V' (suc k) V'⊆ bV = record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; ω-obs = λ ω∈ → ⊥-elim (V'⊆ _ ω∈)
  ; nonempty-obs = λ ne → D-ne (ne-head ne)
  ; app-obs = clos-app k bV
  ; nth-obs = λ i W' W'⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W'⊆ d d∈))
  ; left-obs = λ W' W'⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W'⊆ d d∈))
  ; right-obs = λ W' W'⊆ → R-∅ k (λ d d∈ → V'⊆ _ (W'⊆ d d∈))
  }
  where
  T' = 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ')
  T = 𝒯 n (⟦ fvs ⟧₊ ρ)
  D = ⟦ clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆ ⟧ ρ

  T'~ : consis T'
  T'~ = ⟦⟧'-consis (tuple n ⦅ del-map-args fvs ⦆') ρ' ρ'~

  T-ne : nonempty T' → nonempty T
  T-ne ⟨ t' , t'∈ ⟩ =
    Obs.nonempty-obs (reflect-𝒯 fvs ρ' ρ NE ρ'~ ρ⊳ (t' ∷ []) (suc (depth t'))
                        (single⊆ t'∈) (Bnd-single t')) (λ ())

  {- a source closure contains ν as soon as its environment is nonempty -}
  D-ne : Σ[ v ∈ Value ] v ⋵ V' → nonempty D
  D-ne ⟨ v , v∈ ⟩ with T-ne (pair-ne v (V'⊆ v v∈))
  ... | ⟨ t , t∈ ⟩ = ⟨ ν , ⟨ t ∷ [] , ⟨ ⟨ tt , (λ ()) ⟩ , ⟨ single⊆ t∈ , (λ ()) ⟩ ⟩ ⟩ ⟩

  Cdrs⊆T' : Cdrs V' ⊆ T'
  Cdrs⊆T' fv e∈ = cdr-pair {B = T'} (V'⊆ _ e∈)

  clos-app : ∀ j → Bnd (suc j) V' → ∀ U' E → mem U' ⊆ Args-of V' → consis (mem U')
    → R j U' E → ∀ W' → mem W' ⊆ Apps V' U' → R j W' (D ● E)
  clos-app zero _ U' E _ _ _ W' _ = ptt
  clos-app (suc j) bV' U' E U'⊆ U'~ rU [] _ = R-∅ (suc j) (λ _ ())
  clos-app (suc j) bV' U' E U'⊆ U'~ rU (w ∷ W') W'⊆ = R-mono (suc j) N⊆ IH
    where
    wit = W'⊆ w (here refl)

    NE-E : nonempty E
    NE-E = Obs.nonempty-obs rU (ne-⊆ (AppWit.U₀⊆ wit) (AppWit.U₀≢[] wit))

    NE-T : nonempty T
    NE-T = T-ne (ne-mem (AppWit.FV≢[] wit) (λ d d∈ → Cdrs⊆T' d (AppWit.FV⊆ wit d d∈)))

    ρs : Env
    ρs = E • T • (λ _ → Init)

    ρ'' : Env
    ρ'' = mem U' • Cdrs V' • (λ _ → Init)

    W⊆B : mem (w ∷ W') ⊆ ⟦ delay N ⟧' ρ''
    W⊆B x x∈ with W'⊆ x x∈
    ... | appwit FV U₀ e∈ neFV FV⊆ neU U₀⊆ with V'⊆ _ e∈
    ... | ⟨ t , ⟨ ⟨ ⟨ x∈B , _ ⟩ , _ ⟩ , _ ⟩ ⟩ =
      S4.⟦⟧-monotone {ρ = mem U₀ • mem FV • (λ _ → Init)} {ρ′ = ρ''} (delay N) env⊆ x x∈B
      where
      env⊆ : ∀ y → (mem U₀ • mem FV • (λ _ → Init)) y ⊆ ρ'' y
      env⊆ zero = U₀⊆
      env⊆ (suc zero) = FV⊆
      env⊆ (suc (suc y)) = λ d z → z

    ρ''~ : ∀ y → consis (ρ'' y)
    ρ''~ zero = U'~
    ρ''~ (suc zero) a b a∈ b∈ = T'~ a b (Cdrs⊆T' a a∈) (Cdrs⊆T' b b∈)
    ρ''~ (suc (suc y)) = Init-consis

    NE-ρs : nonempty-env ρs
    NE-ρs zero = NE-E
    NE-ρs (suc zero) = NE-T
    NE-ρs (suc (suc y)) = ⟨ ω , refl ⟩

    ρ''⊳ρs : ρ'' ⊳ₑ ρs
    ρ''⊳ρs zero Y' i Y'⊆ bY =
      R-irr (suc j) i (Bnd-⊆ Y'⊆ (Bnd-Args bV' U'⊆)) bY (R-⊆ (suc j) Y'⊆ rU)
    ρ''⊳ρs (suc zero) Y' i Y'⊆ bY =
      reflect-𝒯 fvs ρ' ρ NE ρ'~ ρ⊳ Y' i (λ y y∈ → Cdrs⊆T' y (Y'⊆ y y∈)) bY
    ρ''⊳ρs (suc (suc x)) Y' i Y'⊆ bY = R-flat i Y'⊆ (λ v v∈ → Init-flat (Y'⊆ v v∈))

    IH : R (suc j) (w ∷ W') (⟦ N ⟧ ρs)
    IH = delay-reflect N ρ'' ρs NE-ρs ρ''~ ρ''⊳ρs (w ∷ W') (suc j) W⊆B (Bnd-Apps bV' W'⊆)

    {- the beta rule for early application, using continuity -}
    N⊆ : ⟦ N ⟧ ρs ⊆ (D ● E)
    N⊆ x x∈ with src-continuous N ρs NE-ρs x x∈
    ... | ⟨ Vs , ⟨ ok , x∈fin ⟩ ⟩ =
      ⟨ Vs 0 , ⟨ ⟨ Vs 1 , ⟨ ⟨ ⟨ x∈' , proj₁ (ok 0) ⟩ , proj₁ (ok 1) ⟩
                          , ⟨ proj₂ (ok 1) , proj₁ (ok 1) ⟩ ⟩ ⟩
               , ⟨ proj₂ (ok 0) , proj₁ (ok 0) ⟩ ⟩ ⟩
      where
      env⊆ : ∀ y → mem (Vs y) ⊆ (mem (Vs 0) • mem (Vs 1) • (λ _ → Init)) y
      env⊆ zero = λ d z → z
      env⊆ (suc zero) = λ d z → z
      env⊆ (suc (suc y)) = proj₂ (ok (suc (suc y)))
      x∈' = S3.⟦⟧-monotone {ρ = λ y → mem (Vs y)}
                           {ρ′ = mem (Vs 0) • mem (Vs 1) • (λ _ → Init)} N env⊆ x x∈fin

reflect-case-left L M N ρ' ρ NE ρ'~ ρ⊳ v lv V' k V'⊆ bV = R-mono k M⊆ IH
  where
  L' = ⟦ delay L ⟧' ρ'
  L'~ = ⟦⟧'-consis (delay L) ρ' ρ'~

  {- by consistency, the target scrutinee has no right elements,
     so every element of V' comes from the left branch -}
  V'⊆F : mem V' ⊆ ⟦ delay M ⟧' (Lefts L' • ρ')
  V'⊆F x x∈ with V'⊆ x x∈
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL , x∈F ⟩ ⟩ ⟩ =
    S4.⟦⟧-monotone {ρ = mem (u ∷ U) • ρ'} {ρ′ = Lefts L' • ρ'} (delay M) env⊆ x x∈F
    where
    env⊆ : ∀ y → (mem (u ∷ U) • ρ') y ⊆ (Lefts L' • ρ') y
    env⊆ zero = allL
    env⊆ (suc y) = λ d z → z
  ... | inj₂ ⟨ u , ⟨ U , ⟨ allR , _ ⟩ ⟩ ⟩ = ⊥-elim (L'~ (left v) (right u) lv (allR u (here refl)))

  rL : ∀ Y' j → mem Y' ⊆ Lefts L' → Bnd j Y' → R j Y' (Lefts (⟦ L ⟧ ρ))
  rL Y' j Y'⊆ bY =
    Obs.left-obs (delay-reflect L ρ' ρ NE ρ'~ ρ⊳ (lmap left Y') (suc j) mY bm) Y'
      (λ d d∈ → ∈-map⁺ left d∈)
    where
    mY : mem (lmap left Y') ⊆ L'
    mY d d∈ with ∈-map⁻ left d∈
    ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = Y'⊆ y y∈
    bm : Bnd (suc j) (lmap left Y')
    bm d d∈ with ∈-map⁻ left d∈
    ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = s≤s (bY y y∈)

  NE-Lefts : nonempty (Lefts (⟦ L ⟧ ρ))
  NE-Lefts = Obs.nonempty-obs (rL (v ∷ []) (suc (depth v)) (single⊆ lv) (Bnd-single v)) (λ ())

  ρL : Env
  ρL = Lefts (⟦ L ⟧ ρ) • ρ

  ρL' : Env
  ρL' = Lefts L' • ρ'

  NE-ρL : nonempty-env ρL
  NE-ρL zero = NE-Lefts
  NE-ρL (suc y) = NE y

  ρL'~ : ∀ y → consis (ρL' y)
  ρL'~ zero a b a∈ b∈ = L'~ (left a) (left b) a∈ b∈
  ρL'~ (suc y) = ρ'~ y

  ρL⊳ : ρL' ⊳ₑ ρL
  ρL⊳ zero = rL
  ρL⊳ (suc y) = ρ⊳ y

  IH : R k V' (⟦ M ⟧ ρL)
  IH = delay-reflect M ρL' ρL NE-ρL ρL'~ ρL⊳ V' k V'⊆F bV

  M⊆ : ⟦ M ⟧ ρL ⊆ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ
  M⊆ x x∈ with cont-1 M ρ (Lefts (⟦ L ⟧ ρ)) NE NE-Lefts x x∈
  ... | ⟨ u , ⟨ U , ⟨ sub , x∈' ⟩ ⟩ ⟩ = inj₁ ⟨ u , ⟨ U , ⟨ sub , x∈' ⟩ ⟩ ⟩

reflect-case-right L M N ρ' ρ NE ρ'~ ρ⊳ v rv V' k V'⊆ bV = R-mono k N⊆ IH
  where
  L' = ⟦ delay L ⟧' ρ'
  L'~ = ⟦⟧'-consis (delay L) ρ' ρ'~

  V'⊆G : mem V' ⊆ ⟦ delay N ⟧' (Rights L' • ρ')
  V'⊆G x x∈ with V'⊆ x x∈
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL , _ ⟩ ⟩ ⟩ = ⊥-elim (L'~ (right v) (left u) rv (allL u (here refl)))
  ... | inj₂ ⟨ u , ⟨ U , ⟨ allR , x∈G ⟩ ⟩ ⟩ =
    S4.⟦⟧-monotone {ρ = mem (u ∷ U) • ρ'} {ρ′ = Rights L' • ρ'} (delay N) env⊆ x x∈G
    where
    env⊆ : ∀ y → (mem (u ∷ U) • ρ') y ⊆ (Rights L' • ρ') y
    env⊆ zero = allR
    env⊆ (suc y) = λ d z → z

  rR : ∀ Y' j → mem Y' ⊆ Rights L' → Bnd j Y' → R j Y' (Rights (⟦ L ⟧ ρ))
  rR Y' j Y'⊆ bY =
    Obs.right-obs (delay-reflect L ρ' ρ NE ρ'~ ρ⊳ (lmap right Y') (suc j) mY bm) Y'
      (λ d d∈ → ∈-map⁺ right d∈)
    where
    mY : mem (lmap right Y') ⊆ L'
    mY d d∈ with ∈-map⁻ right d∈
    ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = Y'⊆ y y∈
    bm : Bnd (suc j) (lmap right Y')
    bm d d∈ with ∈-map⁻ right d∈
    ... | ⟨ y , ⟨ y∈ , refl ⟩ ⟩ = s≤s (bY y y∈)

  NE-Rights : nonempty (Rights (⟦ L ⟧ ρ))
  NE-Rights = Obs.nonempty-obs (rR (v ∷ []) (suc (depth v)) (single⊆ rv) (Bnd-single v)) (λ ())

  ρR : Env
  ρR = Rights (⟦ L ⟧ ρ) • ρ

  ρR' : Env
  ρR' = Rights L' • ρ'

  NE-ρR : nonempty-env ρR
  NE-ρR zero = NE-Rights
  NE-ρR (suc y) = NE y

  ρR'~ : ∀ y → consis (ρR' y)
  ρR'~ zero a b a∈ b∈ = L'~ (right a) (right b) a∈ b∈
  ρR'~ (suc y) = ρ'~ y

  ρR⊳ : ρR' ⊳ₑ ρR
  ρR⊳ zero = rR
  ρR⊳ (suc y) = ρ⊳ y

  IH : R k V' (⟦ N ⟧ ρR)
  IH = delay-reflect N ρR' ρR NE-ρR ρR'~ ρR⊳ V' k V'⊆G bV

  N⊆ : ⟦ N ⟧ ρR ⊆ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ
  N⊆ x x∈ with cont-1 N ρ (Rights (⟦ L ⟧ ρ)) NE NE-Rights x x∈
  ... | ⟨ u , ⟨ U , ⟨ sub , x∈' ⟩ ⟩ ⟩ = inj₂ ⟨ u , ⟨ U , ⟨ sub , x∈' ⟩ ⟩ ⟩

{- The end theorem (backward half) --------------------------------------------}

delay-reflect-closed : ∀ (M : AST) V' k → mem V' ⊆ ⟦ delay M ⟧' ρ₀ → Bnd k V'
  → R k V' (⟦ M ⟧ ρ₀)
delay-reflect-closed M =
  delay-reflect M ρ₀ ρ₀ (λ _ → ⟨ ω , refl ⟩) (λ _ → Init-consis) Init⊳Init

reflect-const : ∀ (M : AST) {B} (c : base-rep B)
  → const c ∈ ⟦ delay M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀
reflect-const M c c∈ =
  Obs.const-obs (delay-reflect-closed M (const c ∷ []) 1 (single⊆ c∈) (Bnd-single (const c)))
    c (here refl)

reflect-nonempty : ∀ (M : AST) → nonempty (⟦ delay M ⟧' ρ₀) → nonempty (⟦ M ⟧ ρ₀)
reflect-nonempty M ⟨ v , v∈ ⟩ =
  Obs.nonempty-obs (delay-reflect-closed M (v ∷ []) (suc (depth v)) (single⊆ v∈) (Bnd-single v))
    (λ ())
