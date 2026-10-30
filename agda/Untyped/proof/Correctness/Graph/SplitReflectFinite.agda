{-

  Backward (reflect) direction of the correctness of the split pass
  (Clos3 → Clos4), using the logical relation of SplitFiniteRel, indexed
  by *finite lists of target observations* (see issue #1).

  The function clause (app-obs) is the only place where the cars and cdrs
  of target closures meet, and they meet inside the finite list V',
  so junk entries and mixed closures never produce a target-only result.

  The proof uses two properties of the semantics:
  - denotations are consistent (Clos3-con, Clos4-con), which follows from
    the consistency of the operators;
  - source denotations are continuous (body-continuous, let-β, clos-β).
-}

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Untyped.Language.Clos3 as L3
open import Untyped.Language.Clos4 as L4
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import Untyped.proof.Semantics.Graph.Clos3Iswim as S3
open import Untyped.proof.Semantics.Graph.Clos4Iswim as S4 renaming
  (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
open import Untyped.Compiler.Split using (split; del-map-args)
open import proof.Framework.GraphModel.Env using (nonempty-env; •-~; extend-nonempty-env)
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import Untyped.proof.Correctness.Graph.SplitFiniteCommon
open import Untyped.proof.Correctness.Graph.SplitFiniteRel
open import Untyped.proof.Correctness.Graph.SplitApp using (let-app-≃)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Level using (lift; lower)
open import Language.Prim using (δ)

module Untyped.proof.Correctness.Graph.SplitReflectFinite where

{- Collecting the finite witnesses of a target application -------------------}

{- a target application V' ⊆ (car L' ● cdr L') ● N' is a batch of calls of
   a finite W ⊆ L' on a finite U ⊆ N' -}
collect : ∀ (L' N' : 𝒫 Value) V' → mem V' ⊆ (L' ⊙ N')
  → Σ[ W ∈ List Value ] Σ[ U ∈ List Value ]
      mem W ⊆ L' × mem U ⊆ N' × Calls W U V'
collect L' N' [] _ =
  ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , record { results = λ _ () ; args = λ _ () } ⟩ ⟩ ⟩ ⟩
collect L' N' (w ∷ V') V'⊆
    with V'⊆ w (here refl) | collect L' N' V' (λ d d∈ → V'⊆ d (there d∈))
... | ⟨ U₀ , ⟨ ⟨ FV , ⟨ ⟨ t , e∈L' ⟩ , ⟨ FV⊆Cdr , neFV ⟩ ⟩ ⟩ , ⟨ U₀⊆N' , neU₀ ⟩ ⟩ ⟩
    | ⟨ W , ⟨ U , ⟨ W⊆ , ⟨ U⊆ , cs ⟩ ⟩ ⟩ ⟩
    with cdr-witness FV FV⊆Cdr
... | ⟨ C , ⟨ C⊆L' , FV⊆C ⟩ ⟩ =
  ⟨ e ∷ (C ++ W) , ⟨ U₀ ++ U , ⟨ W⊆' , ⟨ U⊆' , record { results = res ; args = arg } ⟩ ⟩ ⟩ ⟩
  where
  e = ⦅ FV ↦ (U₀ ↦ w) , t ⦆
  inW : mem W ⊆ mem (e ∷ (C ++ W))
  inW d d∈ = there (∈-++⁺ʳ C d∈)

  W⊆' : mem (e ∷ (C ++ W)) ⊆ L'
  W⊆' _ (here refl) = e∈L'
  W⊆' d (there d∈) with ∈-++⁻ C d∈
  ... | inj₂ d∈W = W⊆ d d∈W
  ... | inj₁ d∈C = C⊆L' d d∈C

  U⊆' : mem (U₀ ++ U) ⊆ N'
  U⊆' d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = U₀⊆N' d d∈U₀
  ... | inj₂ d∈U = U⊆ d d∈U

  ent : CarEntry (e ∷ (C ++ W)) U₀ w
  ent = car-entry FV t (here refl) neFV
          (λ d d∈ → let ⟨ u , i ⟩ = FV⊆C d d∈ in ⟨ u , there (∈-++⁺ˡ i) ⟩)

  res : ∀ x → x ⋵ (w ∷ V') → Σ[ U₁ ∈ List Value ]
          CarEntry (e ∷ (C ++ W)) U₁ x × U₁ ≢ [] × mem U₁ ⊆ mem (U₀ ++ U)
  res _ (here refl) = ⟨ U₀ , ⟨ ent , ⟨ neU₀ , (λ d → ∈-++⁺ˡ) ⟩ ⟩ ⟩
  res x (there x∈) = let ⟨ U₁ , ⟨ e₁ , ⟨ ne , U₁⊆ ⟩ ⟩ ⟩ = Calls.results cs x x∈
                     in ⟨ U₁ , ⟨ CarEntry-⊆ inW e₁ , ⟨ ne , (λ d d∈ → ∈-++⁺ʳ U₀ (U₁⊆ d d∈)) ⟩ ⟩ ⟩

  arg : ∀ u → u ⋵ (U₀ ++ U) → Σ[ U₁ ∈ List Value ] Σ[ x ∈ Value ]
          CarEntry (e ∷ (C ++ W)) U₁ x × u ⋵ U₁
  arg u u∈ with ∈-++⁻ U₀ u∈
  ... | inj₁ u∈U₀ = ⟨ U₀ , ⟨ w , ⟨ ent , u∈U₀ ⟩ ⟩ ⟩
  ... | inj₂ u∈U = let ⟨ U₁ , ⟨ x , ⟨ e₁ , u∈₁ ⟩ ⟩ ⟩ = Calls.args cs u u∈U
                   in ⟨ U₁ , ⟨ x , ⟨ CarEntry-⊆ inW e₁ , u∈₁ ⟩ ⟩ ⟩

{- The fundamental lemma ------------------------------------------------------}

{- the hypotheses on the environments -}
record Envs (ρ' ρ : Env) : Set₁ where
  constructor envs
  field
    NE : nonempty-env ρ
    ρ~ : Con-env ρ
    ρ'~ : Con-env ρ'
    ρ⊳ : ρ' ⊳ₑ ρ

split-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ
  → ∀ V' → mem V' ⊆ ⟦ split M ⟧' ρ' → R V' (⟦ M ⟧ ρ)

reflect-nth : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → (i : Fin n) → ∀ V' → mem V' ⊆ nthD (⟦ del-map-args args ⟧₊' ρ') i
  → R V' (nthD (⟦ args ⟧₊ ρ) i)

reflect-𝒯 : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → ∀ V' → mem V' ⊆ 𝒯 n (⟦ del-map-args args ⟧₊' ρ') → R V' (𝒯 n (⟦ args ⟧₊ ρ))

{- a nonempty target set yields a nonempty source set -}
ne-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → nonempty (⟦ split M ⟧' ρ') → nonempty (⟦ M ⟧ ρ)
ne-reflect M E ⟨ v , v∈ ⟩ =
  Obs.nonempty-obs (unfold (split-reflect M E (v ∷ []) (single⊆ v∈))) (λ ())

{- the tagged parts of a reflected set are related -}
tag-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → ∀ t W → mem W ⊆ Untag t (⟦ split M ⟧' ρ')
  → R W (Untag t (⟦ M ⟧ ρ))
tag-reflect M E t W W⊆ =
  Obs.tag-obs (unfold (split-reflect M E (lmap (tag t) W) mW)) t W (λ d d∈ → ∈-map⁺ (tag t) d∈)
  where
  mW : mem (lmap (tag t) W) ⊆ _
  mW d d∈ with ∈-map⁻ (tag t) d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = W⊆ x x∈

{- the cases for case-op: by consistency, all the target results come from
   the branch B on the side s of the scrutinee L -}
reflect-branch : ∀ (s : Tag) (L B : AST) {ρ' ρ C} → Envs ρ' ρ
  → ∀ v → tag s v ∈ ⟦ split L ⟧' ρ' → (∀ {a b} → tag s a ~ tag s b → a ~ b)
  → (nonempty (Untag s (⟦ L ⟧ ρ)) → ⟦ B ⟧ (Untag s (⟦ L ⟧ ρ) • ρ) ⊆ C)
  → ∀ V' → mem V' ⊆ ⟦ split B ⟧' (Untag s (⟦ split L ⟧' ρ') • ρ') → R V' C
reflect-branch s L B {ρ'}{ρ} E v sv s~ B⊆ V' V'⊆ =
  R-mono (B⊆ NE-s) (split-reflect B (envs NE' (Con-• (Untag-con s s~ (Clos3-con L ρ~)) ρ~) ρ'~' ρ⊳') V' V'⊆)
  where
  open Envs E
  NE-s = Obs.nonempty-obs (unfold (tag-reflect L E s (v ∷ []) (single⊆ sv))) (λ ())
  NE' = extend-nonempty-env NE NE-s
  ρ'~' = Con-• (Untag-con s s~ (Clos4-con (split L) ρ'~)) ρ'~
  ρ⊳' : (Untag s (⟦ split L ⟧' ρ') • ρ') ⊳ₑ (Untag s (⟦ L ⟧ ρ) • ρ)
  ρ⊳' zero = tag-reflect L E s
  ρ⊳' (suc x) = ρ⊳ x

inl-ne : ∀ {D : 𝒫 Value} v → v ∈ inl ⟨ D , ptt ⟩ → nonempty D
inl-ne (left d) d∈ = ⟨ d , d∈ ⟩

inr-ne : ∀ {D : 𝒫 Value} v → v ∈ inr ⟨ D , ptt ⟩ → nonempty D
inr-ne (right d) d∈ = ⟨ d , d∈ ⟩

pair-ne : ∀ {A B : 𝒫 Value} v → v ∈ pair ⟨ A , ⟨ B , ptt ⟩ ⟩ → nonempty B
pair-ne ⦅ u , v ⦆ ⟨ _ , v∈ ⟩ = ⟨ v , v∈ ⟩

pair-tag : ∀ {A B : 𝒫 Value} t {d} → tag t d ∈ pair ⟨ A , ⟨ B , ptt ⟩ ⟩ → Data.Empty.⊥
pair-tag (tupT i) ()
pair-tag leftT ()
pair-tag rightT ()

split-reflect (` x) E = Envs.ρ⊳ E x

split-reflect (app ⦅ L ,, N ,, Nil ⦆) {ρ'} E V' V'⊆
    with collect (⟦ split L ⟧' ρ') (⟦ split N ⟧' ρ') V'
           (λ d d∈ → proj₁ (let-app-≃ (split L) (split N) ρ' (Clos4-con (split L) (Envs.ρ'~ E))) d (V'⊆ d d∈))
... | ⟨ W , ⟨ U , ⟨ W⊆L' , ⟨ U⊆N' , cs ⟩ ⟩ ⟩ ⟩ =
  Obs.app-obs (unfold (split-reflect L E W W⊆L')) cs _ (Clos3-con N (Envs.ρ~ E))
    (Con-⊆ (Clos4-con (split N) (Envs.ρ'~ E)) U⊆N') (split-reflect N E U U⊆N')

split-reflect (lit B c ⦅ Nil ⦆) E V' V'⊆ = R-flat V'⊆ (λ v v∈ → ℬ-flat v (V'⊆ v v∈))

split-reflect (prim p ⦅ L ,, M ,, Nil ⦆) E V' V'⊆ = R-data V⊆ dt
  where
  const-reflect : ∀ N {c : base-rep Int} → const c ∈ ⟦ split N ⟧' _ → const c ∈ ⟦ N ⟧ _
  const-reflect N {c} c∈ = Obs.const-obs (unfold (split-reflect N E (const c ∷ []) (single⊆ c∈))) c (here refl)
  V⊆ : mem V' ⊆ ⟦ prim p ⦅ L ,, M ,, Nil ⦆ ⟧ _
  V⊆ v v∈ with V'⊆ v v∈
  ... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
    ⟨ n , ⟨ m , ⟨ const-reflect L n∈ , ⟨ const-reflect M m∈ , refl ⟩ ⟩ ⟩ ⟩
  dt : ∀ v → v ⋵ V' → Data v
  dt v v∈ with V'⊆ v v∈
  ... | ⟨ n , ⟨ m , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩ = out-data (δ p n m)

split-reflect (tuple n ⦅ args ⦆) = reflect-𝒯 args

split-reflect (get i ⦅ M ,, Nil ⦆) E = tag-reflect M E (tupT i)

split-reflect (inl-op ⦅ M ,, Nil ⦆) E V' V'⊆ = fold record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → let ⟨ v , v∈ ⟩ = ne-mem ne V'⊆
                              ⟨ m , m∈ ⟩ = ne-reflect M E (inl-ne v v∈) in ⟨ left m , m∈ ⟩
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V'⊆ _ uv∈) cs)
  ; tag-obs = λ { leftT W W⊆ →
                    split-reflect M E W (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈)) }
  }

split-reflect (inr-op ⦅ M ,, Nil ⦆) E V' V'⊆ = fold record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → let ⟨ v , v∈ ⟩ = ne-mem ne V'⊆
                              ⟨ m , m∈ ⟩ = ne-reflect M E (inr-ne v v∈) in ⟨ right m , m∈ ⟩
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V'⊆ _ uv∈) cs)
  ; tag-obs = λ { rightT W W⊆ →
                    split-reflect M E W (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; leftT W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈)) }
  }

split-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) E [] V'⊆ = R-∅ (λ _ ())
split-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ'}{ρ} E (w ∷ V') V'⊆
    with V'⊆ w (here refl)
... | inj₁ ⟨ v , ⟨ _ , ⟨ allL , _ ⟩ ⟩ ⟩ =
  reflect-branch leftT L M E v lv (λ a~b → a~b) M⊆ (w ∷ V') V'⊆F
  where
  lv = allL v (here refl)
  M⊆ : nonempty (Lefts (⟦ L ⟧ ρ)) → ⟦ M ⟧ (Lefts (⟦ L ⟧ ρ) • ρ) ⊆ _
  M⊆ ne = 𝒞-left {⟦ L ⟧ ρ} {λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ N ⟧ (X • ρ)} (S3.body-continuous M ρ (Envs.NE E) _ ne)
                  (Untag-con leftT (λ c → c) (Clos3-con L (Envs.ρ~ E)))
  V'⊆F : mem (w ∷ V') ⊆ ⟦ split M ⟧' (Lefts (⟦ split L ⟧' ρ') • ρ')
  V'⊆F x x∈ with V'⊆ x x∈
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL' , ⟨ x∈F , _ ⟩ ⟩ ⟩ ⟩ =
    S4.⟦⟧-monotone (split M) (λ { zero → allL' ; (suc y) → λ d z → z }) x x∈F
  ... | inj₂ ⟨ u , ⟨ U , ⟨ allR , _ ⟩ ⟩ ⟩ =
    ⊥-elim (Clos4-con (split L) (Envs.ρ'~ E) _ _ lv (allR u (here refl)))
... | inj₂ ⟨ v , ⟨ _ , ⟨ allR , _ ⟩ ⟩ ⟩ =
  reflect-branch rightT L N E v rv (λ a~b → a~b) N⊆ (w ∷ V') V'⊆G
  where
  rv = allR v (here refl)
  N⊆ : nonempty (Rights (⟦ L ⟧ ρ)) → ⟦ N ⟧ (Rights (⟦ L ⟧ ρ) • ρ) ⊆ _
  N⊆ ne = 𝒞-right {⟦ L ⟧ ρ} {λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ N ⟧ (X • ρ)} (S3.body-continuous N ρ (Envs.NE E) _ ne)
                   (Untag-con rightT (λ c → c) (Clos3-con L (Envs.ρ~ E)))
  V'⊆G : mem (w ∷ V') ⊆ ⟦ split N ⟧' (Rights (⟦ split L ⟧' ρ') • ρ')
  V'⊆G x x∈ with V'⊆ x x∈
  ... | inj₂ ⟨ u , ⟨ U , ⟨ allR' , ⟨ x∈G , _ ⟩ ⟩ ⟩ ⟩ =
    S4.⟦⟧-monotone (split N) (λ { zero → allR' ; (suc y) → λ d z → z }) x x∈G
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL , _ ⟩ ⟩ ⟩ =
    ⊥-elim (Clos4-con (split L) (Envs.ρ'~ E) _ _ rv (allL u (here refl)))

split-reflect (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) E [] V'⊆ = R-∅ (λ _ ())
split-reflect (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ'}{ρ} E (w ∷ V') V'⊆ with letD-collect (S4.body-mono (split N) ρ') (w ∷ V') V'⊆
... | ⟨ U , ⟨ U⊆ , V'⊆N ⟩ ⟩ =
  R-mono (proj₂ (S3.let-β N ρ _ NE NE-M (Clos3-con M ρ~)))
    (split-reflect N (envs NE' (Con-• (Clos3-con M ρ~) ρ~) (Con-• (Con-⊆ (Clos4-con (split M) ρ'~) U⊆) ρ'~) ρ⊳')
       (w ∷ V') V'⊆N)
  where
  open Envs E
  NE-M = let ⟨ _ , ⟨ _ , ⟨ U₀⊆ , ne ⟩ ⟩ ⟩ = V'⊆ w (here refl) in ne-reflect M E (ne-mem ne U₀⊆)
  NE' = extend-nonempty-env NE NE-M
  ρ⊳' : (mem U • ρ') ⊳ₑ (⟦ M ⟧ ρ • ρ)
  ρ⊳' zero Y' Y'⊆ = split-reflect M E Y' (λ d d∈ → U⊆ d (Y'⊆ d d∈))
  ρ⊳' (suc x) = ρ⊳ x

split-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) {ρ'}{ρ} E V' V'⊆ =
  fold record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → let ⟨ t , t∈ ⟩ = T-ne (let ⟨ v , v∈ ⟩ = ne-mem ne V'⊆ in pair-ne v v∈)
                          in ⟨ ν , ⟨ t ∷ [] , ⟨ ⟨ tt , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ single⊆ t∈ , (λ ()) ⟩ ⟩ ⟩ ⟩
  ; app-obs = clos-app
  ; tag-obs = λ t W W⊆ → R-∅ (λ d d∈ → pair-tag t (V'⊆ _ (W⊆ d d∈)))
  }
  where
  open Envs E
  T' = 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ')
  T = 𝒯 n (⟦ fvs ⟧₊ ρ)
  D = ⟦ clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆ ⟧ ρ

  T-ne : nonempty T' → nonempty T
  T-ne ⟨ t' , t'∈ ⟩ =
    Obs.nonempty-obs (unfold (reflect-𝒯 fvs E (t' ∷ []) (single⊆ t'∈))) (λ ())

  Cdrs⊆T' : Cdrs V' ⊆ T'
  Cdrs⊆T' fv ⟨ _ , e∈ ⟩ = proj₂ (V'⊆ _ e∈)

  clos-app : ∀ {U' W'} → Calls V' U' W' → ∀ E → Con E → Con (mem U') → R U' E → R W' (D ● E)
  clos-app {W' = []} _ E _ U'~ rU = R-∅ (λ _ ())
  clos-app {U'} {w ∷ W'} cs Es cE U'~ rU =
    R-mono (S3.clos-β N (λ _ → ⟨ ω , refl ⟩) NE-T NE-E cT cE)
      (split-reflect N (envs NE-ρs (Con-• cE (Con-• cT (λ _ → Con-⌈⌉ ω))) ρ''~ ρ''⊳ρs) (w ∷ W') W⊆B)
    where
    wit = Calls.results cs w (here refl)
    ent = proj₁ (proj₂ wit)
    NE-E = Obs.nonempty-obs (unfold rU) (ne-⊆ (proj₂ (proj₂ (proj₂ wit))) (proj₁ (proj₂ (proj₂ wit))))
    NE-T = T-ne (ne-mem (CarEntry.FV≢[] ent) (λ d d∈ → Cdrs⊆T' d (CarEntry.FV⊆ ent d d∈)))

    ρ'' : Env
    ρ'' = mem U' • Cdrs V' • (λ _ → Init)

    W⊆B : mem (w ∷ W') ⊆ ⟦ split N ⟧' ρ''
    W⊆B x x∈ with Calls.results cs x x∈
    ... | ⟨ U₀ , ⟨ car-entry FV t e∈ neFV FV⊆ , ⟨ _ , U₀⊆ ⟩ ⟩ ⟩ with V'⊆ _ e∈
    ... | ⟨ ⟨ ⟨ x∈B , _ ⟩ , _ ⟩ , _ ⟩ =
      S4.⟦⟧-monotone (split N) (λ { zero → U₀⊆ ; (suc zero) → FV⊆ ; (suc (suc y)) → λ d z → z })
        x x∈B

    cT = Clos3-con (tuple n ⦅ fvs ⦆) ρ~
    ρ''~ : Con-env ρ''
    ρ''~ = Con-• U'~ (Con-• (Con-⊆ (Clos4-con (tuple n ⦅ del-map-args fvs ⦆') ρ'~) Cdrs⊆T')
                            (λ _ → Con-⌈⌉ ω))

    NE-ρs = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) NE-T) NE-E

    ρ''⊳ρs : ρ'' ⊳ₑ (Es • T • (λ _ → Init))
    ρ''⊳ρs zero Y' Y'⊆ = R-⊆ Y'⊆ rU
    ρ''⊳ρs (suc zero) Y' Y'⊆ = reflect-𝒯 fvs E Y' (λ y y∈ → Cdrs⊆T' y (Y'⊆ y y∈))
    ρ''⊳ρs (suc (suc x)) Y' Y'⊆ = R-flat Y'⊆ (λ v v∈ → Init-flat (Y'⊆ v v∈))

reflect-nth (M ,, args) E zero = split-reflect M E
reflect-nth (M ,, args) E (suc i) = reflect-nth args E i

reflect-𝒯 {zero} args E V' V'⊆ =
  R-flat (λ v v∈ → proj₁ (𝒯0-flat v (V'⊆ v v∈))) (λ v v∈ → proj₂ (𝒯0-flat v (V'⊆ v v∈)))
reflect-𝒯 {suc n} args {ρ'}{ρ} E V' V'⊆ = fold record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → tup-ne (ne-mem ne V'⊆)
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V'⊆ _ uv∈) cs)
  ; tag-obs = λ { (tupT i) W W⊆ → nth-case i W W⊆
                ; leftT W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈)) }
  }
  where
  Ds' = ⟦ del-map-args args ⟧₊' ρ'
  Ds = ⟦ args ⟧₊ ρ

  comp-ne : ∀ j → nonempty (nthD Ds' j) → nonempty (nthD Ds j)
  comp-ne j ⟨ d , d∈ ⟩ =
    Obs.nonempty-obs (unfold (reflect-nth args E j (d ∷ []) (single⊆ d∈))) (λ ())

  tup-ne : nonempty (𝒯 (suc n) Ds') → nonempty (𝒯 (suc n) Ds)
  tup-ne ⟨ tup[ i ] d , ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ ⟩ =
    let ⟨ d₀ , d₀∈ ⟩ = comp-ne i ⟨ d , d∈ ⟩ in ⟨ tup[ i ] d₀ , ⟨ refl , ⟨ d₀∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩ ⟩

  nth-case : ∀ {m} (i : Fin m) W' → mem W' ⊆ Untag (tupT i) (mem V')
    → R W' (Untag (tupT i) (𝒯 (suc n) Ds))
  nth-case i [] _ = R-∅ (λ _ ())
  nth-case i (w ∷ W') W'⊆ with V'⊆ _ (W'⊆ w (here refl))
  ... | ⟨ refl , ⟨ _ , ne ⟩ ⟩ =
    R-mono (λ d d∈ → ⟨ refl , ⟨ d∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩)
      (reflect-nth args E i (w ∷ W') sub)
    where
    sub : mem (w ∷ W') ⊆ nthD Ds' i
    sub d d∈ with V'⊆ _ (W'⊆ d d∈)
    ... | ⟨ refl , ⟨ d∈' , _ ⟩ ⟩ = d∈'

{- The end theorem (backward half) --------------------------------------------}

Envs₀ : Envs ρ₀ ρ₀
Envs₀ = envs (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ _ → Con-⌈⌉ ω) Init⊳Init

reflect-const : ∀ (M : AST) {B} (c : base-rep B)
  → const c ∈ ⟦ split M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀
reflect-const M c c∈ =
  Obs.const-obs (unfold (split-reflect M Envs₀ (const c ∷ []) (single⊆ c∈))) c (here refl)

reflect-nonempty : ∀ (M : AST) → nonempty (⟦ split M ⟧' ρ₀) → nonempty (⟦ M ⟧ ρ₀)
reflect-nonempty M = ne-reflect M Envs₀
