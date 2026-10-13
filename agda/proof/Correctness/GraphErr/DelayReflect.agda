{-

  Backward (reflect) direction of the correctness of the delay pass
  (Clos3 → Clos4) in the graph model with errors, using the relation of
  DelayRel, as in proof/Correctness/Graph/DelayReflectFinite.agda.

  New with errors: a target set can hold ω, from an error of the target
  operator, beside the results the source explains as before. Every
  target error is traced to a source error, in the same order:

  * an application: the closure errs, or is not a pair (fst fails), and
    then the source operator errs or is not a function (the early check);
    or the closure is a pair and the argument errs, and then the source
    operator is a function and its argument errs. The late code check of
    the target call never fails: the car of a target closure is a
    function (pair-obs);
  * the other operators: an error in an operand, or an operand of the
    wrong kind, which corresponds to a source operand of the wrong kind
    (Corr).

  By consistency, the results of a let, a case or a closure are either
  all from the success of the operator or all ω.

-}

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Semantics.GraphErr.Prim
open import Language.Clos3 as L3
open import Language.Clos4 as L4
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import proof.Semantics.GraphErr.Clos3 as S3
open import proof.Semantics.GraphErr.Clos4 as S4 renaming
  (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
open import Compiler.Delay using (delay; del-map-args)
open import proof.Framework.GraphModel.Env using (nonempty-env; •-~; extend-nonempty-env)
open import proof.Correctness.GraphErr.DelayRel
open import proof.Correctness.GraphErr.DelayApp using (let-app-≃)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Level using (lift; lower)
open import Language.Prim using (δ)

module proof.Correctness.GraphErr.DelayReflect where

{- Collecting the finite witnesses of a target application -------------------}

{- finitely many pairs of L whose cdrs cover FV -}
cdr-witness : ∀ {L} FV → mem FV ⊆ cdrᵉ ⟨ L , ptt ⟩ → NoErr FV
  → Σ[ P ∈ List Value ] mem P ⊆ L × mem FV ⊆ Cdrs P
cdr-witness [] _ _ = ⟨ [] , ⟨ (λ _ ()) , (λ _ ()) ⟩ ⟩
cdr-witness (fv ∷ FV) FV⊆ n with FV⊆ fv (here refl) | cdr-witness FV (λ d d∈ → FV⊆ d (there d∈)) (λ i → n (there i))
... | inj₂ ⟨ refl , _ ⟩ | _ = ⊥-elim (n (here refl))
... | inj₁ ⟨ u , u∈ ⟩ | ⟨ P , ⟨ P⊆ , FV⊆P ⟩ ⟩ = ⟨ ⦅ u , fv ⦆ ∷ P , ⟨ P⊆′ , FV⊆′ ⟩ ⟩
  where
  P⊆′ : mem (⦅ u , fv ⦆ ∷ P) ⊆ _
  P⊆′ _ (here refl) = u∈
  P⊆′ d (there d∈) = P⊆ d d∈
  FV⊆′ : mem (fv ∷ FV) ⊆ Cdrs (⦅ u , fv ⦆ ∷ P)
  FV⊆′ _ (here refl) = ⟨ u , here refl ⟩
  FV⊆′ d (there d∈) = let ⟨ u′ , i ⟩ = FV⊆P d d∈ in ⟨ u′ , there i ⟩

{- the errors of a target call -}
TErr : 𝒫 Value → 𝒫 Value → Set
TErr L' N' = errs 3 ⟨ carᵉ ⟨ L' , ptt ⟩ , ⟨ cdrᵉ ⟨ L' , ptt ⟩ , ⟨ N' , ptt ⟩ ⟩ ⟩
           ⊎ (wrong IsFun (carᵉ ⟨ L' , ptt ⟩) × val∈ (cdrᵉ ⟨ L' , ptt ⟩) × val∈ N')

{- a target application V' ⊆ L' ⊙ N': its results other than ω are a batch
   Vs of calls of a finite W ⊆ L' on a finite U ⊆ N', and its ω is one of
   them or an error of the call -}
collect : ∀ (L' N' : 𝒫 Value) V' → mem V' ⊆ (L' ⊙ N')
  → Σ[ W ∈ List Value ] Σ[ U ∈ List Value ] Σ[ Vs ∈ List Value ]
      mem W ⊆ L' × mem U ⊆ N' × Calls W U Vs
      × (∀ w → w ⋵ V' → w ≢ ω → w ⋵ Vs) × (ω ⋵ V' → ω ⋵ Vs ⊎ TErr L' N')
collect L' N' [] _ =
  ⟨ [] , ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , ⟨ record { results = λ _ () ; args = λ _ () ; noerr = λ () }
  , ⟨ (λ _ ()) , (λ ()) ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
collect L' N' (w ∷ V') V'⊆ with collect L' N' V' (λ d d∈ → V'⊆ d (there d∈))
... | ⟨ W , ⟨ U , ⟨ Vs , ⟨ W⊆ , ⟨ U⊆ , ⟨ cs , ⟨ keep , ωok ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ with V'⊆ w (here refl)
... | inj₂ ⟨ refl , terr ⟩ =
  ⟨ W , ⟨ U , ⟨ Vs , ⟨ W⊆ , ⟨ U⊆ , ⟨ cs , ⟨ keep′ , ωok′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  keep′ : ∀ x → x ⋵ (ω ∷ V') → x ≢ ω → x ⋵ Vs
  keep′ x (here refl) x≢ = ⊥-elim (x≢ refl)
  keep′ x (there x∈) x≢ = keep x x∈ x≢
  ωok′ : ω ⋵ (ω ∷ V') → ω ⋵ Vs ⊎ TErr L' N'
  ωok′ _ = inj₂ terr
... | inj₁ ⟨ FV , ⟨ U₀ , ⟨ inj₂ ⟨ () , _ ⟩ , _ ⟩ ⟩ ⟩
... | inj₁ ⟨ FV , ⟨ U₀ , ⟨ inj₁ ⟨ t , e∈L' ⟩ , ⟨ FV⊆Cdr , ⟨ U₀⊆N' , ⟨ neFV , ⟨ neU₀ , ⟨ nFV , nU₀ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
    with cdr-witness FV FV⊆Cdr nFV
... | ⟨ C , ⟨ C⊆L' , FV⊆C ⟩ ⟩ =
  ⟨ e ∷ (C ++ W) , ⟨ U₀ ++ U , ⟨ w ∷ Vs , ⟨ W⊆' , ⟨ U⊆' , ⟨ record { results = res ; args = arg ; noerr = nU }
  , ⟨ keep′ , ωok′ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  e = ⦅ FV ↦ (U₀ ↦ w) , t ⦆
  inW : Pairs⊆ W (e ∷ (C ++ W))
  inW u v d∈ = there (∈-++⁺ʳ C d∈)

  W⊆' : mem (e ∷ (C ++ W)) ⊆ L'
  W⊆' _ (here refl) = e∈L'
  W⊆' d (there d∈) with ∈-++⁻ C d∈
  ... | inj₂ d∈W = W⊆ d d∈W
  ... | inj₁ d∈C = C⊆L' d d∈C

  U⊆' : mem (U₀ ++ U) ⊆ N'
  U⊆' d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = U₀⊆N' d d∈U₀
  ... | inj₂ d∈U = U⊆ d d∈U

  nU : NoErr (U₀ ++ U)
  nU ω∈ with ∈-++⁻ U₀ ω∈
  ... | inj₁ i = nU₀ i
  ... | inj₂ i = Calls.noerr cs i

  ent : CarEntry (e ∷ (C ++ W)) U₀ w
  ent = car-entry FV t (here refl) neFV
          (λ d d∈ → let ⟨ u , i ⟩ = FV⊆C d d∈ in ⟨ u , there (∈-++⁺ˡ i) ⟩)

  res : ∀ x → x ⋵ (w ∷ Vs) → Σ[ U₁ ∈ List Value ]
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

  keep′ : ∀ x → x ⋵ (w ∷ V') → x ≢ ω → x ⋵ (w ∷ Vs)
  keep′ x (here refl) _ = here refl
  keep′ x (there x∈) x≢ = there (keep x x∈ x≢)

  ωok′ : ω ⋵ (w ∷ V') → ω ⋵ (w ∷ Vs) ⊎ TErr L' N'
  ωok′ (here refl) = inj₁ (here refl)
  ωok′ (there i) with ωok i
  ... | inj₁ j = inj₁ (there j)
  ... | inj₂ te = inj₂ te

{- The fundamental lemma ------------------------------------------------------}

record Envs (ρ' ρ : Env) : Set₁ where
  constructor envs
  field
    NE : nonempty-env ρ
    NE' : nonempty-env ρ'
    ρ~ : Con-env ρ
    ρ'~ : Con-env ρ'
    ρ⊳ : ρ' ⊳ₑ ρ

delay-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ
  → ∀ V' → mem V' ⊆ ⟦ delay M ⟧' ρ' → R V' (⟦ M ⟧ ρ)

reflect-nth : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → (i : Fin n) → ∀ V' → mem V' ⊆ nthD (⟦ del-map-args args ⟧₊' ρ') i
  → R V' (nthD (⟦ args ⟧₊ ρ) i)

reflect-𝒯 : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → ∀ V' → mem V' ⊆ 𝒯ᵉ n (⟦ del-map-args args ⟧₊' ρ') → R V' (𝒯ᵉ n (⟦ args ⟧₊ ρ))

{- single target observations -}
one : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → ∀ d → d ∈ ⟦ delay M ⟧' ρ' → R (d ∷ []) (⟦ M ⟧ ρ)
one M E d d∈ = delay-reflect M E (d ∷ []) (single⊆ d∈)

err-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → ω ∈ ⟦ delay M ⟧' ρ' → ω ∈ ⟦ M ⟧ ρ
err-reflect M E ω∈ = R-err (one M E ω ω∈) (here refl)

val-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → val∈ (⟦ delay M ⟧' ρ') → val∈ (⟦ M ⟧ ρ)
val-reflect M E ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = R-val (one M E d d∈) d (here refl) d≢

ne-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → val∈ (⟦ delay M ⟧' ρ') → nonempty (⟦ M ⟧ ρ)
ne-reflect M E v = let ⟨ d , ⟨ d∈ , _ ⟩ ⟩ = val-reflect M E v in ⟨ d , d∈ ⟩

wrong-reflect′ : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → ∀ {P P' : Value → Set}
  → (∀ d s → Corr d s → P s → P' d) → wrong P' (⟦ delay M ⟧' ρ') → wrong P (⟦ M ⟧ ρ)
wrong-reflect′ M E corr ⟨ d , ⟨ d∈ , ⟨ d≢ , np ⟩ ⟩ ⟩ = wrong-reflect corr (one M E d d∈) d (here refl) d≢ np

const-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → ∀ {B} {c : base-rep B} → const c ∈ ⟦ delay M ⟧' ρ' → const c ∈ ⟦ M ⟧ ρ
const-reflect M E c∈ with Obs.shape-obs (unfold (one M E _ c∈)) _ (here refl) (λ ())
... | ⟨ s , ⟨ s∈ , ⟨ _ , refl ⟩ ⟩ ⟩ = s∈

{- the tagged parts of a reflected set are related -}
tag-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → ∀ t W → mem W ⊆ Untag t (⟦ delay M ⟧' ρ')
  → R W (Untag t (⟦ M ⟧ ρ))
tag-reflect M E t W W⊆ =
  Obs.tag-obs (unfold (delay-reflect M E (lmap (tag t) W) mW)) t W (λ d d∈ → ∈-map⁺ (tag t) d∈)
  where
  mW : mem (lmap (tag t) W) ⊆ _
  mW d d∈ with ∈-map⁻ (tag t) d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = W⊆ x x∈

{- a list of ω's, when the source set holds ω -}
R-ω : ∀ {V D} → (∀ w → w ⋵ V → w ≡ ω) → (ω ⋵ V → ω ∈ D) → R V D
R-ω {V} allω err = R-sub {V₁ = []} (λ w w∈ w≢ → ⊥-elim (w≢ (allω w w∈))) err (R-∅ (λ _ ()))

reflect-errs : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → errs n (⟦ del-map-args args ⟧₊' ρ') → errs n (⟦ args ⟧₊ ρ)
reflect-errs {suc n} (M ,, args) E (inj₁ ω∈) = inj₁ (err-reflect M E ω∈)
reflect-errs {suc n} (M ,, args) E (inj₂ ⟨ v , e ⟩) = inj₂ ⟨ val-reflect M E v , reflect-errs args E e ⟩

reflect-vals : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → vals n (⟦ del-map-args args ⟧₊' ρ') → vals n (⟦ args ⟧₊ ρ)
reflect-vals args E vs i = let ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = vs i in R-val (reflect-nth args E i (d ∷ []) (single⊆ d∈)) d (here refl) d≢

{- the cases for case-op: the branch B on the side s of the scrutinee L -}
reflect-branch : ∀ (s : Tag) (L B : AST) {ρ' ρ C} → Envs ρ' ρ
  → ∀ v → tag s v ∈ ⟦ delay L ⟧' ρ' → v ≢ ω → (∀ {a b} → tag s a ~ tag s b → a ~ b)
  → (nonempty (Untag s (⟦ L ⟧ ρ)) → Clean (Untag s (⟦ L ⟧ ρ)) → ⟦ B ⟧ (Untag s (⟦ L ⟧ ρ) • ρ) ⊆ C)
  → ∀ V' → mem V' ⊆ ⟦ delay B ⟧' (Untag s (⟦ delay L ⟧' ρ') • ρ') → R V' C
reflect-branch s L B {ρ'}{ρ} E v sv v≢ s~ B⊆ V' V'⊆ =
  R-mono (B⊆ NE-s cl) (delay-reflect B (envs NE'' NE''' (Con-• cS ρ~) ρ'~' ρ⊳') V' V'⊆)
  where
  open Envs E
  vs = R-val (tag-reflect L E s (v ∷ []) (single⊆ sv)) v (here refl) v≢
  NE-s = ⟨ proj₁ vs , proj₁ (proj₂ vs) ⟩
  cS = Untag-con s s~ (Clos3ᵉ-con L ρ~)
  cl = con-val-clean cS vs
  NE'' = extend-nonempty-env NE NE-s
  NE''' = extend-nonempty-env NE' ⟨ v , sv ⟩
  ρ'~' = Con-• (Untag-con s s~ (Clos4ᵉ-con (delay L) ρ'~)) ρ'~
  ρ⊳' : (Untag s (⟦ delay L ⟧' ρ') • ρ') ⊳ₑ (Untag s (⟦ L ⟧ ρ) • ρ)
  ρ⊳' zero = tag-reflect L E s
  ρ⊳' (suc x) = ρ⊳ x

pair-tag : ∀ {A B : 𝒫 Value} t {d} → tag t d ∈ pairᵉ ⟨ A , ⟨ B , ptt ⟩ ⟩ → ⊥
pair-tag (tupT i) ()
pair-tag leftT ()
pair-tag rightT ()

delay-reflect (` x) E = Envs.ρ⊳ E x

delay-reflect (app ⦅ L ,, N ,, Nil ⦆) {ρ'}{ρ} E V' V'⊆
    with collect (⟦ delay L ⟧' ρ') (⟦ delay N ⟧' ρ') V'
           (λ d d∈ → proj₁ (let-app-≃ (delay L) (delay N) ρ' (Envs.NE' E) (Clos4ᵉ-con (delay L) (Envs.ρ'~ E))) d (V'⊆ d d∈))
... | ⟨ W , ⟨ U , ⟨ Vs , ⟨ W⊆L' , ⟨ U⊆N' , ⟨ cs , ⟨ keep , ωok ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
  R-sub keep err RVs
  where
  L' = ⟦ delay L ⟧' ρ'
  N' = ⟦ delay N ⟧' ρ'
  RVs = Obs.app-obs (unfold (delay-reflect L E W W⊆L')) cs _ (Clos3ᵉ-con N (Envs.ρ~ E))
          (Con-⊆ (Clos4ᵉ-con (delay N) (Envs.ρ'~ E)) U⊆N') (delay-reflect N E U U⊆N')
  src : 𝒫 Value
  src = ⟦ app ⦅ L ,, N ,, Nil ⦆ ⟧ ρ
  {- the code of a target pair is a function, and its environment is not ω -}
  pairs : ∀ c t → ⦅ c , t ⦆ ∈ L' → IsFun c × t ≢ ω
  pairs c t ct∈ = Obs.pair-obs (unfold (one L E _ ct∈)) c t (here refl)
  car-err : ω ∈ carᵉ ⟨ L' , ptt ⟩ → ω ∈ src
  car-err (inj₁ ⟨ t , ct∈ ⟩) = ⊥-elim (proj₁ (pairs ω t ct∈))
  car-err (inj₂ ⟨ _ , inj₁ ω∈ ⟩) = inj₂ ⟨ refl , inj₁ (err-reflect L E ω∈) ⟩
  car-err (inj₂ ⟨ _ , inj₂ wr ⟩) = inj₂ ⟨ refl , inj₂ (inj₁ (wrong-reflect′ L E corr-fun wr)) ⟩
  cdr-err : ω ∈ cdrᵉ ⟨ L' , ptt ⟩ → ω ∈ src
  cdr-err (inj₁ ⟨ c , ct∈ ⟩) = ⊥-elim (proj₂ (pairs c ω ct∈) refl)
  cdr-err (inj₂ ⟨ _ , inj₁ ω∈ ⟩) = inj₂ ⟨ refl , inj₁ (err-reflect L E ω∈) ⟩
  cdr-err (inj₂ ⟨ _ , inj₂ wr ⟩) = inj₂ ⟨ refl , inj₂ (inj₁ (wrong-reflect′ L E corr-fun wr)) ⟩
  {- a code that is a value comes from a target closure, so the source operator is a function -}
  car-fun : val∈ (carᵉ ⟨ L' , ptt ⟩) → Σ[ f ∈ Value ] f ∈ ⟦ L ⟧ ρ × IsFun f
  car-fun ⟨ c , ⟨ inj₁ ⟨ t , ct∈ ⟩ , _ ⟩ ⟩ with Obs.shape-obs (unfold (one L E _ ct∈)) _ (here refl) (λ ())
  ... | ⟨ s , ⟨ s∈ , ⟨ _ , isf ⟩ ⟩ ⟩ = ⟨ s , ⟨ s∈ , isf ⟩ ⟩
  car-fun ⟨ c , ⟨ inj₂ ⟨ refl , _ ⟩ , c≢ ⟩ ⟩ = ⊥-elim (c≢ refl)
  terr : TErr L' N' → ω ∈ src
  terr (inj₁ (inj₁ ω∈)) = car-err ω∈
  terr (inj₁ (inj₂ ⟨ _ , inj₁ ω∈ ⟩)) = cdr-err ω∈
  terr (inj₁ (inj₂ ⟨ vc , inj₂ ⟨ _ , inj₁ ω∈ ⟩ ⟩)) =
    inj₂ ⟨ refl , inj₂ (inj₂ ⟨ car-fun vc , err-reflect N E ω∈ ⟩) ⟩
  terr (inj₁ (inj₂ ⟨ _ , inj₂ ⟨ _ , inj₂ () ⟩ ⟩))
  terr (inj₂ ⟨ ⟨ c , ⟨ inj₁ ⟨ t , ct∈ ⟩ , ⟨ _ , nf ⟩ ⟩ ⟩ , _ ⟩) = ⊥-elim (nf (proj₁ (pairs c t ct∈)))
  terr (inj₂ ⟨ ⟨ c , ⟨ inj₂ ⟨ refl , _ ⟩ , ⟨ c≢ , _ ⟩ ⟩ ⟩ , _ ⟩) = ⊥-elim (c≢ refl)
  err : ω ⋵ V' → ω ∈ src
  err ω∈ with ωok ω∈
  ... | inj₁ i = R-err RVs i
  ... | inj₂ te = terr te

delay-reflect (lit B c ⦅ Nil ⦆) E V' V'⊆ = R-data V'⊆ (λ v v∈ → flat-data (ℬ-flat v (V'⊆ v v∈)))

delay-reflect (prim p ⦅ L ,, M ,, Nil ⦆) {ρ'}{ρ} E V' V'⊆ = R-data V⊆ dt
  where
  V⊆ : mem V' ⊆ ⟦ prim p ⦅ L ,, M ,, Nil ⦆ ⟧ ρ
  V⊆ v v∈ with V'⊆ v v∈
  ... | inj₁ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
    inj₁ ⟨ n , ⟨ m , ⟨ const-reflect L E n∈ , ⟨ const-reflect M E m∈ , refl ⟩ ⟩ ⟩ ⟩
  ... | inj₂ ⟨ refl , inj₁ (inj₁ ω∈) ⟩ = inj₂ ⟨ refl , inj₁ (inj₁ (err-reflect L E ω∈)) ⟩
  ... | inj₂ ⟨ refl , inj₁ (inj₂ ⟨ vL , inj₁ ω∈ ⟩) ⟩ =
    inj₂ ⟨ refl , inj₁ (inj₂ ⟨ val-reflect L E vL , inj₁ (err-reflect M E ω∈) ⟩) ⟩
  ... | inj₂ ⟨ refl , inj₁ (inj₂ ⟨ _ , inj₂ () ⟩) ⟩
  ... | inj₂ ⟨ refl , inj₂ (inj₁ ⟨ wr , vM ⟩) ⟩ =
    inj₂ ⟨ refl , inj₂ (inj₁ ⟨ wrong-reflect′ L E corr-int wr , val-reflect M E vM ⟩) ⟩
  ... | inj₂ ⟨ refl , inj₂ (inj₂ ⟨ vL , wr ⟩) ⟩ =
    inj₂ ⟨ refl , inj₂ (inj₂ ⟨ val-reflect L E vL , wrong-reflect′ M E corr-int wr ⟩) ⟩
  dt : ∀ v → v ⋵ V' → Data v
  dt v v∈ with V'⊆ v v∈
  ... | inj₁ ⟨ n , ⟨ m , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩ = out-data (δ p n m)
  ... | inj₂ ⟨ refl , _ ⟩ = flat-ω

delay-reflect (tuple n ⦅ args ⦆) = reflect-𝒯 args

delay-reflect (get i ⦅ M ,, Nil ⦆) {ρ'}{ρ} E V' V'⊆ =
  R-sub (dropω-keep V') err (R-mono (λ d d∈ → inj₁ d∈) (tag-reflect M E (tupT i) (dropω V') W⊆))
  where
  W⊆ : mem (dropω V') ⊆ Untag (tupT i) (⟦ delay M ⟧' ρ')
  W⊆ d d∈ with V'⊆ d (dropω-⊆ V' d d∈)
  ... | inj₁ t∈ = t∈
  ... | inj₂ ⟨ refl , _ ⟩ = ⊥-elim (dropω-noω V' ω d∈ refl)
  err : ω ⋵ V' → ω ∈ ⟦ get i ⦅ M ,, Nil ⦆ ⟧ ρ
  err ω∈ with V'⊆ ω ω∈
  ... | inj₁ t∈ = inj₁ (R-err (tag-reflect M E (tupT i) (ω ∷ []) (single⊆ t∈)) (here refl))
  ... | inj₂ ⟨ _ , inj₁ ω∈' ⟩ = inj₂ ⟨ refl , inj₁ (err-reflect M E ω∈') ⟩
  ... | inj₂ ⟨ _ , inj₂ wr ⟩ = inj₂ ⟨ refl , inj₂ (wrong-reflect′ M E corr-tup wr) ⟩

delay-reflect (inl-op ⦅ M ,, Nil ⦆) {ρ'}{ρ} E V' V'⊆ = fold record
  { err-obs = λ ω∈ → err-reflect M E (V'⊆ ω ω∈)
  ; shape-obs = shape
  ; pair-obs = λ c t ct∈ → ⊥-elim (V'⊆ _ ct∈)
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V'⊆ _ uv∈) cs)
  ; tag-obs = λ { leftT W W⊆ → lefts W W⊆
                ; rightT W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈)) }
  }
  where
  shape : ∀ d → d ⋵ V' → d ≢ ω → Σ[ s ∈ Value ] s ∈ ⟦ inl-op ⦅ M ,, Nil ⦆ ⟧ ρ × s ≢ ω × Corr d s
  shape d d∈ d≢ with inlᵉ-inv d (V'⊆ d d∈)
  ... | inj₂ ⟨ refl , _ ⟩ = ⊥-elim (d≢ refl)
  ... | inj₁ ⟨ x , ⟨ refl , ⟨ x∈ , x≢ ⟩ ⟩ ⟩ =
    let ⟨ y , ⟨ y∈ , y≢ ⟩ ⟩ = val-reflect M E ⟨ x , ⟨ x∈ , x≢ ⟩ ⟩
    in ⟨ left y , ⟨ ⟨ y∈ , y≢ ⟩ , ⟨ (λ ()) , ⟨ y , refl ⟩ ⟩ ⟩ ⟩
  lefts : ∀ W → mem W ⊆ Untag leftT (mem V') → R W (Untag leftT (⟦ inl-op ⦅ M ,, Nil ⦆ ⟧ ρ))
  lefts [] _ = R-∅ (λ _ ())
  lefts (w ∷ W) W⊆ =
    R-mono (λ d d∈ → ⟨ d∈ , cl d d∈ ⟩) (delay-reflect M E (w ∷ W) (λ d d∈ → proj₁ (V'⊆ _ (W⊆ d d∈))))
    where
    w∈ = V'⊆ _ (W⊆ w (here refl))
    cl = con-val-clean (Clos3ᵉ-con M (Envs.ρ~ E)) (val-reflect M E ⟨ w , w∈ ⟩)

delay-reflect (inr-op ⦅ M ,, Nil ⦆) {ρ'}{ρ} E V' V'⊆ = fold record
  { err-obs = λ ω∈ → err-reflect M E (V'⊆ ω ω∈)
  ; shape-obs = shape
  ; pair-obs = λ c t ct∈ → ⊥-elim (V'⊆ _ ct∈)
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V'⊆ _ uv∈) cs)
  ; tag-obs = λ { rightT W W⊆ → rights W W⊆
                ; leftT W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈)) }
  }
  where
  shape : ∀ d → d ⋵ V' → d ≢ ω → Σ[ s ∈ Value ] s ∈ ⟦ inr-op ⦅ M ,, Nil ⦆ ⟧ ρ × s ≢ ω × Corr d s
  shape d d∈ d≢ with inrᵉ-inv d (V'⊆ d d∈)
  ... | inj₂ ⟨ refl , _ ⟩ = ⊥-elim (d≢ refl)
  ... | inj₁ ⟨ x , ⟨ refl , ⟨ x∈ , x≢ ⟩ ⟩ ⟩ =
    let ⟨ y , ⟨ y∈ , y≢ ⟩ ⟩ = val-reflect M E ⟨ x , ⟨ x∈ , x≢ ⟩ ⟩
    in ⟨ right y , ⟨ ⟨ y∈ , y≢ ⟩ , ⟨ (λ ()) , ⟨ y , refl ⟩ ⟩ ⟩ ⟩
  rights : ∀ W → mem W ⊆ Untag rightT (mem V') → R W (Untag rightT (⟦ inr-op ⦅ M ,, Nil ⦆ ⟧ ρ))
  rights [] _ = R-∅ (λ _ ())
  rights (w ∷ W) W⊆ =
    R-mono (λ d d∈ → ⟨ d∈ , cl d d∈ ⟩) (delay-reflect M E (w ∷ W) (λ d d∈ → proj₁ (V'⊆ _ (W⊆ d d∈))))
    where
    w∈ = V'⊆ _ (W⊆ w (here refl))
    cl = con-val-clean (Clos3ᵉ-con M (Envs.ρ~ E)) (val-reflect M E ⟨ w , w∈ ⟩)

delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) E [] V'⊆ = R-∅ (λ _ ())
delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ'}{ρ} E (w ∷ V') V'⊆
    with V'⊆ w (here refl)
... | inj₁ ⟨ v , ⟨ _ , ⟨ allL , ⟨ _ , ⟨ _ , nv ⟩ ⟩ ⟩ ⟩ ⟩ =
  reflect-branch leftT L M E v lv (λ { refl → nv (here refl) }) (λ a~b → a~b) M⊆ (w ∷ V') V'⊆F
  where
  lv = allL v (here refl)
  cL' = Clos4ᵉ-con (delay L) (Envs.ρ'~ E)
  M⊆ : nonempty (Lefts (⟦ L ⟧ ρ)) → Clean (Lefts (⟦ L ⟧ ρ)) → ⟦ M ⟧ (Lefts (⟦ L ⟧ ρ) • ρ) ⊆ _
  M⊆ ne cl = 𝒞ᵉ-left {⟦ L ⟧ ρ} {λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ N ⟧ (X • ρ)}
               (S3.body-continuous M ρ (Envs.NE E) _ ne)
               (Untag-con leftT (λ c → c) (Clos3ᵉ-con L (Envs.ρ~ E))) cl
  V'⊆F : mem (w ∷ V') ⊆ ⟦ delay M ⟧' (Lefts (⟦ delay L ⟧' ρ') • ρ')
  V'⊆F x x∈ with V'⊆ x x∈
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL' , ⟨ x∈F , _ ⟩ ⟩ ⟩ ⟩ =
    S4.⟦⟧-monotone (delay M) (λ { zero → allL' ; (suc y) → λ d z → z }) x x∈F
  ... | inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ allR , _ ⟩ ⟩ ⟩) = ⊥-elim (cL' _ _ lv (allR u (here refl)))
  ... | inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩) = ⊥-elim (cL' _ _ lv ω∈)
  ... | inj₂ (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩) = ⊥-elim (ni (inl~ e (cL' _ _ lv e∈)))
... | inj₂ (inj₁ ⟨ v , ⟨ _ , ⟨ allR , ⟨ _ , ⟨ _ , nv ⟩ ⟩ ⟩ ⟩ ⟩) =
  reflect-branch rightT L N E v rv (λ { refl → nv (here refl) }) (λ a~b → a~b) N⊆ (w ∷ V') V'⊆G
  where
  rv = allR v (here refl)
  cL' = Clos4ᵉ-con (delay L) (Envs.ρ'~ E)
  N⊆ : nonempty (Rights (⟦ L ⟧ ρ)) → Clean (Rights (⟦ L ⟧ ρ)) → ⟦ N ⟧ (Rights (⟦ L ⟧ ρ) • ρ) ⊆ _
  N⊆ ne cl = 𝒞ᵉ-right {⟦ L ⟧ ρ} {λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ N ⟧ (X • ρ)}
               (S3.body-continuous N ρ (Envs.NE E) _ ne)
               (Untag-con rightT (λ c → c) (Clos3ᵉ-con L (Envs.ρ~ E))) cl
  V'⊆G : mem (w ∷ V') ⊆ ⟦ delay N ⟧' (Rights (⟦ delay L ⟧' ρ') • ρ')
  V'⊆G x x∈ with V'⊆ x x∈
  ... | inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ allR' , ⟨ x∈G , _ ⟩ ⟩ ⟩ ⟩) =
    S4.⟦⟧-monotone (delay N) (λ { zero → allR' ; (suc y) → λ d z → z }) x x∈G
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL , _ ⟩ ⟩ ⟩ = ⊥-elim (cL' _ _ rv (allL u (here refl)))
  ... | inj₂ (inj₂ ⟨ refl , inj₁ ω∈ ⟩) = ⊥-elim (cL' _ _ rv ω∈)
  ... | inj₂ (inj₂ ⟨ refl , inj₂ ⟨ e , ⟨ e∈ , ⟨ _ , ni ⟩ ⟩ ⟩ ⟩) = ⊥-elim (ni (inr~ e (cL' _ _ rv e∈)))
... | inj₂ (inj₂ ⟨ refl , e ⟩) = R-ω allω (λ _ → err e)
  where
  cL' = Clos4ᵉ-con (delay L) (Envs.ρ'~ E)
  inj-~ : ∀ d e → IsInj d → d ~ e → IsInj e
  inj-~ (left x) e _ c = inl~ e c
  inj-~ (right x) e _ c = inr~ e c
  {- the scrutinee holds ω, or a value that is not an injection: no branch runs -}
  nobranch : ∀ {d} → (ω ∈ ⟦ delay L ⟧' ρ' ⊎ wrong IsInj (⟦ delay L ⟧' ρ')) → d ∈ ⟦ delay L ⟧' ρ' → IsInj d → ⊥
  nobranch {left x} (inj₁ ω∈) d∈ _ with cL' _ _ ω∈ d∈
  ... | ()
  nobranch {right x} (inj₁ ω∈) d∈ _ with cL' _ _ ω∈ d∈
  ... | ()
  nobranch {d} (inj₂ ⟨ e' , ⟨ e'∈ , ⟨ _ , ni ⟩ ⟩ ⟩) d∈ inj = ni (inj-~ d e' inj (cL' _ _ d∈ e'∈))
  allω : ∀ x → x ⋵ (ω ∷ V') → x ≡ ω
  allω x x∈ with V'⊆ x x∈
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL , _ ⟩ ⟩ ⟩ = ⊥-elim (nobranch e (allL u (here refl)) tt)
  ... | inj₂ (inj₁ ⟨ u , ⟨ U , ⟨ allR , _ ⟩ ⟩ ⟩) = ⊥-elim (nobranch e (allR u (here refl)) tt)
  ... | inj₂ (inj₂ ⟨ refl , _ ⟩) = refl
  err : (ω ∈ ⟦ delay L ⟧' ρ' ⊎ wrong IsInj (⟦ delay L ⟧' ρ')) → ω ∈ ⟦ case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆ ⟧ ρ
  err (inj₁ ω∈) = inj₂ (inj₂ ⟨ refl , inj₁ (err-reflect L E ω∈) ⟩)
  err (inj₂ wr) = inj₂ (inj₂ ⟨ refl , inj₂ (wrong-reflect′ L E corr-inj wr) ⟩)

delay-reflect (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) E [] V'⊆ = R-∅ (λ _ ())
delay-reflect (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ'}{ρ} E (w ∷ V') V'⊆ with V'⊆ w (here refl)
... | inj₁ ⟨ U₀ , ⟨ _ , ⟨ U₀⊆ , ⟨ neU₀ , nU₀ ⟩ ⟩ ⟩ ⟩
    with ne-mem neU₀ (λ d d∈ → d∈)
... | ⟨ u₀ , u₀∈ ⟩
    with letᵉ-collect (S4.body-mono (delay N) ρ') clM' (w ∷ V') V'⊆
  where
  clM' = con-val-clean (Clos4ᵉ-con (delay M) (Envs.ρ'~ E)) ⟨ u₀ , ⟨ U₀⊆ u₀ u₀∈ , (λ { refl → nU₀ u₀∈ }) ⟩ ⟩
... | ⟨ U , ⟨ U⊆ , V'⊆N ⟩ ⟩ =
  R-mono (proj₂ (letᵉ-β (S3.body-mono N ρ) (S3.body-continuous N ρ NE _ NE-M) cM clM))
    (delay-reflect N (envs NE'' NE''' (Con-• cM ρ~) (Con-• (Con-⊆ (Clos4ᵉ-con (delay M) ρ'~) U'⊆) ρ'~) ρ⊳')
       (w ∷ V') (λ d d∈ → S4.body-mono (delay N) ρ' (λ x x∈ → there x∈) d (V'⊆N d d∈)))
  where
  open Envs E
  U' = u₀ ∷ U
  U'⊆ : mem U' ⊆ ⟦ delay M ⟧' ρ'
  U'⊆ _ (here refl) = U₀⊆ u₀ u₀∈
  U'⊆ d (there d∈) = U⊆ d d∈
  cM = Clos3ᵉ-con M ρ~
  vM = val-reflect M E ⟨ u₀ , ⟨ U₀⊆ u₀ u₀∈ , (λ { refl → nU₀ u₀∈ }) ⟩ ⟩
  NE-M = ⟨ proj₁ vM , proj₁ (proj₂ vM) ⟩
  clM = con-val-clean cM vM
  NE'' = extend-nonempty-env NE NE-M
  NE''' = extend-nonempty-env NE' ⟨ u₀ , here refl ⟩
  ρ⊳' : (mem U' • ρ') ⊳ₑ (⟦ M ⟧ ρ • ρ)
  ρ⊳' zero Y' Y'⊆ = delay-reflect M E Y' (λ d d∈ → U'⊆ d (Y'⊆ d d∈))
  ρ⊳' (suc x) = ρ⊳ x
delay-reflect (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ'}{ρ} E (w ∷ V') V'⊆ | inj₂ ⟨ refl , inj₁ () ⟩
delay-reflect (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ'}{ρ} E (w ∷ V') V'⊆ | inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩ =
  ⊥-elim (nf (Λᵉ-fun d d∈))
delay-reflect (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ'}{ρ} E (w ∷ V') V'⊆ | inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩ =
  R-ω allω (λ _ → inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , err-reflect M E ω∈ ⟩) ⟩)
  where
  cM' = Clos4ᵉ-con (delay M) (Envs.ρ'~ E)
  allω : ∀ x → x ⋵ (ω ∷ V') → x ≡ ω
  allω x x∈ with V'⊆ x x∈
  ... | inj₁ ⟨ U , ⟨ _ , ⟨ U⊆ , ⟨ neU , nU ⟩ ⟩ ⟩ ⟩ = ⊥-elim (ω-noerr cM' U U⊆ neU nU ω∈)
  ... | inj₂ ⟨ refl , _ ⟩ = refl

delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) {ρ'}{ρ} E V' V'⊆ =
  fold record
  { err-obs = err
  ; shape-obs = shape
  ; pair-obs = λ c t ct∈ → let ⟨ c∈ , ⟨ _ , ⟨ _ , t≢ ⟩ ⟩ ⟩ = V'⊆ _ ct∈ in ⟨ Λᵉ-fun c c∈ , t≢ ⟩
  ; app-obs = clos-app
  ; tag-obs = λ t W W⊆ → R-∅ (λ d d∈ → pair-tag t (V'⊆ _ (W⊆ d d∈)))
  }
  where
  open Envs E
  T' = 𝒯ᵉ n (⟦ del-map-args fvs ⟧₊' ρ')
  T = 𝒯ᵉ n (⟦ fvs ⟧₊ ρ)
  D = ⟦ clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆ ⟧ ρ
  cT = Clos3ᵉ-con (tuple n ⦅ fvs ⦆) ρ~

  T-val : ∀ {t'} → t' ∈ T' → t' ≢ ω → val∈ T
  T-val {t'} t'∈ t'≢ = R-val (reflect-𝒯 fvs E (t' ∷ []) (single⊆ t'∈)) t' (here refl) t'≢

  {- a closure whose environment has a value has the value ν -}
  ν∈ : val∈ T → ν ∈ D
  ν∈ ⟨ t , ⟨ t∈ , t≢ ⟩ ⟩ =
    inj₁ ⟨ t ∷ [] , ⟨ ⟨ tt , ⟨ (λ ()) , ⟨ ≈-single , nt ⟩ ⟩ ⟩ , ⟨ single⊆ t∈ , ⟨ (λ ()) , nt ⟩ ⟩ ⟩ ⟩
    where nt = λ { (here eq) → t≢ (sym eq) }

  err : ω ⋵ V' → ω ∈ D
  err ω∈ with V'⊆ ω ω∈
  ... | inj₁ ()
  ... | inj₂ ⟨ _ , inj₁ e ⟩ = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , reflect-errs fvs E e ⟩) ⟩
  ... | inj₂ ⟨ _ , inj₂ () ⟩

  shape : ∀ d → d ⋵ V' → d ≢ ω → Σ[ s ∈ Value ] s ∈ D × s ≢ ω × Corr d s
  shape d d∈ d≢ with pairᵉ-inv d (V'⊆ d d∈)
  ... | inj₂ ⟨ refl , _ ⟩ = ⊥-elim (d≢ refl)
  ... | inj₁ ⟨ c , ⟨ t' , ⟨ refl , ⟨ _ , ⟨ t'∈ , ⟨ _ , t'≢ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = ⟨ ν , ⟨ ν∈ (T-val t'∈ t'≢) , ⟨ (λ ()) , tt ⟩ ⟩ ⟩

  Cdrs⊆T' : Cdrs V' ⊆ T'
  Cdrs⊆T' fv ⟨ _ , e∈ ⟩ = proj₁ (proj₂ (V'⊆ _ e∈))

  clos-app : ∀ {U' W'} → Calls V' U' W' → ∀ E → Con E → Con (mem U') → R U' E → R W' (D ● E)
  clos-app {W' = []} _ Es _ U'~ rU = R-∅ (λ _ ())
  clos-app {U'} {w ∷ W'} cs Es cE U'~ rU =
    R-mono (ΛΛᵉ-β cT cE clT clE (S3.body2-continuous N (λ _ → ⌈ ω ⌉) (λ _ → ⟨ ω , refl ⟩) NE-T NE-E))
      (delay-reflect N (envs NE-ρs NE-ρ'' (Con-• cE (Con-• cT (λ _ → Con-⌈⌉ ω))) ρ''~ ρ''⊳ρs) (w ∷ W') W⊆B)
    where
    wit = Calls.results cs w (here refl)
    ent = proj₁ (proj₂ wit)
    U₀ = proj₁ wit
    u₀ = proj₁ (ne-mem (proj₁ (proj₂ (proj₂ wit))) (λ d d∈ → d∈))
    u₀∈U₀ = proj₂ (ne-mem (proj₁ (proj₂ (proj₂ wit))) (λ d d∈ → d∈))
    u₀∈ = proj₂ (proj₂ (proj₂ wit)) u₀ u₀∈U₀
    vE = R-val rU u₀ u₀∈ (λ eq → Calls.noerr cs (subst (_⋵ U') eq u₀∈))
    NE-E = ⟨ proj₁ vE , proj₁ (proj₂ vE) ⟩
    clE = con-val-clean cE vE
    fv₀ = proj₁ (ne-mem (CarEntry.FV≢[] ent) (λ d d∈ → d∈))
    fv₀∈ = proj₂ (ne-mem (CarEntry.FV≢[] ent) (λ d d∈ → d∈))
    fv₀∈T' = Cdrs⊆T' fv₀ (CarEntry.FV⊆ ent fv₀ fv₀∈)
    fv₀≢ : fv₀ ≢ ω
    fv₀≢ = let ⟨ u , i ⟩ = CarEntry.FV⊆ ent fv₀ fv₀∈ in proj₂ (proj₂ (proj₂ (V'⊆ _ i)))
    vT = T-val fv₀∈T' fv₀≢
    NE-T = ⟨ proj₁ vT , proj₁ (proj₂ vT) ⟩
    clT = con-val-clean cT vT

    ρ'' : Env
    ρ'' = mem U' • Cdrs V' • (λ _ → ⌈ ω ⌉)

    W⊆B : mem (w ∷ W') ⊆ ⟦ delay N ⟧' ρ''
    W⊆B x x∈ with Calls.results cs x x∈
    ... | ⟨ U₁ , ⟨ car-entry FV t e∈ neFV FV⊆ , ⟨ _ , U₁⊆ ⟩ ⟩ ⟩ with V'⊆ _ e∈
    ... | ⟨ ⟨ x∈B , _ ⟩ , _ ⟩ =
      S4.⟦⟧-monotone (delay N) (λ { zero → U₁⊆ ; (suc zero) → FV⊆ ; (suc (suc y)) → λ d z → z })
        x (proj₁ x∈B)

    ρ''~ : Con-env ρ''
    ρ''~ = Con-• U'~ (Con-• (Con-⊆ (Clos4ᵉ-con (L4.tuple n ⦅ del-map-args fvs ⦆') ρ'~) Cdrs⊆T')
                            (λ _ → Con-⌈⌉ ω))

    NE-ρs = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) NE-T) NE-E
    NE-ρ'' = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩)
               ⟨ fv₀ , CarEntry.FV⊆ ent fv₀ fv₀∈ ⟩) ⟨ u₀ , u₀∈ ⟩

    ρ''⊳ρs : ρ'' ⊳ₑ (Es • T • (λ _ → ⌈ ω ⌉))
    ρ''⊳ρs zero Y' Y'⊆ = R-⊆ Y'⊆ rU
    ρ''⊳ρs (suc zero) Y' Y'⊆ = reflect-𝒯 fvs E Y' (λ y y∈ → Cdrs⊆T' y (Y'⊆ y y∈))
    ρ''⊳ρs (suc (suc x)) Y' Y'⊆ = R-data Y'⊆ (λ v v∈ → flat-data (Init-flat (Y'⊆ v v∈)))

reflect-nth (M ,, args) E zero = delay-reflect M E
reflect-nth (M ,, args) E (suc i) = reflect-nth args E i

reflect-𝒯 {zero} args {ρ'}{ρ} E V' V'⊆ = R-data src (λ v v∈ → flat-data (fl v (V'⊆ v v∈)))
  where
  fl : ∀ v → v ∈ 𝒯ᵉ zero (⟦ del-map-args args ⟧₊' ρ') → Flat v
  fl ⟨⟩ _ = flat-⟨⟩
  src : mem V' ⊆ 𝒯ᵉ zero (⟦ args ⟧₊ ρ)
  src v v∈ with V'⊆ v v∈
  src ⟨⟩ v∈ | _ = tt
reflect-𝒯 {suc n} args {ρ'}{ρ} E V' V'⊆ = fold record
  { err-obs = λ ω∈ → reflect-errs args E (V'⊆ ω ω∈)
  ; shape-obs = shape
  ; pair-obs = λ c t ct∈ → ⊥-elim (V'⊆ _ ct∈)
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V'⊆ _ uv∈) cs)
  ; tag-obs = λ { (tupT i) W W⊆ → nth-case i W W⊆
                ; leftT W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → R-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈)) }
  }
  where
  Ds' = ⟦ del-map-args args ⟧₊' ρ'
  Ds = ⟦ args ⟧₊ ρ

  shape : ∀ d → d ⋵ V' → d ≢ ω → Σ[ s ∈ Value ] s ∈ 𝒯ᵉ (suc n) Ds × s ≢ ω × Corr d s
  shape d d∈ d≢ with 𝒯ᵉ-inv (suc n) d (V'⊆ d d∈)
  ... | inj₁ ⟨ refl , _ ⟩ = ⊥-elim (d≢ refl)
  ... | inj₂ (inj₂ ⟨ () , _ ⟩)
  ... | inj₂ (inj₁ ⟨ i , ⟨ x , ⟨ refl , ⟨ _ , vs' ⟩ ⟩ ⟩ ⟩) =
    let vs = reflect-vals args E vs'
        ⟨ y , ⟨ y∈ , _ ⟩ ⟩ = vs i
    in ⟨ tup[ i ] y , ⟨ ⟨ refl , ⟨ y∈ , vs ⟩ ⟩ , ⟨ (λ ()) , ⟨ y , refl ⟩ ⟩ ⟩ ⟩

  nth-case : ∀ {m} (i : Fin m) W' → mem W' ⊆ Untag (tupT i) (mem V')
    → R W' (Untag (tupT i) (𝒯ᵉ (suc n) Ds))
  nth-case i [] _ = R-∅ (λ _ ())
  nth-case i (w ∷ W') W'⊆ with V'⊆ _ (W'⊆ w (here refl))
  ... | ⟨ refl , ⟨ _ , vs' ⟩ ⟩ =
    R-mono (λ d d∈ → ⟨ refl , ⟨ d∈ , reflect-vals args E vs' ⟩ ⟩)
      (reflect-nth args E i (w ∷ W') sub)
    where
    sub : mem (w ∷ W') ⊆ nthD Ds' i
    sub d d∈ with V'⊆ _ (W'⊆ d d∈)
    ... | ⟨ refl , ⟨ d∈' , _ ⟩ ⟩ = d∈'

{- The end theorem (backward half) --------------------------------------------}

Envs₀ : Envs ρ₀ ρ₀
Envs₀ = envs (λ _ → ⟨ ω , refl ⟩) (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ _ → Con-⌈⌉ ω) Init⊳Init

reflect-error : ∀ (M : AST) → ω ∈ ⟦ delay M ⟧' ρ₀ → ω ∈ ⟦ M ⟧ ρ₀
reflect-error M = err-reflect M Envs₀

reflect-const : ∀ (M : AST) {B} (c : base-rep B) → const c ∈ ⟦ delay M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀
reflect-const M c = const-reflect M Envs₀

reflect-val : ∀ (M : AST) → val∈ (⟦ delay M ⟧' ρ₀) → val∈ (⟦ M ⟧ ρ₀)
reflect-val M = val-reflect M Envs₀
