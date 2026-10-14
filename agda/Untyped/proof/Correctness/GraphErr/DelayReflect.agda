{-

  Backward (reflect) direction of the correctness of the delay pass
  (Clos3 → Clos4) in the graph model with errors, with the
  relation of DelayRel, as in proof/Correctness/Graph/DelayReflectFinite.agda.

  The errors are reflected by the monad: each operator of the target
  is binds and checks around the graph model's kernel, and R-bind and
  R-check reflect them to the source's. What is left for each
  construct is the kernel, as in the graph model. The application is
  the one construct whose target binds differ from the source's: the
  target binds the closure, its code and environment (fst, snd) and the
  argument, and checks the code late; its errors are the source's, as
  a target closure is a pair whose code is a function (pair-obs).

-}

open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.Ops
  using (⋆; 𝒯; proj; inl; inr; 𝒞; pair; car; cdr; letD; 𝒞-left; 𝒞-right; letD-collect; ⋆-mono; ⋆₂-mono)
open import proof.Framework.GraphModel.DomainUtil using (cdr-witness; 𝒯0-flat)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Semantics.GraphErr.Prim using (primD; out)
open import Untyped.Language.Clos3 as L3
open import Untyped.Language.Clos4 as L4
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import Untyped.proof.Semantics.GraphErr.Clos3 as S3
open import Untyped.proof.Semantics.GraphErr.Clos4 as S4 renaming
  (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
open import Untyped.Compiler.Delay using (delay; del-map-args)
open import proof.Framework.GraphModel.Env using (nonempty-env; •-~; extend-nonempty-env)
open import Untyped.proof.Correctness.GraphErr.DelayRel
open import Untyped.proof.Correctness.GraphErr.DelayApp using (let-app-≃)

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
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)
open import Level using (lift; lower)
open import Language.Prim using (δ)

module Untyped.proof.Correctness.GraphErr.DelayReflect where

clean⌊⌋ : ∀ {D} → Clean ⌊ D ⌋
clean⌊⌋ d d∈ = proj₂ d∈

{- Collecting the finite witnesses of a target call ----------------------------}

{- a target call V' ⊆ (car X' ● cdr X') ● N' is a batch of calls of a
   finite W ⊆ X' on a finite U ⊆ N' -}
collect : ∀ (X' N' : 𝒫 Value) → Clean N' → ∀ V'
  → mem V' ⊆ ⋆ ⟨ ⋆ ⟨ car ⟨ X' , ptt ⟩ , ⟨ cdr ⟨ X' , ptt ⟩ , ptt ⟩ ⟩ , ⟨ N' , ptt ⟩ ⟩
  → Σ[ W ∈ List Value ] Σ[ U ∈ List Value ] mem W ⊆ X' × mem U ⊆ N' × Calls W U V'
collect X' N' clN [] _ =
  ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , record { results = λ _ () ; args = λ _ () ; noerr = λ () } ⟩ ⟩ ⟩ ⟩
collect X' N' clN (w ∷ V') V'⊆
    with V'⊆ w (here refl) | collect X' N' clN V' (λ d d∈ → V'⊆ d (there d∈))
... | ⟨ U₀ , ⟨ ⟨ FV , ⟨ ⟨ t , e∈X' ⟩ , ⟨ FV⊆Cdr , neFV ⟩ ⟩ ⟩ , ⟨ U₀⊆N' , neU₀ ⟩ ⟩ ⟩
    | ⟨ W , ⟨ U , ⟨ W⊆ , ⟨ U⊆ , cs ⟩ ⟩ ⟩ ⟩
    with cdr-witness FV FV⊆Cdr
... | ⟨ C , ⟨ C⊆X' , FV⊆C ⟩ ⟩ =
  ⟨ e ∷ (C ++ W) , ⟨ U₀ ++ U , ⟨ W⊆' , ⟨ U⊆' , record { results = res ; args = arg ; noerr = λ ω∈ → clN ω (U⊆' ω ω∈) refl } ⟩ ⟩ ⟩ ⟩
  where
  e = ⦅ FV ↦ (U₀ ↦ w) , t ⦆
  inW : Pairs⊆ W (e ∷ (C ++ W))
  inW u v d∈ = there (∈-++⁺ʳ C d∈)
  W⊆' : mem (e ∷ (C ++ W)) ⊆ X'
  W⊆' _ (here refl) = e∈X'
  W⊆' d (there d∈) with ∈-++⁻ C d∈
  ... | inj₂ d∈W = W⊆ d d∈W
  ... | inj₁ d∈C = C⊆X' d d∈C
  U⊆' : mem (U₀ ++ U) ⊆ N'
  U⊆' d d∈ with ∈-++⁻ U₀ d∈
  ... | inj₁ d∈U₀ = U₀⊆N' d d∈U₀
  ... | inj₂ d∈U = U⊆ d d∈U
  ent : CarEntry (e ∷ (C ++ W)) U₀ w
  ent = car-entry FV t (here refl) neFV (λ d d∈ → let ⟨ u , i ⟩ = FV⊆C d d∈ in ⟨ u , there (∈-++⁺ˡ i) ⟩)
  res : ∀ x → x ⋵ (w ∷ V') → Σ[ U₁ ∈ List Value ] CarEntry (e ∷ (C ++ W)) U₁ x × U₁ ≢ [] × mem U₁ ⊆ mem (U₀ ++ U)
  res _ (here refl) = ⟨ U₀ , ⟨ ent , ⟨ neU₀ , (λ d → ∈-++⁺ˡ) ⟩ ⟩ ⟩
  res x (there x∈) = let ⟨ U₁ , ⟨ e₁ , ⟨ ne , U₁⊆ ⟩ ⟩ ⟩ = Calls.results cs x x∈
                     in ⟨ U₁ , ⟨ CarEntry-⊆ inW e₁ , ⟨ ne , (λ d d∈ → ∈-++⁺ʳ U₀ (U₁⊆ d d∈)) ⟩ ⟩ ⟩
  arg : ∀ u → u ⋵ (U₀ ++ U) → Σ[ U₁ ∈ List Value ] Σ[ x ∈ Value ] CarEntry (e ∷ (C ++ W)) U₁ x × u ⋵ U₁
  arg u u∈ with ∈-++⁻ U₀ u∈
  ... | inj₁ u∈U₀ = ⟨ U₀ , ⟨ w , ⟨ ent , u∈U₀ ⟩ ⟩ ⟩
  ... | inj₂ u∈U = let ⟨ U₁ , ⟨ x , ⟨ e₁ , u∈₁ ⟩ ⟩ ⟩ = Calls.args cs u u∈U
                   in ⟨ U₁ , ⟨ x , ⟨ CarEntry-⊆ inW e₁ , u∈₁ ⟩ ⟩ ⟩

{- Kernels, on related sets of values -------------------------------------------}

tag-R : ∀ {X' X} → Rel X' X → ∀ t → Rel (Untag t X') (Untag t X)
tag-R h t W W⊆ = Obs.tag-obs (unfold (h (lmap (tag t) W) mW)) t W (λ d d∈ → ∈-map⁺ (tag t) d∈)
  where
  mW : mem (lmap (tag t) W) ⊆ _
  mW d d∈ with ∈-map⁻ (tag t) d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = W⊆ x x∈

inl-R : ∀ {X' X} → Clean X' → Rel X' X → Rel (inl ⟨ X' , ptt ⟩) (inl ⟨ X , ptt ⟩)
inl-R {X'} {X} cl h V V⊆ = fold record
  { err-obs = λ ω∈ → ⊥-elim (V⊆ ω ω∈)
  ; const-obs = λ c c∈ → ⊥-elim (V⊆ _ c∈)
  ; kind-obs = λ d d∈ _ → kd d (V⊆ d d∈)
  ; pair-obs = λ c t ct∈ → ⊥-elim (V⊆ _ ct∈)
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V⊆ _ uv∈) cs)
  ; tag-obs = λ { leftT W W⊆ → h W (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈)) } }
  where
  kd : ∀ d → d ∈ inl ⟨ X' , ptt ⟩ → Σ[ s ∈ Value ] s ∈ ⌊ inl ⟨ X , ptt ⟩ ⌋ × tgt (kind s) ≡ kind d
  kd (left d) d∈ = let ⟨ s , ⟨ s∈ , _ ⟩ ⟩ = R-kind (h _ (single⊆ d∈)) (cl d d∈) in ⟨ left s , ⟨ ⟨ proj₁ s∈ , (λ ()) ⟩ , refl ⟩ ⟩

inr-R : ∀ {X' X} → Clean X' → Rel X' X → Rel (inr ⟨ X' , ptt ⟩) (inr ⟨ X , ptt ⟩)
inr-R {X'} {X} cl h V V⊆ = fold record
  { err-obs = λ ω∈ → ⊥-elim (V⊆ ω ω∈)
  ; const-obs = λ c c∈ → ⊥-elim (V⊆ _ c∈)
  ; kind-obs = λ d d∈ _ → kd d (V⊆ d d∈)
  ; pair-obs = λ c t ct∈ → ⊥-elim (V⊆ _ ct∈)
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V⊆ _ uv∈) cs)
  ; tag-obs = λ { rightT W W⊆ → h W (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; leftT W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈)) } }
  where
  kd : ∀ d → d ∈ inr ⟨ X' , ptt ⟩ → Σ[ s ∈ Value ] s ∈ ⌊ inr ⟨ X , ptt ⟩ ⌋ × tgt (kind s) ≡ kind d
  kd (right d) d∈ = let ⟨ s , ⟨ s∈ , _ ⟩ ⟩ = R-kind (h _ (single⊆ d∈)) (cl d d∈) in ⟨ right s , ⟨ ⟨ proj₁ s∈ , (λ ()) ⟩ , refl ⟩ ⟩

primD-R : ∀ {p X' X Y' Y} → Rel X' X → Rel Y' Y
  → Rel (primD p ⟨ X' , ⟨ Y' , ptt ⟩ ⟩) (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩)
primD-R {p} {X'} {X} {Y'} {Y} hX hY V V⊆ = R-data V⊆' dt
  where
  cst : ∀ {A' A} {c : base-rep Int} → Rel A' A → const c ∈ A' → const c ∈ A
  cst {c = c} h c∈ = Obs.const-obs (unfold (h (const c ∷ []) (single⊆ c∈))) c (here refl)
  V⊆' : mem V ⊆ primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩
  V⊆' v v∈ with V⊆ v v∈
  ... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ = ⟨ n , ⟨ m , ⟨ cst hX n∈ , ⟨ cst hY m∈ , refl ⟩ ⟩ ⟩ ⟩
  dt : ∀ v → v ⋵ V → Data v
  dt v v∈ with V⊆ v v∈
  ... | ⟨ n , ⟨ m , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩ = out-data (δ p n m)

𝒯-R : ∀ n {Xs' Xs} → (∀ i → Clean (nthD Xs' i)) → (∀ i → Rel (nthD Xs' i) (nthD Xs i)) → Rel (𝒯 n Xs') (𝒯 n Xs)
𝒯-R zero cl hs V V⊆ =
  R-data (λ v v∈ → proj₁ (𝒯0-flat v (V⊆ v v∈))) (λ v v∈ → flat-data (proj₂ (𝒯0-flat v (V⊆ v v∈))))
𝒯-R (suc n) {Xs'} {Xs} cl hs V V⊆ = fold record
  { err-obs = λ ω∈ → ⊥-elim (V⊆ ω ω∈)
  ; const-obs = λ c c∈ → ⊥-elim (V⊆ _ c∈)
  ; kind-obs = λ d d∈ _ → kd d (V⊆ d d∈)
  ; pair-obs = λ c t ct∈ → ⊥-elim (V⊆ _ ct∈)
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V⊆ _ uv∈) cs)
  ; tag-obs = λ { (tupT i) W W⊆ → nth-case i W W⊆
                ; leftT W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈)) } }
  where
  comp-ne : ∀ j → nonempty (nthD Xs' j) → nonempty (nthD Xs j)
  comp-ne j ⟨ d , d∈ ⟩ = let ⟨ s , ⟨ s∈ , _ ⟩ ⟩ = R-kind (hs j _ (single⊆ d∈)) (cl j d d∈) in ⟨ s , proj₁ s∈ ⟩
  kd : ∀ d → d ∈ 𝒯 (suc n) Xs' → Σ[ s ∈ Value ] s ∈ ⌊ 𝒯 (suc n) Xs ⌋ × tgt (kind s) ≡ kind d
  kd (tup[ i ] x) ⟨ refl , ⟨ x∈ , ne ⟩ ⟩ =
    let ⟨ y , y∈ ⟩ = comp-ne i ⟨ x , x∈ ⟩
    in ⟨ tup[ i ] y , ⟨ ⟨ ⟨ refl , ⟨ y∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩ , (λ ()) ⟩ , refl ⟩ ⟩
  nth-case : ∀ {m} (i : Fin m) W' → mem W' ⊆ Untag (tupT i) (mem V) → R W' (Untag (tupT i) (𝒯 (suc n) Xs))
  nth-case i [] _ = R-∅ (λ _ ())
  nth-case i (w ∷ W') W'⊆ with V⊆ _ (W'⊆ w (here refl))
  ... | ⟨ refl , ⟨ _ , ne ⟩ ⟩ = R-mono (λ d d∈ → ⟨ refl , ⟨ d∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩) (hs i (w ∷ W') sub)
    where
    sub : mem (w ∷ W') ⊆ nthD Xs' i
    sub d d∈ with V⊆ _ (W'⊆ d d∈)
    ... | ⟨ refl , ⟨ d∈' , _ ⟩ ⟩ = d∈'

{- n binds reflect to n binds -}
R-binds : ∀ n {Ds' Ds : Results (𝒫 Value) (replicate n ■)} {K' K}
  → (∀ i → Rel (nthD Ds' i) (nthD Ds i)) → (∀ i → Con (nthD Ds i))
  → (∀ {Xs' Xs} → (∀ i → Clean (nthD Xs' i)) → (∀ i → Rel (nthD Xs' i) (nthD Xs i)) → Rel (K' Xs') (K Xs))
  → Rel (binds n Ds' K') (binds n Ds K)
R-binds zero h c hK = hK (λ ()) (λ ())
R-binds (suc n) {⟨ D' , Ds' ⟩} {⟨ D , Ds ⟩} {K'} {K} h c hK =
  R-bind {F' = λ X' → binds n Ds' (λ Xs' → K' ⟨ X' , Xs' ⟩)} {F = λ X → binds n Ds (λ Xs → K ⟨ X , Xs ⟩)} (c zero) (h zero)
    λ _ _ hX → R-binds n (λ i → h (suc i)) (λ i → c (suc i))
      (λ cl hs → hK (λ { zero → clean⌊⌋ ; (suc i) → cl i }) (λ { zero → hX ; (suc i) → hs i }))

{- The fundamental lemma ------------------------------------------------------}

record Envs (ρ' ρ : Env) : Set₁ where
  constructor envs
  field
    NE : nonempty-env ρ
    NE' : nonempty-env ρ'
    ρ~ : Con-env ρ
    ρ'~ : Con-env ρ'
    ρ⊳ : ρ' ⊳ₑ ρ

args-con : ∀ {n} (args : L3.Args (replicate n ■)) {ρ} → Con-env ρ → ∀ i → Con (nthD (⟦ args ⟧₊ ρ) i)
args-con {suc n} (M ,, args) c zero = Clos3ᵐ-con M c
args-con {suc n} (M ,, args) c (suc i) = args-con args c i

delay-reflect : ∀ (M : AST) {ρ' ρ} → Envs ρ' ρ → Rel (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
reflect-nth : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → (i : Fin n) → Rel (nthD (⟦ del-map-args args ⟧₊' ρ') i) (nthD (⟦ args ⟧₊ ρ) i)
reflect-𝒯 : ∀ {n} (args : L3.Args (replicate n ■)) {ρ' ρ} → Envs ρ' ρ
  → Rel (𝒯ᵐ n (⟦ del-map-args args ⟧₊' ρ')) (𝒯ᵐ n (⟦ args ⟧₊ ρ))

delay-reflect (` x) E = Envs.ρ⊳ E x

delay-reflect (lit B c ⦅ Nil ⦆) E V V⊆ = R-data V⊆ (λ v v∈ → flat-data (ℬ-flat v (V⊆ v v∈)))

delay-reflect (prim p ⦅ L ,, M ,, Nil ⦆) {ρ'} {ρ} E =
  R-bind {F' = λ X → ⟦ delay M ⟧' ρ' ≫= K X} {F = λ X → ⟦ M ⟧ ρ ≫= K X} (Clos3ᵐ-con L (Envs.ρ~ E)) (delay-reflect L E) λ _ _ hX →
  R-bind {F' = K _} {F = K _} (Clos3ᵐ-con M (Envs.ρ~ E)) (delay-reflect M E) λ _ _ hY →
  R-check {base Int} clean⌊⌋ hX (R-check {base Int} clean⌊⌋ hY (primD-R hX hY))
  where K = λ X Y → checked (base Int) X (checked (base Int) Y (primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩))

delay-reflect (tuple n ⦅ args ⦆) = reflect-𝒯 args

delay-reflect (get {n} i ⦅ M ,, Nil ⦆) E =
  R-bind {F' = λ X → checked (tup n) X (proj i ⟨ X , ptt ⟩)} {F = λ X → checked (tup n) X (proj i ⟨ X , ptt ⟩)}
    (Clos3ᵐ-con M (Envs.ρ~ E)) (delay-reflect M E) λ _ _ hX → R-check {tup n} clean⌊⌋ hX (tag-R hX (tupT i))

delay-reflect (inl-op ⦅ M ,, Nil ⦆) E =
  R-bind {F' = λ X → inl ⟨ X , ptt ⟩} {F = λ X → inl ⟨ X , ptt ⟩} (Clos3ᵐ-con M (Envs.ρ~ E)) (delay-reflect M E) λ _ _ hX → inl-R clean⌊⌋ hX

delay-reflect (inr-op ⦅ M ,, Nil ⦆) E =
  R-bind {F' = λ X → inr ⟨ X , ptt ⟩} {F = λ X → inr ⟨ X , ptt ⟩} (Clos3ᵐ-con M (Envs.ρ~ E)) (delay-reflect M E) λ _ _ hX → inr-R clean⌊⌋ hX

delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) {ρ'} {ρ} E =
  R-bind {F' = λ Y → checked inj Y (𝒞 ⟨ Y ⇂ ValPayload , ⟨ F₁' , ⟨ F₂' , ptt ⟩ ⟩ ⟩)}
         {F = λ Y → checked inj Y (𝒞 ⟨ Y ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)}
    (Clos3ᵐ-con L ρ~) (delay-reflect L E) λ _ _ hX → R-check {inj} clean⌊⌋ hX (K hX)
  where
  open Envs E
  X' = ⌊ ⟦ delay L ⟧' ρ' ⌋ ⇂ ValPayload
  X = ⌊ ⟦ L ⟧ ρ ⌋ ⇂ ValPayload
  cX' : Con X'
  cX' = Con-⊆ (Clos4ᵐ-con (delay L) ρ'~) (λ d d∈ → proj₁ (proj₁ d∈))
  cX : Con X
  cX = Con-⊆ (Clos3ᵐ-con L ρ~) (λ d d∈ → proj₁ (proj₁ d∈))
  F₁ = λ Y → ⟦ M ⟧ (Y • ρ)
  F₂ = λ Y → ⟦ N ⟧ (Y • ρ)
  F₁' = λ Y → ⟦ delay M ⟧' (Y • ρ')
  F₂' = λ Y → ⟦ delay N ⟧' (Y • ρ')
  {- the branch B, on the side s of the scrutinee -}
  branch : ∀ (s : Tag) (B : AST) {C} → Rel ⌊ ⟦ delay L ⟧' ρ' ⌋ ⌊ ⟦ L ⟧ ρ ⌋
    → (∀ {y} → y ≢ ω → ValPayload (tag s y)) → (∀ {y} → ValPayload (tag s y) → y ≢ ω)
    → (∀ {a b} → tag s a ~ tag s b → a ~ b)
    → ∀ v → tag s v ∈ X'
    → (nonempty (Untag s X) → ⟦ B ⟧ (Untag s X • ρ) ⊆ C)
    → Rel (⟦ delay B ⟧' (Untag s X' • ρ')) C
  branch s B {C} hX vp vp⁻ s~ v sv B⊆ V' V'⊆ =
    R-mono (B⊆ NE-s) (delay-reflect B (envs NE'' NE''' (Con-• cS ρ~) (Con-• (Untag-con s s~ cX') ρ'~) ρ⊳') V' V'⊆)
    where
    hs = tag-R hX s
    cU = Untag-con s s~ (Con-⊆ (Clos3ᵐ-con L ρ~) ⌊⌋-⊆)
    conv = R-conv (hs (v ∷ []) (single⊆ (proj₁ sv))) (vp⁻ (proj₂ sv))
    clU = con-clean cU conv
    U⊆ : Untag s ⌊ ⟦ L ⟧ ρ ⌋ ⊆ Untag s X
    U⊆ y y∈ = ⟨ y∈ , vp (clU y y∈) ⟩
    NE-s = let ⟨ y , y∈ ⟩ = conv in ⟨ y , U⊆ y (proj₁ y∈) ⟩
    cS = Untag-con s s~ cX
    NE'' = extend-nonempty-env NE NE-s
    NE''' = extend-nonempty-env NE' ⟨ v , sv ⟩
    ρ⊳' : (Untag s X' • ρ') ⊳ₑ (Untag s X • ρ)
    ρ⊳' zero W W⊆ = R-mono U⊆ (hs W (λ d d∈ → proj₁ (W⊆ d d∈)))
    ρ⊳' (suc x) = ρ⊳ x
  K : Rel ⌊ ⟦ delay L ⟧' ρ' ⌋ ⌊ ⟦ L ⟧ ρ ⌋
    → Rel (𝒞 ⟨ X' , ⟨ (λ Y → ⟦ delay M ⟧' (Y • ρ')) , ⟨ (λ Y → ⟦ delay N ⟧' (Y • ρ')) , ptt ⟩ ⟩ ⟩)
          (𝒞 ⟨ X , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)
  K hX [] _ = R-∅ (λ _ ())
  K hX (w ∷ V') V'⊆ with V'⊆ w (here refl)
  ... | inj₁ ⟨ v , ⟨ _ , ⟨ allL , _ ⟩ ⟩ ⟩ =
    branch leftT M hX (λ y≢ → y≢) (λ y≢ → y≢) (λ c → c) v lv
      (λ ne → 𝒞-left {X} {F₁} {F₂} (S3.body-continuous M ρ NE _ ne) (Untag-con leftT (λ c → c) cX)) (w ∷ V') V'⊆F
    where
    lv = allL v (here refl)
    V'⊆F : mem (w ∷ V') ⊆ ⟦ delay M ⟧' (Lefts X' • ρ')
    V'⊆F x x∈ with V'⊆ x x∈
    ... | inj₁ ⟨ u , ⟨ U , ⟨ allL' , ⟨ x∈F , _ ⟩ ⟩ ⟩ ⟩ = S4.⟦⟧-monotone (delay M) (λ { zero → allL' ; (suc y) → λ d z → z }) x x∈F
    ... | inj₂ ⟨ u , ⟨ U , ⟨ allR , _ ⟩ ⟩ ⟩ = ⊥-elim (cX' _ _ lv (allR u (here refl)))
  ... | inj₂ ⟨ v , ⟨ _ , ⟨ allR , _ ⟩ ⟩ ⟩ =
    branch rightT N hX (λ y≢ → y≢) (λ y≢ → y≢) (λ c → c) v rv
      (λ ne → 𝒞-right {X} {F₁} {F₂} (S3.body-continuous N ρ NE _ ne) (Untag-con rightT (λ c → c) cX)) (w ∷ V') V'⊆G
    where
    rv = allR v (here refl)
    V'⊆G : mem (w ∷ V') ⊆ ⟦ delay N ⟧' (Rights X' • ρ')
    V'⊆G x x∈ with V'⊆ x x∈
    ... | inj₂ ⟨ u , ⟨ U , ⟨ allR' , ⟨ x∈G , _ ⟩ ⟩ ⟩ ⟩ = S4.⟦⟧-monotone (delay N) (λ { zero → allR' ; (suc y) → λ d z → z }) x x∈G
    ... | inj₁ ⟨ u , ⟨ U , ⟨ allL , _ ⟩ ⟩ ⟩ = ⊥-elim (cX' _ _ rv (allL u (here refl)))

delay-reflect (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) {ρ'} {ρ} E V V⊆ =
  R-mono (proj₂ (⋆ᵐ-val {Λᵐ ⟨ F , ptt ⟩} {⟦ M ⟧ ρ} Λᵐ-clean ⟨ ν , ⟨ tt , tt ⟩ ⟩ Λᵐ-fun))
    (R-bind {F' = λ X → ⋆ ⟨ Λᵐ ⟨ F' , ptt ⟩ , ⟨ X , ptt ⟩ ⟩} {F = λ X → ⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ X , ptt ⟩ ⟩}
       (Clos3ᵐ-con M ρ~) (delay-reflect M E) K V (λ d d∈ → proj₁ (⋆ᵐ-val {Λᵐ ⟨ F' , ptt ⟩} {⟦ delay M ⟧' ρ'} Λᵐ-clean ⟨ ν , ⟨ tt , tt ⟩ ⟩ Λᵐ-fun) d (V⊆ d d∈)))
  where
  open Envs E
  F = λ Y → ⟦ N ⟧ (Y • ρ)
  F' = λ Y → ⟦ delay N ⟧' (Y • ρ')
  K : Conv (⟦ delay M ⟧' ρ') → Conv (⟦ M ⟧ ρ) → Rel ⌊ ⟦ delay M ⟧' ρ' ⌋ ⌊ ⟦ M ⟧ ρ ⌋
    → Rel (⋆ ⟨ Λᵐ ⟨ F' , ptt ⟩ , ⟨ ⌊ ⟦ delay M ⟧' ρ' ⌋ , ptt ⟩ ⟩) (⋆ ⟨ Λᵐ ⟨ F , ptt ⟩ , ⟨ ⌊ ⟦ M ⟧ ρ ⌋ , ptt ⟩ ⟩)
  K _ ⟨ m , m∈ ⟩ hX [] _ = R-∅ (λ _ ())
  K _ ⟨ m , m∈ ⟩ hX (w ∷ W) W⊆ with W⊆ w (here refl)
  ... | ⟨ U₀ , ⟨ _ , ⟨ U₀⊆ , neU₀ ⟩ ⟩ ⟩ with ne-mem neU₀ (λ d d∈ → d∈)
  ... | ⟨ u₀ , u₀∈ ⟩ with letD-collect (S4.body-mono (delay N) ρ') (w ∷ W) (λ { d d∈ → let ⟨ V , ⟨ ⟨ e∈ , _ ⟩ , r ⟩ ⟩ = W⊆ d d∈ in ⟨ V , ⟨ e∈ , r ⟩ ⟩ })
  ... | ⟨ U , ⟨ U⊆ , W⊆N ⟩ ⟩ =
    R-mono (proj₂ (Λᵐ-β (S3.body-mono N ρ) (S3.body-continuous N ρ NE _ ⟨ m , m∈ ⟩) cM clean⌊⌋))
      (delay-reflect N (envs (extend-nonempty-env NE ⟨ m , m∈ ⟩) (extend-nonempty-env NE' ⟨ u₀ , here refl ⟩)
                         (Con-• cM ρ~) (Con-• (Con-⊆ (Con-⊆ (Clos4ᵐ-con (delay M) ρ'~) ⌊⌋-⊆) U'⊆) ρ'~) ρ⊳')
         (w ∷ W) (λ d d∈ → S4.body-mono (delay N) ρ' (λ x x∈ → there x∈) d (W⊆N d d∈)))
    where
    cM = Con-⊆ (Clos3ᵐ-con M ρ~) ⌊⌋-⊆
    U'⊆ : mem (u₀ ∷ U) ⊆ ⌊ ⟦ delay M ⟧' ρ' ⌋
    U'⊆ _ (here refl) = U₀⊆ u₀ u₀∈
    U'⊆ d (there d∈) = U⊆ d d∈
    ρ⊳' : (mem (u₀ ∷ U) • ρ') ⊳ₑ (⌊ ⟦ M ⟧ ρ ⌋ • ρ)
    ρ⊳' zero Y' Y'⊆ = hX Y' (λ d d∈ → U'⊆ d (Y'⊆ d d∈))
    ρ⊳' (suc x) = ρ⊳ x

delay-reflect (app ⦅ L ,, N ,, Nil ⦆) {ρ'} {ρ} E V V⊆ =
  R-bind {F' = λ X → X ⊙ N'} {F = λ Xs → checked fun Xs (Nₛ ≫= λ Y → ⋆ ⟨ Xs , ⟨ Y , ptt ⟩ ⟩)}
    (Clos3ᵐ-con L ρ~) (delay-reflect L E) APP V
    (λ d d∈ → proj₁ (let-app-≃ (delay L) (delay N) ρ' NE' (Clos4ᵐ-con (delay L) ρ'~)) d (V⊆ d d∈))
  where
  open Envs E
  N' = ⟦ delay N ⟧' ρ'
  Nₛ = ⟦ N ⟧ ρ
  APP : Conv (⟦ delay L ⟧' ρ') → Conv (⟦ L ⟧ ρ) → Rel ⌊ ⟦ delay L ⟧' ρ' ⌋ ⌊ ⟦ L ⟧ ρ ⌋
    → Rel (⌊ ⟦ delay L ⟧' ρ' ⌋ ⊙ N') (checked fun ⌊ ⟦ L ⟧ ρ ⌋ (Nₛ ≫= λ Y → ⋆ ⟨ ⌊ ⟦ L ⟧ ρ ⌋ , ⟨ Y , ptt ⟩ ⟩))
  APP _ ⟨ l , l∈ ⟩ hX =
    R-bindₗ {Car} {λ C → Cdr ≫= λ T → N' ≫= λ Y → K C T Y} {Src} car-err λ _ →
    R-bindₗ {Cdr} {λ T → N' ≫= λ Y → K ⌊ Car ⌋ T Y} {Src} cdr-err λ _ →
    R-bindₗ {N'} {K ⌊ Car ⌋ ⌊ Cdr ⌋} {Src} arg-err λ _ →
    R-checkₗ {fun} {⌊ Car ⌋} {⋆ ⟨ ⋆ ⟨ ⌊ Car ⌋ , ⟨ ⌊ Cdr ⌋ , ptt ⟩ ⟩ , ⟨ ⌊ N' ⌋ , ptt ⟩ ⟩} {Src} late kernel
    where
    X' = ⌊ ⟦ delay L ⟧' ρ' ⌋
    Car = carᵐ ⟨ X' , ptt ⟩
    Cdr = cdrᵐ ⟨ X' , ptt ⟩
    K = λ C T Y → checked fun C (⋆ ⟨ ⋆ ⟨ C , ⟨ T , ptt ⟩ ⟩ , ⟨ Y , ptt ⟩ ⟩)
    Xs = ⌊ ⟦ L ⟧ ρ ⌋
    Src = checked fun Xs (Nₛ ≫= λ Y → ⋆ ⟨ Xs , ⟨ Y , ptt ⟩ ⟩)
    pairs : ∀ {c t} → ⦅ c , t ⦆ ∈ X' → kind c ≡ fun × t ≢ ω
    pairs ct∈ = Obs.pair-obs (unfold (hX _ (single⊆ ct∈))) _ _ (here refl)
    bad : Bad prod ⌊ X' ⌋ → ω ∈ Src
    bad ⟨ d , ⟨ d∈ , dk ⟩ ⟩ = inj₁ ⟨ refl , bad-reflect {fun} clean⌊⌋ hX ⟨ d , ⟨ proj₁ d∈ , dk ⟩ ⟩ ⟩
    car-err : ω ∈ carᵐ ⟨ X' , ptt ⟩ → ω ∈ Src
    car-err (inj₁ ⟨ _ , ω∈ ⟩) = ⊥-elim (proj₂ ω∈ refl)
    car-err (inj₂ ⟨ _ , inj₁ ⟨ _ , b ⟩ ⟩) = bad b
    car-err (inj₂ ⟨ _ , inj₂ ⟨ t , ct∈ ⟩ ⟩) with proj₁ (pairs (proj₁ ct∈))
    ... | ()
    cdr-err : ω ∈ cdrᵐ ⟨ X' , ptt ⟩ → ω ∈ Src
    cdr-err (inj₁ ⟨ _ , ω∈ ⟩) = ⊥-elim (proj₂ ω∈ refl)
    cdr-err (inj₂ ⟨ _ , inj₁ ⟨ _ , b ⟩ ⟩) = bad b
    cdr-err (inj₂ ⟨ _ , inj₂ ⟨ c , ct∈ ⟩ ⟩) = ⊥-elim (proj₂ (pairs (proj₁ ct∈)) refl)
    arg-err : ω ∈ N' → ω ∈ Src
    arg-err ω∈ = inj₂ (inj₁ ⟨ refl , R-err (delay-reflect N E _ (single⊆ ω∈)) ⟩)
    car⊆ : ⌊ carᵐ ⟨ X' , ptt ⟩ ⌋ ⊆ car ⟨ X' , ptt ⟩
    car⊆ c c∈ = let ⟨ t , ct∈ ⟩ = ⌊checked⌋ {prod} {⌊ X' ⌋} {car ⟨ ⌊ X' ⌋ , ptt ⟩} c
                                ⟨ ⌊≫=⌋ {X'} {λ P → checked prod P (car ⟨ P , ptt ⟩)} c c∈ , proj₂ c∈ ⟩ in ⟨ t , proj₁ ct∈ ⟩
    cdr⊆ : ⌊ cdrᵐ ⟨ X' , ptt ⟩ ⌋ ⊆ cdr ⟨ X' , ptt ⟩
    cdr⊆ t t∈ = let ⟨ c , ct∈ ⟩ = ⌊checked⌋ {prod} {⌊ X' ⌋} {cdr ⟨ ⌊ X' ⌋ , ptt ⟩} t
                                ⟨ ⌊≫=⌋ {X'} {λ P → checked prod P (cdr ⟨ P , ptt ⟩)} t t∈ , proj₂ t∈ ⟩ in ⟨ c , proj₁ ct∈ ⟩
    late : Bad fun ⌊ carᵐ ⟨ X' , ptt ⟩ ⌋ → ω ∈ Src
    late ⟨ c , ⟨ c∈ , ck ⟩ ⟩ = ⊥-elim (ck (proj₁ (pairs (proj₂ (car⊆ c c∈)))))
    kernel : Rel (⋆ ⟨ ⋆ ⟨ ⌊ carᵐ ⟨ X' , ptt ⟩ ⌋ , ⟨ ⌊ cdrᵐ ⟨ X' , ptt ⟩ ⌋ , ptt ⟩ ⟩ , ⟨ ⌊ N' ⌋ , ptt ⟩ ⟩) Src
    kernel W W⊆ with collect X' ⌊ N' ⌋ clean⌊⌋ W
                       (λ d d∈ → lower (⋆₂-mono _ _ ⟨ lift car⊆ , ⟨ lift cdr⊆ , ⟨ lift (λ x z → z) , ptt ⟩ ⟩ ⟩) d (W⊆ d d∈))
    ... | ⟨ Ws , ⟨ U , ⟨ Ws⊆ , ⟨ U⊆ , cs ⟩ ⟩ ⟩ ⟩ =
      R-mono (proj₁ (≫=-β {F = λ G → checked fun G (Nₛ ≫= λ Y → ⋆ ⟨ G , ⟨ Y , ptt ⟩ ⟩)}
                         (λ G⊆ → checked-mono G⊆ (≫=-mono (λ d z → z) (λ Y⊆ → lower (⋆-mono _ _ ⟨ lift G⊆ , ⟨ lift Y⊆ , ptt ⟩ ⟩))))
                         clean⌊⌋ ⟨ l , l∈ ⟩))
        (Obs.app-obs (unfold (hX Ws Ws⊆)) cs Nₛ (Clos3ᵐ-con N ρ~)
           (Con-⊆ (Clos4ᵐ-con (delay N) ρ'~) (λ d d∈ → proj₁ (U⊆ d d∈)))
           (delay-reflect N E U (λ d d∈ → proj₁ (U⊆ d d∈))))

delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) {ρ'} {ρ} E =
  R-bindₗ {ΛΛᵐ ⟨ F' , ptt ⟩} {λ C → T' ≫= λ Y → pair ⟨ C , ⟨ Y , ptt ⟩ ⟩} {⟦ clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆ ⟧ ρ}
    (λ { ⟨ () , _ ⟩ }) λ _ V V⊆ →
    R-mono (proj₂ (⋆ᵐ-val {ΛΛᵐ ⟨ F , ptt ⟩} {T} (λ { .ω ⟨ () , _ ⟩ refl }) ⟨ ν , ⟨ tt , tt ⟩ ⟩ ΛΛ-fun))
      (R-bind {F' = λ Y → pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ Y , ptt ⟩ ⟩} {F = λ Y → ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ Y , ptt ⟩ ⟩}
              (Clos3ᵐ-con (tuple n ⦅ fvs ⦆) ρ~) (reflect-𝒯 fvs E) K V V⊆)
  where
  open Envs E
  F = λ X Y → ⟦ N ⟧ (Y • X • (λ _ → ⌈ ω ⌉))
  F' = λ X Y → ⟦ delay N ⟧' (Y • X • (λ _ → ⌈ ω ⌉))
  T = 𝒯ᵐ n (⟦ fvs ⟧₊ ρ)
  T' = 𝒯ᵐ n (⟦ del-map-args fvs ⟧₊' ρ')
  ΛΛ-fun : ∀ {G} d → d ∈ ΛΛᵐ ⟨ G , ptt ⟩ → kind d ≡ fun
  ΛΛ-fun (V ↦ w) _ = refl
  ΛΛ-fun ν _ = refl
  K : Conv T' → Conv T → Rel ⌊ T' ⌋ ⌊ T ⌋
    → Rel (pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ ⌊ T' ⌋ , ptt ⟩ ⟩) (⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ ⌊ T ⌋ , ptt ⟩ ⟩)
  K _ ⟨ t₀ , t₀∈ ⟩ hT V' V'⊆ = fold record
    { err-obs = λ ω∈ → ⊥-elim (V'⊆ ω ω∈)
    ; const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
    ; kind-obs = λ d d∈ _ → kd d (V'⊆ d d∈)
    ; pair-obs = λ c t ct∈ → ⟨ ΛΛ-fun c (proj₁ (proj₁ (V'⊆ _ ct∈))) , proj₂ (proj₂ (V'⊆ _ ct∈)) ⟩
    ; app-obs = clos-app
    ; tag-obs = λ t W W⊆ → R-∅ (λ d d∈ → pair-tag t (V'⊆ _ (W⊆ d d∈)))
    }
    where
    D = ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ ⌊ T ⌋ , ptt ⟩ ⟩
    pair-tag : ∀ t {d} → tag t d ∈ pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ ⌊ T' ⌋ , ptt ⟩ ⟩ → ⊥
    pair-tag (tupT i) ()
    pair-tag leftT ()
    pair-tag rightT ()
    ν∈ : ν ∈ ⌊ D ⌋
    ν∈ = ⟨ ⟨ t₀ ∷ [] , ⟨ ⟨ ⟨ tt , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ (λ { (here eq) → proj₂ t₀∈ (sym eq) }) , tt ⟩ ⟩
                       , ⟨ single⊆ t₀∈ , (λ ()) ⟩ ⟩ ⟩ , (λ ()) ⟩
    kd : ∀ d → d ∈ pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ ⌊ T' ⌋ , ptt ⟩ ⟩ → Σ[ s ∈ Value ] s ∈ ⌊ D ⌋ × tgt (kind s) ≡ kind d
    kd ⦅ c , t ⦆ _ = ⟨ ν , ⟨ ν∈ , refl ⟩ ⟩
    Cdrs⊆T' : Cdrs V' ⊆ ⌊ T' ⌋
    Cdrs⊆T' fv ⟨ _ , e∈ ⟩ = proj₂ (V'⊆ _ e∈)
    cT = Con-⊆ (Clos3ᵐ-con (tuple n ⦅ fvs ⦆) ρ~) ⌊⌋-⊆
    clos-app : ∀ {U' W'} → Calls V' U' W' → ∀ Es → Con Es → Con (mem U') → R U' Es → R W' (D ● Es)
    clos-app {W' = []} _ Es _ _ _ = R-∅ (λ _ ())
    clos-app {U'} {w ∷ W'} cs Es cE U'~ rU =
      R-mono (ΛΛᵐ-β {F} cT cE clean⌊⌋ clE ⟨ t₀ , t₀∈ ⟩ NE-E
                (S3.body2-continuous N (λ _ → ⌈ ω ⌉) (λ _ → ⟨ ω , refl ⟩) ⟨ t₀ , t₀∈ ⟩ NE-E))
        (delay-reflect N (envs NE-ρs NE-ρ'' (Con-• cE (Con-• cT (λ _ → Con-⌈⌉ ω))) ρ''~ ρ''⊳ρs) (w ∷ W') W⊆B)
      where
      wit = Calls.results cs w (here refl)
      ent = proj₁ (proj₂ wit)
      u₀ = proj₁ (ne-mem (proj₁ (proj₂ (proj₂ wit))) (λ d d∈ → d∈))
      u₀∈ = proj₂ (proj₂ (proj₂ wit)) u₀ (proj₂ (ne-mem (proj₁ (proj₂ (proj₂ wit))) (λ d d∈ → d∈)))
      vE = R-conv (R-⊆ (single⊆ u₀∈) rU) (λ eq → Calls.noerr cs (subst (_⋵ U') eq u₀∈))
      NE-E = ⟨ proj₁ vE , proj₁ (proj₂ vE) ⟩
      clE = con-clean cE vE
      fv₀ = proj₁ (ne-mem (CarEntry.FV≢[] ent) (λ d d∈ → d∈))
      fv₀∈ = proj₂ (ne-mem (CarEntry.FV≢[] ent) (λ d d∈ → d∈))
      ρ'' : Env
      ρ'' = mem U' • Cdrs V' • (λ _ → ⌈ ω ⌉)
      W⊆B : mem (w ∷ W') ⊆ ⟦ delay N ⟧' ρ''
      W⊆B x x∈ with Calls.results cs x x∈
      ... | ⟨ U₁ , ⟨ car-entry FV t e∈ neFV FV⊆ , ⟨ _ , U₁⊆ ⟩ ⟩ ⟩ with V'⊆ _ e∈
      ... | ⟨ ⟨ ⟨ ⟨ ⟨ x∈B , _ ⟩ , _ ⟩ , _ ⟩ , _ ⟩ , _ ⟩ =
        S4.⟦⟧-monotone (delay N) (λ { zero → U₁⊆ ; (suc zero) → FV⊆ ; (suc (suc y)) → λ d z → z }) x x∈B
      ρ''~ : Con-env ρ''
      ρ''~ = Con-• U'~ (Con-• (Con-⊆ (Con-⊆ (Clos4ᵐ-con (L4.tuple n ⦅ del-map-args fvs ⦆') ρ'~) ⌊⌋-⊆) Cdrs⊆T')
                              (λ _ → Con-⌈⌉ ω))
      NE-ρs = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) ⟨ t₀ , t₀∈ ⟩) NE-E
      NE-ρ'' = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩)
                 ⟨ fv₀ , CarEntry.FV⊆ ent fv₀ fv₀∈ ⟩) ⟨ u₀ , u₀∈ ⟩
      ρ''⊳ρs : ρ'' ⊳ₑ (Es • ⌊ T ⌋ • (λ _ → ⌈ ω ⌉))
      ρ''⊳ρs zero Y' Y'⊆ = R-⊆ Y'⊆ rU
      ρ''⊳ρs (suc zero) Y' Y'⊆ = hT Y' (λ y y∈ → Cdrs⊆T' y (Y'⊆ y y∈))
      ρ''⊳ρs (suc (suc x)) Y' Y'⊆ = R-data Y'⊆ (λ v v∈ → flat-data (Init-flat (Y'⊆ v v∈)))

reflect-nth (M ,, args) E zero = delay-reflect M E
reflect-nth (M ,, args) E (suc i) = reflect-nth args E i

reflect-𝒯 {n} args E = R-binds n (reflect-nth args E) (args-con args (Envs.ρ~ E)) (λ cl hs → 𝒯-R n cl hs)

{- The end theorem (backward half) --------------------------------------------}

Envs₀ : Envs ρ₀ ρ₀
Envs₀ = envs (λ _ → ⟨ ω , refl ⟩) (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ _ → Con-⌈⌉ ω) Init⊳Init

reflect-error : ∀ (M : AST) → ω ∈ ⟦ delay M ⟧' ρ₀ → ω ∈ ⟦ M ⟧ ρ₀
reflect-error M ω∈ = R-err (delay-reflect M Envs₀ _ (single⊆ ω∈))

reflect-const : ∀ (M : AST) {B} (c : base-rep B) → const c ∈ ⟦ delay M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀
reflect-const M c c∈ = Obs.const-obs (unfold (delay-reflect M Envs₀ _ (single⊆ c∈))) c (here refl)

reflect-val : ∀ (M : AST) → Conv (⟦ delay M ⟧' ρ₀) → Conv (⟦ M ⟧ ρ₀)
reflect-val M ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = R-conv (delay-reflect M Envs₀ _ (single⊆ d∈)) d≢
