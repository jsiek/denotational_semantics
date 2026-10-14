{-

  Backward (reflect) direction of the correctness of typed delay
  (Clos3ᵀ → Clos4ᵀ) in the graph model with errors, with the relation of
  DelayRel, as in proof/Correctness/GraphErr/DelayReflect.agda.

  The errors are reflected by the monad (R-bind); each construct is then
  its kernel. The closure is reflected by its applications: callc binds
  the closure and the argument, and its batch of calls (collect) of the
  code (car) on the environment (cdr) is the source's application
  (app-obs). project is the one check (R-checkₗ, R-restrict).

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Ops using (⋆; 𝒯; proj; inl; inr; 𝒞; pair; car; cdr; 𝒞-left; 𝒞-right)
open import Semantics.GraphErr.Typed.Ops using (kindᶠ; checkedᵠ)
open import proof.Framework.GraphModel.DomainUtil using (cdr-witness; 𝒯0-flat)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env)
open import proof.Semantics.GraphErr.Prim using (primD; out)
open import Language.Typed.Type using (Any; ⟪_⟫; code; tup; _∋_; Z; S; idx; flat)
open import Language.Typed.Clos3 as L3 using (Tm; `_; clos; app; lit; tuple; get; case; prim; let′; inject; project)
import Language.Typed.Clos4 as T
import proof.Semantics.GraphErr.Typed.Clos3 as S3
open S3 using (⟦_⟧; ⟦_⟧s)
import proof.Semantics.GraphErr.Typed.Clos4 as S4
open S4 using (fin₁; fin₂; ΛΛᵐ-call; kind₄) renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧s to ⟦_⟧s')
open import Compiler.Typed.Delay using (Ren; ext; delay; delays; delay-program)
open import proof.Correctness.Typed.GraphErr.DelayRel

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Level using (lift; lower)
open import Language.Prim using (δ)

module proof.Correctness.Typed.GraphErr.DelayReflect where


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
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V⊆ _ uv∈) cs)
  ; tag-obs = λ { leftT W W⊆ → h W (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈)) } }
  where
  kd : ∀ d → d ∈ inl ⟨ X' , ptt ⟩ → Σ[ s ∈ Value ] s ∈ ⌊ inl ⟨ X , ptt ⟩ ⌋ × kind s ≡ kind₄ (kind d)
  kd (left d) d∈ = let ⟨ s , ⟨ s∈ , _ ⟩ ⟩ = R-conv (h _ (single⊆ d∈)) (cl d d∈) in ⟨ left s , ⟨ ⟨ s∈ , (λ ()) ⟩ , refl ⟩ ⟩

inr-R : ∀ {X' X} → Clean X' → Rel X' X → Rel (inr ⟨ X' , ptt ⟩) (inr ⟨ X , ptt ⟩)
inr-R {X'} {X} cl h V V⊆ = fold record
  { err-obs = λ ω∈ → ⊥-elim (V⊆ ω ω∈)
  ; const-obs = λ c c∈ → ⊥-elim (V⊆ _ c∈)
  ; kind-obs = λ d d∈ _ → kd d (V⊆ d d∈)
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V⊆ _ uv∈) cs)
  ; tag-obs = λ { rightT W W⊆ → h W (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; leftT W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈)) } }
  where
  kd : ∀ d → d ∈ inr ⟨ X' , ptt ⟩ → Σ[ s ∈ Value ] s ∈ ⌊ inr ⟨ X , ptt ⟩ ⌋ × kind s ≡ kind₄ (kind d)
  kd (right d) d∈ = let ⟨ s , ⟨ s∈ , _ ⟩ ⟩ = R-conv (h _ (single⊆ d∈)) (cl d d∈) in ⟨ right s , ⟨ ⟨ s∈ , (λ ()) ⟩ , refl ⟩ ⟩

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
  ; app-obs = λ cs _ _ _ _ → R-∅ (Calls-none (λ u v uv∈ → V⊆ _ uv∈) cs)
  ; tag-obs = λ { (tupT i) W W⊆ → nth-case i W W⊆
                ; leftT W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → R-∅ (λ d d∈ → V⊆ _ (W⊆ d d∈)) } }
  where
  comp-ne : ∀ j → nonempty (nthD Xs' j) → nonempty (nthD Xs j)
  comp-ne j ⟨ d , d∈ ⟩ = let ⟨ s , ⟨ s∈ , _ ⟩ ⟩ = R-conv (hs j _ (single⊆ d∈)) (cl j d d∈) in ⟨ s , s∈ ⟩
  kd : ∀ d → d ∈ 𝒯 (suc n) Xs' → Σ[ s ∈ Value ] s ∈ ⌊ 𝒯 (suc n) Xs ⌋ × kind s ≡ kind₄ (kind d)
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

record Envs {Γ Δ} (r : Ren Γ Δ) (ρ' ρ : Env Value) : Set₁ where
  constructor envs
  field
    NE : nonempty-env ρ
    NE' : nonempty-env ρ'
    ρ~ : Con-env ρ
    ρ'~ : Con-env ρ'
    ρ⊳ : ∀ {A} (x : Γ ∋ A) → Rel (ρ' (idx (r x))) (ρ (idx x))

ext-envs : ∀ {Γ Δ B} {r : Ren Γ Δ} {ρ' ρ X' X} → Envs r ρ' ρ → nonempty X → nonempty X' → Con X → Con X'
  → Rel X' X → Envs (ext {B = B} r) (X' • ρ') (X • ρ)
ext-envs (envs NE NE' ρ~ ρ'~ ρ⊳) nX nX' cX cX' h =
  envs (extend-nonempty-env NE nX) (extend-nonempty-env NE' nX') (Con-• cX ρ~) (Con-• cX' ρ'~) λ { Z → h ; (S x) → ρ⊳ x }

args-con : ∀ {Γ n} (Ms : Vec (Tm Γ Any) n) {ρ} → Con-env ρ → ∀ i → Con (nthD (⟦ Ms ⟧s ρ) i)
args-con (M ∷ Ms) c zero = S3.con M c
args-con (M ∷ Ms) c (suc i) = args-con Ms c i

delay-reflect : ∀ {Γ Δ A} (M : Tm Γ A) {r : Ren Γ Δ} {ρ' ρ} → Envs r ρ' ρ → Rel (⟦ delay r M ⟧' ρ') (⟦ M ⟧ ρ)
reflect-nth : ∀ {Γ Δ n} (Ms : Vec (Tm Γ Any) n) {r : Ren Γ Δ} {ρ' ρ} → Envs r ρ' ρ
  → (i : Fin n) → Rel (nthD (⟦ delays r Ms ⟧s' ρ') i) (nthD (⟦ Ms ⟧s ρ) i)
reflect-𝒯 : ∀ {Γ Δ n} (Ms : Vec (Tm Γ Any) n) {r : Ren Γ Δ} {ρ' ρ} → Envs r ρ' ρ
  → Rel (𝒯ᵐ n (⟦ delays r Ms ⟧s' ρ')) (𝒯ᵐ n (⟦ Ms ⟧s ρ))

delay-reflect (` x) E = Envs.ρ⊳ E x

delay-reflect (lit B c) E V V⊆ = R-data V⊆ (λ v v∈ → flat-data (ℬ-flat v (V⊆ v v∈)))

delay-reflect (prim p L M) {r} {ρ'} {ρ} E =
  R-bind {F' = λ X → ⟦ delay r M ⟧' ρ' ≫= K X} {F = λ X → ⟦ M ⟧ ρ ≫= K X} (S3.con L (Envs.ρ~ E)) (delay-reflect L E) λ _ _ hX →
  R-bind {F' = K ⌊ ⟦ delay r L ⟧' ρ' ⌋} {F = K ⌊ ⟦ L ⟧ ρ ⌋} (S3.con M (Envs.ρ~ E)) (delay-reflect M E) λ _ _ hY → primD-R {p} hX hY
  where K = λ X Y → primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩

delay-reflect (tuple Ms) = reflect-𝒯 Ms

delay-reflect (get i M) E =
  R-bind {F' = λ X → proj i ⟨ X , ptt ⟩} {F = λ X → proj i ⟨ X , ptt ⟩} (S3.con M (Envs.ρ~ E)) (delay-reflect M E)
    λ _ _ hX → tag-R hX (tupT i)

delay-reflect (L3.inl M) E =
  R-bind {F' = λ X → inl ⟨ X , ptt ⟩} {F = λ X → inl ⟨ X , ptt ⟩} (S3.con M (Envs.ρ~ E)) (delay-reflect M E) λ _ _ hX → inl-R clean⌊⌋ hX

delay-reflect (L3.inr M) E =
  R-bind {F' = λ X → inr ⟨ X , ptt ⟩} {F = λ X → inr ⟨ X , ptt ⟩} (S3.con M (Envs.ρ~ E)) (delay-reflect M E) λ _ _ hX → inr-R clean⌊⌋ hX

delay-reflect {Γ} (case L M N) {r} {ρ'} {ρ} E =
  R-bind {F' = λ Y → 𝒞 ⟨ Y ⇂ ValPayload , ⟨ F₁' , ⟨ F₂' , ptt ⟩ ⟩ ⟩} {F = λ Y → 𝒞 ⟨ Y ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩}
    (S3.con L ρ~) (delay-reflect L E) λ _ _ hX → K hX
  where
  open Envs E
  X' = ⌊ ⟦ delay r L ⟧' ρ' ⌋ ⇂ ValPayload
  X = ⌊ ⟦ L ⟧ ρ ⌋ ⇂ ValPayload
  cX' : Con X'
  cX' = Con-⊆ (S4.con (delay r L) ρ'~) (λ d d∈ → proj₁ (proj₁ d∈))
  cX : Con X
  cX = Con-⊆ (S3.con L ρ~) (λ d d∈ → proj₁ (proj₁ d∈))
  F₁ = λ Y → ⟦ M ⟧ (Y • ρ)
  F₂ = λ Y → ⟦ N ⟧ (Y • ρ)
  F₁' = λ Y → ⟦ delay (ext r) M ⟧' (Y • ρ')
  F₂' = λ Y → ⟦ delay (ext r) N ⟧' (Y • ρ')
  {- the branch B, on the side s of the scrutinee -}
  branch : ∀ (s : Tag) (B : Tm (Any ∷ Γ) Any) {C} → Rel ⌊ ⟦ delay r L ⟧' ρ' ⌋ ⌊ ⟦ L ⟧ ρ ⌋
    → (∀ {y} → y ≢ ω → ValPayload (tag s y)) → (∀ {y} → ValPayload (tag s y) → y ≢ ω)
    → (∀ {a b} → tag s a ~ tag s b → a ~ b)
    → ∀ v → tag s v ∈ X'
    → (nonempty (Untag s X) → ⟦ B ⟧ (Untag s X • ρ) ⊆ C)
    → Rel (⟦ delay (ext r) B ⟧' (Untag s X' • ρ')) C
  branch s B {C} hX vp vp⁻ s~ v sv B⊆ V' V'⊆ =
    R-mono (B⊆ NE-s) (delay-reflect B (ext-envs E NE-s ⟨ v , sv ⟩ (Untag-con s s~ cX) (Untag-con s s~ cX') ρ⊳') V' V'⊆)
    where
    hs = tag-R hX s
    conv = R-conv (hs (v ∷ []) (single⊆ (proj₁ sv))) (vp⁻ (proj₂ sv))
    clU = con-clean (Untag-con s s~ (Con-⊆ (S3.con L ρ~) ⌊⌋-⊆)) conv
    U⊆ : Untag s ⌊ ⟦ L ⟧ ρ ⌋ ⊆ Untag s X
    U⊆ y y∈ = ⟨ y∈ , vp (clU y y∈) ⟩
    NE-s = let ⟨ y , y∈ ⟩ = conv in ⟨ y , U⊆ y (proj₁ y∈) ⟩
    ρ⊳' : Rel (Untag s X') (Untag s X)
    ρ⊳' W W⊆ = R-mono U⊆ (hs W (λ d d∈ → proj₁ (W⊆ d d∈)))
  K : Rel ⌊ ⟦ delay r L ⟧' ρ' ⌋ ⌊ ⟦ L ⟧ ρ ⌋ → Rel (𝒞 ⟨ X' , ⟨ F₁' , ⟨ F₂' , ptt ⟩ ⟩ ⟩) (𝒞 ⟨ X , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩)
  K hX [] _ = R-∅ (λ _ ())
  K hX (w ∷ V') V'⊆ with V'⊆ w (here refl)
  ... | inj₁ ⟨ v , ⟨ _ , ⟨ allL , _ ⟩ ⟩ ⟩ =
    branch leftT M hX (λ y≢ → y≢) (λ y≢ → y≢) (λ c → c) v lv
      (λ ne → 𝒞-left {X} {F₁} {F₂} (fin₁ (S3.ok M) NE ne) (Untag-con leftT (λ c → c) cX)) (w ∷ V') V'⊆F
    where
    lv = allL v (here refl)
    V'⊆F : mem (w ∷ V') ⊆ F₁' (Lefts X')
    V'⊆F x x∈ with V'⊆ x x∈
    ... | inj₁ ⟨ u , ⟨ U , ⟨ allL' , ⟨ x∈F , _ ⟩ ⟩ ⟩ ⟩ = proj₁ (S4.ok (delay (ext r) M)) (λ { zero → allL' ; (suc y) → λ d z → z }) x x∈F
    ... | inj₂ ⟨ u , ⟨ U , ⟨ allR , _ ⟩ ⟩ ⟩ = ⊥-elim (cX' _ _ lv (allR u (here refl)))
  ... | inj₂ ⟨ v , ⟨ _ , ⟨ allR , _ ⟩ ⟩ ⟩ =
    branch rightT N hX (λ y≢ → y≢) (λ y≢ → y≢) (λ c → c) v rv
      (λ ne → 𝒞-right {X} {F₁} {F₂} (fin₁ (S3.ok N) NE ne) (Untag-con rightT (λ c → c) cX)) (w ∷ V') V'⊆G
    where
    rv = allR v (here refl)
    V'⊆G : mem (w ∷ V') ⊆ F₂' (Rights X')
    V'⊆G x x∈ with V'⊆ x x∈
    ... | inj₂ ⟨ u , ⟨ U , ⟨ allR' , ⟨ x∈G , _ ⟩ ⟩ ⟩ ⟩ = proj₁ (S4.ok (delay (ext r) N)) (λ { zero → allR' ; (suc y) → λ d z → z }) x x∈G
    ... | inj₁ ⟨ u , ⟨ U , ⟨ allL , _ ⟩ ⟩ ⟩ = ⊥-elim (cX' _ _ rv (allL u (here refl)))

delay-reflect (let′ M N) {r} {ρ'} {ρ} E =
  R-bind {F' = λ X → ⟦ delay (ext r) N ⟧' (X • ρ')} {F = λ X → ⟦ N ⟧ (X • ρ)} (S3.con M ρ~) (delay-reflect M E) λ c' c hX →
    delay-reflect N (ext-envs E c c' (Con-⊆ (S3.con M ρ~) ⌊⌋-⊆) (Con-⊆ (S4.con (delay r M) ρ'~) ⌊⌋-⊆) hX)
  where open Envs E

delay-reflect (inject G M) E = delay-reflect M E

delay-reflect (project t M) E =
  R-bind {F' = λ X → checkedᵠ kind₄ G X (X ⇂ λ d → kind₄ (kind d) ≡ G)} {F = λ X → checked G X (X ⇂ λ d → kind d ≡ G)}
    (S3.con M (Envs.ρ~ E)) (delay-reflect M E) λ _ _ hX →
  R-checkₗ (λ b → inj₁ ⟨ refl , bad-reflect clean⌊⌋ hX b ⟩) (λ W W⊆ → R-mono (λ x → inj₂) (R-restrict G hX W W⊆))
  where G = kindᶠ (flat t)

delay-reflect (app L M) {r} {ρ'} {ρ} E =
  R-bind {F' = λ P → Arg ≫= K P} {F = λ F → F ● ⟦ M ⟧ ρ} (S3.con L ρ~) (delay-reflect L E) λ _ _ hX →
  R-bindₗ {Arg} {K P} (λ ω∈ → inj₁ ⟨ refl , R-err (delay-reflect M E _ (single⊆ ω∈)) ⟩) λ _ W W⊆ →
  let ⟨ Ws , ⟨ U , ⟨ Ws⊆ , ⟨ U⊆ , cs ⟩ ⟩ ⟩ ⟩ = collect P ⌊ Arg ⌋ clean⌊⌋ W W⊆ in
  Obs.app-obs (unfold (hX Ws Ws⊆)) cs (⟦ M ⟧ ρ) (S3.con M ρ~)
    (Con-⊆ (S4.con (delay r M) ρ'~) (λ d d∈ → proj₁ (U⊆ d d∈))) (delay-reflect M E U (λ d d∈ → proj₁ (U⊆ d d∈)))
  where
  open Envs E
  Arg = ⟦ delay r M ⟧' ρ'
  P = ⌊ ⟦ delay r L ⟧' ρ' ⌋
  K = λ P X → ⋆ ⟨ ⋆ ⟨ car ⟨ P , ptt ⟩ , ⟨ cdr ⟨ P , ptt ⟩ , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩

delay-reflect (clos {n = n} N Ms) {r} {ρ'} {ρ} E =
  R-bindₗ {ΛΛᵐ ⟨ F' , ptt ⟩} {λ C → T' ≫= λ Y → pair ⟨ C , ⟨ Y , ptt ⟩ ⟩} {⟦ clos N Ms ⟧ ρ} (λ { ⟨ () , _ ⟩ }) λ _ →
    R-bind {F' = λ Y → pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ Y , ptt ⟩ ⟩} {F = λ Y → ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ Y , ptt ⟩ ⟩}
      (S3.con (tuple Ms) ρ~) (reflect-𝒯 Ms E) K
  where
  open Envs E
  F = λ X Y → ⟦ N ⟧ (Y • X • (λ _ → ⌈ ω ⌉))
  F' = λ X Y → ⟦ delay (λ x → x) N ⟧' (Y • X • (λ _ → ⌈ ω ⌉))
  T = 𝒯ᵐ n (⟦ Ms ⟧s ρ)
  T' = 𝒯ᵐ n (⟦ delays r Ms ⟧s' ρ')
  K : Conv T' → Conv T → Rel ⌊ T' ⌋ ⌊ T ⌋
    → Rel (pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ ⌊ T' ⌋ , ptt ⟩ ⟩) (⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ ⌊ T ⌋ , ptt ⟩ ⟩)
  K _ ⟨ t₀ , t₀∈ ⟩ hT V' V'⊆ = fold record
    { err-obs = λ ω∈ → ⊥-elim (V'⊆ ω ω∈)
    ; const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
    ; kind-obs = λ d d∈ _ → kd d (V'⊆ d d∈)
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
    kd : ∀ d → d ∈ pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ ⌊ T' ⌋ , ptt ⟩ ⟩ → Σ[ s ∈ Value ] s ∈ ⌊ D ⌋ × kind s ≡ kind₄ (kind d)
    kd ⦅ c , t ⦆ _ = ⟨ ν , ⟨ ν∈ , refl ⟩ ⟩
    Cdrs⊆T' : Cdrs V' ⊆ ⌊ T' ⌋
    Cdrs⊆T' fv ⟨ _ , e∈ ⟩ = proj₂ (V'⊆ _ e∈)
    cT = Con-⊆ (S3.con (tuple Ms) ρ~) ⌊⌋-⊆
    clos-app : ∀ {U' W'} → Calls V' U' W' → ∀ Es → Con Es → Con (mem U') → R U' Es → R W' (D ● Es)
    clos-app {W' = []} _ Es _ _ _ = R-∅ (λ _ ())
    clos-app {U'} {w ∷ W'} cs Es cE U'~ rU =
      R-mono (λ x x∈ → inj₂ ⟨ vE , ΛΛᵐ-call {F} cT (Con-⊆ cE ⌊⌋-⊆) clean⌊⌋ clean⌊⌋ (fin₂ (S3.ok N) ⟨ t₀ , t₀∈ ⟩ vE) x x∈ ⟩)
        (delay-reflect N (envs NE-ρs NE-ρ'' (Con-• (Con-⊆ cE ⌊⌋-⊆) (Con-• cT (λ _ → Con-⌈⌉ ω))) ρ''~ ρ''⊳ρs) (w ∷ W') W⊆B)
      where
      wit = Calls.results cs w (here refl)
      ent = proj₁ (proj₂ wit)
      u₀ = proj₁ (ne-mem (proj₁ (proj₂ (proj₂ wit))) (λ d d∈ → d∈))
      u₀∈ = proj₂ (proj₂ (proj₂ wit)) u₀ (proj₂ (ne-mem (proj₁ (proj₂ (proj₂ wit))) (λ d d∈ → d∈)))
      vE = R-conv (R-⊆ (single⊆ u₀∈) rU) (λ eq → Calls.noerr cs (subst (_⋵ U') eq u₀∈))
      fv₀ = proj₁ (ne-mem (CarEntry.FV≢[] ent) (λ d d∈ → d∈))
      fv₀∈ = proj₂ (ne-mem (CarEntry.FV≢[] ent) (λ d d∈ → d∈))
      ρ'' : Env Value
      ρ'' = mem U' • Cdrs V' • (λ _ → ⌈ ω ⌉)
      W⊆B : mem (w ∷ W') ⊆ ⟦ delay (λ x → x) N ⟧' ρ''
      W⊆B x x∈ with Calls.results cs x x∈
      ... | ⟨ U₁ , ⟨ car-entry FV t e∈ neFV FV⊆ , ⟨ _ , U₁⊆ ⟩ ⟩ ⟩ with V'⊆ _ e∈
      ... | ⟨ ⟨ ⟨ ⟨ ⟨ x∈B , _ ⟩ , _ ⟩ , _ ⟩ , _ ⟩ , _ ⟩ =
        proj₁ (S4.ok (delay (λ x → x) N)) (λ { zero → U₁⊆ ; (suc zero) → FV⊆ ; (suc (suc y)) → λ d z → z }) x x∈B
      ρ''~ : Con-env ρ''
      ρ''~ = Con-• U'~ (Con-• (Con-⊆ (Con-⊆ (S4.con (T.tuple (delays r Ms)) ρ'~) ⌊⌋-⊆) Cdrs⊆T') (λ _ → Con-⌈⌉ ω))
      NE-ρs = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) ⟨ t₀ , t₀∈ ⟩) vE
      NE-ρ'' = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩)
                 ⟨ fv₀ , CarEntry.FV⊆ ent fv₀ fv₀∈ ⟩) ⟨ u₀ , u₀∈ ⟩
      ρ''⊳ρs : ∀ {A} (x : (Any ∷ ⟪ tup n ⟫ ∷ []) ∋ A) → Rel (ρ'' (idx x)) ((⌊ Es ⌋ • ⌊ T ⌋ • (λ _ → ⌈ ω ⌉)) (idx x))
      ρ''⊳ρs Z Y' Y'⊆ = R-mono (⌊⌋-clean (con-clean cE vE)) (R-⊆ Y'⊆ rU)
      ρ''⊳ρs (S Z) Y' Y'⊆ = hT Y' (λ y y∈ → Cdrs⊆T' y (Y'⊆ y y∈))

reflect-nth (M ∷ Ms) E zero = delay-reflect M E
reflect-nth (M ∷ Ms) E (suc i) = reflect-nth Ms E i

reflect-𝒯 {n = n} Ms E = R-binds n (reflect-nth Ms E) (args-con Ms (Envs.ρ~ E)) (λ cl hs → 𝒯-R n cl hs)

{- The end theorem (backward half) --------------------------------------------}

Envs₀ : ∀ (r : Ren [] []) → Envs r ρ₀ ρ₀
Envs₀ r = envs (λ _ → ⟨ ω , refl ⟩) (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ _ → Con-⌈⌉ ω) (λ ())

reflect-error : ∀ (M : Tm [] Any) → ω ∈ ⟦ delay-program M ⟧' ρ₀ → ω ∈ ⟦ M ⟧ ρ₀
reflect-error M ω∈ = R-err (delay-reflect M (Envs₀ _) _ (single⊆ ω∈))

reflect-const : ∀ (M : Tm [] Any) {B} (c : base-rep B) → const c ∈ ⟦ delay-program M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀
reflect-const M c c∈ = Obs.const-obs (unfold (delay-reflect M (Envs₀ _) _ (single⊆ c∈))) c (here refl)

reflect-val : ∀ (M : Tm [] Any) → val∈ (⟦ delay-program M ⟧' ρ₀) → val∈ (⟦ M ⟧ ρ₀)
reflect-val M ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ = let ⟨ s , ⟨ s∈ , s≢ ⟩ ⟩ = R-conv (delay-reflect M (Envs₀ _) _ (single⊆ d∈)) d≢ in ⟨ s , ⟨ s∈ , s≢ ⟩ ⟩
