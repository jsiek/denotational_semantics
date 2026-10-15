{-

  Backward (reflect) direction of delay (Clos3μ → Clos4μ) in the graph
  model, as for typed delay (proof/Correctness/Graph/DelayReflect.agda),
  with the approximant logical relation ApproxLR of DelayRel (source
  sets against finite target approximants). The target call (callc) is
  the source application on the calls collected from finitely many
  pairs (collect). There is no project, so no acc-reflect; fold and
  unfold are the identity on both sides.

-}

open import proof.Framework.GraphModel.Prelude
open import Framework.Primitives
open import proof.Framework.GraphModel.Ops using (⋆; 𝒯; pair; car; cdr; nthD; 𝒞-left; 𝒞-right; Λ-β; ΛΛ-β; letD-collect; Mono₁)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.DomainUtil using (cdr-witness; 𝒯0-flat)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import Mu.Language.Type using (Ctx; Type; tup; _⊹_; _∋_; Z; S; idx)
open import Mu.Language.Clos3
import Mu.Language.Clos4 as T
import Mu.proof.Semantics.Graph.Clos3 as S3
import Mu.proof.Semantics.Graph.Clos4 as S4
open S3 using (⟦_⟧; ⟦_⟧s)
open S4 using () renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧s to ⟦_⟧s')
open import proof.Framework.GraphModel.TypedOkBase using (Ok; fin₁; fin₂)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Mu.Compiler.Delay using (Ren; ext; delay; delays; delay-program)
open import Mu.proof.Correctness.Graph.DelayRel renaming (fold to foldᴬ; unfold to unfoldᴬ)
open import Language.Prim using (δ)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length; replicate) renaming (map to lmap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺; ∈-map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

module Mu.proof.Correctness.Graph.DelayReflect where

{- a body is monotone in its argument -}
mono₁ : ∀ {E} → Ok E → ∀ ρ → Mono₁ (λ X → E (X • ρ))
mono₁ o ρ X⊆ = proj₁ o (•-~ _⊆_ (λ _ _ z → z) X⊆)

{- a target call V' ⊆ L' ⊙ N' is a batch of calls of a finite W ⊆ L' on a finite U ⊆ N' -}
collect : ∀ (L' N' : 𝒫 Value) V' → mem V' ⊆ (L' ⊙ N')
  → Σ[ W ∈ List Value ] Σ[ U ∈ List Value ] mem W ⊆ L' × mem U ⊆ N' × Calls W U V'
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

{- The fundamental lemma ------------------------------------------------------}

record Envs {Γ Δ} (r : Ren Γ Δ) (ρ ρ' : Env Value) : Set₁ where
  constructor envs
  field
    NE : nonempty-env ρ
    ρ~ : Con-env ρ
    ρ'~ : Con-env ρ'
    ρ⊳ : ∀ {A} (x : Γ ∋ A) V → mem V ⊆ ρ' (idx (r x)) → ApproxLR (ρ (idx x)) V

ext-envs : ∀ {Γ Δ B} {r : Ren Γ Δ} {ρ ρ' X X'} → Envs r ρ ρ' → nonempty X → Con X → Con X'
  → (∀ V → mem V ⊆ X' → ApproxLR X V) → Envs (ext {B = B} r) (X • ρ) (X' • ρ')
ext-envs (envs NE ρ~ ρ'~ ρ⊳) ne c c' h =
  envs (extend-nonempty-env NE ne) (Con-• c ρ~) (Con-• c' ρ'~) (λ { Z → h ; (S x) → ρ⊳ x })

delay-reflect : ∀ {Γ Δ A} (M : Tm Γ A) {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → ∀ V' → mem V' ⊆ ⟦ delay r M ⟧' ρ' → ApproxLR (⟦ M ⟧ ρ) V'
reflect-nth : ∀ {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → (i : Fin (length Δ')) → ∀ V' → mem V' ⊆ nthD (⟦ delays r Ms ⟧s' ρ') i → ApproxLR (nthD (⟦ Ms ⟧s ρ) i) V'
reflect-𝒯 : ∀ {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → ∀ V' → mem V' ⊆ 𝒯 (length Δ') (⟦ delays r Ms ⟧s' ρ') → ApproxLR (𝒯 (length Δ') (⟦ Ms ⟧s ρ)) V'

ne-reflect : ∀ {Γ Δ A} (M : Tm Γ A) {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → nonempty (⟦ delay r M ⟧' ρ') → nonempty (⟦ M ⟧ ρ)
ne-reflect M E ⟨ v , v∈ ⟩ = ApproxLRLayer.nonempty-obs (unfoldᴬ (delay-reflect M E (v ∷ []) (single⊆ v∈))) (λ ())

tag-reflect : ∀ {Γ Δ A} (M : Tm Γ A) {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → ∀ t W → mem W ⊆ Untag t (⟦ delay r M ⟧' ρ') → ApproxLR (Untag t (⟦ M ⟧ ρ)) W
tag-reflect M E t W W⊆ =
  ApproxLRLayer.tag-obs (unfoldᴬ (delay-reflect M E (lmap (tag t) W) mW)) t W (λ d d∈ → ∈-map⁺ (tag t) d∈)
  where
  mW : mem (lmap (tag t) W) ⊆ _
  mW d d∈ with ∈-map⁻ (tag t) d∈
  ... | ⟨ x , ⟨ x∈ , refl ⟩ ⟩ = W⊆ x x∈

{- by consistency, all the results of a target case come from the branch B on the side s -}
reflect-branch : ∀ {Γ Δ} {A₁ A₂ A C : Type} (s : Tag) (L : Tm Γ (A₁ ⊹ A₂)) (B : Tm (A ∷ Γ) C) {r : Ren Γ Δ} {ρ ρ' C} → Envs r ρ ρ'
  → ∀ v → tag s v ∈ ⟦ delay r L ⟧' ρ' → (∀ {a b} → tag s a ~ tag s b → a ~ b)
  → (nonempty (Untag s (⟦ L ⟧ ρ)) → ⟦ B ⟧ (Untag s (⟦ L ⟧ ρ) • ρ) ⊆ C)
  → ∀ V' → mem V' ⊆ ⟦ delay (ext r) B ⟧' (Untag s (⟦ delay r L ⟧' ρ') • ρ') → ApproxLR C V'
reflect-branch s L B {r} E v sv s~ B⊆ V' V'⊆ =
  ApproxLR-mono (B⊆ NE-s)
    (delay-reflect B (ext-envs E NE-s (Untag-con s s~ (S3.con L ρ~)) (Untag-con s s~ (S4.con (delay r L) ρ'~))
       (tag-reflect L E s)) V' V'⊆)
  where
  open Envs E
  NE-s = ApproxLRLayer.nonempty-obs (unfoldᴬ (tag-reflect L E s (v ∷ []) (single⊆ sv))) (λ ())

delay-reflect (` x) E = Envs.ρ⊳ E x

delay-reflect (app L N) {r} {ρ' = ρ'} E V' V'⊆ with collect (⟦ delay r L ⟧' ρ') (⟦ delay r N ⟧' ρ') V' V'⊆
... | ⟨ W , ⟨ U , ⟨ W⊆L' , ⟨ U⊆N' , cs ⟩ ⟩ ⟩ ⟩ =
  ApproxLRLayer.app-obs (unfoldᴬ (delay-reflect L E W W⊆L')) cs _ (S3.con N (Envs.ρ~ E))
    (Con-⊆ (S4.con (delay r N) (Envs.ρ'~ E)) U⊆N') (delay-reflect N E U U⊆N')

delay-reflect (lit B c) E V' V'⊆ = ApproxLR-flat V'⊆ (λ v v∈ → ℬ-flat v (V'⊆ v v∈))

delay-reflect (prim p L M) E V' V'⊆ = ApproxLR-data V⊆ dt
  where
  const-reflect : ∀ N {c : base-rep Int} → const c ∈ ⟦ delay _ N ⟧' _ → const c ∈ ⟦ N ⟧ _
  const-reflect N {c} c∈ = ApproxLRLayer.const-obs (unfoldᴬ (delay-reflect N E (const c ∷ []) (single⊆ c∈))) c (here refl)
  V⊆ : mem V' ⊆ ⟦ prim p L M ⟧ _
  V⊆ v v∈ with V'⊆ v v∈
  ... | ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ = ⟨ n , ⟨ m , ⟨ const-reflect L n∈ , ⟨ const-reflect M m∈ , refl ⟩ ⟩ ⟩ ⟩
  dt : ∀ v → v ⋵ V' → Data v
  dt v v∈ with V'⊆ v v∈
  ... | ⟨ n , ⟨ m , ⟨ _ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩ = out-data (δ p n m)

delay-reflect (tuple Ms) = reflect-𝒯 Ms

delay-reflect (get i M) E = tag-reflect M E (tupT (pos i))

delay-reflect M₀@(inl M) E V' V'⊆ = foldᴬ record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → let ⟨ v , v∈ ⟩ = ne-mem ne V'⊆ in inj-ne v v∈
  ; app-obs = λ cs _ _ _ _ → ApproxLR-∅ (Calls-none (λ u v uv∈ → V'⊆ _ uv∈) cs)
  ; tag-obs = λ { leftT W W⊆ → delay-reflect M E W (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → ApproxLR-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → ApproxLR-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈)) } }
  where
  inj-ne : ∀ v → v ∈ ⟦ delay _ M₀ ⟧' _ → nonempty (⟦ M₀ ⟧ _)
  inj-ne (left d) d∈ = let ⟨ m , m∈ ⟩ = ne-reflect M E ⟨ d , d∈ ⟩ in ⟨ left m , m∈ ⟩

delay-reflect M₀@(inr M) E V' V'⊆ = foldᴬ record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → let ⟨ v , v∈ ⟩ = ne-mem ne V'⊆ in inj-ne v v∈
  ; app-obs = λ cs _ _ _ _ → ApproxLR-∅ (Calls-none (λ u v uv∈ → V'⊆ _ uv∈) cs)
  ; tag-obs = λ { rightT W W⊆ → delay-reflect M E W (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; leftT W W⊆ → ApproxLR-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; (tupT i) W W⊆ → ApproxLR-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈)) } }
  where
  inj-ne : ∀ v → v ∈ ⟦ delay _ M₀ ⟧' _ → nonempty (⟦ M₀ ⟧ _)
  inj-ne (right d) d∈ = let ⟨ m , m∈ ⟩ = ne-reflect M E ⟨ d , d∈ ⟩ in ⟨ right m , m∈ ⟩

delay-reflect (case L M N) E [] V'⊆ = ApproxLR-∅ (λ _ ())
delay-reflect (case L M N) {r} {ρ} {ρ'} E (w ∷ V') V'⊆ with V'⊆ w (here refl)
... | inj₁ ⟨ v , ⟨ _ , ⟨ allL , _ ⟩ ⟩ ⟩ =
  reflect-branch leftT L M E v lv (λ a~b → a~b) M⊆ (w ∷ V') V'⊆F
  where
  open Envs E
  lv = allL v (here refl)
  M⊆ : nonempty (Lefts (⟦ L ⟧ ρ)) → ⟦ M ⟧ (Lefts (⟦ L ⟧ ρ) • ρ) ⊆ _
  M⊆ ne = 𝒞-left {⟦ L ⟧ ρ} {λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ N ⟧ (X • ρ)} (fin₁ (S3.ok M) NE ne)
                  (Untag-con leftT (λ c → c) (S3.con L ρ~))
  V'⊆F : mem (w ∷ V') ⊆ ⟦ delay (ext r) M ⟧' (Lefts (⟦ delay r L ⟧' ρ') • ρ')
  V'⊆F x x∈ with V'⊆ x x∈
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL' , ⟨ x∈F , _ ⟩ ⟩ ⟩ ⟩ = mono₁ (S4.ok (delay (ext r) M)) ρ' allL' x x∈F
  ... | inj₂ ⟨ u , ⟨ U , ⟨ allR , _ ⟩ ⟩ ⟩ = ⊥-elim (S4.con (delay r L) ρ'~ _ _ lv (allR u (here refl)))
... | inj₂ ⟨ v , ⟨ _ , ⟨ allR , _ ⟩ ⟩ ⟩ =
  reflect-branch rightT L N E v rv (λ a~b → a~b) N⊆ (w ∷ V') V'⊆G
  where
  open Envs E
  rv = allR v (here refl)
  N⊆ : nonempty (Rights (⟦ L ⟧ ρ)) → ⟦ N ⟧ (Rights (⟦ L ⟧ ρ) • ρ) ⊆ _
  N⊆ ne = 𝒞-right {⟦ L ⟧ ρ} {λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ N ⟧ (X • ρ)} (fin₁ (S3.ok N) NE ne)
                   (Untag-con rightT (λ c → c) (S3.con L ρ~))
  V'⊆G : mem (w ∷ V') ⊆ ⟦ delay (ext r) N ⟧' (Rights (⟦ delay r L ⟧' ρ') • ρ')
  V'⊆G x x∈ with V'⊆ x x∈
  ... | inj₂ ⟨ u , ⟨ U , ⟨ allR' , ⟨ x∈G , _ ⟩ ⟩ ⟩ ⟩ = mono₁ (S4.ok (delay (ext r) N)) ρ' allR' x x∈G
  ... | inj₁ ⟨ u , ⟨ U , ⟨ allL , _ ⟩ ⟩ ⟩ = ⊥-elim (S4.con (delay r L) ρ'~ _ _ rv (allL u (here refl)))

delay-reflect (let′ M N) E [] V'⊆ = ApproxLR-∅ (λ _ ())
delay-reflect (let′ M N) {r} {ρ} {ρ'} E (w ∷ V') V'⊆
    with letD-collect (mono₁ (S4.ok (delay (ext r) N)) ρ') (w ∷ V') V'⊆
... | ⟨ U , ⟨ U⊆ , V'⊆N ⟩ ⟩ =
  ApproxLR-mono (proj₂ (Λ-β (mono₁ (S3.ok N) ρ) (fin₁ (S3.ok N) NE NE-M) (S3.con M ρ~)))
    (delay-reflect N (ext-envs E NE-M (S3.con M ρ~) (Con-⊆ (S4.con (delay r M) ρ'~) U⊆)
       (λ Y' Y'⊆ → delay-reflect M E Y' (λ d d∈ → U⊆ d (Y'⊆ d d∈)))) (w ∷ V') V'⊆N)
  where
  open Envs E
  NE-M = let ⟨ _ , ⟨ _ , ⟨ U₀⊆ , ne ⟩ ⟩ ⟩ = V'⊆ w (here refl) in ne-reflect M E (ne-mem ne U₀⊆)

delay-reflect (fold M) E = delay-reflect M E

delay-reflect (unfold M) E = delay-reflect M E

delay-reflect (clos {Δ} N Ms) {r} {ρ} {ρ'} E V' V'⊆ = foldᴬ record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → let ⟨ v , v∈ ⟩ = ne-mem ne V'⊆ in ⟨ ν , ν∈ (pair-ne v v∈) ⟩
  ; app-obs = clos-app
  ; tag-obs = λ t W W⊆ → ApproxLR-∅ (λ d d∈ → pair-tag t (V'⊆ _ (W⊆ d d∈)))
  }
  where
  open Envs E
  n = length Δ
  T' = 𝒯 n (⟦ delays r Ms ⟧s' ρ')
  T = 𝒯 n (⟦ Ms ⟧s ρ)
  D = ⟦ clos N Ms ⟧ ρ

  pair-ne : ∀ v → v ∈ ⟦ delay r (clos N Ms) ⟧' ρ' → nonempty T'
  pair-ne ⦅ u , v ⦆ ⟨ _ , v∈ ⟩ = ⟨ v , v∈ ⟩
  pair-tag : ∀ {A B : 𝒫 Value} t {d} → tag t d ∈ pair ⟨ A , ⟨ B , ptt ⟩ ⟩ → Data.Empty.⊥
  pair-tag (tupT i) ()
  pair-tag leftT ()
  pair-tag rightT ()

  T-ne : nonempty T' → nonempty T
  T-ne ⟨ t' , t'∈ ⟩ = ApproxLRLayer.nonempty-obs (unfoldᴬ (reflect-𝒯 Ms E (t' ∷ []) (single⊆ t'∈))) (λ ())
  ν∈ : nonempty T' → ν ∈ D
  ν∈ ne = let ⟨ t , t∈ ⟩ = T-ne ne in ⟨ t ∷ [] , ⟨ ⟨ tt , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ single⊆ t∈ , (λ ()) ⟩ ⟩ ⟩

  Cdrs⊆T' : Cdrs V' ⊆ T'
  Cdrs⊆T' fv ⟨ _ , e∈ ⟩ = proj₂ (V'⊆ _ e∈)

  clos-app : ∀ {U' W'} → Calls V' U' W' → ∀ E → Con E → Con (mem U') → ApproxLR E U' → ApproxLR (D ● E) W'
  clos-app {W' = []} _ _ _ _ _ = ApproxLR-∅ (λ _ ())
  clos-app {U'} {w ∷ W'} cs Es cE U'~ rU =
    ApproxLR-mono (ΛΛ-β {F = λ X Y → ⟦ N ⟧ (Y • X • λ _ → ⌈ ω ⌉)} cT cE (fin₂ (S3.ok N) NE-T NE-E))
      (delay-reflect N {r = λ x → x} (envs NE-ρs (Con-• cE (Con-• cT (λ _ → Con-⌈⌉ ω))) ρ''~ ρ''⊳) (w ∷ W') W⊆B)
    where
    wit = Calls.results cs w (here refl)
    ent = proj₁ (proj₂ wit)
    NE-E = ApproxLRLayer.nonempty-obs (unfoldᴬ rU) (ne-⊆ (proj₂ (proj₂ (proj₂ wit))) (proj₁ (proj₂ (proj₂ wit))))
    NE-T = T-ne (ne-mem (CarEntry.FV≢[] ent) (λ d d∈ → Cdrs⊆T' d (CarEntry.FV⊆ ent d d∈)))
    ρ'' : Env Value
    ρ'' = mem U' • Cdrs V' • (λ _ → ⌈ ω ⌉)
    W⊆B : mem (w ∷ W') ⊆ ⟦ delay (λ x → x) N ⟧' ρ''
    W⊆B x x∈ with Calls.results cs x x∈
    ... | ⟨ U₀ , ⟨ car-entry FV t e∈ neFV FV⊆ , ⟨ _ , U₀⊆ ⟩ ⟩ ⟩ with V'⊆ _ e∈
    ... | ⟨ ⟨ ⟨ x∈B , _ ⟩ , _ ⟩ , _ ⟩ =
      proj₁ (S4.ok (delay (λ x → x) N)) (λ { zero → U₀⊆ ; (suc zero) → FV⊆ ; (suc (suc y)) → λ d z → z }) x x∈B
    cT = S3.con (tuple Ms) ρ~
    ρ''~ : Con-env ρ''
    ρ''~ = Con-• U'~ (Con-• (Con-⊆ (S4.con (T.tuple (delays r Ms)) ρ'~) Cdrs⊆T') (λ _ → Con-⌈⌉ ω))
    NE-ρs = extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) NE-T) NE-E
    ρ''⊳ : ∀ {A} (x : (_ ∷ tup Δ ∷ []) ∋ A) V → mem V ⊆ ρ'' (idx x) → ApproxLR ((Es • T • (λ _ → ⌈ ω ⌉)) (idx x)) V
    ρ''⊳ Z Y' Y'⊆ = ApproxLR-⊆ Y'⊆ rU
    ρ''⊳ (S Z) Y' Y'⊆ = reflect-𝒯 Ms E Y' (λ y y∈ → Cdrs⊆T' y (Y'⊆ y y∈))

reflect-nth (M ∷ Ms) E zero = delay-reflect M E
reflect-nth (M ∷ Ms) E (suc i) = reflect-nth Ms E i

reflect-𝒯 [] E V' V'⊆ =
  ApproxLR-flat (λ v v∈ → proj₁ (𝒯0-flat v (V'⊆ v v∈))) (λ v v∈ → proj₂ (𝒯0-flat v (V'⊆ v v∈)))
reflect-𝒯 {Δ' = _ ∷ Δ'} Ms {r} {ρ} {ρ'} E V' V'⊆ = foldᴬ record
  { const-obs = λ c c∈ → ⊥-elim (V'⊆ _ c∈)
  ; nonempty-obs = λ ne → tup-ne (ne-mem ne V'⊆)
  ; app-obs = λ cs _ _ _ _ → ApproxLR-∅ (Calls-none (λ u v uv∈ → V'⊆ _ uv∈) cs)
  ; tag-obs = λ { (tupT i) W W⊆ → nth-case i W W⊆
                ; leftT W W⊆ → ApproxLR-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈))
                ; rightT W W⊆ → ApproxLR-∅ (λ d d∈ → V'⊆ _ (W⊆ d d∈)) } }
  where
  n = length Δ'
  Ds' = ⟦ delays r Ms ⟧s' ρ'
  Ds = ⟦ Ms ⟧s ρ
  comp-ne : ∀ j → nonempty (nthD Ds' j) → nonempty (nthD Ds j)
  comp-ne j ⟨ d , d∈ ⟩ = ApproxLRLayer.nonempty-obs (unfoldᴬ (reflect-nth Ms E j (d ∷ []) (single⊆ d∈))) (λ ())
  tup-ne : nonempty (𝒯 (suc n) Ds') → nonempty (𝒯 (suc n) Ds)
  tup-ne ⟨ tup[ i ] d , ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ ⟩ =
    let ⟨ d₀ , d₀∈ ⟩ = comp-ne i ⟨ d , d∈ ⟩ in ⟨ tup[ i ] d₀ , ⟨ refl , ⟨ d₀∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩ ⟩
  nth-case : ∀ {m} (i : Fin m) W' → mem W' ⊆ Untag (tupT i) (mem V') → ApproxLR (Untag (tupT i) (𝒯 (suc n) Ds)) W'
  nth-case i [] _ = ApproxLR-∅ (λ _ ())
  nth-case i (w ∷ W') W'⊆ with V'⊆ _ (W'⊆ w (here refl))
  ... | ⟨ refl , ⟨ _ , ne ⟩ ⟩ =
    ApproxLR-mono (λ d d∈ → ⟨ refl , ⟨ d∈ , (λ j → comp-ne j (ne j)) ⟩ ⟩) (reflect-nth Ms E i (w ∷ W') sub)
    where
    sub : mem (w ∷ W') ⊆ nthD Ds' i
    sub d d∈ with V'⊆ _ (W'⊆ d d∈)
    ... | ⟨ refl , ⟨ d∈' , _ ⟩ ⟩ = d∈'

{- The end theorem (backward half) --------------------------------------------}

Envs₀ : ∀ (r : Ren [] []) → Envs r ρ₀ ρ₀
Envs₀ r = envs (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ _ → Con-⌈⌉ ω) (λ ())

reflect-const : ∀ {A} (M : Tm [] A) {B} (c : base-rep B) → const c ∈ ⟦ delay-program M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀
reflect-const M c c∈ = ApproxLRLayer.const-obs (unfoldᴬ (delay-reflect M (Envs₀ _) (const c ∷ []) (single⊆ c∈))) c (here refl)

reflect-nonempty : ∀ {A} (M : Tm [] A) → nonempty (⟦ delay-program M ⟧' ρ₀) → nonempty (⟦ M ⟧ ρ₀)
reflect-nonempty M = ne-reflect M (Envs₀ _)
