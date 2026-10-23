{-

  Backward (reflect) direction of delay (EnvClosμ → FlatClosμ) in the graph
  model, as for typed delay (proof/Correctness/Graph/DelayReflect.agda),
  with the approximant logical relation ApproxLR of DelayRel (source
  sets against finite target approximants). The target call (callc) is
  the source application on the calls collected from finitely many
  pairs (collect). There is no project, so no acc-reflect; fold and
  unfold are the identity on both sides.

-}

open import proof.Framework.GraphModel.Prelude hiding (ρ₀)
open import Mu.Semantics.GraphModel.Closed using (ρ₀)
open import Framework.Primitives
open import proof.Framework.GraphModel.Ops using (⋆; 𝒯; pair; car; cdr; nthD; 𝒞-left; 𝒞-right; Λ-β; ΛΛ-β; letD-collect)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.DomainUtil using (cdr-witness; 𝒯0-flat)
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env)
open import Mu.proof.Semantics.GraphModel.Binders using (body-mono)
open import Mu.Language.Type using (Ctx; Type; tup; _⊹_; _∋_; Z; S; idx)
open import Mu.Language.EnvClos
import Mu.Language.FlatClos as T
import Mu.proof.Semantics.GraphModel.EnvClos as S3
import Mu.proof.Semantics.GraphModel.FlatClos as S4
open S3 using (⟦_⟧; ⟦_⟧s)
open S4 using () renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧s to ⟦_⟧s')
open import proof.Framework.GraphModel.TypedOkBase using (fin₁; fin₂)
open import Mu.Framework.AllUtil using (All; []; _∷_; pos)
open import Mu.Compiler.Delay using (Ren; ext; delay; delays; delay-program)
open import Mu.proof.Correctness.GraphModel.DelayRel renaming (fold to foldᴬ; unfold to unfoldᴬ)
open import Language.Prim using (δ)

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _⋵_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

module Mu.proof.Correctness.GraphModel.DelayReflect where

{- a target call V' ⊆ L' ⊙ N' is a batch of calls of a finite W ⊆ L' on a finite U ⊆ N' -}
collect : ∀ (L' N' : 𝒫 Value) V' → mem V' ⊆ (L' ⊙ N')
  → Σ[ W ∈ List Value ] Σ[ U ∈ List Value ] mem W ⊆ L' × mem U ⊆ N' × Batch W U V'
collect L' N' [] _ =
  ⟨ [] , ⟨ [] , ⟨ (λ _ ()) , ⟨ (λ _ ()) , record { results = λ _ () ; args = λ _ () } ⟩ ⟩ ⟩ ⟩
collect L' N' (w ∷ V') V'⊆
    with V'⊆ w (here refl) | collect L' N' V' (λ d d∈ → V'⊆ d (there d∈))
... | ⟨ U₀ , ⟨ ⟨ FV , ⟨ ⟨ t , e∈L' ⟩ , ⟨ FV⊆Cdr , neFV ⟩ ⟩ ⟩ , ⟨ U₀⊆N' , neU₀ ⟩ ⟩ ⟩
    | ⟨ W , ⟨ U , ⟨ W⊆ , ⟨ U⊆ , cs ⟩ ⟩ ⟩ ⟩
    with cdr-witness FV FV⊆Cdr
... | ⟨ C , ⟨ C⊆L' , FV⊆C ⟩ ⟩ =
  ⟨ e ∷ (C ++ W) , ⟨ U₀ ++ U , ⟨ ++⊆ (λ { _ (here refl) → e∈L' ; d (there d∈) → C⊆L' d d∈ }) W⊆ , ⟨ ++⊆ U₀⊆N' U⊆
  , Batch-++ (record { results = λ { _ (here refl) → ⟨ U₀ , ⟨ ent , ⟨ neU₀ , (λ _ d∈ → d∈) ⟩ ⟩ ⟩ ; _ (there ()) }
                     ; args = λ u u∈ → ⟨ U₀ , ⟨ w , ⟨ ent , u∈ ⟩ ⟩ ⟩ })
             (Batch-⊆ (λ d d∈ → there (∈-++⁺ʳ C d∈)) cs) ⟩ ⟩ ⟩ ⟩
  where
  e = ⦅ FV ↦ (U₀ ↦ w) , t ⦆
  ent = usable-entry FV t (here refl) neFV (λ d d∈ → let ⟨ u , i ⟩ = FV⊆C d d∈ in ⟨ u , there (∈-++⁺ˡ i) ⟩)
  ++⊆ : ∀ {A B : List Value} {D} → mem A ⊆ D → mem B ⊆ D → mem (A ++ B) ⊆ D
  ++⊆ {A} A⊆ B⊆ d d∈ = [ A⊆ d , B⊆ d ]′ (∈-++⁻ A d∈)

{- The fundamental lemma ------------------------------------------------------}

record Envs {Γ Δ} (r : Ren Γ Δ) (ρ ρ' : Env Value) : Set₁ where
  constructor envs
  field
    NE : nonempty-env ρ
    ρ~ : Con-env ρ
    ρ'~ : Con-env ρ'
    ρ⊳ : ∀ {A} (x : Γ ∋ A) → Approx (ρ (idx x)) (ρ' (idx (r x)))

ext-envs : ∀ {Γ Δ B} {r : Ren Γ Δ} {ρ ρ' X X'} → Envs r ρ ρ' → nonempty X → Con X → Con X' → Approx X X'
  → Envs (ext {B = B} r) (X • ρ) (X' • ρ')
ext-envs (envs NE ρ~ ρ'~ ρ⊳) ne c c' h =
  envs (extend-nonempty-env NE ne) (Con-• c ρ~) (Con-• c' ρ'~) (λ { Z → h ; (S x) → ρ⊳ x })

delay-reflect : ∀ {Γ Δ A} (M : Tm Γ A) {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ' → Approx (⟦ M ⟧ ρ) (⟦ delay r M ⟧' ρ')
reflect-nth : ∀ {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → (i : Fin (length Δ')) → Approx (nthD (⟦ Ms ⟧s ρ) i) (nthD (⟦ delays r Ms ⟧s' ρ') i)
reflect-𝒯 : ∀ {Γ Δ Δ'} (Ms : All (Tm Γ) Δ') {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → Approx (𝒯 (length Δ') (⟦ Ms ⟧s ρ)) (𝒯 (length Δ') (⟦ delays r Ms ⟧s' ρ'))

{- by consistency, all the results of a target case come from the branch B on the side s -}
reflect-branch : ∀ {Γ Δ} {A₁ A₂ A C : Type} (s : Tag) (L : Tm Γ (A₁ ⊹ A₂)) (B : Tm (A ∷ Γ) C) {r : Ren Γ Δ} {ρ ρ' C} → Envs r ρ ρ'
  → ∀ v → tag s v ∈ ⟦ delay r L ⟧' ρ' → (∀ {a b} → tag s a ~ tag s b → a ~ b)
  → (nonempty (Untag s (⟦ L ⟧ ρ)) → ⟦ B ⟧ (Untag s (⟦ L ⟧ ρ) • ρ) ⊆ C)
  → Approx C (⟦ delay (ext r) B ⟧' (Untag s (⟦ delay r L ⟧' ρ') • ρ'))
reflect-branch s L B {r} E v sv s~ B⊆ V' V'⊆ =
  ApproxLR-mono (B⊆ NE-s)
    (delay-reflect B (ext-envs E NE-s (Untag-con s s~ (S3.con L ρ~)) (Untag-con s s~ (S4.con (delay r L) ρ'~))
       (Approx-untag s (delay-reflect L E))) V' V'⊆)
  where
  open Envs E
  NE-s = Approx-ne (Approx-untag s (delay-reflect L E)) ⟨ v , sv ⟩

delay-reflect (` x) E = Envs.ρ⊳ E x

delay-reflect (app L N) {r} {ρ' = ρ'} E V' V'⊆ with collect (⟦ delay r L ⟧' ρ') (⟦ delay r N ⟧' ρ') V' V'⊆
... | ⟨ W , ⟨ U , ⟨ W⊆L' , ⟨ U⊆N' , cs ⟩ ⟩ ⟩ ⟩ =
  ApproxLRLayer.app-obs (unfoldᴬ (delay-reflect L E W W⊆L')) cs _ (S3.con N (Envs.ρ~ E))
    (Con-⊆ (S4.con (delay r N) (Envs.ρ'~ E)) U⊆N') (delay-reflect N E U U⊆N')

delay-reflect (lit B c) E V' V'⊆ = ApproxLR-data (λ v v∈ → ⟨ V'⊆ v v∈ , flat-data (ℬ-flat v (V'⊆ v v∈)) ⟩)

delay-reflect (prim p L M) E V' V'⊆ = ApproxLR-data (λ v v∈ → prim-data (V'⊆ v v∈))
  where
  prim-data : ∀ {v} → v ∈ ⟦ delay _ (prim p L M) ⟧' _ → v ∈ ⟦ prim p L M ⟧ _ × Data v
  prim-data ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
    ⟨ ⟨ n , ⟨ m , ⟨ Approx-const (delay-reflect L E) n∈ , ⟨ Approx-const (delay-reflect M E) m∈ , refl ⟩ ⟩ ⟩ ⟩ , out-data (δ p n m) ⟩

delay-reflect (tuple Ms) = reflect-𝒯 Ms

delay-reflect (get i M) E = Approx-untag (tupT (pos i)) (delay-reflect M E)

delay-reflect M₀@(inl M) {r} {ρ} {ρ'} E = Approx-fold₀ (λ _ ()) inl-ne (λ _ _ ())
  λ { leftT → delay-reflect M E ; rightT _ → ApproxLR-∅ ; (tupT i) _ → ApproxLR-∅ }
  where
  inl-ne : nonempty (⟦ delay r M₀ ⟧' ρ') → nonempty (⟦ M₀ ⟧ ρ)
  inl-ne ⟨ left d , d∈ ⟩ = let ⟨ m , m∈ ⟩ = Approx-ne (delay-reflect M E) ⟨ d , d∈ ⟩ in ⟨ left m , m∈ ⟩

delay-reflect M₀@(inr M) {r} {ρ} {ρ'} E = Approx-fold₀ (λ _ ()) inr-ne (λ _ _ ())
  λ { rightT → delay-reflect M E ; leftT _ → ApproxLR-∅ ; (tupT i) _ → ApproxLR-∅ }
  where
  inr-ne : nonempty (⟦ delay r M₀ ⟧' ρ') → nonempty (⟦ M₀ ⟧ ρ)
  inr-ne ⟨ right d , d∈ ⟩ = let ⟨ m , m∈ ⟩ = Approx-ne (delay-reflect M E) ⟨ d , d∈ ⟩ in ⟨ right m , m∈ ⟩

delay-reflect (case L M N) E [] V'⊆ = ApproxLR-∅ (λ _ ())
delay-reflect (case L M N) {r} {ρ} {ρ'} E (w ∷ V') V'⊆ with V'⊆ w (here refl)
... | inj₁ ⟨ v , ⟨ _ , ⟨ allL , _ ⟩ ⟩ ⟩ =
  reflect-branch leftT L M E v (allL v (here refl)) (λ a~b → a~b)
    (λ ne → 𝒞-left {⟦ L ⟧ ρ} {λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ N ⟧ (X • ρ)} (fin₁ (S3.ok M) NE ne)
              (Untag-con leftT (λ c → c) (S3.con L ρ~))) (w ∷ V') V'⊆F
  where
  open Envs E
  V'⊆F : mem (w ∷ V') ⊆ ⟦ delay (ext r) M ⟧' (Lefts (⟦ delay r L ⟧' ρ') • ρ')
  V'⊆F x x∈ with V'⊆ x x∈
  ... | inj₁ ⟨ _ , ⟨ _ , ⟨ allL' , ⟨ x∈F , _ ⟩ ⟩ ⟩ ⟩ = body-mono (S4.ok (delay (ext r) M)) ρ' allL' x x∈F
  ... | inj₂ ⟨ u , ⟨ _ , ⟨ allR , _ ⟩ ⟩ ⟩ = ⊥-elim (S4.con (delay r L) ρ'~ _ _ (allL v (here refl)) (allR u (here refl)))
... | inj₂ ⟨ v , ⟨ _ , ⟨ allR , _ ⟩ ⟩ ⟩ =
  reflect-branch rightT L N E v (allR v (here refl)) (λ a~b → a~b)
    (λ ne → 𝒞-right {⟦ L ⟧ ρ} {λ X → ⟦ M ⟧ (X • ρ)} {λ X → ⟦ N ⟧ (X • ρ)} (fin₁ (S3.ok N) NE ne)
              (Untag-con rightT (λ c → c) (S3.con L ρ~))) (w ∷ V') V'⊆G
  where
  open Envs E
  V'⊆G : mem (w ∷ V') ⊆ ⟦ delay (ext r) N ⟧' (Rights (⟦ delay r L ⟧' ρ') • ρ')
  V'⊆G x x∈ with V'⊆ x x∈
  ... | inj₂ ⟨ _ , ⟨ _ , ⟨ allR' , ⟨ x∈G , _ ⟩ ⟩ ⟩ ⟩ = body-mono (S4.ok (delay (ext r) N)) ρ' allR' x x∈G
  ... | inj₁ ⟨ u , ⟨ _ , ⟨ allL , _ ⟩ ⟩ ⟩ = ⊥-elim (S4.con (delay r L) ρ'~ _ _ (allR v (here refl)) (allL u (here refl)))

delay-reflect (let′ M N) E [] V'⊆ = ApproxLR-∅ (λ _ ())
delay-reflect (let′ M N) {r} {ρ} {ρ'} E (w ∷ V') V'⊆
    with letD-collect (body-mono (S4.ok (delay (ext r) N)) ρ') (w ∷ V') V'⊆
... | ⟨ U , ⟨ U⊆ , V'⊆N ⟩ ⟩ =
  ApproxLR-mono (proj₂ (Λ-β (body-mono (S3.ok N) ρ) (fin₁ (S3.ok N) NE NE-M) (S3.con M ρ~)))
    (delay-reflect N (ext-envs E NE-M (S3.con M ρ~) (Con-⊆ (S4.con (delay r M) ρ'~) U⊆)
       (λ Y' Y'⊆ → delay-reflect M E Y' (λ d d∈ → U⊆ d (Y'⊆ d d∈)))) (w ∷ V') V'⊆N)
  where
  open Envs E
  NE-M = let ⟨ _ , ⟨ _ , ⟨ U₀⊆ , ne ⟩ ⟩ ⟩ = V'⊆ w (here refl) in Approx-ne (delay-reflect M E) (ne-mem ne U₀⊆)

delay-reflect (fold M) E = delay-reflect M E

delay-reflect (unfold M) E = delay-reflect M E

delay-reflect (clos {Δ} N Ms) {r} {ρ} {ρ'} E = Approx-fold (λ _ ()) (λ ne → ⟨ ν , ν∈ (pair-ne ne) ⟩) clos-app
  λ { (tupT i) _ → ApproxLR-∅ ; leftT _ → ApproxLR-∅ ; rightT _ → ApproxLR-∅ }
  where
  open Envs E
  T' = 𝒯 (length Δ) (⟦ delays r Ms ⟧s' ρ')

  pair-ne : nonempty (⟦ delay r (clos N Ms) ⟧' ρ') → nonempty T'
  pair-ne ⟨ ⦅ u , v ⦆ , ⟨ _ , v∈ ⟩ ⟩ = ⟨ v , v∈ ⟩
  ν∈ : nonempty T' → ν ∈ ⟦ clos N Ms ⟧ ρ
  ν∈ ne = let ⟨ t , t∈ ⟩ = Approx-ne (reflect-𝒯 Ms E) ne in ⟨ t ∷ [] , ⟨ ⟨ tt , ⟨ (λ ()) , ≈-single ⟩ ⟩ , ⟨ single⊆ t∈ , (λ ()) ⟩ ⟩ ⟩

  clos-app : AppObs (⟦ clos N Ms ⟧ ρ) (⟦ delay r (clos N Ms) ⟧' ρ')
  clos-app {W = []} _ _ _ _ _ _ = ApproxLR-∅ (λ _ ())
  clos-app {V'} {U'} {w ∷ W'} V'⊆ cs Es cE U'~ rU with Batch.results cs w (here refl)
  ... | ⟨ U₀ , ⟨ usable-entry FV _ _ neFV FV⊆ , ⟨ neU₀ , U₀⊆ ⟩ ⟩ ⟩ =
    ApproxLR-mono (ΛΛ-β {F = λ X Y → ⟦ N ⟧ (Y • X • λ _ → ⌈ ⟨⟩ ⌉)} cT cE (fin₂ (S3.ok N) NE-T NE-E))
      (delay-reflect N {r = λ x → x}
         (envs (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ⟨⟩ , refl ⟩) NE-T) NE-E) (Con-• cE (Con-• cT (λ _ → Con-⌈⌉ ⟨⟩)))
               (Con-• U'~ (Con-• (Con-⊆ (S4.con (T.tuple (delays r Ms)) ρ'~) Cdrs⊆T') (λ _ → Con-⌈⌉ ⟨⟩)))
               (λ { Z Y' Y'⊆ → ApproxLR-⊆ Y'⊆ rU ; (S Z) Y' Y'⊆ → reflect-𝒯 Ms E Y' (λ y y∈ → Cdrs⊆T' y (Y'⊆ y y∈)) }))
         (w ∷ W') W⊆B)
    where
    cT = S3.con (tuple Ms) ρ~
    Cdrs⊆T' : Cdrs V' ⊆ T'
    Cdrs⊆T' fv ⟨ _ , e∈ ⟩ = proj₂ (V'⊆ _ e∈)
    NE-E = ApproxLRLayer.nonempty-obs (unfoldᴬ rU) (ne-⊆ U₀⊆ neU₀)
    NE-T = Approx-ne (reflect-𝒯 Ms E) (ne-mem neFV (λ d d∈ → Cdrs⊆T' d (FV⊆ d d∈)))
    W⊆B : mem (w ∷ W') ⊆ ⟦ delay (λ x → x) N ⟧' (mem U' • Cdrs V' • (λ _ → ⌈ ⟨⟩ ⌉))
    W⊆B x x∈ with Batch.results cs x x∈
    ... | ⟨ _ , ⟨ usable-entry _ _ e∈ _ FV⊆' , ⟨ _ , U₁⊆ ⟩ ⟩ ⟩ with V'⊆ _ e∈
    ... | ⟨ ⟨ ⟨ x∈B , _ ⟩ , _ ⟩ , _ ⟩ =
      proj₁ (S4.ok (delay (λ x → x) N)) (λ { zero → U₁⊆ ; (suc zero) → FV⊆' ; (suc (suc y)) → λ d z → z }) x x∈B

reflect-nth (M ∷ Ms) E zero = delay-reflect M E
reflect-nth (M ∷ Ms) E (suc i) = reflect-nth Ms E i

reflect-𝒯 [] E V' V'⊆ = ApproxLR-data (λ v v∈ → let ⟨ v∈ , f ⟩ = 𝒯0-flat v (V'⊆ v v∈) in ⟨ v∈ , flat-data f ⟩)
reflect-𝒯 {Δ' = _ ∷ Δ'} Ms {r} {ρ} {ρ'} E = Approx-fold₀ (λ _ ()) tup-ne (λ _ _ ())
  λ { (tupT i) → nth-case i ; leftT _ → ApproxLR-∅ ; rightT _ → ApproxLR-∅ }
  where
  n = length Δ'
  Ds' = ⟦ delays r Ms ⟧s' ρ'
  Ds = ⟦ Ms ⟧s ρ
  tup-ne : nonempty (𝒯 (suc n) Ds') → nonempty (𝒯 (suc n) Ds)
  tup-ne ⟨ tup[ i ] d , ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ ⟩ = let ⟨ d₀ , d₀∈ ⟩ = Approx-ne (reflect-nth Ms E i) ⟨ d , d∈ ⟩
    in ⟨ tup[ i ] d₀ , ⟨ refl , ⟨ d₀∈ , (λ j → Approx-ne (reflect-nth Ms E j) (ne j)) ⟩ ⟩ ⟩
  nth-case : ∀ {m} (i : Fin m) → Approx (Untag (tupT i) (𝒯 (suc n) Ds)) (Untag (tupT i) (𝒯 (suc n) Ds'))
  nth-case i [] _ = ApproxLR-∅ (λ _ ())
  nth-case i (w ∷ W') W'⊆ with W'⊆ w (here refl)
  ... | ⟨ refl , ⟨ _ , ne ⟩ ⟩ =
    ApproxLR-mono (λ d d∈ → ⟨ refl , ⟨ d∈ , (λ j → Approx-ne (reflect-nth Ms E j) (ne j)) ⟩ ⟩) (reflect-nth Ms E i (w ∷ W') sub)
    where
    sub : mem (w ∷ W') ⊆ nthD Ds' i
    sub d d∈ with W'⊆ d d∈
    ... | ⟨ refl , ⟨ d∈' , _ ⟩ ⟩ = d∈'

{- The end theorem (backward half) --------------------------------------------}

Envs₀ : ∀ (r : Ren [] []) → Envs r ρ₀ ρ₀
Envs₀ r = envs (λ _ → ⟨ ⟨⟩ , refl ⟩) (λ _ → Con-⌈⌉ ⟨⟩) (λ _ → Con-⌈⌉ ⟨⟩) (λ ())

reflect-const : ∀ {A} (M : Tm [] A) {B} (c : base-rep B) → const c ∈ ⟦ delay-program M ⟧' ρ₀ → const c ∈ ⟦ M ⟧ ρ₀
reflect-const M c = Approx-const (delay-reflect M (Envs₀ _))

reflect-nonempty : ∀ {A} (M : Tm [] A) → nonempty (⟦ delay-program M ⟧' ρ₀) → nonempty (⟦ M ⟧ ρ₀)
reflect-nonempty M = Approx-ne (delay-reflect M (Envs₀ _))
