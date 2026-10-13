{-

  The semantics of Clos2 in the graph model with errors is continuous:
  every element of a denotation is already in the denotation in a
  finite, nonempty part of the environment.

  The operators other than closures are Good (ErrorContinuity.agda). A
  closure applies its body to the denotations of its free variables
  directly, which need not be finite, so the body must be continuous in
  environments that are not finite; the framework's operators assume it
  only for finite ones (BodyCont). So this is proved by induction on the
  term, for every nonempty environment (SCont): the body gives a finite
  part of the environment it runs in, and the free variables a finite
  part of theirs (EnvCont). (The graph model proves no continuity for
  Clos2, whose correctness proofs do not need it.)

-}

module proof.Semantics.GraphErr.Clos2Continuous where

open import Framework.Syntax.SigUtil
open import Framework.Syntax.SyntaxUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Framework.GraphModel.ContinuityBase
open import proof.Framework.GraphModel.ErrorContinuity
open import proof.Framework.GraphModel.Env
  using (Env; nonempty-env; finiteNE-env; extend-nonempty-env; _⊆ₑ_; •-~; single-env; single-fin; single-⊆; v∈single[xv]x)
open import proof.Semantics.GraphErr.Prim
open import Language.Clos2
open import proof.Semantics.GraphErr.Clos2

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import Level using (lift; lower)
open import Data.Unit using (⊤)

{- The bodies of the operands ----------------------------------------------------}

body : ∀ {b} → Arg b → VEnv → 𝒫 Value
body (ast M) = ⟦ M ⟧
body (bind a) = body a
body (clear a) = body a

bodies : ∀ {bs} → Args bs → Bodies bs
bodies nil = ptt
bodies (cons a as) = ⟨ body a , bodies as ⟩

body-mono : ∀ {b} (a : Arg b) → Mono (body a)
body-mono (ast M) = ⟦⟧-monotone M
body-mono (bind a) = body-mono a
body-mono (clear a) = body-mono a

{- the operands and their bodies agree -}
arg⊆ : ∀ {b} (a : Arg b) {ρ ρ′} → ρ ⊆ₑ ρ′
  → result-rel-pres _⊆_ b (⟦ a ⟧ₐ ρ) (⟪ b ⟫ (body a) ρ′) × result-rel-pres _⊆_ b (⟪ b ⟫ (body a) ρ) (⟦ a ⟧ₐ ρ′)
arg⊆ (ast M) ρ⊆ = ⟨ lift (⟦⟧-monotone M ρ⊆) , lift (⟦⟧-monotone M ρ⊆) ⟩
arg⊆ (bind a) ρ⊆ = ⟨ (λ X Y X⊆ → proj₁ (arg⊆ a (•-~ _⊆_ ρ⊆ X⊆))) , (λ X Y X⊆ → proj₂ (arg⊆ a (•-~ _⊆_ ρ⊆ X⊆))) ⟩
arg⊆ (clear a) ρ⊆ = arg⊆ a (λ _ _ d∈ → d∈)

args⊆ : ∀ {bs} (as : Args bs) {ρ ρ′} → ρ ⊆ₑ ρ′
  → results-rel-pres _⊆_ bs (⟦ as ⟧₊ ρ) (⟪ bs ⟫₊ (bodies as) ρ′)
  × results-rel-pres _⊆_ bs (⟪ bs ⟫₊ (bodies as) ρ) (⟦ as ⟧₊ ρ′)
args⊆ nil ρ⊆ = ⟨ ptt , ptt ⟩
args⊆ (cons a as) ρ⊆ = ⟨ ⟨ proj₁ (arg⊆ a ρ⊆) , proj₁ (args⊆ as ρ⊆) ⟩ , ⟨ proj₂ (arg⊆ a ρ⊆) , proj₂ (args⊆ as ρ⊆) ⟩ ⟩

{- for first-order operands, they are equal -}
fvs≡ : ∀ n (fvs : Args (replicate n ■)) ρ → ⟦ fvs ⟧₊ ρ ≡ ⟪ replicate n ■ ⟫₊ (bodies fvs) ρ
fvs≡ zero Nil ρ = refl
fvs≡ (suc n) (M ,, fvs) ρ = cong (λ Ds → ⟨ ⟦ M ⟧ ρ , Ds ⟩) (fvs≡ n fvs ρ)

{- continuity wherever the operand puts the body, for every nonempty set
   a binder binds (not only the finite ones, as BodyCont) -}
SCont : Sig → (VEnv → 𝒫 Value) → VEnv → Set₁
SCont ■ E ρ = Cont E ρ
SCont (ν b) E ρ = ∀ X → nonempty X → SCont b E (X • ρ)
SCont (∁ b) E ρ = SCont b E (λ _ → ⌈ ω ⌉)

scont→bodycont : ∀ b {E ρ} → SCont b E ρ → BodyCont b E ρ
scont→bodycont ■ s = s
scont→bodycont (ν b) s V ne = scont→bodycont b (s (mem V) (E≢[]⇒nonempty-mem ne))
scont→bodycont (∁ b) s = scont→bodycont b s

{- a body under the n + 1 binders of a closure, applied -}
scont-apply : ∀ n {E σ} (Ds : Results (𝒫 Value) (replicate n ■)) → SCont (ν-n n (ν ■)) E σ
  → (∀ i → nonempty (nthD Ds i)) → ∀ Y → nonempty Y → Cont E (Y • push Ds σ)
scont-apply zero Ds s ne Y neY = s Y neY
scont-apply (suc n) ⟨ D , Ds ⟩ s ne Y neY = scont-apply n Ds (s D (ne fzero)) (λ i → ne (fsuc i)) Y neY

apply-body : ∀ k (a : Arg (ν-n k (ν ■))) σ Ds Y → apply-n k (⟦ a ⟧ₐ σ) Ds Y ≡ body a (Y • push Ds σ)
apply-body zero (bind (ast N)) σ Ds Y = refl
apply-body (suc k) (bind a) σ ⟨ D , Ds ⟩ Y = apply-body k a (D • σ) Ds Y

push-ne : ∀ n (Ds : Results (𝒫 Value) (replicate n ■)) σ → (∀ i → nonempty (nthD Ds i))
  → nonempty-env σ → nonempty-env (push Ds σ)
push-ne zero _ σ _ NE = NE
push-ne (suc n) ⟨ D , Ds ⟩ σ ne NE = push-ne n Ds (D • σ) (λ i → ne (fsuc i)) (extend-nonempty-env NE (ne fzero))

val-ne : ∀ {D} → val∈ D → nonempty D
val-ne ⟨ d , ⟨ d∈ , _ ⟩ ⟩ = ⟨ d , d∈ ⟩

{- Environments as functions of the environment -------------------------------------}

EnvMono : (VEnv → VEnv) → Set₁
EnvMono H = ∀ {ρ ρ′} → ρ ⊆ₑ ρ′ → H ρ ⊆ₑ H ρ′

{- a finite part of H ρ is in H of a finite part of ρ -}
EnvCont : (VEnv → VEnv) → VEnv → Set₁
EnvCont H ρ = ∀ ρ″ → finiteNE-env ρ″ → ρ″ ⊆ₑ H ρ → Σ[ a ∈ Approx ρ ] ρ″ ⊆ₑ H (env a)

const-envcont : ∀ {σ ρ} → nonempty-env ρ → EnvCont (λ _ → σ) ρ
const-envcont NE ρ″ fin ρ″⊆ = ⟨ approx-init NE , ρ″⊆ ⟩

ext-envcont : ∀ {D : VEnv → 𝒫 Value} {H ρ} → nonempty-env ρ → Mono D → Cont D ρ
  → EnvMono H → EnvCont H ρ → EnvCont (λ ρ → D ρ • H ρ) ρ
ext-envcont {D} {H} NE mD cD mH cH ρ″ fin ρ″⊆
    with fin 0
... | ⟨ V , ⟨ ≃V , _ ⟩ ⟩
    with many D NE mD cD V (λ d d∈ → ρ″⊆ 0 d (proj₂ ≃V d d∈))
       | cH (λ x → ρ″ (suc x)) (λ x → fin (suc x)) (λ x → ρ″⊆ (suc x))
... | ⟨ a , V⊆ ⟩ | ⟨ b , T⊆ ⟩ = ⟨ approx-join a b , G ⟩
  where
  G : ρ″ ⊆ₑ (λ x → (D (env (approx-join a b)) • H (env (approx-join a b))) x)
  G zero d d∈ = mD (join-l a b) d (V⊆ d (proj₁ ≃V d d∈))
  G (suc x) d d∈ = mH (join-r a b) x d (T⊆ x d d∈)

push-mono : ∀ n (fvs : Args (replicate n ■)) {S : VEnv → VEnv} → EnvMono S
  → EnvMono (λ ρ → push (⟦ fvs ⟧₊ ρ) (S ρ))
push-mono zero Nil mS = mS
push-mono (suc n) (M ,, fvs) {S} mS =
  push-mono n fvs {λ ρ → ⟦ M ⟧ ρ • S ρ} (λ ρ⊆ → λ { zero → ⟦⟧-monotone M ρ⊆ ; (suc x) → mS ρ⊆ x })

push-envcont : ∀ n (fvs : Args (replicate n ■)) {S : VEnv → VEnv} {ρ} → nonempty-env ρ
  → OK (replicate n ■) (bodies fvs) ρ → EnvMono S → EnvCont S ρ
  → EnvCont (λ ρ → push (⟦ fvs ⟧₊ ρ) (S ρ)) ρ
push-envcont zero Nil NE _ mS cS = cS
push-envcont (suc n) (M ,, fvs) {S} NE ⟨ ⟨ mM , cM ⟩ , oks ⟩ mS cS =
  push-envcont n fvs {λ ρ → ⟦ M ⟧ ρ • S ρ} NE oks
    (λ ρ⊆ → λ { zero → ⟦⟧-monotone M ρ⊆ ; (suc x) → mS ρ⊆ x })
    (ext-envcont {⟦ M ⟧} {S} NE mM cM mS cS)

{- The semantics is continuous ---------------------------------------------------------}

⟦⟧-cont : ∀ M {ρ} → nonempty-env ρ → Cont ⟦ M ⟧ ρ
arg-cont : ∀ {b} (a : Arg b) {ρ} → nonempty-env ρ → SCont b (body a) ρ
args-ok : ∀ {bs} (as : Args bs) {ρ} → nonempty-env ρ → OK bs (bodies as) ρ
via : ∀ op (as : Args (sig op)) → Good ⊤ (sig op) (𝕆-Clos2ᵉ op) → ∀ {ρ} → nonempty-env ρ
  → Cont ⟦ op ⦅ as ⦆ ⟧ ρ

via op as g {ρ} NE v v∈
    with cont g (bodies as) NE (args-ok as NE) v
           (lower (mono g (⟦ as ⟧₊ ρ) (⟪ sig op ⟫₊ (bodies as) ρ) (proj₁ (args⊆ as (λ _ _ d∈ → d∈)))) v v∈)
... | ⟨ ρ′ , ⟨ f , ⟨ s , v∈′ ⟩ ⟩ ⟩ =
  ⟨ ρ′ , ⟨ f , ⟨ s , lower (mono g (⟪ sig op ⟫₊ (bodies as) ρ′) (⟦ as ⟧₊ ρ′)
                             (proj₂ (args⊆ as (λ _ _ d∈ → d∈)))) v v∈′ ⟩ ⟩ ⟩

arg-cont (ast M) NE = ⟦⟧-cont M NE
arg-cont (bind a) NE X neX = arg-cont a (extend-nonempty-env NE neX)
arg-cont (clear a) NE = arg-cont a (λ _ → ⟨ ω , refl ⟩)

args-ok nil NE = ptt
args-ok {b ∷ bs} (cons a as) NE = ⟨ ⟨ body-mono a , scont→bodycont b (arg-cont a NE) ⟩ , args-ok as NE ⟩

⟦⟧-cont (` x) {ρ} NE v v∈ =
  ⟨ single-env x ⌈ v ⌉ ρ NE , ⟨ single-fin {Value} {v} {x} , ⟨ single-⊆ v∈ , v∈single[xv]x {Value} {v} {x} ⟩ ⟩ ⟩
⟦⟧-cont (app ⦅ as ⦆) NE = via app as ⋆ᵉ-good NE
⟦⟧-cont (lit B k ⦅ as ⦆) NE = via (lit B k) as (ℬ-good B k) NE
⟦⟧-cont (tuple n ⦅ as ⦆) NE = via (tuple n) as (𝒯ᵉ-good n) NE
⟦⟧-cont (get i ⦅ as ⦆) NE = via (get i) as (projᵉ-good i) NE
⟦⟧-cont (inl-op ⦅ as ⦆) NE = via inl-op as inlᵉ-good NE
⟦⟧-cont (inr-op ⦅ as ⦆) NE = via inr-op as inrᵉ-good NE
⟦⟧-cont (case-op ⦅ as ⦆) NE = via case-op as 𝒞ᵉ-good NE
⟦⟧-cont (prim p ⦅ as ⦆) NE = via (prim p) as (primᵉ-good p) NE
⟦⟧-cont (let-op ⦅ as ⦆) NE = via let-op as letᵉ-good NE
⟦⟧-cont (clos-op n ⦅ cons (clear a) fvs ⦆) {ρ} NE v (inj₁ ⟨ refl , e ⟩)
    with errs-cont n (bodies fvs) NE (args-ok fvs NE) (subst (errs n) (fvs≡ n fvs ρ) e)
... | ⟨ b , e′ ⟩ =
  done ⟦ clos-op n ⦅ cons (clear a) fvs ⦆ ⟧ b ω (inj₁ ⟨ refl , subst (errs n) (sym (fvs≡ n fvs (env b))) e′ ⟩)
⟦⟧-cont (clos-op n ⦅ cons (clear a) fvs ⦆) {ρ} NE ν (inj₂ ⟨ vs , _ ⟩)
    with vals-cont n (bodies fvs) NE (args-ok fvs NE) (subst (vals n) (fvs≡ n fvs ρ) vs)
... | ⟨ b , vs′ ⟩ =
  done ⟦ clos-op n ⦅ cons (clear a) fvs ⦆ ⟧ b ν (inj₂ ⟨ subst (vals n) (sym (fvs≡ n fvs (env b))) vs′ , tt ⟩)
⟦⟧-cont (clos-op n ⦅ cons (clear a) fvs ⦆) {ρ} NE (V ↦ w) (inj₂ ⟨ vs , ⟨ w∈ , r ⟩ ⟩)
    with scont-apply n (⟦ fvs ⟧₊ ρ) (arg-cont a {λ _ → ⌈ ω ⌉} (λ _ → ⟨ ω , refl ⟩))
           (λ i → val-ne (vs i)) (mem V) (E≢[]⇒nonempty-mem (proj₁ r))
           w (subst (w ∈_) (apply-body n a (λ _ → ⌈ ω ⌉) (⟦ fvs ⟧₊ ρ) (mem V)) w∈)
... | ⟨ ρ″ , ⟨ fin , ⟨ ρ″⊆ , w∈″ ⟩ ⟩ ⟩
    with ext-envcont {λ _ → mem V} {λ ρ → push (⟦ fvs ⟧₊ ρ) (λ _ → ⌈ ω ⌉)} NE
           (λ _ d d∈ → d∈) (const-cont NE)
           (push-mono n fvs {λ _ → λ _ → ⌈ ω ⌉} (λ _ _ d d∈ → d∈))
           (push-envcont n fvs NE (args-ok fvs NE) (λ _ _ d d∈ → d∈) (const-envcont NE))
           ρ″ fin ρ″⊆
       | vals-cont n (bodies fvs) NE (args-ok fvs NE) (subst (vals n) (fvs≡ n fvs ρ) vs)
... | ⟨ b , ρ″⊆′ ⟩ | ⟨ c , vs′ ⟩ =
  done ⟦ clos-op n ⦅ cons (clear a) fvs ⦆ ⟧ (approx-join b c) (V ↦ w)
    (inj₂ ⟨ subst (vals n) (sym (fvs≡ n fvs (env (approx-join b c))))
              (vals-mono n _ _ (oks-mono n (bodies fvs) (args-ok fvs NE) (join-r b c)) vs′)
          , ⟨ subst (w ∈_) (sym (apply-body n a (λ _ → ⌈ ω ⌉) (⟦ fvs ⟧₊ (env (approx-join b c))) (mem V)))
                (body-mono a (λ x d d∈ → G x d (ρ″⊆′ x d d∈)) w w∈″)
            , r ⟩ ⟩)
  where
  G : (λ x → (mem V • push (⟦ fvs ⟧₊ (env b)) (λ _ → ⌈ ω ⌉)) x)
      ⊆ₑ (mem V • push (⟦ fvs ⟧₊ (env (approx-join b c))) (λ _ → ⌈ ω ⌉))
  G zero d d∈ = d∈
  G (suc x) = push-mono n fvs {λ _ → λ _ → ⌈ ω ⌉} (λ _ _ d d∈ → d∈) (join-l b c) x
