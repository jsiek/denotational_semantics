{-

  Correctness of typed remove complex operands (Clos5ᵀ → Monᵀ, run as
  its embedding into Clos5ᵀ), clock for clock (see the design note in
  Semantics/Interp/Clock.agda). The pass only adds lets, which do not
  tick, and an atom evaluates without calling anything (and cannot
  fail), so a term and its rco, in environments that agree through the
  renaming ρ (Agree), give the same result for every clock.

  atomize M ρ k evaluates M and passes its atom to the continuation k,
  under any further lets (Kripke): if k, for an atom of value v in any
  environment that extends φ, means K v (KOk K k φ), then atomize M ρ k
  means the value of M passed to K (atomize-ok).

-}

module proof.Correctness.Interp.RCOFuel where

open import Language.Typed.Type
open import Framework.Primitives using (Int)
open import Language.Typed.Clos5
import Language.Typed.Mon as M
open M using (Atm; var; lit; ref; ren; ⌜_⌝; ⌜_⌝ᵃ; ⌜_⌝ᵛ; ⌜_⌝ₚ)
open import Compiler.RCO
open import proof.Semantics.Interp.Clock
import Semantics.Interp.Typed.Clos5 as C
open C using (eval; evals; call)
open import Framework.Lookup using (_!_)
open import Semantics.Interp.Typed.Imp using (atom)
open import proof.Semantics.Interp.Typed.Clos5 using (def-map; atm-bind; atoms-bind; either-cong)

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

module _ {Σ : List ℕ} (ds : All (Code Σ) Σ) where
  open C.Vals Σ
  private ds' = All-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds)

  {- the environment γ of the source is held, through ρ, by that of the target φ -}
  Agree : ∀ {Γ Δ} → Ren Γ Δ → Env Γ → Env Δ → Set
  Agree ρ γ φ = ∀ {A} (x : _ ∋ A) → γ ! x ≡ φ ! ρ x

  atom-ren : ∀ {Δ Δ' A} {r : Ren Δ Δ'} {φ φ'} (a : Atm Σ Δ A) → Agree r φ φ' → atom φ a ≡ atom φ' (ren r a)
  atom-ren (var x) h = h x
  atom-ren (lit B c) h = refl
  atom-ren (ref f) h = refl

  K-prim : ∀ p → Val ⟪ base Int ⟫ → Val ⟪ base Int ⟫ → Result (Val ⟪ out-flat p ⟫)
  K-prim p v w = ret (δ p v w)

  module _ (ck : ℕ) (calls : ∀ f w → call ds ck f w ≡ call ds' ck f w) where

    {- K v is what k means, given an atom of value v in an environment that extends φ -}
    KOk : ∀ {Δ A B} → (Val A → Result (Val B)) → K Σ Δ A B → Env Δ → Set
    KOk {Δ} K k φ = ∀ {Δ'} (r : Ren Δ Δ') φ' a → Agree r φ φ' → K (atom φ' a) ≡ eval ds' ck φ' ⌜ k r a ⌝

    rco-ok : ∀ {Γ Δ A} (N : Tm Σ Γ A) (ρ : Ren Γ Δ) {γ φ} → Agree ρ γ φ
      → eval ds ck γ N ≡ eval ds' ck φ ⌜ rco N ρ ⌝
    atomize-ok : ∀ {Γ Δ A B} (N : Tm Σ Γ A) (ρ : Ren Γ Δ) {k : K Σ Δ A B} {K' γ φ} → Agree ρ γ φ → KOk K' k φ
      → (eval ds ck γ N >>= K') ≡ eval ds' ck φ ⌜ atomize N ρ k ⌝
    atomize-let : ∀ {Γ Δ A B} (N : Tm Σ Γ A) (ρ : Ren Γ Δ) {k : K Σ Δ A B} {K' γ φ} → Agree ρ γ φ → KOk K' k φ
      → (eval ds ck γ N >>= K') ≡ eval ds' ck φ ⌜ M.let′ (rco N ρ) (k S (var Z)) ⌝
    atomizes-ok : ∀ {Γ Δ n B} (Ns : Vec (Tm Σ Γ Any) n) (ρ : Ren Γ Δ)
      {k : ∀ {Δ'} → Ren Δ Δ' → Vec (Atm Σ Δ' Any) n → M.Exp Σ Δ' B} {K' : Vec (Val Any) n → Result (Val B)} {γ φ} → Agree ρ γ φ
      → (∀ {Δ'} (r : Ren Δ Δ') φ' as → Agree r φ φ' → K' (map (atom φ') as) ≡ eval ds' ck φ' ⌜ k r as ⌝)
      → (evals ds ck γ Ns >>= K') ≡ eval ds' ck φ ⌜ atomizes Ns ρ k ⌝
    atomize₂-ok : ∀ {Γ Δ A₁ A₂ B} (L : Tm Σ Γ A₁) (N : Tm Σ Γ A₂) (ρ : Ren Γ Δ)
      {k : ∀ {Δ'} → Atm Σ Δ' A₁ → Atm Σ Δ' A₂ → M.Exp Σ Δ' B} {K₂ : Val A₁ → Val A₂ → Result (Val B)} {γ φ} → Agree ρ γ φ
      → (∀ {Δ'} (φ' : Env Δ') a b → K₂ (atom φ' a) (atom φ' b) ≡ eval ds' ck φ' ⌜ k a b ⌝)
      → (eval ds ck γ L >>= λ v → eval ds ck γ N >>= K₂ v) ≡ eval ds' ck φ ⌜ atomize₂ L N ρ k ⌝

    rco-ok (` x) ρ ag = cong ret (ag x)
    rco-ok (fun-ref f) ρ ag = refl
    rco-ok (pack L N) ρ ag = atomize₂-ok L N ρ {k = M.pack} {K₂ = λ v w → ret (pack v w)} ag λ φ' a b → sym (trans (atm-bind a) (atm-bind b))
    rco-ok (callc L N) ρ ag =
      trans (bind-cong (eval ds ck _ L) λ f → bind-cong (eval ds ck _ N) λ w → calls f w)
        (atomize₂-ok L N ρ {k = M.callc} {K₂ = call ds' ck} ag λ φ' a b → sym (trans (atm-bind a) (atm-bind b)))
    rco-ok (lit B c) ρ ag = refl
    rco-ok (tuple Ns) ρ ag = atomizes-ok Ns ρ {k = λ _ as → M.tuple as} {K' = λ vs → ret (tup vs)} ag λ r φ' as h → sym (atoms-bind as)
    rco-ok (get i N) ρ ag = atomize-ok N ρ {k = λ _ a → M.get i a} {K' = λ v → ret (nth i v)} ag λ r φ' a h → sym (atm-bind a)
    rco-ok (inl N) ρ ag = atomize-ok N ρ {k = λ _ a → M.inl a} {K' = λ v → ret (inl v)} ag λ r φ' a h → sym (atm-bind a)
    rco-ok (inr N) ρ ag = atomize-ok N ρ {k = λ _ a → M.inr a} {K' = λ v → ret (inr v)} ag λ r φ' a h → sym (atm-bind a)
    rco-ok (case L N₁ N₂) ρ {γ} ag =
      atomize-ok L ρ {K' = λ u → either u (λ v → eval ds ck (v ∷ γ) N₁) (λ v → eval ds ck (v ∷ γ) N₂)} ag λ r φ' a h →
      trans (either-cong (atom φ' a)
        (λ v → rco-ok N₁ _ λ { Z → refl ; (S x) → trans (ag x) (h (ρ x)) })
        (λ v → rco-ok N₂ _ λ { Z → refl ; (S x) → trans (ag x) (h (ρ x)) })) (sym (atm-bind a))
    rco-ok (prim p L N) ρ ag = atomize₂-ok L N ρ {k = M.prim p} {K₂ = K-prim p} ag λ φ' a b → sym (trans (atm-bind a) (atm-bind b))
    rco-ok (let′ N₁ N₂) ρ ag =
      bind≡ (rco-ok N₁ ρ ag) λ v → rco-ok N₂ (ext ρ) λ { Z → refl ; (S x) → ag x }
    rco-ok (inject G N) ρ ag = atomize-ok N ρ {k = λ _ a → M.inject G a} {K' = λ v → ret (dyn G v)} ag λ r φ' a h → sym (atm-bind a)
    rco-ok (project t N) ρ ag = atomize-ok N ρ {k = λ _ a → M.project t a} {K' = project? t} ag λ r φ' a h → sym (atm-bind a)

    atomize-let N ρ ag kok = bind≡ (rco-ok N ρ ag) λ v → kok S (v ∷ _) (var Z) λ x → refl

    atomize-ok (` x) ρ {K' = K'} {γ = γ} ag kok = trans (cong K' (ag x)) (kok (λ y → y) _ (var (ρ x)) λ y → refl)
    atomize-ok (fun-ref f) ρ ag kok = kok (λ y → y) _ (ref f) λ y → refl
    atomize-ok (lit B c) ρ ag kok = kok (λ y → y) _ (lit B c) λ y → refl
    atomize-ok N@(pack _ _) = atomize-let N
    atomize-ok N@(callc _ _) = atomize-let N
    atomize-ok N@(tuple _) = atomize-let N
    atomize-ok N@(get _ _) = atomize-let N
    atomize-ok N@(inl _) = atomize-let N
    atomize-ok N@(inr _) = atomize-let N
    atomize-ok N@(case _ _ _) = atomize-let N
    atomize-ok N@(prim _ _ _) = atomize-let N
    atomize-ok N@(let′ _ _) = atomize-let N
    atomize-ok N@(inject _ _) = atomize-let N
    atomize-ok N@(project _ _) = atomize-let N

    atomizes-ok [] ρ ag kok = kok (λ y → y) _ [] λ y → refl
    atomizes-ok (N ∷ Ns) ρ {k} {K'} {γ} {φ} ag kok =
      trans (trans (bind-assoc (eval ds ck γ N)) (bind-cong (eval ds ck γ N) λ v → bind-assoc (evals ds ck γ Ns)))
        (atomize-ok N ρ {K' = λ v → evals ds ck γ Ns >>= λ vs → K' (v ∷ vs)} ag λ r φ' a h →
           atomizes-ok Ns _ {K' = λ vs → K' (atom φ' a ∷ vs)} (λ x → trans (ag x) (h (ρ x))) λ r' φ'' as h' →
           trans (cong (λ u → K' (u ∷ map (atom φ'') as)) (atom-ren {φ = φ'} {φ''} a h'))
                 (kok _ φ'' (ren r' a ∷ as) λ x → trans (h x) (h' (r x))))

    atomize₂-ok L N ρ {k} {K₂} {γ} ag kok =
      atomize-ok L ρ {K' = λ v → eval ds ck γ N >>= K₂ v} ag λ r φ' a h →
        atomize-ok N _ {K' = K₂ (atom φ' a)} (λ x → trans (ag x) (h (ρ x))) λ r' φ'' b h' →
        trans (cong (λ u → K₂ u (atom φ'' b)) (atom-ren {φ = φ'} {φ''} a h')) (kok φ'' (ren r' a) b)

  calls≡ : ∀ ck f w → call ds ck f w ≡ call ds' ck f w
  calls≡ zero f w = refl
  calls≡ (suc ck) (pack (code f) e) w
    rewrite def-map ⌜_⌝ (All-map (λ D → rco D (λ x → x)) ds) f | def-map (λ D → rco D (λ x → x)) ds f =
    rco-ok ck (calls≡ ck) (ds ! f) (λ x → x) λ x → refl

rco-correct : ∀ (P : Program) → Equivalent (C.sem P) (C.sem ⌜ rco-program P ⌝ₚ)
rco-correct (program ds N) = clocked-≡ λ ck → rco-ok ds ck (calls≡ ds ck) N (λ x → x) λ x → refl
