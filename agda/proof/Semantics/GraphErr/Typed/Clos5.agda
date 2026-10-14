{-

  Lemmas about the semantics of Clos5ᵀ in the graph model with errors
  (Semantics/GraphErr/Typed/Clos5.agda):

  * wk-≃: a term over a table, weakened to a bigger one, means the same
    under tables that agree on its references and environments that are
    equal (a congruence, with r the identity);
  * ok: its denotations are monotone, continuous and consistent (Ok),
    under a consistent table, as for Clos4ᵀ;
  * tbl-map: the tables of two lists of definitions agree when their
    codes do under agreeing tables; tbl-val, tbl-con: their entries
    are sets of values, consistent when the codes are.

-}

module proof.Semantics.GraphErr.Typed.Clos5 where

open import Semantics.GraphErr.Typed.Clos5 public
open import proof.Framework.GraphModel.TypedOk using (Ok; Oks; ok-op; var-ok; const-ok; let-ok; split; ok-vec) public
open import proof.Framework.GraphModel.TypedBinders using (code-ok; callc-good; callcᵈ)

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.Continuity using (ℬ-good)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env using (Env; _~ₑ[_]_; •-~)
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Semantics.GraphErr.Typed.Clos2
  using (get-good; case-good; prim-good; project-good; getᵗ-≃; caseᵗ-≃; primᵗ-≃; projectᵗ-≃; ⌊⌋-≃)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.Clos5

open import Data.Fin using (zero; suc)
open import Data.List using (List; _∷_; length; replicate)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; _≟_)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)

callc-≃ : ∀ {L L' M M'} → L ≃ L' → M ≃ M' → binds 2 ⟨ L , ⟨ M , ptt ⟩ ⟩ callcᵈ ≃ binds 2 ⟨ L' , ⟨ M' , ptt ⟩ ⟩ callcᵈ
callc-≃ L≃ M≃ = mono-≃ (mono (binds-good {⊤} 2 callc-good)) ⟨ lift L≃ , ⟨ lift M≃ , ptt ⟩ ⟩

{- Weakening -------------------------------------------------------------------}

module _ {Σ Σ'} (r : ∀ {n} → Σ ∋ n → Σ' ∋ n) {T T' : Table} (TT : ∀ {n} (f : Σ ∋ n) → T (lvl (r f)) ≃ T' (lvl f)) where

  wk-≃ : ∀ {Γ A} (M : Tm Σ Γ A) {ρ ρ'} → ρ ~ₑ[ _≃_ ] ρ' → ⟦ wk r M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T' ] ρ'
  wks-≃ : ∀ {Γ n} (Ms : Vec (Tm Σ Γ Any) n) {ρ ρ'} → ρ ~ₑ[ _≃_ ] ρ'
    → ∀ i → nthD (⟦ wks r Ms ⟧s[ T ] ρ) i ≃ nthD (⟦ Ms ⟧s[ T' ] ρ') i

  wk-≃ (` x) ρ~ = ρ~ (idx x)
  wk-≃ (fun-ref f) ρ~ = TT f
  wk-≃ (pack L M) ρ~ = pairᵐ-≃ (wk-≃ L ρ~) (wk-≃ M ρ~)
  wk-≃ (callc L M) ρ~ = callc-≃ (wk-≃ L ρ~) (wk-≃ M ρ~)
  wk-≃ (lit B c) ρ~ = ≃-refl
  wk-≃ (tuple {n = n} Ms) ρ~ = 𝒯ᵐ-≃ n (wks-≃ Ms ρ~)
  wk-≃ (get i M) ρ~ = getᵗ-≃ i (wk-≃ M ρ~)
  wk-≃ (inl M) ρ~ = inlᵐ-≃ (wk-≃ M ρ~)
  wk-≃ (inr M) ρ~ = inrᵐ-≃ (wk-≃ M ρ~)
  wk-≃ (case L M N) {ρ} {ρ'} ρ~ = caseᵗ-≃ {F = λ X → ⟦ wk r M ⟧[ T ] (X • ρ)} {λ X → ⟦ M ⟧[ T' ] (X • ρ')} {λ X → ⟦ wk r N ⟧[ T ] (X • ρ)} {λ X → ⟦ N ⟧[ T' ] (X • ρ')}
    (wk-≃ L ρ~) (λ _ _ _ _ → wk-≃ M (•-~ _≃_ ρ~ ≃-refl)) (λ _ _ _ _ → wk-≃ N (•-~ _≃_ ρ~ ≃-refl))
  wk-≃ (prim p L M) ρ~ = primᵗ-≃ p (wk-≃ L ρ~) (wk-≃ M ρ~)
  wk-≃ (let′ M N) {ρ} {ρ'} ρ~ = ≫=-≃ {F = λ X → ⟦ wk r N ⟧[ T ] (X • ρ)} {λ X → ⟦ N ⟧[ T' ] (X • ρ')} (wk-≃ M ρ~) λ _ _ → wk-≃ N (•-~ _≃_ ρ~ (⌊⌋-≃ (wk-≃ M ρ~)))
  wk-≃ (inject G M) ρ~ = wk-≃ M ρ~
  wk-≃ (project t M) ρ~ = projectᵗ-≃ kind₄ t (wk-≃ M ρ~)

  wks-≃ (M ∷ Ms) ρ~ zero = wk-≃ M ρ~
  wks-≃ (M ∷ Ms) ρ~ (suc i) = wks-≃ Ms ρ~ i

wk-id : ∀ {Σ Γ A} (M : Tm Σ Γ A) → wk (λ f → f) M ≡ M
wks-id : ∀ {Σ Γ n} (Ms : Vec (Tm Σ Γ Any) n) → wks (λ f → f) Ms ≡ Ms
wk-id (` x) = refl
wk-id (fun-ref f) = refl
wk-id (pack L M) = cong₂ pack (wk-id L) (wk-id M)
wk-id (callc L M) = cong₂ callc (wk-id L) (wk-id M)
wk-id (lit B c) = refl
wk-id (tuple Ms) = cong tuple (wks-id Ms)
wk-id (get i M) = cong (get i) (wk-id M)
wk-id (inl M) = cong inl (wk-id M)
wk-id (inr M) = cong inr (wk-id M)
wk-id (case L M N) = trans (cong₂ (λ L M → case L M (wk (λ f → f) N)) (wk-id L) (wk-id M)) (cong (case L M) (wk-id N))
wk-id (prim p L M) = cong₂ (prim p) (wk-id L) (wk-id M)
wk-id (let′ M N) = cong₂ let′ (wk-id M) (wk-id N)
wk-id (inject G M) = cong (inject G) (wk-id M)
wk-id (project t M) = cong (project t) (wk-id M)
wks-id [] = refl
wks-id (M ∷ Ms) = cong₂ _∷_ (wk-id M) (wks-id Ms)

{- the same term under agreeing tables -}
tm-≃ : ∀ {Σ Γ A} {T T' : Table} → (∀ k → T k ≃ T' k) → (M : Tm Σ Γ A) {ρ ρ' : Env Value} → ρ ~ₑ[ _≃_ ] ρ'
  → ⟦ M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T' ] ρ'
tm-≃ {T = T} TT M {ρ} ρ~ = ≃-trans (≃-reflexive (cong (λ N → ⟦ N ⟧[ T ] ρ) (sym (wk-id M)))) (wk-≃ (λ f → f) (λ f → TT (lvl f)) M ρ~)

{- Monotone, continuous and consistent -----------------------------------------}

module _ {T : Table} (TC : ∀ k → Con (T k)) where

  ok : ∀ {Σ Γ A} (M : Tm Σ Γ A) → Ok ⟦ M ⟧[ T ]
  oks : ∀ {Σ Γ n} (Ms : Vec (Tm Σ Γ Any) n) → Oks (replicate n ■) (split n ⟦ Ms ⟧s[ T ])

  ok (` x) = var-ok (idx x)
  ok (fun-ref f) = const-ok (TC (lvl f))
  ok (pack L M) = ok-op pairᵐ-good ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
  ok (callc L M) = ok-op (binds-good 2 callc-good) ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
  ok (lit B c) = ok-op (ℬ-good B c) ptt
  ok (tuple Ms) = ok-vec (𝒯ᵐ-good _) (oks Ms)
  ok (get i M) = ok-op (get-good i) ⟨ ok M , ptt ⟩
  ok (inl M) = ok-op inlᵐ-good ⟨ ok M , ptt ⟩
  ok (inr M) = ok-op inrᵐ-good ⟨ ok M , ptt ⟩
  ok (case L M N) = ok-op case-good ⟨ ok L , ⟨ ok M , ⟨ ok N , ptt ⟩ ⟩ ⟩
  ok (prim p L M) = ok-op (prim-good p) ⟨ ok L , ⟨ ok M , ptt ⟩ ⟩
  ok (let′ M N) = let-ok (ok M) (ok N)
  ok (inject G M) = ok M
  ok (project t M) = ok-op (project-good kind₄ t) ⟨ ok M , ptt ⟩

  oks [] = ptt
  oks (M ∷ Ms) = ⟨ ok M , oks Ms ⟩

  con : ∀ {Σ Γ A} (M : Tm Σ Γ A) {ρ} → Con-env ρ → Con (⟦ M ⟧[ T ] ρ)
  con M c = proj₂ (proj₂ (ok M)) c

  code₅-con : ∀ {Σ n} (N : Code Σ n) → Con (code₅ T N)
  code₅-con N = ΛΛᵐ-con λ X X' Y Y' X~ Y~ → proj₂ (proj₂ (ok N)) (•-~ (Every _~_) (•-~ (Every _~_) (λ _ → Con-⌈⌉ ω) X~) Y~)

{- Tables ------------------------------------------------------------------------}

{- under an invariant I of the source tables (iv) -}
tbl-map : ∀ {P P' Q : ℕ → Set} {c : Table → ∀ {n} → P n → 𝒫 Value} {c' : Table → ∀ {n} → P' n → 𝒫 Value}
  (I : Table → Set) (f : ∀ {n} → Q n → P n) (g : ∀ {n} → Q n → P' n) → (∀ {ns} (ds : All Q ns) → I (tbl c' (All-map g ds)))
  → (∀ {T T'} → (∀ k → T k ≃ T' k) → I T' → ∀ {n} (d : Q n) → c T (f d) ≃ c' T' (g d))
  → ∀ {ns} (ds : All Q ns) k → tbl c (All-map f ds) k ≃ tbl c' (All-map g ds) k
tbl-map I f g iv h [] k = ≃-refl
tbl-map I f g iv h {_ ∷ ns} (d ∷ ds) k with k ≟ length ns
... | yes _ = h (tbl-map I f g iv h ds) (iv ds) d
... | no _ = tbl-map I f g iv h ds k

map-id : ∀ {Q : ℕ → Set} {ns} (ds : All Q ns) → All-map (λ x → x) ds ≡ ds
map-id [] = refl
map-id (d ∷ ds) = cong (d ∷_) (map-id ds)

{- the entries of a table of code are sets of values -}
tbl-val : ∀ {P : ℕ → Set} {c : Table → ∀ {n} → P n → 𝒫 Value} → (∀ {T n} (d : P n) → Val (c T d))
  → ∀ {ns} (ds : All P ns) k → Val (tbl c ds k)
tbl-val h [] k = ΛΛᵐ-val
tbl-val h {_ ∷ ns} (d ∷ ds) k with k ≟ length ns
... | yes _ = h d
... | no _ = tbl-val h ds k

{- the tables of programs are consistent, when their codes are -}
tbl-con : ∀ {P : ℕ → Set} {c : Table → ∀ {n} → P n → 𝒫 Value} → (∀ {T} → (∀ k → Con (T k)) → ∀ {n} (d : P n) → Con (c T d))
  → ∀ {ns} (ds : All P ns) k → Con (tbl c ds k)
tbl-con h [] k = errcode-con
tbl-con h {_ ∷ ns} (d ∷ ds) k with k ≟ length ns
... | yes _ = h (tbl-con h ds) d
... | no _ = tbl-con h ds k
