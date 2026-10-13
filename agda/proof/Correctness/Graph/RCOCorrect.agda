{-

  Correctness of remove complex operands (Clos5 → Clos5,
  Compiler/RCO.agda): the pass preserves denotations exactly.

    rco-correct : ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ    (ρ nonempty, T and ρ consistent)
    rco-program-correct : ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ

  The laws behind it:

  - let is strict, and otherwise substitutes the meaning of the
    right-hand side for the variable (let-strict, let-β; let-β uses
    continuity, hence a nonempty environment, and binds a finite part
    of the right-hand side, hence a consistent one);
  - renaming (proof/Framework/GraphModel/RenameSem.agda), for the atoms and the operands that
    the lets put under more binders;
  - every operator of a construct whose operands rco names is strict
    (a Strict operator below), so binding an operand first by a strict
    let changes nothing (lift-≃, the let chain, stated once);

  after which each construct is one line, by the congruence of its
  operator.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.Ops
open import proof.Semantics.Graph.Prim
open import Language.Clos5
open import proof.Framework.Syntax.Rename Op sig using (rename; rename-args; ext)
open import Compiler.RCO
  using (rco; rco-args; rco-program; atom?; lift; case-on)
open import Semantics.Graph.Clos5Iswim
  using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; code; table; ⟦_⟧ₚ; init)
open import proof.Semantics.Graph.Clos5IswimContinuous
  using (Clos5-Semantics; let-β; Clos5-con; table-con)
import proof.Framework.GraphModel.RenameSem Op sig as RenameSem
open import proof.Correctness.Graph.CompilerCorrect
  using (Same; Same-trans; ≃→Same; compile-same)
open import Compiler.Pipeline using (compile; compile-mon)
open import proof.Semantics.Graph.ISWIM using () renaming (⟦_⟧ to ⟦_⟧ᵢ)
import Language.ISWIM as ISWIM
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; Nil)
open import Framework.Primitives using (base-rep)

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate; map; length)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lower) renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

module proof.Correctness.Graph.RCOCorrect where

open import proof.Framework.GraphModel.Strict

{- Laws of the semantics -------------------------------------------------------}

rename-≃ : ∀ T M r (ρ ρ' : Env Value) → (∀ x → ρ (r x) ≃ ρ' x)
  → ⟦ rename r M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ'
rename-≃ T = RenameSem.rename-≃ {{Clos5-Semantics T}}

rename-args-≃ : ∀ T {n} (Ms : Args (replicate n ■)) r (ρ ρ' : Env Value) → (∀ x → ρ (r x) ≃ ρ' x)
  → RRs (replicate n ■) (⟦ rename-args r Ms ⟧₊[ T ] ρ) (⟦ Ms ⟧₊[ T ] ρ')
rename-args-≃ T {zero} Nil r ρ ρ' rel = ptt
rename-args-≃ T {suc n} (M ,, Ms) r ρ ρ' rel =
  ⟨ up (rename-≃ T M r ρ ρ' rel) , rename-args-≃ T Ms r ρ ρ' rel ⟩

LET : AST → AST → AST
LET M N = let-op ⦅ M ,, ⟩ N ,, Nil ⦆

let-strict : ∀ T M N ρ w → w ∈ ⟦ LET M N ⟧[ T ] ρ → nonempty (⟦ M ⟧[ T ] ρ)
let-strict T M N ρ w ⟨ V , ⟨ _ , ⟨ V⊆ , V≢[] ⟩ ⟩ ⟩ = ne-mem V≢[] V⊆

{- ρ' is ρ under k more bound variables -}
Ext : ℕ → Env Value → Env Value → Set
Ext k ρ' ρ = ∀ x → ρ' (k + x) ≃ ρ x

ext-suc : ∀ {k ρ' ρ D} → Ext k ρ' (D • ρ) → Ext (suc k) ρ' ρ
ext-suc {k} {ρ'} {ρ} e x = subst (λ y → ρ' y ≃ ρ x) (+-suc k x) (e (suc x))

ext-top : ∀ {k ρ' ρ D} → Ext k ρ' (D • ρ) → ρ' k ≃ D
ext-top {k} {ρ'} {ρ} {D} e = subst (λ y → ρ' y ≃ D) (+-identityʳ k) (e 0)

{- f k, on atoms in an environment ρ under k more bound variables, means O -}
Denotes : ∀ {n} → Table → (ℕ → Args (replicate n ■) → AST) → Strict n → Env Value → Set₁
Denotes T f O ρ = ∀ k ρ' As → Ext k ρ' ρ → ⟦ f k As ⟧[ T ] ρ' ≃ op O (⟦ As ⟧₊[ T ] ρ')

{- The let chain: binding the complex operands first does not change the
   meaning of a strict operator on them -}
lift-≃ : ∀ T (TC : ∀ k → Con (T k)) {n} f (Ms : Args (replicate n ■)) (O : Strict n) ρ → nonempty-env ρ
  → Con-env ρ → Denotes T f O ρ → ⟦ lift f Ms ⟧[ T ] ρ ≃ op O (⟦ Ms ⟧₊[ T ] ρ)
lift-≃ T TC {zero} f Nil O ρ NE C den = den 0 ρ Nil (λ x → ≃-refl)
lift-≃ T TC {suc n} f (M ,, Ms) O ρ NE C den with atom? M
... | yes _ = lift-≃ T TC (λ k As → f k (rename (k +_) M ,, As)) Ms (⟦ M ⟧[ T ] ρ ▷ O) ρ NE C
  λ k ρ' As e → ≃-trans (den k ρ' _ e) (cong O ⟨ up (rename-≃ T M (k +_) ρ' ρ e) , RRs-refl _ ⟩)
... | no _ = ≃-when (let-strict T M B ρ) (λ w w∈ → proj₁ (ne-of O _ w w∈)) λ neD →
  ≃-trans (let-β T B ρ D NE neD cD)
  (≃-trans (lift-≃ T TC f' Ms' (D ▷ O) (D • ρ) (extend-nonempty-env NE neD) (Con-• cD C)
              λ k ρ' As e → ≃-trans (den (suc k) ρ' _ (ext-suc {k} {ρ'} {ρ} {D} e))
                                    (cong O ⟨ up (ext-top {k} {ρ'} {ρ} {D} e) , RRs-refl _ ⟩))
           (cong O ⟨ up ≃-refl , rename-args-≃ T Ms suc (D • ρ) ρ (λ x → ≃-refl) ⟩))
  where D = ⟦ M ⟧[ T ] ρ
        cD = Clos5-con T TC M C
        f' = λ k As → f (suc k) (` k ,, As)
        Ms' = rename-args suc Ms
        B = lift f' Ms'

prim-op : ∀ p → Strict 2
prim-op p = record { op = primD p ; cong = mono-≃ (primD-mono p)
  ; ne-of = λ { _ w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , _ ⟩ ⟩ ⟩ ⟩ → ⟨ ⟨ _ , n∈ ⟩ , ⟨ ⟨ _ , m∈ ⟩ , tt ⟩ ⟩ } }

{- The pass preserves denotations ---------------------------------------------}

{- a construct c whose operator is O: its operands, under their lets -}
rco-op : ∀ T T' (TC : ∀ k → Con (T k)) {n} (c : Args (replicate n ■) → AST) (O : Strict n)
  (Ms : Args (replicate n ■)) ρ → nonempty-env ρ → Con-env ρ → (∀ T ρ As → ⟦ c As ⟧[ T ] ρ ≃ op O (⟦ As ⟧₊[ T ] ρ))
  → RRs (replicate n ■) (⟦ rco-args Ms ⟧₊[ T ] ρ) (⟦ Ms ⟧₊[ T' ] ρ)
  → ⟦ lift (λ _ → c) (rco-args Ms) ⟧[ T ] ρ ≃ ⟦ c Ms ⟧[ T' ] ρ
rco-op T T' TC c O Ms ρ NE C den IH =
  ≃-trans (lift-≃ T TC (λ _ → c) (rco-args Ms) O ρ NE C (λ k ρ' As _ → den T ρ' As))
          (≃-trans (cong O IH) (≃-sym (den T' ρ Ms)))

{- with the same meanings in the tables T and T' -}
rco-sem : ∀ T T' → (∀ k → Con (T k)) → (∀ k → T k ≃ T' k) → ∀ M ρ → nonempty-env ρ → Con-env ρ
  → ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T' ] ρ
rco-args-sem : ∀ T T' → (∀ k → Con (T k)) → (∀ k → T k ≃ T' k) → ∀ {n} (Ms : Args (replicate n ■)) ρ
  → nonempty-env ρ → Con-env ρ → RRs (replicate n ■) (⟦ rco-args Ms ⟧₊[ T ] ρ) (⟦ Ms ⟧₊[ T' ] ρ)

rco-sem T T' TC TT (` x) ρ NE C = ≃-refl
rco-sem T T' TC TT (fun-ref k ⦅ Nil ⦆) ρ NE C = TT k
rco-sem T T' TC TT (app ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (app ⦅_⦆) app-op Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (lit B k ⦅ Nil ⦆) ρ NE C = ≃-refl
rco-sem T T' TC TT (pair-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (pair-op ⦅_⦆) pair-op′ Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (fst-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (fst-op ⦅_⦆) car-op Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (snd-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (snd-op ⦅_⦆) cdr-op Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (tuple n ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (tuple n ⦅_⦆) (tuple-op n) Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (get i ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (get i ⦅_⦆) (get-op i) Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (inl-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (inl-op ⦅_⦆) inl-op′ Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (inr-op ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (inr-op ⦅_⦆) inr-op′ Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (prim p ⦅ Ms ⦆) ρ NE C = rco-op T T' TC (prim p ⦅_⦆) (prim-op p) Ms ρ NE C (λ _ _ _ → ≃-refl) (rco-args-sem T T' TC TT Ms ρ NE C)
rco-sem T T' TC TT (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ NE C =
  ≃-trans (lift-≃ T TC (case-on (rco M) (rco N)) (rco L ,, Nil) O ρ NE C den)
          (cong O ⟨ up (rco-sem T T' TC TT L ρ NE C) , ptt ⟩)
  where
  O = case-op′ (λ X → ⟦ M ⟧[ T' ] (X • ρ)) (λ X → ⟦ N ⟧[ T' ] (X • ρ))
  branch : ∀ k ρ' → Ext k ρ' ρ → ∀ B v V → (v ∷ V) ≈ (v ∷ V)
    → ⟦ rename (ext (k +_)) (rco B) ⟧[ T ] (mem (v ∷ V) • ρ') ≃ ⟦ B ⟧[ T' ] (mem (v ∷ V) • ρ)
  branch k ρ' e B v V c =
    ≃-trans (rename-≃ T (rco B) (ext (k +_)) (mem (v ∷ V) • ρ') (mem (v ∷ V) • ρ)
               λ { zero → ≃-refl ; (suc x) → e x })
            (rco-sem T T' TC TT B (mem (v ∷ V) • ρ) (extend-nonempty-env NE ⟨ v , here refl ⟩) (Con-• (≈⇒Con c) C))
  den : Denotes T (case-on (rco M) (rco N)) O ρ
  den k ρ' (A ,, Nil) e =
    𝒞-≃ {⟦ A ⟧[ T ] ρ'} {⟦ A ⟧[ T ] ρ'} {λ X → ⟦ rename (ext (k +_)) (rco M) ⟧[ T ] (X • ρ')} {λ X → ⟦ M ⟧[ T' ] (X • ρ)}
        {λ X → ⟦ rename (ext (k +_)) (rco N) ⟧[ T ] (X • ρ')} {λ X → ⟦ N ⟧[ T' ] (X • ρ)}
        ≃-refl (branch k ρ' e M) (branch k ρ' e N)
rco-sem T T' TC TT (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ρ NE C =
  ⋆-≃ (Λ-≃ {λ X → ⟦ rco N ⟧[ T ] (X • ρ)} {λ X → ⟦ N ⟧[ T' ] (X • ρ)} λ V ne c →
         rco-sem T T' TC TT N (mem V • ρ) (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne)) (Con-• (≈⇒Con c) C))
      (rco-sem T T' TC TT M ρ NE C)

rco-args-sem T T' TC TT {zero} Nil ρ NE C = ptt
rco-args-sem T T' TC TT {suc n} (M ,, Ms) ρ NE C =
  ⟨ up (rco-sem T T' TC TT M ρ NE C) , rco-args-sem T T' TC TT Ms ρ NE C ⟩

rco-correct : ∀ T → (∀ k → Con (T k)) → ∀ M ρ → nonempty-env ρ → Con-env ρ
  → ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ
rco-correct T TC = rco-sem T T TC (λ k → ≃-refl)

{- Programs ---------------------------------------------------------------------}

code-≃ : ∀ {T T'} → (∀ k → Con (T k)) → (∀ k → T k ≃ T' k) → ∀ N → code T (rco N) ≃ code T' N
code-≃ {T} {T'} TC TT N =
  Λ-≃ λ V neV cV → Λ-≃ λ U neU cU → rco-sem T T' TC TT N _
    (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (E≢[]⇒nonempty-mem neV))
                         (E≢[]⇒nonempty-mem neU))
    (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω)))

table-rco : ∀ ds k → table (map rco ds) k ≃ table ds k
table-rco [] k = ≃-refl
table-rco (N ∷ Ns) k with k ≟ length (map rco Ns) | k ≟ length Ns
... | yes _ | yes _ = code-≃ (table-con (map rco Ns)) (table-rco Ns) N
... | no _ | no _ = table-rco Ns k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-map rco Ns)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-map rco Ns))))

rco-program-correct : ∀ P → ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ
rco-program-correct (program ds M) =
  rco-sem (table (map rco ds)) (table ds) (table-con (map rco ds)) (table-rco ds) M (λ _ → init)
    (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω)

{- The whole compiler, into monadic normal form --------------------------------

  compile-mon = rco-program ∘ compile (Compiler/Pipeline.agda): as for
  compile (CompilerCorrect.agda), the result produces the same constants
  as the ISWIM program, and produces something exactly when it does. -}

compile-mon-same : ∀ (M : ISWIM.AST) → Same (⟦ M ⟧ᵢ ρ₀) ⟦ compile-mon M ⟧ₚ
compile-mon-same M =
  Same-trans (compile-same M) (≃→Same (≃-sym (rco-program-correct (compile M))))

compile-mon-correct-const : ∀ (M : ISWIM.AST) → ∀ {B} (c : base-rep B)
  → (const c ∈ ⟦ M ⟧ᵢ ρ₀ → const c ∈ ⟦ compile-mon M ⟧ₚ)
  × (const c ∈ ⟦ compile-mon M ⟧ₚ → const c ∈ ⟦ M ⟧ᵢ ρ₀)
compile-mon-correct-const M = proj₁ (compile-mon-same M)

compile-mon-correct-nonempty : ∀ (M : ISWIM.AST)
  → (nonempty (⟦ M ⟧ᵢ ρ₀) → nonempty ⟦ compile-mon M ⟧ₚ)
  × (nonempty ⟦ compile-mon M ⟧ₚ → nonempty (⟦ M ⟧ᵢ ρ₀))
compile-mon-correct-nonempty M = proj₂ (compile-mon-same M)
