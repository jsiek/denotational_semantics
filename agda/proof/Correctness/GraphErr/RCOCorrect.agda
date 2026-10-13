{-

  Correctness of remove complex operands (Clos5 → Clos5,
  Compiler/RCO.agda) in the graph model with errors
  (Semantics/GraphErr/Clos5.agda): the pass preserves the meaning of a
  well-scoped program exactly.

    rco-correct : Scoped P → ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ

  As in the graph model (proof/Correctness/Graph/RCOCorrect.agda), each
  complex operand is bound by a let, left to right, and every operator
  whose operands rco names is strict in them. With errors, strict means
  left to right (ErrsOp): an element of the operator comes from an error
  in its operands, in order (errs), or needs all of them to have values;
  and an error in the operands, in order, is one of the operator. So
  binding the first operand by a let changes nothing: if it errs, both
  err, and nothing else (by consistency); if it diverges, both are empty;
  otherwise it is a set of values and let is β.

  The atoms that rco leaves in place are evaluated after the operands
  bound before them, so they must not err: they are variables in scope,
  which the environment binds to values (Good), literals, and references
  to definitions, which are code. That is why the theorem is for
  well-scoped programs (Scoped, which the compiler's output is): in ρ₀
  a variable out of scope is an error, and rco may move it after an
  operand that diverges.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.ErrorOps
open import proof.Semantics.GraphErr.Prim
open import Language.Clos5
open import Language.Mon using (Atom; var; lit; ref)
open import proof.Framework.Syntax.Rename Op sig using (rename; rename-args; ext)
open import Compiler.RCO
  using (rco; rco-args; rco-program; atom?; lift; case-on; lets; atomize; binds; atoms; Bound; bound)
open import proof.Semantics.GraphErr.Clos5
  using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; code; table; ⟦_⟧ₚ; init; Clos5ᵉ-Semantics; Clos5ᵉ-con; table-con;
         body-mono; body-continuous)
import proof.Framework.GraphModel.RenameSem Op sig as RenameSem
open import Framework.Syntax.Scope Op sig using (WS; WS-args)
open import Compiler.PipelineScope using (Scoped)
open import proof.Compiler.PipelineScope using (compile-scoped)
open import Compiler.EncloseScope using (Closed)
open import Compiler.Pipeline using (compile; compile-mon)
import Language.ISWIM as ISWIM
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env; •-~)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; Nil)

open import Data.Nat using (ℕ; zero; suc; _+_; _≟_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate; map; length)
open import Data.List.Properties using (length-map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lower) renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Relation.Nullary using (Dec; yes; no)

module proof.Correctness.GraphErr.RCOCorrect where

open import proof.Framework.GraphModel.ErrorStrict

{- the primitives, as a strict operator -}
prim-op : ∀ p → ErrsOp 2
prim-op p = record { op = primᵉ p ; mono = λ {Ds} {Es} s → lower (primᵉ-mono p Ds Es s) ; split = S ; err = λ Ds e → inj₂ ⟨ refl , inj₁ e ⟩ }
  where
  S : ∀ Ds w → w ∈ primᵉ p Ds → (w ≡ ω × errs 2 Ds) ⊎ vals 2 Ds
  S ⟨ D , ⟨ E , _ ⟩ ⟩ w (inj₁ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , _ ⟩ ⟩ ⟩ ⟩) =
    inj₂ (vals-cons ⟨ _ , ⟨ n∈ , (λ ()) ⟩ ⟩ (vals-cons ⟨ _ , ⟨ m∈ , (λ ()) ⟩ ⟩ (λ ())))
  S Ds w (inj₂ ⟨ refl , inj₁ e ⟩) = inj₁ ⟨ refl , e ⟩
  S ⟨ D , ⟨ E , _ ⟩ ⟩ w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ ⟨ d , ⟨ d∈ , ⟨ d≢ , _ ⟩ ⟩ ⟩ , vE ⟩) ⟩) =
    inj₂ (vals-cons ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ (vals-cons vE (λ ())))
  S ⟨ D , ⟨ E , _ ⟩ ⟩ w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ vD , ⟨ d , ⟨ d∈ , ⟨ d≢ , _ ⟩ ⟩ ⟩ ⟩) ⟩) =
    inj₂ (vals-cons vD (vals-cons ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ (λ ())))

{- Laws of the semantics of Clos5 ----------------------------------}

rename-≃ : ∀ T M r (ρ ρ' : Env Value) → (∀ x → ρ (r x) ≃ ρ' x)
  → ⟦ rename r M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T ] ρ'
rename-≃ T = RenameSem.rename-≃ {{Clos5ᵉ-Semantics T}}

rename-args-≃ : ∀ T {n} (Ms : Args (replicate n ■)) r (ρ ρ' : Env Value) → (∀ x → ρ (r x) ≃ ρ' x)
  → RRs (replicate n ■) (⟦ rename-args r Ms ⟧₊[ T ] ρ) (⟦ Ms ⟧₊[ T ] ρ')
rename-args-≃ T {zero} Nil r ρ ρ' rel = ptt
rename-args-≃ T {suc n} (M ,, Ms) r ρ ρ' rel =
  ⟨ up (rename-≃ T M r ρ ρ' rel) , rename-args-≃ T Ms r ρ ρ' rel ⟩

{- ρ' is ρ under k more bound variables -}
Ext : ℕ → Env Value → Env Value → Set
Ext k ρ' ρ = ∀ x → ρ' (k + x) ≃ ρ x

ext-suc : ∀ {k ρ' ρ D} → Ext k ρ' (D • ρ) → Ext (suc k) ρ' ρ
ext-suc {k} {ρ'} {ρ} e x = subst (λ y → ρ' y ≃ ρ x) (+-suc k x) (e (suc x))

ext-top : ∀ {k ρ' ρ D} → Ext k ρ' (D • ρ) → ρ' k ≃ D
ext-top {k} {ρ'} {ρ} {D} e = subst (λ y → ρ' y ≃ D) (+-identityʳ k) (e 0)

{- f k, on atoms in an environment ρ' under k more bound variables than
   ρ, means O -}
Denotes : ∀ {n} → Table → (ℕ → Args (replicate n ■) → AST) → ErrsOp n → Env Value → Set₁
Denotes T f O ρ = ∀ k ρ' As → Ext k ρ' ρ → ⟦ f k As ⟧[ T ] ρ' ≃ op O (⟦ As ⟧₊[ T ] ρ')

{- the atoms among the operands mean sets of values -}
AtomsOK : ∀ {n} → Table → Env Value → Args (replicate n ■) → Set
AtomsOK {zero} T ρ Nil = ⊤
AtomsOK {suc n} T ρ (M ,, Ms) = (Atom M → Vals (⟦ M ⟧[ T ] ρ)) × AtomsOK T ρ Ms

atom-unrename : ∀ r M → Atom (rename r M) → Atom M
atom-unrename r (` x) _ = var x
atom-unrename r (fun-ref k ⦅ Nil ⦆) _ = ref k
atom-unrename r (lit B k ⦅ Nil ⦆) _ = lit B k
atom-unrename r (app ⦅ _ ⦆) ()
atom-unrename r (pair-op ⦅ _ ⦆) ()
atom-unrename r (fst-op ⦅ _ ⦆) ()
atom-unrename r (snd-op ⦅ _ ⦆) ()
atom-unrename r (tuple n ⦅ _ ⦆) ()
atom-unrename r (get i ⦅ _ ⦆) ()
atom-unrename r (inl-op ⦅ _ ⦆) ()
atom-unrename r (inr-op ⦅ _ ⦆) ()
atom-unrename r (case-op ⦅ _ ⦆) ()
atom-unrename r (prim p ⦅ _ ⦆) ()
atom-unrename r (let-op ⦅ _ ⦆) ()

AtomsOK-rename : ∀ T X ρ {n} (Ms : Args (replicate n ■)) → AtomsOK T ρ Ms → AtomsOK T (X • ρ) (rename-args suc Ms)
AtomsOK-rename T X ρ {zero} Nil _ = tt
AtomsOK-rename T X ρ {suc n} (M ,, Ms) ⟨ h , hs ⟩ =
  ⟨ (λ a → Vals-≃ (≃-sym (rename-≃ T M suc (X • ρ) ρ (λ x → ≃-refl))) (h (atom-unrename suc M a)))
  , AtomsOK-rename T X ρ Ms hs ⟩

{- The let chain: binding the complex operands first, left to right,
   does not change the meaning of an operator that is strict in them -}
lift-≃ : ∀ T (TC : ∀ k → Con (T k)) {n} f (Ms : Args (replicate n ■)) (O : ErrsOp n) ρ → nonempty-env ρ
  → Con-env ρ → AtomsOK T ρ Ms → Denotes T f O ρ → ⟦ lift f Ms ⟧[ T ] ρ ≃ op O (⟦ Ms ⟧₊[ T ] ρ)
lift-≃ T TC {zero} f Nil O ρ NE C _ den = den 0 ρ Nil (λ x → ≃-refl)
lift-≃ T TC {suc n} f (M ,, Ms) O ρ NE C ⟨ aM , aMs ⟩ den with atom? M
... | yes a = lift-≃ T TC (λ k As → f k (rename (k +_) M ,, As)) Ms (⟨ ⟦ M ⟧[ T ] ρ , aM a ⟩ ▷ O) ρ NE C aMs
  λ k ρ' As e → ≃-trans (den k ρ' _ e) (cong-op O ⟨ up (rename-≃ T M (k +_) ρ' ρ e) , RRs-refl _ ⟩)
... | no _ = ⟨ G , H ⟩
  where
  D = ⟦ M ⟧[ T ] ρ
  cD = Clos5ᵉ-con T TC M C
  Ds = ⟦ Ms ⟧₊[ T ] ρ
  f' = λ k As → f (suc k) (` k ,, As)
  Ms' = rename-args suc Ms
  B = lift f' Ms'

  {- the rest, with a set of values X for the first operand -}
  rest : ∀ X (vX : Vals X) → Con X → ⟦ B ⟧[ T ] (X • ρ) ≃ op O ⟨ X , Ds ⟩
  rest X vX cX =
    ≃-trans (lift-≃ T TC f' Ms' (⟨ X , vX ⟩ ▷ O) (X • ρ)
               (extend-nonempty-env NE ⟨ proj₁ (proj₁ vX) , proj₁ (proj₂ (proj₁ vX)) ⟩) (Con-• cX C)
               (AtomsOK-rename T X ρ Ms aMs)
               λ k ρ' As e → ≃-trans (den (suc k) ρ' _ (ext-suc {k} {ρ'} {ρ} {X} e))
                                     (cong-op O ⟨ up (ext-top {k} {ρ'} {ρ} {X} e) , RRs-refl _ ⟩))
            (cong-op O ⟨ up ≃-refl , rename-args-≃ T Ms suc (X • ρ) ρ (λ x → ≃-refl) ⟩)

  G : letᵉ ⟨ D , ⟨ (λ X → ⟦ B ⟧[ T ] (X • ρ)) , ptt ⟩ ⟩ ⊆ op O ⟨ D , Ds ⟩
  G w (inj₁ ⟨ V , ⟨ ⟨ w∈ , ⟨ ne , ⟨ c , nV ⟩ ⟩ ⟩ , ⟨ V⊆ , _ ⟩ ⟩ ⟩) =
    mono O ⟨ up V⊆ , ⊆-refl* Ds ⟩ w (proj₁ (rest (mem V) (NoErr-Vals V ne nV) (≈⇒Con c)) w w∈)
  G w (inj₂ ⟨ refl , inj₁ () ⟩)
  G w (inj₂ ⟨ refl , inj₂ (inj₁ ⟨ d , ⟨ d∈ , ⟨ _ , nf ⟩ ⟩ ⟩) ⟩) = ⊥-elim (nf (Λᵉ-fun d d∈))
  G w (inj₂ ⟨ refl , inj₂ (inj₂ ⟨ _ , ω∈ ⟩) ⟩) = err O ⟨ D , Ds ⟩ (inj₁ ω∈)

  {- when D has a value, it holds no ω, and the let is β -}
  viaβ : val∈ D → op O ⟨ D , Ds ⟩ ⊆ letᵉ ⟨ D , ⟨ (λ X → ⟦ B ⟧[ T ] (X • ρ)) , ptt ⟩ ⟩
  viaβ vD w w∈ =
    proj₂ (letᵉ-β (body-mono T B ρ) (body-continuous T B ρ NE D ⟨ proj₁ vD , proj₁ (proj₂ vD) ⟩) cD clD) w
      (proj₂ (rest D ⟨ vD , clD ⟩ cD) w w∈)
    where clD = con-val-clean cD vD

  H : op O ⟨ D , Ds ⟩ ⊆ letᵉ ⟨ D , ⟨ (λ X → ⟦ B ⟧[ T ] (X • ρ)) , ptt ⟩ ⟩
  H w w∈ with split O _ w w∈
  ... | inj₁ ⟨ refl , inj₁ ω∈ ⟩ = inj₂ ⟨ refl , inj₂ (inj₂ ⟨ ⟨ ν , ⟨ tt , tt ⟩ ⟩ , ω∈ ⟩) ⟩
  ... | inj₁ ⟨ refl , inj₂ ⟨ vD , _ ⟩ ⟩ = viaβ vD w w∈
  ... | inj₂ vs = viaβ (vals-head vs) w w∈

{- Atoms ---------------------------------------------------------------------------}

{- the variables below k mean sets of values -}
Good : ℕ → Env Value → Set
Good k ρ = ∀ x → x < k → Vals (ρ x)

Good-ext : ∀ {k ρ X} → Vals X → Good k ρ → Good (suc k) (X • ρ)
Good-ext vX G zero _ = vX
Good-ext vX G (suc x) (s≤s x<k) = G x x<k

atom-val : ∀ T ρ k A → (∀ j → Vals (T j)) → Good k ρ → Atom A → WS k A → Vals (⟦ A ⟧[ T ] ρ)
atom-val T ρ k .(` x) TV G (var x) ws = G x ws
atom-val T ρ k .(lit B c ⦅ nil ⦆) TV G (lit B c) ws = ⟨ ⟨ const c , ⟨ ⟨ refl , refl ⟩ , (λ ()) ⟩ ⟩ , ℬ-clean ⟩
atom-val T ρ k .(fun-ref j ⦅ nil ⦆) TV G (ref j) ws = TV j

let-noatom : ∀ {M N} → Atom (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) → ⊥
let-noatom ()

no-atom-lets : ∀ {n} (f : ℕ → Args (replicate n ■) → AST) (B : Bound n) → (∀ k As → Atom (f k As) → ⊥)
  → Atom (lets (binds B) (f (length (binds B)) (atoms B))) → ⊥
no-atom-lets f (bound [] As) h a = h 0 As a
no-atom-lets f (bound (M ∷ bs) As) h a = let-noatom a

case-noatom : ∀ M N k (As : Args (■ ∷ [])) → Atom (case-on M N k As) → ⊥
case-noatom M N k (A ,, Nil) ()

{- an operand that rco leaves an atom was that atom -}
rco-atom : ∀ M → Atom (rco M) → rco M ≡ M
rco-atom (` x) _ = refl
rco-atom (fun-ref k ⦅ Nil ⦆) _ = refl
rco-atom (lit B k ⦅ Nil ⦆) _ = refl
rco-atom (app ⦅ Ms ⦆) a = ⊥-elim (no-atom-lets {3} (λ _ → app ⦅_⦆) (atomize (rco-args Ms)) (λ _ _ ()) a)
rco-atom (pair-op ⦅ Ms ⦆) a = ⊥-elim (no-atom-lets {2} (λ _ → pair-op ⦅_⦆) (atomize (rco-args Ms)) (λ _ _ ()) a)
rco-atom (fst-op ⦅ Ms ⦆) a = ⊥-elim (no-atom-lets {1} (λ _ → fst-op ⦅_⦆) (atomize (rco-args Ms)) (λ _ _ ()) a)
rco-atom (snd-op ⦅ Ms ⦆) a = ⊥-elim (no-atom-lets {1} (λ _ → snd-op ⦅_⦆) (atomize (rco-args Ms)) (λ _ _ ()) a)
rco-atom (tuple n ⦅ Ms ⦆) a = ⊥-elim (no-atom-lets {n} (λ _ → tuple n ⦅_⦆) (atomize (rco-args Ms)) (λ _ _ ()) a)
rco-atom (get i ⦅ Ms ⦆) a = ⊥-elim (no-atom-lets {1} (λ _ → get i ⦅_⦆) (atomize (rco-args Ms)) (λ _ _ ()) a)
rco-atom (inl-op ⦅ Ms ⦆) a = ⊥-elim (no-atom-lets {1} (λ _ → inl-op ⦅_⦆) (atomize (rco-args Ms)) (λ _ _ ()) a)
rco-atom (inr-op ⦅ Ms ⦆) a = ⊥-elim (no-atom-lets {1} (λ _ → inr-op ⦅_⦆) (atomize (rco-args Ms)) (λ _ _ ()) a)
rco-atom (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) a =
  ⊥-elim (no-atom-lets (case-on (rco M) (rco N)) (atomize (rco L ,, Nil)) (case-noatom (rco M) (rco N)) a)
rco-atom (prim p ⦅ Ms ⦆) a = ⊥-elim (no-atom-lets {2} (λ _ → prim p ⦅_⦆) (atomize (rco-args Ms)) (λ _ _ ()) a)
rco-atom (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) ()

rco-atomsOK : ∀ T ρ k → (∀ j → Vals (T j)) → Good k ρ → ∀ {n} (Ms : Args (replicate n ■)) → WS-args k Ms
  → AtomsOK T ρ (rco-args Ms)
rco-atomsOK T ρ k TV G {zero} Nil _ = tt
rco-atomsOK T ρ k TV G {suc n} (M ,, Ms) ⟨ wsM , wsMs ⟩ =
  ⟨ (λ a → subst (λ X → Vals (⟦ X ⟧[ T ] ρ)) (sym (rco-atom M a))
             (atom-val T ρ k M TV G (subst Atom (rco-atom M a) a) wsM))
  , rco-atomsOK T ρ k TV G Ms wsMs ⟩

{- The pass preserves denotations ---------------------------------------------}

module _ (T T' : Table) (TC : ∀ k → Con (T k)) (TT : ∀ k → T k ≃ T' k) (TV : ∀ k → Vals (T k)) where

  rco-sem : ∀ M k ρ → WS k M → nonempty-env ρ → Con-env ρ → Good k ρ
    → ⟦ rco M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T' ] ρ
  rco-args-sem : ∀ {n} (Ms : Args (replicate n ■)) k ρ → WS-args k Ms → nonempty-env ρ → Con-env ρ → Good k ρ
    → RRs (replicate n ■) (⟦ rco-args Ms ⟧₊[ T ] ρ) (⟦ Ms ⟧₊[ T' ] ρ)

  {- a construct c whose operator is O, on operands under their lets -}
  rco-op : ∀ {n} (c : Args (replicate n ■) → AST) (O : ErrsOp n) (Ms : Args (replicate n ■)) k ρ
    → WS-args k Ms → nonempty-env ρ → Con-env ρ → Good k ρ
    → (∀ T ρ As → ⟦ c As ⟧[ T ] ρ ≃ op O (⟦ As ⟧₊[ T ] ρ))
    → ⟦ lift (λ _ → c) (rco-args Ms) ⟧[ T ] ρ ≃ ⟦ c Ms ⟧[ T' ] ρ
  rco-op c O Ms k ρ ws NE C G den =
    ≃-trans (lift-≃ T TC (λ _ → c) (rco-args Ms) O ρ NE C (rco-atomsOK T ρ k TV G Ms ws) (λ j ρ' As _ → den T ρ' As))
            (≃-trans (cong-op O (rco-args-sem Ms k ρ ws NE C G)) (≃-sym (den T' ρ Ms)))

  rco-sem (` x) k ρ ws NE C G = ≃-refl
  rco-sem (fun-ref j ⦅ Nil ⦆) k ρ ws NE C G = TT j
  rco-sem (app ⦅ Ms ⦆) k ρ ws NE C G = rco-op (app ⦅_⦆) call-op Ms k ρ ws NE C G (λ _ _ _ → ≃-refl)
  rco-sem (lit B c ⦅ Nil ⦆) k ρ ws NE C G = ≃-refl
  rco-sem (pair-op ⦅ Ms ⦆) k ρ ws NE C G = rco-op (pair-op ⦅_⦆) pair-op′ Ms k ρ ws NE C G (λ _ _ _ → ≃-refl)
  rco-sem (fst-op ⦅ Ms ⦆) k ρ ws NE C G = rco-op (fst-op ⦅_⦆) car-op Ms k ρ ws NE C G (λ _ _ _ → ≃-refl)
  rco-sem (snd-op ⦅ Ms ⦆) k ρ ws NE C G = rco-op (snd-op ⦅_⦆) cdr-op Ms k ρ ws NE C G (λ _ _ _ → ≃-refl)
  rco-sem (tuple n ⦅ Ms ⦆) k ρ ws NE C G = rco-op (tuple n ⦅_⦆) (tuple-op n) Ms k ρ ws NE C G (λ _ _ _ → ≃-refl)
  rco-sem (get i ⦅ Ms ⦆) k ρ ws NE C G = rco-op (get i ⦅_⦆) (get-op i) Ms k ρ ws NE C G (λ _ _ _ → ≃-refl)
  rco-sem (inl-op ⦅ Ms ⦆) k ρ ws NE C G = rco-op (inl-op ⦅_⦆) inl-op′ Ms k ρ ws NE C G (λ _ _ _ → ≃-refl)
  rco-sem (inr-op ⦅ Ms ⦆) k ρ ws NE C G = rco-op (inr-op ⦅_⦆) inr-op′ Ms k ρ ws NE C G (λ _ _ _ → ≃-refl)
  rco-sem (prim p ⦅ Ms ⦆) k ρ ws NE C G = rco-op (prim p ⦅_⦆) (prim-op p) Ms k ρ ws NE C G (λ _ _ _ → ≃-refl)
  rco-sem (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) k ρ ⟨ wsL , ⟨ wsM , ⟨ wsN , _ ⟩ ⟩ ⟩ NE C G =
    ≃-trans (lift-≃ T TC (case-on (rco M) (rco N)) (rco L ,, Nil) O ρ NE C
               (rco-atomsOK T ρ k TV G (L ,, Nil) ⟨ wsL , tt ⟩) den)
            (cong-op O ⟨ up (rco-sem L k ρ wsL NE C G) , ptt ⟩)
    where
    O = case-op′ (λ X → ⟦ M ⟧[ T' ] (X • ρ)) (λ X → ⟦ N ⟧[ T' ] (X • ρ))
    branch : ∀ j ρ' → Ext j ρ' ρ → ∀ B → WS (suc k) B → ∀ v V → (v ∷ V) ≈ (v ∷ V) → NoErr (v ∷ V)
      → ⟦ rename (ext (j +_)) (rco B) ⟧[ T ] (mem (v ∷ V) • ρ') ≃ ⟦ B ⟧[ T' ] (mem (v ∷ V) • ρ)
    branch j ρ' e B wsB v V c n =
      ≃-trans (rename-≃ T (rco B) (ext (j +_)) (mem (v ∷ V) • ρ') (mem (v ∷ V) • ρ)
                 λ { zero → ≃-refl ; (suc x) → e x })
              (rco-sem B (suc k) (mem (v ∷ V) • ρ) wsB (extend-nonempty-env NE ⟨ v , here refl ⟩)
                 (Con-• (≈⇒Con c) C) (Good-ext (NoErr-Vals (v ∷ V) (λ ()) n) G))
    den : Denotes T (case-on (rco M) (rco N)) O ρ
    den j ρ' (A ,, Nil) e =
      𝒞ᵉ-≃ {⟦ A ⟧[ T ] ρ'} {⟦ A ⟧[ T ] ρ'} {λ X → ⟦ rename (ext (j +_)) (rco M) ⟧[ T ] (X • ρ')} {λ X → ⟦ M ⟧[ T' ] (X • ρ)}
           {λ X → ⟦ rename (ext (j +_)) (rco N) ⟧[ T ] (X • ρ')} {λ X → ⟦ N ⟧[ T' ] (X • ρ)}
           ≃-refl (branch j ρ' e M wsM) (branch j ρ' e N wsN)
  rco-sem (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) k ρ ⟨ wsM , ⟨ wsN , _ ⟩ ⟩ NE C G =
    letᵉ-≃ (rco-sem M k ρ wsM NE C G)
      (λ V ne c n → rco-sem N (suc k) (mem V • ρ) wsN (extend-nonempty-env NE (E≢[]⇒nonempty-mem ne))
                      (Con-• (≈⇒Con c) C) (Good-ext (NoErr-Vals V ne n) G))

  rco-args-sem {zero} Nil k ρ ws NE C G = ptt
  rco-args-sem {suc n} (M ,, Ms) k ρ ⟨ wsM , wsMs ⟩ NE C G =
    ⟨ up (rco-sem M k ρ wsM NE C G) , rco-args-sem Ms k ρ wsMs NE C G ⟩

{- Programs ---------------------------------------------------------------------}

table-vals : ∀ ds k → Vals (table ds k)
table-vals [] k = ⟨ ⟨ ν , ⟨ tt , (λ ()) ⟩ ⟩ , Λᵉ-clean ⟩
table-vals (N ∷ Ns) k with k ≟ length Ns
... | yes _ = ⟨ ⟨ ν , ⟨ tt , (λ ()) ⟩ ⟩ , Λᵉ-clean ⟩
... | no _ = table-vals Ns k

code-≃ : ∀ T T' (TC : ∀ k → Con (T k)) → (∀ k → T k ≃ T' k) → (∀ k → Vals (T k)) → ∀ N → WS 2 N
  → code T (rco N) ≃ code T' N
code-≃ T T' TC TT TV N ws =
  Λᵉ-≃ λ V neV cV nV → Λᵉ-≃ λ U neU cU nU →
    rco-sem T T' TC TT TV N 2 _ ws
      (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (E≢[]⇒nonempty-mem neV))
                           (E≢[]⇒nonempty-mem neU))
      (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω)))
      (Good-ext (NoErr-Vals U neU nU) (Good-ext (NoErr-Vals V neV nV) (λ x ())))

table-rco : ∀ ds → All (WS 2) ds → ∀ k → table (map rco ds) k ≃ table ds k
table-rco [] _ k = ≃-refl
table-rco (N ∷ Ns) (ws ∷ wss) k with k ≟ length (map rco Ns) | k ≟ length Ns
... | yes _ | yes _ =
  code-≃ (table (map rco Ns)) (table Ns) (table-con (map rco Ns)) (table-rco Ns wss) (table-vals (map rco Ns)) N ws
... | no _ | no _ = table-rco Ns wss k
... | yes k≡ | no k≢ = ⊥-elim (k≢ (trans k≡ (length-map rco Ns)))
... | no k≢ | yes k≡ = ⊥-elim (k≢ (trans k≡ (sym (length-map rco Ns))))

{- rco preserves the meaning of a well-scoped program exactly -}
rco-correct : ∀ (P : Program) → Scoped P → ⟦ rco-program P ⟧ₚ ≃ ⟦ P ⟧ₚ
rco-correct (program ds M) ⟨ wds , wM ⟩ =
  rco-sem (table (map rco ds)) (table ds) (table-con (map rco ds)) (table-rco ds wds) (table-vals (map rco ds))
    M 0 (λ _ → init) wM (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ x ())

{- the compiler's output, in monadic normal form -}
rco-correct-compile : ∀ (M : ISWIM.AST) → Closed M → ⟦ compile-mon M ⟧ₚ ≃ ⟦ compile M ⟧ₚ
rco-correct-compile M c = rco-correct (compile M) (compile-scoped M c)
