{-

  Adequacy of the graph model with errors for the typed compiler
  (Compiler/Pipeline.agda): the denotation of compile M (Clos5ᵀ) and of
  compile-x86 M (X86ᵀ) tells the three outcomes of its machine apart,
  for a closed ISWIM program M.

  X86ᵀ: the adequacy of its semantics for its machine (Adequacy/GraphErr/
  X86.agda), whose conditions the programs of the compiler meet (OK):
  * the code of each definition depends only on the older ones: it means
    the code of the Clos5ᵀ definition it comes from, under any table of
    sets of values, consistent (x86-code: select, explicate control, lift
    locals and rco preserve the meaning of code), and globalize makes
    only references to older definitions (proof/Compiler/GlobalizeOlder.agda);
  * the table is consistent, as that of CFGᵀ is (select's table-≃).
  The ISWIM machine on M and the X86ᵀ machine on compile-x86 M agree on
  every outcome (end-to-end-x86): the denotations of M and compile-x86 M
  are the Same (Correctness/GraphErr/CompilerCorrect.agda), and both
  machines are adequate.

  Clos5ᵀ: not a logical relation of its own. The ISWIM machine on M and
  the Clos5ᵀ machine on compile M agree on every outcome (the CEK
  column, Correctness/CEK/PipelineSim.agda), the denotations of M
  and compile M are the Same (Correctness/GraphErr/
  CompilerCorrect.agda), and the ISWIM machine is adequate
  (Adequacy/GraphErr/ISWIM.agda).

-}

module proof.Adequacy.GraphErr.EndToEnd where

open import Framework.Primitives using (base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ω; ρ₀; Con; Con-⊆; Con-•; Con-⌈⌉; ≈⇒Con; _•_) renaming (const to dconst)
open import proof.Framework.GraphModel.ErrorMonad
  using (ΛΛᵐ-≃; ΛΛᵐ-≃′; noerr-val; pairᵐ-≃; 𝒯ᵐ-≃; inlᵐ-≃; inrᵐ-≃; ≫=-≃) renaming (Val to Valᴰ)
open import proof.Framework.GraphModel.Env using (extend-nonempty-env; •-~; _~ₑ[_]_)
open import Language.ISWIM using (AST)
open import Language.Typed.Type hiding (_≟_)
open import Language.Typed.Clos5 using (Tm; Code; `_; fun-ref; pack; callc; lit; tuple; get; inl; inr; case; prim; let′; inject; project)
open import Semantics.Observation using (o-const; o-error; Converges; _⇔_)
open import proof.Semantics.CEK.Smallstep using (Terminates; Diverges)
import Semantics.CEK.ISWIM as ISWIMₘ
import Semantics.CEK.Typed.Clos5 as Clos5ᵀₘ
import Semantics.CEK.Typed.X86 as X86ᵀₘ
open import Semantics.GraphErr.Typed.Ops using (init)
open import Semantics.GraphErr.Typed.Clos4 using (kind₄)
open import Semantics.GraphErr.Typed.Clos5 using (⟦_⟧₅; ⟦_⟧[_]; ⟦_⟧s[_]; code₅; Table)
open import Semantics.GraphErr.Typed.X86 using (⟦_⟧ₜ; codeₜ)
open import Semantics.GraphErr.ISWIM using (⟦_⟧)
open import Compiler.Pipeline using (compile; compile₄; compile-cfg; compile-x86)
open import Compiler.EncloseScope using (Closed)
open import Compiler.RCO using (rco)
open import Compiler.LiftLocals using (lift)
open import Compiler.Explicate using (explicate-body)
open import Compiler.Select using (def-body)
open import proof.Correctness.GraphErr.CompilerCorrect using (Same; compile-same₅; compile-x86-same)
open import proof.Correctness.GraphErr.SelectCorrect using (code-≃; table-≃)
open import proof.Correctness.GraphErr.ExplicateCorrect using (body-sem)
open import proof.Correctness.GraphErr.LiftLocalsCorrect using (lift-sem)
open import proof.Correctness.GraphErr.RCOCorrect using (rco-sem; mkR)
open import proof.Semantics.GraphErr.Typed.Clos5 using (callc-≃; tbl-con)
open import proof.Semantics.GraphErr.Typed.Clos2 using (getᵗ-≃; caseᵗ-≃; primᵗ-≃; projectᵗ-≃; ⌊⌋-≃)
open import proof.Semantics.GraphErr.Typed.CFG using (codeᶜ-con)
open import proof.Correctness.CEK.PipelineSim using (compile-error; compile-const; compile-converges; compile-diverges)
open import proof.Compiler.GlobalizeOlder using (Older; Olders; OlderDefs; globalize-older)
import proof.Adequacy.GraphErr.ISWIM as A
import proof.Adequacy.GraphErr.X86 as X
import proof.Adequacy.GraphErr.X86Common as C
import Language.Typed.Clos5 as C₅
import Language.Typed.CFG as CFG
import Language.Typed.Mon as Mon
open import Semantics.GraphErr.Typed.CFG using (codeᶜ)
open import Semantics.GraphErr.Typed.Imp using (codeᵢ)
import Language.Typed.X86 as X86ᵀ
open import proof.Adequacy.GraphErr.Agree using (Agree; agree; ⇔-sym; ⇔-trans; Same-sym; empty-Same) public
open import Framework.Lookup using (_!_)
open import Framework.GraphModel.OpsBase using (nthD)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt)
open import Data.Vec using (Vec; []; _∷_)
open import Level using () renaming (lift to up)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst)
open import Relation.Nullary using (¬_)

{- The programs of compile-x86 meet the conditions of X86ᵀ adequacy -----------------}

private
  {- a Clos5ᵀ term that refers only to definitions below k means the same
     under tables that agree below k -}
  module _ {T T' : Table} {k} (TT : ∀ j → j < k → T j ≃ T' j) where
    old-≃ : ∀ {Σ Γ A} (M : Tm Σ Γ A) → Older k M → ∀ {ρ ρ'} → ρ ~ₑ[ _≃_ ] ρ' → ⟦ M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T' ] ρ'
    olds-≃ : ∀ {Σ Γ n} (Ms : Vec (Tm Σ Γ Any) n) → Olders k Ms → ∀ {ρ ρ'} → ρ ~ₑ[ _≃_ ] ρ'
      → ∀ i → nthD (⟦ Ms ⟧s[ T ] ρ) i ≃ nthD (⟦ Ms ⟧s[ T' ] ρ') i
    old-≃ (` x) o ρ~ = ρ~ (idx x)
    old-≃ (fun-ref f) o ρ~ = TT _ o
    old-≃ (pack L M) ⟨ o , o' ⟩ ρ~ = pairᵐ-≃ (old-≃ L o ρ~) (old-≃ M o' ρ~)
    old-≃ (callc L M) ⟨ o , o' ⟩ ρ~ = callc-≃ (old-≃ L o ρ~) (old-≃ M o' ρ~)
    old-≃ (lit B c) o ρ~ = ≃-refl
    old-≃ (tuple {n = n} Ms) o ρ~ = 𝒯ᵐ-≃ n (olds-≃ Ms o ρ~)
    old-≃ (get i M) o ρ~ = getᵗ-≃ i (old-≃ M o ρ~)
    old-≃ (inl M) o ρ~ = inlᵐ-≃ (old-≃ M o ρ~)
    old-≃ (inr M) o ρ~ = inrᵐ-≃ (old-≃ M o ρ~)
    old-≃ (case L M N) ⟨ o , ⟨ o' , o'' ⟩ ⟩ {ρ} {ρ'} ρ~ = caseᵗ-≃ {F = λ X → ⟦ M ⟧[ T ] (X • ρ)} {λ X → ⟦ M ⟧[ T' ] (X • ρ')} {λ X → ⟦ N ⟧[ T ] (X • ρ)} {λ X → ⟦ N ⟧[ T' ] (X • ρ')}
      (old-≃ L o ρ~) (λ _ _ _ _ → old-≃ M o' (•-~ _≃_ ρ~ ≃-refl)) (λ _ _ _ _ → old-≃ N o'' (•-~ _≃_ ρ~ ≃-refl))
    old-≃ (prim p L M) ⟨ o , o' ⟩ ρ~ = primᵗ-≃ p (old-≃ L o ρ~) (old-≃ M o' ρ~)
    old-≃ (let′ M N) ⟨ o , o' ⟩ {ρ} {ρ'} ρ~ = ≫=-≃ {F = λ X → ⟦ N ⟧[ T ] (X • ρ)} {λ X → ⟦ N ⟧[ T' ] (X • ρ')} (old-≃ M o ρ~) λ _ _ → old-≃ N o' (•-~ _≃_ ρ~ (⌊⌋-≃ (old-≃ M o ρ~)))
    old-≃ (inject G M) o ρ~ = old-≃ M o ρ~
    old-≃ (project t M) o ρ~ = projectᵗ-≃ kind₄ t (old-≃ M o ρ~)
    olds-≃ (M ∷ Ms) ⟨ o , _ ⟩ ρ~ zero = old-≃ M o ρ~
    olds-≃ (M ∷ Ms) ⟨ _ , os ⟩ ρ~ (suc i) = olds-≃ Ms os ρ~ i

  {- what the compiler makes of a definition of compile M -}
  pipe : ∀ {Σ n} → Code Σ n → _
  pipe D = def-body (explicate-body (lift (rco D (λ x → x))))

  {- its code is that of the definition, under a table of consistent sets of values -}
  Good : Table → Set
  Good T = ∀ k → Valᴰ (T k) × Con (T k)

  x86-code : ∀ {Σ T n} → Good T → (D : Code Σ n) → code₅ T D ≃ codeₜ T (pipe D)
  x86-code {T = T} gT D =
    ≃-trans {D₂ = code₅ T Mon.⌜ e ⌝} (ΛΛᵐ-≃′ λ V U neV _ nV neU _ nU → rco-sem (λ _ → ≃-refl) (λ k → proj₁ (gT k)) D (λ x → x)
            (mkR λ { Z → ⟨ ≃-refl , noerr-val U neU nU ⟩ ; (S Z) → ⟨ ≃-refl , noerr-val V neV nV ⟩ }))
      (≃-trans {D₂ = codeᵢ T (lift e)} (ΛΛᵐ-≃′ λ V U neV cV _ neU cU _ →
                    lift-sem (λ _ → ≃-refl) (λ k → proj₂ (gT k)) e nothing (up tt)
                      (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) (E≢[]⇒nonempty-mem neV)) (E≢[]⇒nonempty-mem neU))
                      (Con-• (≈⇒Con cU) (Con-• (≈⇒Con cV) (λ _ → Con-⌈⌉ ω))) (λ _ _ → ≃-refl))
        (≃-trans {D₂ = codeᶜ T (explicate-body (lift e))} (ΛΛᵐ-≃ λ X Y → body-sem (λ _ → ≃-refl) (lift e) _)
          (code-≃ (λ _ → ≃-refl) (λ k → proj₂ (gT k)) (explicate-body (lift e)))))
    where e = rco D (λ x → x)

  pipe-! : ∀ {Σ ns n} (ds : All (Code Σ) ns) (f : ns ∋ n)
    → All-map def-body (All-map explicate-body (All-map lift (All-map (λ D → rco D (λ x → x)) ds))) ! f ≡ pipe (ds ! f)
  pipe-! (d ∷ ds) Z = refl
  pipe-! (d ∷ ds) (S f) = pipe-! ds f

  older-at : ∀ {Σ ns n} {ds : All (Code Σ) ns} → OlderDefs ds → (f : ns ∋ n) → Older (lvl f) (ds ! f)
  older-at {ds = d ∷ ds} ⟨ o , _ ⟩ Z = o
  older-at {ds = d ∷ ds} ⟨ _ , os ⟩ (S f) = older-at os f

compile-ok : ∀ M → X.OK (compile-x86 M)
compile-ok M = ⟨ (λ k → Con-⊆ (tbl-con (λ TC d → codeᶜ-con TC d) cds k) (proj₂ (table-≃ cds k))) , ind ⟩
  where
  ds = C₅.Program.defs (compile M)
  cds = CFG.Program.defs (compile-cfg M)
  ind : C.Indep (X86ᵀ.Program.defs (compile-x86 M))
  ind f {T} {T'} gT gT' ag rewrite pipe-! ds f =
    ≃-trans (≃-sym (x86-code gT (ds ! f))) (≃-trans (ΛΛᵐ-≃ λ X Y → old-≃ ag (ds ! f) (older-at (globalize-older (compile₄ M)) f) (λ _ → ≃-refl))
      (x86-code gT' (ds ! f)))

{- The X86ᵀ machine --------------------------------------------------------------------}

x86-error-iff : ∀ M → Closed M → (ω ∈ ⟦ compile-x86 M ⟧ₜ) ⇔ Terminates (X86ᵀₘ.sem (compile-x86 M)) o-error
x86-error-iff M c = X.error-iff (compile-x86 M) (compile-ok M)

x86-const-iff : ∀ M → Closed M → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ compile-x86 M ⟧ₜ) ⇔ Terminates (X86ᵀₘ.sem (compile-x86 M)) (o-const B k)
x86-const-iff M c = X.const-iff (compile-x86 M) (compile-ok M)

x86-converges-iff : ∀ M → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile-x86 M ⟧ₜ × d ≢ ω) ⇔ Converges (Terminates (X86ᵀₘ.sem (compile-x86 M)))
x86-converges-iff M c = X.converges-iff (compile-x86 M) (compile-ok M)

x86-diverges-iff : ∀ M → Closed M
  → Diverges (X86ᵀₘ.sem (compile-x86 M)) ⇔ (∀ d → ¬ (d ∈ ⟦ compile-x86 M ⟧ₜ))
x86-diverges-iff M c = X.diverges-iff (compile-x86 M) (compile-ok M)

{- The Clos5ᵀ machine ------------------------------------------------------------}

private
  Sm : ∀ M → Closed M → Same ⟦ compile M ⟧₅ (⟦ M ⟧ ρ₀)
  Sm M c = Same-sym (compile-same₅ M c)

clos5-error-iff : ∀ M → Closed M → (ω ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) o-error
clos5-error-iff M c = ⇔-trans (proj₁ (Sm M c)) (⇔-trans (A.error-iff M c) (compile-error M c))

clos5-const-iff : ∀ M → Closed M → ∀ {B} {k : base-rep B}
  → (dconst k ∈ ⟦ compile M ⟧₅) ⇔ Terminates (Clos5ᵀₘ.sem (compile M)) (o-const B k)
clos5-const-iff M c {B} {k} =
  ⇔-trans (proj₁ (proj₂ (Sm M c)) k) (⇔-trans (A.const-iff M c) (compile-const M c B k))

clos5-converges-iff : ∀ M → Closed M
  → (Σ[ d ∈ Value ] d ∈ ⟦ compile M ⟧₅ × d ≢ ω) ⇔ Converges (Terminates (Clos5ᵀₘ.sem (compile M)))
clos5-converges-iff M c =
  ⇔-trans (proj₂ (proj₂ (Sm M c))) (⇔-trans (A.converges-iff M c) (compile-converges M c))

clos5-diverges-iff : ∀ M → Closed M
  → Diverges (Clos5ᵀₘ.sem (compile M)) ⇔ (∀ d → ¬ (d ∈ ⟦ compile M ⟧₅))
clos5-diverges-iff M c =
  ⇔-trans (⇔-sym (compile-diverges M c))
    (⇔-trans (A.diverges-iff M c) ⟨ empty-Same (Same-sym (Sm M c)) , empty-Same (Sm M c) ⟩)

{- The compiler, observed through the machines ------------------------------------}

end-to-end : ∀ M → Closed M → Agree (ISWIMₘ.sem M) (Clos5ᵀₘ.sem (compile M))
end-to-end M c =
  agree (compile-same₅ M c) (A.error-iff M c) (clos5-error-iff M c) (A.const-iff M c) (clos5-const-iff M c)
    (A.converges-iff M c) (clos5-converges-iff M c) (A.diverges-iff M c) (clos5-diverges-iff M c)

end-to-end-x86 : ∀ M → Closed M → Agree (ISWIMₘ.sem M) (X86ᵀₘ.sem (compile-x86 M))
end-to-end-x86 M c =
  agree (compile-x86-same M c) (A.error-iff M c) (x86-error-iff M c) (A.const-iff M c) (x86-const-iff M c)
    (A.converges-iff M c) (x86-converges-iff M c) (A.diverges-iff M c) (x86-diverges-iff M c)
