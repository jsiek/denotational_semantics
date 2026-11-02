{-

  Correctness of the hoist pass (Clos4 → Clos5) in the graph model with
  errors (Semantics/GraphErr/{Clos4,Clos5}.agda), as in the graph model
  (proof/Correctness/Graph/HoistCorrect.agda): the pass only moves the
  code of each function into the table of global definitions, so it
  preserves denotations exactly, for every Clos4 program. The code of a
  definition is ΛΛᵐ, as the closed function it replaces, and the table
  only grows; a reference never points past the table, so errcode, the
  meaning of a missing reference, plays no part. Calls are callᵐ (the
  late check) in both languages.

-}

open import Framework.Syntax.SigUtil
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Semantics.GraphErr.Prim
open import Untyped.Language.Clos4
import Untyped.Language.Clos5 as L5
import Language.ISWIM as ISWIM
open import Untyped.proof.Semantics.GraphErr.Clos4
open import Untyped.Semantics.GraphErr.Clos5
  using (Table; ⟦_⟧[_]; ⟦_⟧ₐ[_]; ⟦_⟧₊[_]; code; table; ⟦_⟧ₚ) renaming (init to init₅)
open import Untyped.Compiler.Hoist
open import Untyped.Compiler.Pipeline using (compile₄; compile)
open import Compiler.CaptureScope using (Closed)
open import proof.Framework.GraphModel.Env using (Env; •-~)


open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <-≤-trans; <-irrefl; n<1+n; m≤n+m; n≤1+n)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.List.Properties using (length-++)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

module Untyped.proof.Correctness.GraphErr.HoistCorrect where


{- Environments and results that agree ----------------------------------------}

EnvRel : Env Value → Env Value → Set
EnvRel ρ ρ' = ∀ x → ρ x ≃ ρ' x

{- References to older definitions ----------------------------------------------}

RB : ℕ → L5.AST → Set
RB-arg : ∀ {b} → ℕ → L5.Arg b → Set
RB-args : ∀ {bs} → ℕ → L5.Args bs → Set

RB n (L5.` x) = ⊤
RB n (L5.fun-ref k L5.⦅ args ⦆) = k < n
RB n (op L5.⦅ args ⦆) = RB-args n args

RB-arg n (L5.ast M) = RB n M
RB-arg n (L5.bind a) = RB-arg n a
RB-arg n (L5.clear a) = RB-arg n a

RB-args n L5.nil = ⊤
RB-args n (L5.cons a args) = RB-arg n a × RB-args n args

RB-mono : ∀ {n m} (M : L5.AST) → n ≤ m → RB n M → RB m M
RB-arg-mono : ∀ {n m b} (a : L5.Arg b) → n ≤ m → RB-arg n a → RB-arg m a
RB-args-mono : ∀ {n m bs} (args : L5.Args bs) → n ≤ m → RB-args n args → RB-args m args

RB-mono (L5.` x) n≤m tt = tt
RB-mono (L5.fun-ref k L5.⦅ args ⦆) n≤m k<n = <-≤-trans k<n n≤m
RB-mono (L5.app L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.lit B k L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.pair-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.fst-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.snd-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.tuple x L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.get x L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.inl-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.inr-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.case-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.let-op L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r
RB-mono (L5.prim p L5.⦅ args ⦆) n≤m r = RB-args-mono args n≤m r

RB-arg-mono (L5.ast M) n≤m r = RB-mono M n≤m r
RB-arg-mono (L5.bind a) n≤m r = RB-arg-mono a n≤m r
RB-arg-mono (L5.clear a) n≤m r = RB-arg-mono a n≤m r

RB-args-mono L5.nil n≤m tt = tt
RB-args-mono (L5.cons a args) n≤m ⟨ ra , rs ⟩ = ⟨ RB-arg-mono a n≤m ra , RB-args-mono args n≤m rs ⟩

{- The table only grows ----------------------------------------------------------}

Extends : Defs → Defs → Set
Extends ds ds' = Σ[ more ∈ Defs ] ds' ≡ more ++ ds

ext-trans : ∀ {ds₁ ds₂ ds₃} → Extends ds₁ ds₂ → Extends ds₂ ds₃ → Extends ds₁ ds₃
ext-trans {ds₁} ⟨ m₁ , refl ⟩ ⟨ m₂ , refl ⟩ = ⟨ m₂ ++ m₁ , sym (Data.List.Properties.++-assoc m₂ m₁ ds₁) ⟩

ext-length : ∀ {ds ds'} → Extends ds ds' → length ds ≤ length ds'
ext-length {ds} ⟨ more , refl ⟩ = subst (length ds ≤_) (sym (length-++ more)) (m≤n+m (length ds) (length more))

{- the entries for the older definitions do not change -}
table-ext : ∀ (more ds : Defs) k → k < length ds → table (more ++ ds) k ≡ table ds k
table-ext [] ds k k< = refl
table-ext (N ∷ more) ds k k< with k ≟ length (more ++ ds)
... | yes refl = ⊥-elim (<-irrefl refl (<-≤-trans k< (ext-length {ds} ⟨ more , refl ⟩)))
... | no _ = table-ext more ds k k<

table-top : ∀ (N : L5.AST) (Ns : Defs) → table (N ∷ Ns) (length Ns) ≡ code (table Ns) N
table-top N Ns with length Ns ≟ length Ns
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

Agree : ℕ → Table → Table → Set
Agree n T T' = ∀ k → k < n → T k ≃ T' k

agree-ext : ∀ {ds ds'} → Extends ds ds' → Agree (length ds) (table ds) (table ds')
agree-ext {ds} ⟨ more , refl ⟩ k k< = ≃-reflexive (sym (table-ext more ds k k<))

{- Stability: growing the table does not change older meanings ------------------}

stab : ∀ n T T' (M : L5.AST) ρ ρ' → Agree n T T' → RB n M → EnvRel ρ ρ'
  → ⟦ M ⟧[ T ] ρ ≃ ⟦ M ⟧[ T' ] ρ'
stab-arg : ∀ n T T' {b} (a : L5.Arg b) ρ ρ' → Agree n T T' → RB-arg n a → EnvRel ρ ρ'
  → RR b (⟦ a ⟧ₐ[ T ] ρ) (⟦ a ⟧ₐ[ T' ] ρ')
stab-args : ∀ n T T' {bs} (args : L5.Args bs) ρ ρ' → Agree n T T' → RB-args n args
  → EnvRel ρ ρ' → RRs bs (⟦ args ⟧₊[ T ] ρ) (⟦ args ⟧₊[ T' ] ρ')

stab n T T' (L5.` x) ρ ρ' ag r rel = rel x
stab n T T' (L5.fun-ref k L5.⦅ args ⦆) ρ ρ' ag k<n rel = ag k k<n
stab n T T' (L5.app L5.⦅ args ⦆) ρ ρ' ag r rel = mono-≃ (mono (callᵐ-good {⊤})) (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.lit B k L5.⦅ args ⦆) ρ ρ' ag r rel = ≃-refl
stab n T T' (L5.pair-op L5.⦅ args ⦆) ρ ρ' ag r rel = mono-≃ (mono (pairᵐ-good {⊤})) (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.fst-op L5.⦅ args ⦆) ρ ρ' ag r rel = mono-≃ (mono (carᵐ-good {⊤})) (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.snd-op L5.⦅ args ⦆) ρ ρ' ag r rel = mono-≃ (mono (cdrᵐ-good {⊤})) (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.tuple x L5.⦅ args ⦆) ρ ρ' ag r rel = mono-≃ (mono (𝒯ᵐ-good {⊤} x)) (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.get i L5.⦅ args ⦆) ρ ρ' ag r rel = mono-≃ (mono (projᵐ-good {⊤} i)) (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.inl-op L5.⦅ args ⦆) ρ ρ' ag r rel = mono-≃ (mono (inlᵐ-good {⊤})) (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.inr-op L5.⦅ args ⦆) ρ ρ' ag r rel = mono-≃ (mono (inrᵐ-good {⊤})) (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.case-op L5.⦅ args ⦆) ρ ρ' ag r rel = 𝒞ᵐ-RR (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.let-op L5.⦅ args ⦆) ρ ρ' ag r rel = letᵐ-RR (stab-args n T T' args ρ ρ' ag r rel)
stab n T T' (L5.prim p L5.⦅ args ⦆) ρ ρ' ag r rel = mono-≃ (mono (primᵐ-good {⊤} p)) (stab-args n T T' args ρ ρ' ag r rel)

stab-arg n T T' (L5.ast M) ρ ρ' ag r rel = lift (stab n T T' M ρ ρ' ag r rel)
stab-arg n T T' (L5.bind a) ρ ρ' ag r rel =
  λ X X' X≃ → stab-arg n T T' a (X • ρ) (X' • ρ') ag r (•-~ _≃_ rel X≃)
stab-arg n T T' (L5.clear a) ρ ρ' ag r rel =
  stab-arg n T T' a (λ _ → init₅) (λ _ → init₅) ag r (λ x → ≃-refl)

stab-args n T T' L5.nil ρ ρ' ag tt rel = ptt
stab-args n T T' (L5.cons a args) ρ ρ' ag ⟨ ra , rs ⟩ rel =
  ⟨ stab-arg n T T' a ρ ρ' ag ra rel , stab-args n T T' args ρ ρ' ag rs rel ⟩

{- The shape of the result ------------------------------------------------------}

Shape : Defs → L5.AST × Defs → Set
Shape ds r = Extends ds (proj₂ r) × RB (length (proj₂ r)) (proj₁ r)

glob-shape : ∀ (M : AST) ds → Shape ds (glob M ds)
glob-shape-arg : ∀ {b} (a : Arg b) ds
  → Extends ds (proj₂ (glob-arg a ds)) × RB-arg (length (proj₂ (glob-arg a ds))) (proj₁ (glob-arg a ds))
glob-shape-args : ∀ {bs} (args : Args bs) ds
  → Extends ds (proj₂ (glob-args args ds))
    × RB-args (length (proj₂ (glob-args args ds))) (proj₁ (glob-args args ds))

glob-shape (` x) ds = ⟨ ⟨ [] , refl ⟩ , tt ⟩
glob-shape (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds =
  ⟨ ext-trans (proj₁ (glob-shape N ds)) ⟨ proj₁ (glob N ds) ∷ [] , refl ⟩
  , n<1+n (length (proj₂ (glob N ds))) ⟩
glob-shape (app ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (lit B k ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (pair-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (fst-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (snd-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (tuple n ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (get i ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (inl-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (inr-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (case-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (let-op ⦅ args ⦆) ds = glob-shape-args args ds
glob-shape (prim p ⦅ args ⦆) ds = glob-shape-args args ds

glob-shape-arg (ast M) ds = glob-shape M ds
glob-shape-arg (bind a) ds = glob-shape-arg a ds
glob-shape-arg (clear a) ds = glob-shape-arg a ds

glob-shape-args nil ds = ⟨ ⟨ [] , refl ⟩ , tt ⟩
glob-shape-args (cons a args) ds =
  ⟨ ext-trans (proj₁ sa) (proj₁ ss)
  , ⟨ RB-arg-mono (proj₁ (glob-arg a ds)) (ext-length (proj₁ ss)) (proj₂ sa) , proj₂ ss ⟩ ⟩
  where
  sa = glob-shape-arg a ds
  ss = glob-shape-args args (proj₂ (glob-arg a ds))

{- The main lemma -------------------------------------------------------------}

glob-sem : ∀ (M : AST) ds ρ ρ' → EnvRel ρ ρ'
  → ⟦ M ⟧ ρ ≃ ⟦ proj₁ (glob M ds) ⟧[ table (proj₂ (glob M ds)) ] ρ'
glob-sem-arg : ∀ {b} (a : Arg b) ds ρ ρ' → EnvRel ρ ρ'
  → RR b (⟦ a ⟧ₐ ρ) (⟦ proj₁ (glob-arg a ds) ⟧ₐ[ table (proj₂ (glob-arg a ds)) ] ρ')
glob-sem-args : ∀ {bs} (args : Args bs) ds ρ ρ' → EnvRel ρ ρ'
  → RRs bs (⟦ args ⟧₊ ρ) (⟦ proj₁ (glob-args args ds) ⟧₊[ table (proj₂ (glob-args args ds)) ] ρ')

glob-sem (` x) ds ρ ρ' rel = rel x
glob-sem (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds ρ ρ' rel
  rewrite table-top (proj₁ (glob N ds)) (proj₂ (glob N ds)) =
  ΛΛᵐ-≃ (λ X Y → glob-sem N ds (Y • X • (λ _ → init₅)) (Y • X • (λ _ → init₅)) (λ x → ≃-refl))
glob-sem (app ⦅ args ⦆) ds ρ ρ' rel = mono-≃ (mono (callᵐ-good {⊤})) (glob-sem-args args ds ρ ρ' rel)
glob-sem (lit B k ⦅ args ⦆) ds ρ ρ' rel = ≃-refl
glob-sem (pair-op ⦅ args ⦆) ds ρ ρ' rel = mono-≃ (mono (pairᵐ-good {⊤})) (glob-sem-args args ds ρ ρ' rel)
glob-sem (fst-op ⦅ args ⦆) ds ρ ρ' rel = mono-≃ (mono (carᵐ-good {⊤})) (glob-sem-args args ds ρ ρ' rel)
glob-sem (snd-op ⦅ args ⦆) ds ρ ρ' rel = mono-≃ (mono (cdrᵐ-good {⊤})) (glob-sem-args args ds ρ ρ' rel)
glob-sem (tuple n ⦅ args ⦆) ds ρ ρ' rel = mono-≃ (mono (𝒯ᵐ-good {⊤} n)) (glob-sem-args args ds ρ ρ' rel)
glob-sem (get i ⦅ args ⦆) ds ρ ρ' rel = mono-≃ (mono (projᵐ-good {⊤} i)) (glob-sem-args args ds ρ ρ' rel)
glob-sem (inl-op ⦅ args ⦆) ds ρ ρ' rel = mono-≃ (mono (inlᵐ-good {⊤})) (glob-sem-args args ds ρ ρ' rel)
glob-sem (inr-op ⦅ args ⦆) ds ρ ρ' rel = mono-≃ (mono (inrᵐ-good {⊤})) (glob-sem-args args ds ρ ρ' rel)
glob-sem (case-op ⦅ args ⦆) ds ρ ρ' rel = 𝒞ᵐ-RR (glob-sem-args args ds ρ ρ' rel)
glob-sem (let-op ⦅ args ⦆) ds ρ ρ' rel = letᵐ-RR (glob-sem-args args ds ρ ρ' rel)
glob-sem (prim p ⦅ args ⦆) ds ρ ρ' rel = mono-≃ (mono (primᵐ-good {⊤} p)) (glob-sem-args args ds ρ ρ' rel)

glob-sem-arg (ast M) ds ρ ρ' rel = lift (glob-sem M ds ρ ρ' rel)
glob-sem-arg (bind a) ds ρ ρ' rel =
  λ X X' X≃ → glob-sem-arg a ds (X • ρ) (X' • ρ') (•-~ _≃_ rel X≃)
glob-sem-arg (clear a) ds ρ ρ' rel = glob-sem-arg a ds (λ _ → init₅) (λ _ → init₅) (λ x → ≃-refl)

glob-sem-args nil ds ρ ρ' rel = ptt
glob-sem-args {b ∷ bs} (cons a args) ds ρ ρ' rel =
  ⟨ rr-trans b _ _ _ (glob-sem-arg a ds ρ ρ' rel)
      (stab-arg (length ds₁) (table ds₁) (table ds₂) a' ρ' ρ'
         (agree-ext (proj₁ (glob-shape-args args ds₁))) (proj₂ (glob-shape-arg a ds)) (λ x → ≃-refl))
  , glob-sem-args args ds₁ ρ ρ' rel ⟩
  where
  a' = proj₁ (glob-arg a ds)
  ds₁ = proj₂ (glob-arg a ds)
  ds₂ = proj₂ (glob-args args ds₁)

{- The end theorem ------------------------------------------------------------}

hoist-correct : ∀ (M : AST) → ⟦ M ⟧ ρ₀ ≃ ⟦ hoist M ⟧ₚ
hoist-correct M = glob-sem M [] ρ₀ ρ₀ (λ x → ≃-refl)

{- the compiler's Clos4 output -}
hoist-correct-compile : ∀ (M : ISWIM.AST) → Closed M → ⟦ compile₄ M ⟧ ρ₀ ≃ ⟦ compile M ⟧ₚ
hoist-correct-compile M _ = hoist-correct (compile₄ M)
