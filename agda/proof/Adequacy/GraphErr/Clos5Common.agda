{-

  Definitions shared by the soundness and adequacy proofs for Clos5 in
  the graph model with errors (see Adequacy/GraphErr/Clos5.agda):

  * s ↠ t, runs of the Clos5 machine of a table ds from any state, and
    their determinism;
  * where a definition found by the machine (global ds k) sits in the
    table, and what the semantics makes of it (table-at, table-agree);
    a reference the machine does not find means errcode (table-past);
  * stability (stab⊆): a term that refers only to the first n
    definitions means no more with a table that agrees with a larger one
    on them.

-}

open import Data.List using (List; []; _∷_; _++_; length; reverse)
open import Language.Clos5 using (AST; global)

module proof.Adequacy.GraphErr.Clos5Common (ds : List AST) where

open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain using (Value; ν; _↦_)
open import proof.Framework.GraphModel.ErrorMonad
  using (errcode; Clean; ΛΛᵐ-val; ΛΛᵐ-fun; ΛΛᵐ; kind; Kind; fun; callᵐ-good; pairᵐ-good; carᵐ-good; cdrᵐ-good; 𝒯ᵐ-good; projᵐ-good;
         inlᵐ-good; inrᵐ-good; 𝒞ᵐ-good; letᵐ-good)
open import proof.Framework.GraphModel.ContinuityBase using (mono)
open import proof.Semantics.GraphErr.Prim using (primᵐ-good)
open import Language.Clos5 hiding (AST; global)
open import Semantics.GraphErr.Clos5 using (Table; ⟦_⟧[_]; ⟦_⟧ₐ[_]; ⟦_⟧₊[_]; table; code; init)
open import proof.Framework.GraphModel.DOpSig using (result-rel-pres; results-rel-pres)
open import proof.Framework.GraphModel.Env using (Env; •-~)
open import proof.Framework.ListUtil using (reverse-‼-split; _‼_)
open import Semantics.CEK.Clos5 using (step)
open import proof.Compiler.GlobalizeTable using (_⊑_)
open import proof.Adequacy.GraphErr.Clos5WF using (DefsWF; RB; RB-arg; RB-args)
open import proof.Framework.Runs using (module Runs)

open import Data.List.Properties using (length-reverse; length-++)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_; z≤n; s≤s)
open import Data.Nat.Properties using (n<1+n; ≤-pred; m≤n⇒m<n∨m≡n; <-≤-trans; <-irrefl; ≤-trans; n≤1+n; m≤n+m)
open import Data.Product using (Σ-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt; ⊤)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)
open import Data.Empty using (⊥-elim)

{- Runs of the machine -----------------------------------------------------------}

open Runs (step ds) public

{- The table of global definitions ------------------------------------------------}

{- the definition that the machine finds at k sits on top of the k
   definitions older than it -}
global-split : ∀ k {B} → global ds k ≡ just B → Σ[ Ns ∈ List AST ] (B ∷ Ns ⊑ ds) × length Ns ≡ k
global-split k eq with reverse-‼-split ds k eq
... | ⟨ xs , ⟨ Ns , ⟨ e , len ⟩ ⟩ ⟩ = ⟨ Ns , ⟨ ⟨ xs , e ⟩ , len ⟩ ⟩

DefsWF-⊑ : ∀ {Ns} → Ns ⊑ ds → DefsWF ds → DefsWF Ns
DefsWF-⊑ ⟨ xs , refl ⟩ = go xs
  where
  go : ∀ xs {Ns} → DefsWF (xs ++ Ns) → DefsWF Ns
  go [] w = w
  go (x ∷ xs) w = go xs (proj₂ w)

{- the entries for the older definitions do not change -}
table-ext : ∀ (more Ns : List AST) k → k < length Ns → table (more ++ Ns) k ≡ table Ns k
table-ext [] Ns k k< = refl
table-ext (N ∷ more) Ns k k< with k ≟ length (more ++ Ns)
... | yes refl = ⊥-elim (<-irrefl refl (<-≤-trans k< len≤))
  where
  len≤ : length Ns ≤ length (more ++ Ns)
  len≤ = subst (length Ns ≤_) (sym (length-++ more)) (m≤n+m (length Ns) (length more))
... | no _ = table-ext more Ns k k<

table-top : ∀ (N : AST) (Ns : List AST) → table (N ∷ Ns) (length Ns) ≡ code (table Ns) N
table-top N Ns with length Ns ≟ length Ns
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

{- the meaning of a definition, with the table of the older ones -}
table-at : ∀ {B Ns} → B ∷ Ns ⊑ ds → table ds (length Ns) ≡ code (table Ns) B
table-at {B} {Ns} ⟨ xs , refl ⟩ =
  trans (table-ext xs (B ∷ Ns) (length Ns) (n<1+n (length Ns))) (table-top B Ns)

{- the older definitions mean the same in the whole table -}
table-agree : ∀ {Ns} → Ns ⊑ ds → ∀ j → j < length Ns → table ds j ≡ table Ns j
table-agree {Ns} ⟨ xs , refl ⟩ j j< = table-ext xs Ns j j<

{- a reference past the table means errcode -}
table-past : ∀ (Ns : List AST) k → length Ns ≤ k → table Ns k ≡ errcode
table-past [] k _ = refl
table-past (N ∷ Ns) k len≤ with k ≟ length Ns
... | yes refl = ⊥-elim (<-irrefl refl len≤)
... | no _ = table-past Ns k (≤-trans (n≤1+n (length Ns)) len≤)

‼-nothing : ∀ {A : Set} (xs : List A) k → xs ‼ k ≡ nothing → length xs ≤ k
‼-nothing [] k _ = z≤n
‼-nothing (x ∷ xs) zero ()
‼-nothing (x ∷ xs) (suc k) eq = s≤s (‼-nothing xs k eq)

global-nothing : ∀ k → global ds k ≡ nothing → table ds k ≡ errcode
global-nothing k eq =
  table-past ds k (subst (_≤ k) (length-reverse ds) (‼-nothing (reverse ds) k eq))

{- every entry is a function without ω -}
table-ν : ∀ (Ns : List AST) k → ν ∈ table Ns k
table-ν [] k = ⟨ tt , tt ⟩
table-ν (N ∷ Ns) k with k ≟ length Ns
... | yes _ = ⟨ tt , tt ⟩
... | no _ = table-ν Ns k

table-clean : ∀ (Ns : List AST) k → Clean (table Ns k)
table-clean [] k = proj₁ ΛΛᵐ-val
table-clean (N ∷ Ns) k with k ≟ length Ns
... | yes _ = proj₁ ΛΛᵐ-val
... | no _ = table-clean Ns k

table-fun : ∀ (Ns : List AST) k d → d ∈ table Ns k → kind d ≡ fun
table-fun [] k = ΛΛᵐ-fun
table-fun (N ∷ Ns) k with k ≟ length Ns
... | yes _ = ΛΛᵐ-fun
... | no _ = table-fun Ns k

{- Stability ----------------------------------------------------------------------}

Agree⊆ : ℕ → Table → Table → Set
Agree⊆ n T T' = ∀ k → k < n → T k ⊆ T' k

stab⊆ : ∀ n T T' (M : AST) {ρ ρ' : Env Value} → Agree⊆ n T T' → RB n M → (∀ x → ρ x ⊆ ρ' x)
  → ⟦ M ⟧[ T ] ρ ⊆ ⟦ M ⟧[ T' ] ρ'
stab⊆-arg : ∀ n T T' {b} (a : Arg b) {ρ ρ' : Env Value} → Agree⊆ n T T' → RB-arg n a
  → (∀ x → ρ x ⊆ ρ' x) → result-rel-pres _⊆_ b (⟦ a ⟧ₐ[ T ] ρ) (⟦ a ⟧ₐ[ T' ] ρ')
stab⊆-args : ∀ n T T' {bs} (args : Args bs) {ρ ρ' : Env Value} → Agree⊆ n T T' → RB-args n args
  → (∀ x → ρ x ⊆ ρ' x) → results-rel-pres _⊆_ bs (⟦ args ⟧₊[ T ] ρ) (⟦ args ⟧₊[ T' ] ρ')

stab⊆ n T T' (` x) ag r rel = rel x
stab⊆ n T T' (fun-ref k ⦅ args ⦆) ag k<n rel = ag k k<n
stab⊆ n T T' (app ⦅ args ⦆) ag r rel = lower (mono (callᵐ-good {⊤}) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (lit B k ⦅ args ⦆) ag r rel d d∈ = d∈
stab⊆ n T T' (pair-op ⦅ args ⦆) ag r rel = lower (mono (pairᵐ-good {⊤}) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (fst-op ⦅ args ⦆) ag r rel = lower (mono (carᵐ-good {⊤}) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (snd-op ⦅ args ⦆) ag r rel = lower (mono (cdrᵐ-good {⊤}) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (tuple m ⦅ args ⦆) ag r rel = lower (mono (𝒯ᵐ-good {⊤} m) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (get i ⦅ args ⦆) ag r rel = lower (mono (projᵐ-good {⊤} i) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (inl-op ⦅ args ⦆) ag r rel = lower (mono (inlᵐ-good {⊤}) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (inr-op ⦅ args ⦆) ag r rel = lower (mono (inrᵐ-good {⊤}) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (case-op ⦅ args ⦆) ag r rel = lower (mono (𝒞ᵐ-good {⊤}) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (let-op ⦅ args ⦆) ag r rel = lower (mono (letᵐ-good {⊤}) _ _ (stab⊆-args n T T' args ag r rel))
stab⊆ n T T' (prim p ⦅ args ⦆) ag r rel = lower (mono (primᵐ-good {⊤} p) _ _ (stab⊆-args n T T' args ag r rel))

stab⊆-arg n T T' (ast M) ag r rel = lift (stab⊆ n T T' M ag r rel)
stab⊆-arg n T T' (bind a) ag r rel = λ X X' X⊆ → stab⊆-arg n T T' a ag r (•-~ _⊆_ rel X⊆)
stab⊆-arg n T T' (clear a) ag r rel = stab⊆-arg n T T' a ag r (λ x d d∈ → d∈)

stab⊆-args n T T' nil ag r rel = ptt
stab⊆-args n T T' (cons a args) ag ⟨ ra , rs ⟩ rel =
  ⟨ stab⊆-arg n T T' a ag ra rel , stab⊆-args n T T' args ag rs rel ⟩
