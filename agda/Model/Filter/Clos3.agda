{-# OPTIONS --allow-unsolved-metas #-}

module Model.Filter.Clos3 where
{-

 In this intermediate semantics all functions take two parameters,
   so application have two operands and
 This semantics is after the 'delay' pass,
   and before the 'globalize' pass.

-}

open import Utilities using (_iff_)
open import Primitives
open import ScopedTuple hiding (𝒫)
open import NewSigUtil
open import NewDOpSig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import NewDenotProperties
open import Model.Filter.DomainAnnFun
open import Model.Filter.OperationAnnFun
open import Syntax using (Sig; ext; ∁; ν; ■; Var; _•_; ↑; id; _⨟_) public

open import Data.Empty renaming (⊥ to Bot)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (+-suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Product
   using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Level renaming (zero to lzero; suc to lsuc)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning

{- Syntax ---------------------------------------------------------------------}

data Op : Set where
  clos-op : ℕ → Op
  app : Op
  lit : (B : Base) → (k : base-rep B) → Op
  tuple : ℕ → Op
  get : ℕ → Op
  inl-op : Op
  inr-op : Op
  case-op : Op

sig : Op → List Sig
sig (clos-op n) = ∁ (ν (ν ■)) ∷ (replicate n ■)
sig app = ■ ∷ ■ ∷ []
sig (lit B k) = []
sig (tuple n) = replicate n ■
sig (get i) = ■ ∷ []
sig inl-op = ■ ∷ []
sig inr-op = ■ ∷ []
sig case-op = ■ ∷ ν ■ ∷ ν ■ ∷ []

module ASTMod = Syntax.OpSig Op sig
open ASTMod using (`_; _⦅_⦆; Subst; Ctx; plug; rename; 
                   ⟪_⟫; _[_]; subst-zero; clear; bind; ast; cons; nil;
                   Arg; Args;
                   rename-id; exts-cons-shift; WF; WF-Ctx; ctx-depth;
                   WF-op; WF-cons; WF-nil; WF-ast; WF-bind; WF-var;
                   COp; CAst; CBind; ccons; tcons; append₊)
            renaming (ABT to AST) public

𝕆-Clos3 : DOpSig (𝒫 Value) sig
𝕆-Clos3 (clos-op n) ⟨ F , Ds ⟩ = 
  𝒜⋆ ⟨ Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ 
     , ⟨ 𝒯 n Ds 
     , ptt ⟩ ⟩
𝕆-Clos3 app = ⋆
𝕆-Clos3 (lit B k) = ℬ B k
𝕆-Clos3 (tuple n) = 𝒯 n
𝕆-Clos3 (get i) = proj i
𝕆-Clos3 inl-op = ℒ
𝕆-Clos3 inr-op = ℛ
𝕆-Clos3 case-op = 𝒞

𝕆-Clos3-mono : 𝕆-monotone sig 𝕆-Clos3
𝕆-Clos3-mono (clos-op x) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ = 
    𝒜⋆-mono ⟨ Λ ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 x Ds , ptt ⟩ ⟩ 
            ⟨ Λ ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩ , ⟨ 𝒯 x Ds' , ptt ⟩ ⟩ 
            ⟨ Λ-mono ⟨ (λ X → Λ ⟨ F X , ptt ⟩) , ptt ⟩ 
                     ⟨ (λ X → Λ ⟨ F' X , ptt ⟩) , ptt ⟩ 
                     ⟨ (λ D D' D⊆ → Λ-mono ⟨ F D , ptt ⟩ 
                                           ⟨ F' D' , ptt ⟩ 
                                           ⟨ F~ D D' D⊆ , ptt ⟩) , ptt ⟩ 
            , ⟨ 𝒯-mono x Ds Ds' Ds~ , ptt ⟩ ⟩
     {- Λ-mono ⟨ F , ⟨ 𝒯 x Ds , ptt ⟩ ⟩ ⟨ F' , ⟨ 𝒯 x Ds' , ptt ⟩ ⟩
              ⟨ F~ , ⟨ 𝒯-mono x Ds Ds' Ds~ , ptt ⟩ ⟩ -}

  {- Λn-mono (suc zero) ⟨ F , ⟨ 𝒯 x Ds , ptt ⟩ ⟩ ⟨ F' , ⟨ 𝒯 x Ds' , ptt ⟩ ⟩ 
             ⟨ F~ , ⟨ 𝒯-mono x Ds Ds' Ds~ , ptt ⟩ ⟩
  -}
  {- 𝒜-mono x ⟨ Λ ⟨ F (𝒯 x Ds) , ptt ⟩ , Ds ⟩ ⟨ Λ ⟨ F' (𝒯 x Ds') , ptt ⟩ , Ds' ⟩ 
    ⟨ Λ-mono ⟨ F (𝒯 x Ds) , ptt ⟩ ⟨ F' (𝒯 x Ds') , ptt ⟩ 
             ⟨ F~ (𝒯 x Ds) (𝒯 x Ds') (lower (𝒯-mono x Ds Ds' Ds~)) , ptt ⟩ 
    , Ds~ ⟩ -}
  {- DComp-rest-pres _⊆_ (replicate x ■) ■ ■ (𝒯 x) (𝒯 x) 
                  (λ T → 𝒜 x (Λ (F1 T))) (λ T → 𝒜 x (Λ (F2 T))) 
                  (𝒯-mono x) 
                  (λ T T' T⊆ → 𝒜-mono x (Λ (F1 T)) (Λ (F2 T')) 
                               (Λ-mono (F1 T) (F2 T') (F~ T T' (lower T⊆)))) -}
𝕆-Clos3-mono app = ⋆-mono
𝕆-Clos3-mono (lit B k) _ _ _ = lift (λ d z → z)
𝕆-Clos3-mono (tuple x) = 𝒯-mono x
𝕆-Clos3-mono (get x) = proj-mono x
𝕆-Clos3-mono inl-op = ℒ-mono
𝕆-Clos3-mono inr-op = ℛ-mono
𝕆-Clos3-mono case-op = 𝒞-mono

𝕆-Clos3-consis : 𝕆-consistent _~_ sig 𝕆-Clos3
𝕆-Clos3-consis = {!   !}

{-  (clos-op x) ⟨ F , Ds ⟩ ⟨ F' , Ds' ⟩ ⟨ F~ , Ds~ ⟩ = {!   !}
  {- 𝒜-consis x ⟨ Λ ⟨ F (𝒯 x Ds) , ptt ⟩ , Ds ⟩ ⟨ Λ ⟨ F' (𝒯 x Ds') , ptt ⟩ , Ds' ⟩ 
    ⟨ Λ-consis ⟨ F (𝒯 x Ds) , ptt ⟩ ⟨ F' (𝒯 x Ds') , ptt ⟩ 
             ⟨ F~ (𝒯 x Ds) (𝒯 x Ds') (lower (𝒯-consis x Ds Ds' Ds~)) , ptt ⟩ 
    , Ds~ ⟩ -}
  {- DComp-rest-pres (Every _~_) (replicate x ■) ■ ■ (𝒯 x) (𝒯 x) 
                  (λ T → 𝒜 x (Λ (F1 T))) ((λ T → 𝒜 x (Λ (F2 T)))) 
  (𝒯-consis x) (λ T T' T~ → 𝒜-consis x (Λ (F1 T)) (Λ (F2 T')) 
                            (Λ-consis (F1 T) (F2 T') (F~ T T' (lower T~)))) -}
𝕆-Clos3-consis app = ⋆-consis
𝕆-Clos3-consis (lit B k) = ℬ-consis B k
𝕆-Clos3-consis (tuple x) = 𝒯-consis x
𝕆-Clos3-consis (get x) = proj-consis x
𝕆-Clos3-consis inl-op = ℒ-consis
𝕆-Clos3-consis inr-op = ℛ-consis
𝕆-Clos3-consis case-op = 𝒞-consis
-}


open import Fold2 Op sig
open import NewSemantics Op sig public

instance
  Clos3-Semantics : Semantics
  Clos3-Semantics = record { interp-op = 𝕆-Clos3 ;
                             mono-op = 𝕆-Clos3-mono ;
                             error = ω }
open Semantics {{...}} public
