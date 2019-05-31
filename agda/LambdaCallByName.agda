open import Variables
open import Structures
open import Lambda
open Lambda.ASTMod
   using (`_; _⦅_⦆; Subst;
          exts; cons; bind; nil; rename; ⟪_⟫; subst-zero; _[_]; rename-id)
open Lambda.Reduction using (_—→_; ξ₁-rule; ξ₂-rule; β-rule; ζ-rule)
open import ValueBCD
open DomainAux domain
open OrderingAux domain ordering

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Product using (_×_; Σ; Σ-syntax; ∃; ∃-syntax; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim) renaming (⊥ to Bot)
open import Function using (_∘_)
open import Data.Unit using (⊤; tt)
open import Data.Empty renaming (⊥ to Bot)
open import Relation.Nullary using (¬_; Dec; yes; no)


module LambdaCallByName where

{-
module Preservation
  (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
  (ME : ModelExtra _●_)
  where

  module Den = LambdaDenot _●_
  open Den
  open ModelExtra ME
  open ModelBot MBot
  open ModelBasics MB
  open ModelCong Cong
  module RP = RenamePreserveReflect _●_ Cong
  open RP using (⊑-env; rename-pres)  
  module F = Filter _●_ MB
  open F using (ℰ-⊑; ℰ-⊔)
  open SubstPres _●_ MB


module SubstReflect
  (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
  (ME : ModelExtra _●_)
  where

  open Denot _●_
  open ModelExtra ME
  open ModelBot MBot
  open ModelBasics MB
  open ModelCong Cong
  open Filter _●_ MB using (ℰ-⊑; ℰ-⊔; WF)
  open RenamePreserveReflect _●_ Cong
     using (⊑-env; EnvExt⊑; rename-pres; rename-inc-reflect)  
  open Preservation _●_ ME using (ℰ-⊥)
  
  _var≟_ : ∀ {Γ} → (x y : Var Γ) → Dec (x ≡ y)
  Z var≟ Z  =  yes refl
  Z var≟ (S _)  =  no λ()
  (S _) var≟ Z  =  no λ()
  (S x) var≟ (S y) with  x var≟ y
  ...                 |  yes refl =  yes refl
  ...                 |  no neq   =  no λ{refl → neq refl}

  var≟-refl : ∀ {Γ} (x : Var Γ) → (x var≟ x) ≡ yes refl
  var≟-refl Z = refl
  var≟-refl (S x) rewrite var≟-refl x = refl

  const-env : ∀{Γ} → (x : Var Γ) → Value → Env Γ
  const-env x v y with x var≟ y
  ...             | yes _       = v
  ...             | no _        = ⊥

  nth-const-env : ∀{Γ} {x : Var Γ} {v} → (const-env x v) x ≡ v
  nth-const-env {x = x} rewrite var≟-refl x = refl

  diff-nth-const-env : ∀{Γ} {x y : Var Γ} {v}
    → x ≢ y
      -------------------
    → const-env x v y ≡ ⊥
  diff-nth-const-env {Γ} {x} {y} neq with x var≟ y
  ...  | yes eq  =  ⊥-elim (neq eq)
  ...  | no _    =  refl

  subst-reflect-var : ∀ {Γ Δ} {γ : Env Δ} {x : Var Γ} {v} {σ : Subst Γ Δ}
    → ℰ (σ x) γ v  →  γ `⊢ σ ↓ `⊥
      -----------------------------------------
    → Σ[ δ ∈ Env Γ ] γ `⊢ σ ↓ δ  ×  ℰ (` x) δ v
  subst-reflect-var {Γ}{Δ}{γ}{x}{v}{σ} xv γ⊢σ↓⊥
    rewrite sym (nth-const-env {Γ}{x}{v}) =
      ⟨ const-env x v , ⟨ const-env-ok , ⊑-refl ⟩ ⟩
    where
    const-env-ok : γ `⊢ σ ↓ const-env x v
    const-env-ok y with x var≟ y
    ... | yes x≡y rewrite sym x≡y | nth-const-env {Γ}{x}{v} = xv
    ... | no x≢y rewrite diff-nth-const-env {Γ}{x}{y}{v} x≢y = γ⊢σ↓⊥ y

{-
  subst-⊥ : ∀{Γ Δ}{γ : Env Δ}{σ : Subst Γ Δ}
      -----------------
    → γ `⊢ σ ↓ `⊥
  subst-⊥ {σ = σ} x = ℰ-⊥ {M = σ x}
-}

  subst-⊔ : ∀{Γ Δ}{γ : Env Δ}{γ₁ γ₂ : Env Γ}{σ : Subst Γ Δ}
             → γ `⊢ σ ↓ γ₁
             → γ `⊢ σ ↓ γ₂
               -------------------------
             → γ `⊢ σ ↓ (γ₁ `⊔ γ₂)
  subst-⊔ {σ = σ} γ₁-ok γ₂-ok x = ℰ-⊔ {M = σ x} (γ₁-ok x) (γ₂-ok x)

  split : ∀ {Γ} {M : Term (suc Γ)} {δ : Env (suc Γ)} {v}
    → ℰ M δ v
      ------------------------
    → ℰ M (init δ `, last δ) v
  split {δ = δ} δMv rewrite init-last δ = δMv

  δu⊢extσ⊥ : ∀{Γ}{Δ}{δ : Env Δ}{σ : Subst Γ Δ}{u}
           → δ `⊢ σ ↓ `⊥ → δ `, u `⊢ exts σ ↓ `⊥
  δu⊢extσ⊥ δ⊢σ↓⊥ Z = ⊑-⊥
  δu⊢extσ⊥ {σ = σ} δ⊢σ↓⊥ (S x) =
     rename-pres {M = σ x} S_ (λ x₁ → ⊑-refl) (δ⊢σ↓⊥ x)

  subst-reflect : ∀ {Γ Δ} {δ : Env Δ} {M : Term Γ} {L : Term Δ}
                    {σ : Subst Γ Δ} {v}
    → ℰ L δ v
    → L ≡ ⟪ σ ⟫ M
    → δ `⊢ σ ↓ `⊥
      --------------------------------------------
    → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℰ M γ v
  subst-reflect {δ = δ}{` x}{L}{σ} ℰLδv L≡σM δ⊢σ↓⊥ rewrite L≡σM =
      subst-reflect-var{σ = σ} ℰLδv δ⊢σ↓⊥
  subst-reflect {Γ}{Δ}{δ}{lam ⦅ bind N nil ⦆} {L} {σ} {v} ℰLδv L≡σM δ⊢σ↓⊥
      rewrite L≡σM
      = G {v} ℰLδv
      where
      G : ∀{v}
        → ℱ (ℰ (⟪ exts σ ⟫ N)) δ v
        → Σ[ γ ∈ Env Γ ] δ `⊢ σ ↓ γ  ×  ℱ (ℰ N) γ v
      G {⊥} tt = ⟨ `⊥ , ⟨ δ⊢σ↓⊥ , tt  ⟩ ⟩
      G {u ↦ w} ℰLδv
          with subst-reflect {δ = δ `, u} {M = N} {L = ⟪ exts σ ⟫ N}
                   {σ = exts σ} {w} ℰLδv refl (δu⊢extσ⊥ δ⊢σ↓⊥)
      ... | ⟨ γ , ⟨ subst-γ , m ⟩ ⟩ =
            ⟨ init γ ,
            ⟨ (λ x → rename-inc-reflect {M = σ x} (subst-γ (S x))) ,
              (let m' = split{M = N} m in
               EnvExt⊑{M = N} m' (subst-γ Z)) ⟩ ⟩
      G {u ⊔ w} ⟨ aa , bb ⟩ 
          with G {u} aa | G {w} bb
      ... | ⟨ δ₁ , ⟨ subst-δ₁ , m1 ⟩ ⟩ | ⟨ δ₂ , ⟨ subst-δ₂ , m2 ⟩ ⟩ =
         ⟨ δ₁ `⊔ δ₂ ,
         ⟨ subst-⊔ {σ = σ} subst-δ₁ subst-δ₂ ,
         ⟨ ⊑-env{Γ}{δ₁}{δ₁ `⊔ δ₂}{lam ⦅ bind N nil ⦆}{u}m1(EnvConjR1⊑ δ₁ δ₂) ,
           ⊑-env{Γ}{δ₂}{δ₁ `⊔ δ₂}{lam ⦅ bind N nil ⦆}{w}m2(EnvConjR2⊑ δ₁ δ₂) ⟩
           ⟩ ⟩
  subst-reflect {Γ}{Δ}{δ}{app ⦅ cons L (cons M nil) ⦆}{_}{σ}{v} ℰσL●ℰσMδv
                L≡σM δ⊢σ↓⊥
      {- ●-≡ IS A PROBLEM FOR CBV!! NEED TO ABSTRACT! -}
      rewrite L≡σM | ●-≡ {Δ}{ℰ (⟪ σ ⟫ L)}{ℰ (⟪ σ ⟫ M)}{δ}{v}
      with ℰσL●ℰσMδv
  ... | inj₁ v⊑⊥ = 
        ⟨ `⊥ , ⟨ δ⊢σ↓⊥ , ℰ-⊑{M = L · M} (ℰ-⊥{M = L · M}) v⊑⊥  ⟩ ⟩
  ... | inj₂ ⟨ u , ⟨ ℰσLδu↦v , ℰσMδu ⟩ ⟩
      with subst-reflect{M = L} ℰσLδu↦v refl δ⊢σ↓⊥
         | subst-reflect{M = M} ℰσMδu refl δ⊢σ↓⊥
  ... | ⟨ δ₁  , ⟨ subst-δ₁ , ℰLδ₁u↦v ⟩ ⟩
      | ⟨ δ₂  , ⟨ subst-δ₂ , ℰMδ₂u ⟩ ⟩ =
        ⟨ (δ₁ `⊔ δ₂) ,
        ⟨ (subst-⊔ {γ₁ = δ₁}{γ₂ = δ₂}{σ = σ} subst-δ₁ subst-δ₂) ,
          G ⟩ ⟩
        where
        ℰLδ₁⊔δ₂u↦v : ℰ L (λ z → (δ₁ `⊔ δ₂) z) (u ↦ v)
        ℰLδ₁⊔δ₂u↦v = ⊑-env{M = L} ℰLδ₁u↦v (EnvConjR1⊑ δ₁ δ₂)

        ℰMδ₁⊔δ₂u  : ℰ M (λ z → (δ₁ `⊔ δ₂) z) u
        ℰMδ₁⊔δ₂u = ⊑-env{M = M} ℰMδ₂u (EnvConjR2⊑ δ₁ δ₂)

        G : (ℰ L ● ℰ M) (δ₁ `⊔ δ₂) v
        G rewrite ●-≡ {Γ}{ℰ L}{ℰ M}{δ₁ `⊔ δ₂}{v} =
          inj₂ ⟨ u , ⟨ ℰLδ₁⊔δ₂u↦v , ℰMδ₁⊔δ₂u ⟩ ⟩

  subst-zero-reflect : ∀ {Δ} {δ : Env Δ} {γ : Env (suc Δ)} {M : Term Δ}
    → δ `⊢ subst-zero M ↓ γ
      ----------------------------------------
    → Σ[ w ∈ Value ] γ `⊑ (δ `, w) × ℰ M δ w
  subst-zero-reflect {δ = δ} {γ = γ} δσγ = ⟨ last γ , ⟨ lemma , δσγ Z ⟩ ⟩   
    where
    lemma : γ `⊑ (δ `, last γ)
    lemma Z  =  ⊑-refl
    lemma (S x) = δσγ (S x)

  subst-zero-⊥ : ∀{Γ}{γ : Env Γ}{M : Term Γ}
               → ℰ M γ ⊥
               → γ `⊢ subst-zero M ↓ `⊥
  subst-zero-⊥ ℰMγ⊥ Z = ℰMγ⊥
  subst-zero-⊥ ℰMγ⊥ (S x) = ⊑-⊥

  substitution-reflect : ∀ {Δ} {δ : Env Δ} {N : Term (suc Δ)} {M : Term Δ} {v}
    → ℰ (N [ M ]) δ v  → ℰ M δ ⊥
      ------------------------------------------------
    → Σ[ w ∈ Value ] ℰ M δ w  ×  ℰ N (δ `, w) v
  substitution-reflect{N = N}{M = M} ℰNMδv ℰMδ⊥
       with subst-reflect {M = N} ℰNMδv refl (subst-zero-⊥ ℰMδ⊥)
  ...  | ⟨ γ , ⟨ δσγ , γNv ⟩ ⟩
       with subst-zero-reflect δσγ
  ...  | ⟨ w , ⟨ γ⊑δw , δMw ⟩ ⟩ =
         ⟨ w , ⟨ δMw , ⊑-env {M = N} γNv γ⊑δw ⟩ ⟩


module Reflect
  (_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ)
  (ME : ModelExtra _●_)
  where

  open Denot _●_
  open ModelExtra ME
  open ModelBot MBot
  open ModelBasics MB
  open ModelCong Cong

  cong-● : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
            {D₁′ D₂′ : Denotation Δ}
         → D₁ γ ≃ D₁′ δ → D₂ γ ≃ D₂′ δ → (D₁ ● D₂) γ ≃ (D₁′ ● D₂′) δ
  cong-● {γ = γ}{δ}{D₁}{D₂}{D₁′}{D₂′} eq1 eq2 {w} =
    ⟨ (●-≲{D₁ = D₁}{D₂}{D₁′}{D₂′} (proj₁ eq1) (proj₁ eq2)) {v = w} ,
      (●-≲{D₁ = D₁′}{D₂′}{D₁}{D₂} (proj₂ eq1) (proj₂ eq2)) {v = w} ⟩


  module RP = RenamePreserveReflect _●_ Cong
  open RP using (⊑-env; EnvExt⊑; rename-pres; rename-inc-reflect)  

  module F = Filter _●_ MB
  open F using (ℰ-⊑; ℰ-⊔; WF)

  open Preservation _●_ ME using (ℰ-⊥)

  open SubstReflect _●_ ME

  reflect-beta : ∀{Γ}{γ : Env Γ}{M N}{v}
      → ℰ (N [ M ]) γ v
      → ℰ ((ƛ N) · M) γ v
  reflect-beta {Γ}{γ}{M}{N}{v} d 
      with substitution-reflect{N = N}{M = M} d (ℰ-⊥ {M = M})
  ... | ⟨ v₂′ , ⟨ d₁′ , d₂′ ⟩ ⟩ rewrite ●-≡ {Γ}{ℱ (ℰ N)}{ℰ M}{γ}{v} =
        inj₂ ⟨ v₂′ , ⟨ d₂′ , d₁′ ⟩ ⟩

  reflect : ∀ {Γ} {γ : Env Γ} {M M′ N v}
    →  M —→ M′  →   M′ ≡ N  →  ℰ N γ v
      --------------------------------
    → ℰ M γ v    
  reflect {γ = γ} (ξ₁-rule {L = L}{L′}{M} L—→L′) L′·M≡N
      rewrite sym L′·M≡N =
      ●-≲ (reflect L—→L′ refl) (≲-refl {d = ℰ M γ})
  reflect {γ = γ} (ξ₂-rule {L = L}{M}{M′} M—→M′) L·M′≡N
      rewrite sym L·M′≡N =
      ●-≲ (≲-refl {d = ℰ L γ}) (reflect M—→M′ refl)
  reflect (β-rule {N = N}{M = M}) M′≡N rewrite sym M′≡N =
      reflect-beta {M = M}{N}
  reflect {v = v} (ζ-rule {Γ}{N}{N′} N—→N′) M′≡N rewrite sym M′≡N =
      ℱ-≲ (reflect N—→N′ refl) {v}
-}



infixl 7 _●_
_●_ : ∀{Γ} → Denotation Γ → Denotation Γ → Denotation Γ
_●_ {Γ} D₁ D₂ γ w = w ⊑ ⊥ ⊎ Σ[ v ∈ Value ] D₁ γ (v ↦ w) × D₂ γ v 

model : LambdaModel
model = record { _●_ = _●_ ; ℱ = ℱ }

●-≲ : ∀{Γ Δ}{γ : Env Γ}{δ : Env  Δ}{D₁ D₂ : Denotation Γ}
          {D₁′ D₂′ : Denotation Δ}
       → D₁ γ ≲ D₁′ δ  →  D₂ γ ≲ D₂′ δ
       → (D₁ ● D₂) γ ≲ (D₁′ ● D₂′) δ
●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w} (inj₁ w⊑⊥) =
   inj₁ w⊑⊥
●-≲ {γ = γ} {δ} {D₁} {D₂} {D₁′} {D₂′} D₁γ≲D₁′δ D₂γ≲D₂′δ {w}
    (inj₂ ⟨ v , ⟨ fst₁ , snd ⟩ ⟩)
    with D₁γ≲D₁′δ {w} | D₂γ≲D₂′δ {w}
... | a | b = inj₂ ⟨ v , ⟨ (D₁γ≲D₁′δ fst₁) , (D₂γ≲D₂′δ snd) ⟩ ⟩

●-⊔ : ∀{Γ}{D₁ D₂ : Denotation Γ}{γ : Env Γ} {u v : Value}
    → WFDenot Γ D₁ → WFDenot Γ D₂
    → (D₁ ● D₂) γ u → (D₁ ● D₂) γ v → (D₁ ● D₂) γ (u ⊔ v)
●-⊔ {u = u} {v} wf1 wf2 (inj₁ u⊑⊥) (inj₁ v⊑⊥) = inj₁ (⊑-conj-L u⊑⊥ v⊑⊥)
●-⊔ {u = u} {v} wf1 wf2 (inj₁ u⊑⊥) (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) =
  inj₂ ⟨ v' , ⟨ WFDenot.⊑-closed wf1 fst₁ lt , snd ⟩ ⟩
  where lt : v' ↦ (u ⊔ v) ⊑ v' ↦ v
        lt = ⊑-fun ⊑-refl (⊑-conj-L (⊑-trans u⊑⊥ ⊑-⊥) ⊑-refl)
●-⊔ {u = u} {v} wf1 wf2 (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩) (inj₁ v⊑⊥) =
  inj₂ ⟨ u' , ⟨ (WFDenot.⊑-closed wf1 fst₁ lt) , snd ⟩ ⟩
  where lt : u' ↦ (u ⊔ v) ⊑ u' ↦ u
        lt = ⊑-fun ⊑-refl (⊑-conj-L ⊑-refl (⊑-trans v⊑⊥ ⊑-⊥))
●-⊔ {Γ}{D₁}{D₂}{γ}{u}{v} wf1 wf2 (inj₂ ⟨ u' , ⟨ fst₁ , snd ⟩ ⟩)
                    (inj₂ ⟨ v' , ⟨ fst₃ , snd₁ ⟩ ⟩) =
  let a = WFDenot.⊔-closed wf1 fst₁ fst₃ in                      
  inj₂ ⟨ (u' ⊔ v') ,
       ⟨ WFDenot.⊑-closed wf1 a Dist⊔↦⊔ ,
         WFDenot.⊔-closed wf2 snd snd₁ ⟩ ⟩


●-⊑ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ} {v w : Value}
    → WFDenot Γ D₁ → (D₁ ● D₂) γ v → w ⊑ v
    → (D₁ ● D₂) γ w
●-⊑ d (inj₁ x) w⊑v = inj₁ (⊑-trans w⊑v x)
●-⊑ {v = v}{w} d (inj₂ ⟨ v' , ⟨ fst₁ , snd ⟩ ⟩) w⊑v =
  inj₂ ⟨ v' , ⟨ WFDenot.⊑-closed d fst₁ lt  , snd ⟩ ⟩
  where lt : v' ↦ w ⊑ v' ↦ v
        lt = ⊑-fun ⊑-refl w⊑v

●-⊥ : ∀{Γ}{D₁ D₂ : Denotation Γ} {γ : Env Γ}
    → (D₁ ● D₂) γ ⊥
●-⊥ = inj₁ ⊑-⊥

ℱ-inv : ∀{Γ}{D : Denotation (suc Γ)}{γ : Env Γ}{u : Value}
      → ℱ D γ u
      → u ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] Σ[ w ∈ Value ] D (γ `, v) w × v ↦ w ⊑ u)
ℱ-inv {u = ⊥} tt = inj₁ ⊑-refl
ℱ-inv {u = v ↦ w} ℱDγu = inj₂ ⟨ v , ⟨ w , ⟨ ℱDγu , ⊑-refl ⟩ ⟩ ⟩
ℱ-inv {u = u ⊔ v} ⟨ fst , snd ⟩
    with ℱ-inv{u = u} fst | ℱ-inv{u = v} snd
... | inj₁ u⊑⊥ | inj₁ v⊑⊥ = inj₁ (⊑-conj-L u⊑⊥ v⊑⊥)
... | inj₁ u⊑⊥ | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ =
      inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R2 v'↦w'⊑v ⟩ ⟩ ⟩
... | inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , v'↦w'⊑v ⟩ ⟩ ⟩ | _ =
      inj₂ ⟨ v' , ⟨ w' , ⟨ Dγv'w' , ⊑-conj-R1 v'↦w'⊑v ⟩ ⟩ ⟩

model_basics : LambdaModelBasics model
model_basics = (record { ℱ-≲ = ℱ-≲ ;
               ●-≲ = λ {Γ}{Δ}{γ}{δ}{D₁}{D₂}{D₁′}{D₂′} x y →
                       ●-≲ {D₁ = D₁}{D₂ = D₂}{D₁′ = D₁′}{D₂′ = D₂′} x y;
               ℱ-⊑ = ℱ-⊑;
               ●-⊑ = λ {Γ}{D₁}{D₂} a b c → ●-⊑ {D₂ = D₂} a b c;
               ℱ-⊔ = λ {Γ}{D}{γ}{u}{v} → ℱ-⊔{D = D}{γ}{u}{v} ;
               ●-⊔ = ●-⊔
               })

open import RenamePreserveReflect domain ordering model model_basics
  using (⊑-env)  
open import Filter domain ordering model model_basics
open import SubstitutionPreserve domain ordering model model_basics

open LambdaDenot domain ordering model

ℱ●-inv : ∀{Γ} {D₁ : Denotation (suc Γ)}{D₂ : Denotation Γ}{γ : Env Γ}
          {w : Value}
        → (ℱ D₁ ● D₂) γ w
        → w ⊑ ⊥ ⊎ (Σ[ v ∈ Value ] D₁ (γ `, v) w × D₂ γ v)
ℱ●-inv {Γ}{D₁}{D₂}{γ}{w} ℱD₁●D₂γw
    with ℱD₁●D₂γw
... | inj₁ w⊑⊥ = inj₁ w⊑⊥ 
... | inj₂ ⟨ v , ⟨ ℱD₁γv↦w , D₂γv ⟩ ⟩ =
      inj₂ ⟨ v , ⟨ ℱD₁γv↦w , D₂γv ⟩ ⟩

ℰ-⊥ : ∀{Γ}{γ : Env Γ}{M : Term Γ}
    → ℰ M γ ⊥
ℰ-⊥ {M = ` x} = ⊑-⊥
ℰ-⊥ {Γ}{γ}{M = lam ⦅ bind N nil ⦆} = ℱ-⊥ {Γ}{ℰ N}{γ}
ℰ-⊥ {M = app ⦅ cons L (cons M nil) ⦆} = inj₁ ⊑-⊥

preserve : ∀ {Γ} {γ : Env Γ} {M N v}
  → M —→ N
  → ℰ M γ v
    ----------
  → ℰ N γ v
preserve {γ = γ} (ξ₁-rule{L = L}{L´}{M} L—→L′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L´}{D₂′ = ℰ M}
              (λ x → preserve L—→L′ x)
              (λ x → x)
preserve {γ = γ} (ξ₂-rule{L = L}{M}{M′} M—→M′) =
  ●-≲ {γ = γ}{γ}{D₁ = ℰ L}{D₂ = ℰ M}{D₁′ = ℰ L}{D₂′ = ℰ M′}
              (λ x → x)
              (λ x → preserve M—→M′ x)
preserve (β-rule{N = N}{M = M}) ℱℰN●ℰMγw 
    with ℱ●-inv ℱℰN●ℰMγw
... | inj₁ w⊑⊥ =
    ℰ-⊑ {M = ⟪ subst-zero M ⟫ N} (ℰ-⊥{M = ⟪ subst-zero M ⟫ N}) w⊑⊥
... | inj₂ ⟨ v , ⟨ ℰNγvw , ℰMγv ⟩ ⟩ = 
    substitution{N = N}{M = M} {v} ℰNγvw ℰMγv
preserve {v = v} (ζ-rule {Γ}{N}{N′} N—→N′) = ℱ-≲ (preserve N—→N′) {v}

