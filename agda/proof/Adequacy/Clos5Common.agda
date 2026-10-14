{-

  Definitions shared by the soundness and adequacy proofs for the Clos5ᵀ
  machine (see proof/Adequacy/Clos5.agda):

  * runs of the machine of a table ds from any state, evaluation of a
    term to a value (⇓) and its determinism, observed at every type
    through a continuation that ends in halt (probe);
  * the definitions older than a definition f (older f, drop f), and
    what the semantics makes of the table: definition f means its code
    with the table of the older ones (table-at), and the older
    definitions mean the same in the table of all of them as in their
    own (agree);
  * inversions of the operators whose elements have one shape.

-}

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_)
open import Language.Typed.Type renaming (_≟_ to _≟F_)
open import Language.Typed.Clos5

module proof.Adequacy.Clos5Common {Σ : List ℕ} (ds : All (Code Σ) Σ) where

open import Framework.Primitives using (Base; base-rep)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩) renaming (const to dconst)
open import proof.Framework.GraphModel.Ops using (ℬ; pair; 𝒯; nthD) renaming (inl to inlD; inr to inrD)
open import Semantics.Graph.Typed.Ops using (Table; tables)
open import Semantics.CEK.Typed.Clos5
open import Framework.Lookup using (_!_)
open import proof.Framework.Runs using (module Runs)

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (reverse; _++_)
open import Data.List.Properties using (unfold-reverse; ++-assoc; ++-identityʳ; length-reverse)
open import Data.Nat.Properties using (<-irrefl; <-trans; ≤-refl; m<n⇒m<1+n; +-identityʳ)
open import Data.Product using (_×_; Σ-syntax; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Data.Vec using (Vec; []; _∷_; toList; fromList; replicate)
open import Data.Vec.Properties using (toList∘fromList)
open import Framework.VecUtil using (toVec; collected)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)

open Runs (step ds) public

{- Levels ----------------------------------------------------------------------}

lvl< : ∀ {A : Set} {Γ : List A} {a} (x : Γ ∋ a) → lvl x < length Γ
lvl< Z = ≤-refl
lvl< (S x) = m<n⇒m<1+n (lvl< x)

{- an index is determined by its level -}
lvl-inj : ∀ {Γ : List ℕ} {m n} (f : Γ ∋ m) (g : Γ ∋ n) → lvl f ≡ lvl g → _≡_ {A = ∃[ k ] Γ ∋ k} ⟨ m , f ⟩ ⟨ n , g ⟩
lvl-inj Z Z e = refl
lvl-inj Z (S g) e = ⊥-elim (<-irrefl (sym e) (lvl< g))
lvl-inj (S f) Z e = ⊥-elim (<-irrefl e (lvl< f))
lvl-inj (S f) (S g) e with lvl-inj f g e
... | refl = refl

{- The older definitions ---------------------------------------------------------}

older : ∀ {ns : List ℕ} {n} → ns ∋ n → List ℕ
older {_ ∷ ns} Z = ns
older (S f) = older f

drop : ∀ {P : ℕ → Set} {ns n} (f : ns ∋ n) → All P ns → All P (older f)
drop Z (_ ∷ ps) = ps
drop (S f) (_ ∷ ps) = drop f ps

older-lvl : ∀ {ns : List ℕ} {n} (f : ns ∋ n) → length (older f) ≡ lvl f
older-lvl Z = refl
older-lvl (S f) = older-lvl f

module _ {D : ℕ → Set} (cd : Table Σ → ∀ {n} → D n → 𝒫 Value) where

  {- definition g of a part ps of the table, reached through r -}
  table-at′ : ∀ {ns} (ps : All D ns) (r : ∀ {n} → ns ∋ n → Σ ∋ n) → (∀ {n} (g : ns ∋ n) → lvl (r g) ≡ lvl g)
    → ∀ {n} (g : ns ∋ n) → tables cd ps (r g) ≡ cd (tables cd (drop g ps)) (ps ! g)
  table-at′ {_ ∷ ns} (p ∷ ps) r rl Z with lvl (r Z) ≟ length ns
  ... | yes _ = refl
  ... | no ne = ⊥-elim (ne (rl Z))
  table-at′ {_ ∷ ns} (p ∷ ps) r rl (S g) with lvl (r (S g)) ≟ length ns
  ... | yes e = ⊥-elim (<-irrefl (trans (sym (rl (S g))) e) (lvl< g))
  ... | no _ = table-at′ ps (λ x → r (S x)) (λ x → rl (S x)) g

  {- the definitions older than f mean the same without the newer ones -}
  agree : ∀ {ns n} (ps : All D ns) (f : ns ∋ n) {m} (g : Σ ∋ m) → lvl g < length (older f)
    → tables cd ps g ≡ tables cd (drop f ps) g
  agree {_ ∷ ns} (p ∷ ps) Z g g< with lvl g ≟ length ns
  ... | yes e = ⊥-elim (<-irrefl e g<)
  ... | no _ = refl
  agree {_ ∷ ns} (p ∷ ps) (S f) g g< with lvl g ≟ length ns
  ... | yes e = ⊥-elim (<-irrefl e (<-trans g< (subst (_< length ns) (sym (older-lvl f)) (lvl< f))))
  ... | no _ = agree ps f g g<

table-at : ∀ {D : ℕ → Set} (cd : Table Σ → ∀ {n} → D n → 𝒫 Value) (ps : All D Σ)
  → ∀ {n} (f : Σ ∋ n) → tables cd ps f ≡ cd (tables cd (drop f ps)) (ps ! f)
table-at cd ps = table-at′ cd ps (λ x → x) (λ _ → refl)

{- Evaluation ----------------------------------------------------------------------}

infix 4 _⊢_⇓_
_⊢_⇓_ : ∀ {Γ A} → Env Σ Γ → Tm Σ Γ A → Val Σ A → Set
γ ⊢ M ⇓ v = ∀ κ → eval M γ κ ↠ ret v κ

{- a value of each type, observed through a continuation that halts -}
unit-tup : ∀ n → Val Σ ⟪ tup n ⟫
unit-tup n = tup (replicate n (dyn (tup 0) (tup [])))

K₀ : ∀ A → Cont Σ A
K₀ Any = halt
K₀ ⟪ G ⟫ = injK G halt
K₀ (code n) = letK (inject fun (pack (` Z) (` (S Z)))) (unit-tup n ∷ []) halt

W : ∀ {A} → Val Σ A → Val Σ Any
W {Any} v = v
W {⟪ G ⟫} v = dyn G v
W {code n} v = dyn fun (pack v (unit-tup n))

probe : ∀ {A} (v : Val Σ A) → ret v (K₀ A) ↠ ret (W v) halt
probe {Any} v = done
probe {⟪ G ⟫} v = refl ∷↠ done
probe {code n} v = refl ∷↠ refl ∷↠ refl ∷↠ refl ∷↠ refl ∷↠ refl ∷↠ refl ∷↠ refl ∷↠ done

W-inj : ∀ {A} {v₁ v₂ : Val Σ A} → W v₁ ≡ W v₂ → v₁ ≡ v₂
W-inj {Any} e = e
W-inj {⟪ G ⟫} refl = refl
W-inj {code n} refl = refl

private
  ret-inj : ∀ {a b : Val Σ Any} → ret a halt ≡ ret b halt → a ≡ b
  ret-inj refl = refl

⇓-det : ∀ {Γ A} {γ : Env Σ Γ} {M : Tm Σ Γ A} {v₁ v₂} → γ ⊢ M ⇓ v₁ → γ ⊢ M ⇓ v₂ → v₁ ≡ v₂
⇓-det {A = A} {v₁ = v₁} {v₂} e₁ e₂ =
  W-inj (ret-inj (↠-final-det (e₁ (K₀ A) ++↠ probe v₁) (e₂ (K₀ A) ++↠ probe v₂) refl refl))

{- the values of a tuple's components ---------------------------------------------}

data Evals {Γ} (γ : Env Σ Γ) : ∀ {j} → Vec (Tm Σ Γ Any) j → List (Val Σ Any) → Set where
  [] : Evals γ [] []
  _∷_ : ∀ {j M v} {Ms : Vec _ j} {vs} → γ ⊢ M ⇓ v → Evals γ Ms vs → Evals γ (M ∷ Ms) (v ∷ vs)

toList-toVec : ∀ {A : Set} {n} (xs : List A) (e : length xs ≡ n) → toList (toVec xs e) ≡ xs
toList-toVec xs refl = toList∘fromList xs

toList-collected : ∀ {n} (vs : List (Val Σ Any)) (e : length vs Data.Nat.+ 0 ≡ n) → toList (collected vs e) ≡ reverse vs
toList-collected vs e = toList-toVec (reverse vs) (trans (length-reverse vs) (trans (sym (+-identityʳ _)) e))

tuple-run : ∀ {Γ n j} {γ : Env Σ Γ} acc (Ms : Vec (Tm Σ Γ Any) j) vs (e : length acc Data.Nat.+ j ≡ n)
  → Evals γ Ms vs
  → Σ[ ws ∈ Vec (Val Σ Any) n ] (∀ κ → tuple-next acc Ms γ e κ ↠ ret (tup ws) κ) × toList ws ≡ reverse acc ++ vs
tuple-run acc [] [] e [] = ⟨ collected acc e , ⟨ (λ κ → done) , trans (toList-collected acc e) (sym (++-identityʳ _)) ⟩ ⟩
tuple-run {γ = γ} acc (M ∷ Ms) (v ∷ vs) e (ev ∷ evs) with tuple-run (v ∷ acc) Ms vs _ evs
... | ⟨ ws , ⟨ τ , eq ⟩ ⟩ =
  ⟨ ws , ⟨ (λ κ → ev (tupK acc Ms γ e κ) ++↠ refl ∷↠ τ κ)
       , trans eq (trans (cong (_++ vs) (unfold-reverse v acc)) (++-assoc (reverse acc) (v ∷ []) vs)) ⟩ ⟩

{- Inversions ------------------------------------------------------------------------}

ℬ-inv : ∀ {B} {k : base-rep B} d → d ∈ ℬ B k ptt → d ≡ dconst k
ℬ-inv (dconst k) ⟨ refl , refl ⟩ = refl
ℬ-inv (V ↦ w) ()
ℬ-inv ν ()
ℬ-inv ω ()
ℬ-inv ⦅ u , v ⦆ ()
ℬ-inv (tup[ i ] d) ()
ℬ-inv (left d) ()
ℬ-inv (right d) ()
ℬ-inv ⟨⟩ ()

pair-inv : ∀ {D E} d → d ∈ pair ⟨ D , ⟨ E , ptt ⟩ ⟩ → Σ[ u ∈ Value ] Σ[ u' ∈ Value ] d ≡ ⦅ u , u' ⦆ × u ∈ D × u' ∈ E
pair-inv ⦅ u , u' ⦆ ⟨ u∈ , u'∈ ⟩ = ⟨ u , ⟨ u' , ⟨ refl , ⟨ u∈ , u'∈ ⟩ ⟩ ⟩ ⟩
pair-inv (dconst k) ()
pair-inv (V ↦ w) ()
pair-inv ν ()
pair-inv ω ()
pair-inv (tup[ i ] d) ()
pair-inv (left d) ()
pair-inv (right d) ()
pair-inv ⟨⟩ ()

inl-inv : ∀ {D} d → d ∈ inlD ⟨ D , ptt ⟩ → Σ[ u ∈ Value ] d ≡ left u × u ∈ D
inl-inv (left u) u∈ = ⟨ u , ⟨ refl , u∈ ⟩ ⟩
inl-inv (dconst k) ()
inl-inv (V ↦ w) ()
inl-inv ν ()
inl-inv ω ()
inl-inv ⦅ u , v ⦆ ()
inl-inv (tup[ i ] d) ()
inl-inv (right d) ()
inl-inv ⟨⟩ ()

inr-inv : ∀ {D} d → d ∈ inrD ⟨ D , ptt ⟩ → Σ[ u ∈ Value ] d ≡ right u × u ∈ D
inr-inv (right u) u∈ = ⟨ u , ⟨ refl , u∈ ⟩ ⟩
inr-inv (dconst k) ()
inr-inv (V ↦ w) ()
inr-inv ν ()
inr-inv ω ()
inr-inv ⦅ u , v ⦆ ()
inr-inv (tup[ i ] d) ()
inr-inv (left d) ()
inr-inv ⟨⟩ ()

{- an element of a tuple of n components -}
𝒯-inv : ∀ n {Ds} d → d ∈ 𝒯 n Ds
  → (n ≡ 0 × d ≡ ⟨⟩) ⊎ Σ[ m ∈ ℕ ] Σ[ i ∈ Fin (suc m) ] Σ[ u ∈ Value ] Σ[ e ∈ n ≡ suc m ]
       d ≡ tup[ i ] u × u ∈ nthD Ds (subst Fin (sym e) i) × (∀ j → nonempty (nthD Ds j))
𝒯-inv zero ⟨⟩ _ = inj₁ ⟨ refl , refl ⟩
𝒯-inv (suc n) (tup[ i ] u) ⟨ refl , ⟨ u∈ , ne ⟩ ⟩ = inj₂ ⟨ n , ⟨ i , ⟨ u , ⟨ refl , ⟨ refl , ⟨ u∈ , ne ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
𝒯-inv zero (tup[ i ] u) ()
𝒯-inv (suc n) ⟨⟩ ()
𝒯-inv zero (dconst k) ()
𝒯-inv (suc n) (dconst k) ()
𝒯-inv zero (V ↦ w) ()
𝒯-inv (suc n) (V ↦ w) ()
𝒯-inv zero ν ()
𝒯-inv (suc n) ν ()
𝒯-inv zero ω ()
𝒯-inv (suc n) ω ()
𝒯-inv zero ⦅ u , v ⦆ ()
𝒯-inv (suc n) ⦅ u , v ⦆ ()
𝒯-inv zero (left d) ()
𝒯-inv (suc n) (left d) ()
𝒯-inv zero (right d) ()
𝒯-inv (suc n) (right d) ()
