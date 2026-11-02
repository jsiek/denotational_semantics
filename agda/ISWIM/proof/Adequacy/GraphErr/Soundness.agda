{-

  Soundness of the ISWIM machine with respect to the graph model
  with errors (Semantics/GraphErr/ISWIM.agda): what the machine computes
  is in the denotation of the program, and when it stops with an error,
  ω is. The structure is that of proof/Adequacy/GraphErr/Soundness.agda:
  each machine state denotes a set (𝒮), each step can only shrink it.

  The monad does the error bookkeeping:
  * a continuation passes on ω (𝒦-ω): an erring operand errs in its bind,
    whatever the operator; a later operand errs once the earlier ones,
    values, have been bound;
  * a check of the machine fails on a value of another kind (𝒱-bad): the
    elements of the denotation of a value are of its kind (𝒱-kind), so
    the kernel's check errs;
  * β for a value is the monad's left unit (letᵐ-β, 𝒞ᵐ-inl-β).

-}

module proof.Adequacy.GraphErr.Soundness where

open import Framework.Primitives using (Base; base-rep; Int; Nat; 𝔹; Unit; Void; Blame)
open import Language.Prim using (Out; int; bool; δ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _~_; Con; Con-env; Con-⌈⌉; Con-⊆; ρ₀)
  renaming (const to dconst)
open import proof.Framework.GraphModel.OpsBase using (ℬ; nthD; ℬ-consis)
open import proof.Framework.GraphModel.ErrorMonad renaming (Val to Valᴰ)
open import proof.Framework.GraphModel.ContinuityBase using (mono; consis)
open import proof.Semantics.GraphErr.Prim using (primᵐ; primᵐ-good) renaming (out to dout)
open import proof.Framework.GraphModel.DenotProperties using (Every)
open import proof.Framework.GraphModel.DOpSig using (Results)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Relation.Nullary using (yes; no; ¬_)
open import Level using (lift; lower)
open import Language.ISWIM
open import proof.Semantics.GraphErr.ISWIM
  using (⟦_⟧; ⟦_⟧₊; ⟦⟧-monotone; ISWIMᵐ-con-env; body-mono; body-continuous)
import proof.Framework.GraphModel.Env
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Star; Terminates; next; stop)
open import proof.Framework.ListUtil
open import Semantics.CEK.ISWIM hiding (inl; inr)
import Semantics.CEK.ISWIM as T using (inl; inr)
open import proof.Adequacy.Common

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Data.List.Base using (reverseAcc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

VEnv : Set₁
VEnv = proof.Framework.GraphModel.Env.Env Value

{- Tuples of lists of sets, under binds ------------------------------------------}

At : ∀ {n} → Fin n → List (𝒫 Value) → Value → Set
At {suc n} zero (D ∷ Ds) d = length Ds ≡ n × d ∈ D
At (suc i) (D ∷ Ds) d = At i Ds d
At _ [] d = ⊥

AllNE : List (𝒫 Value) → Set
AllNE [] = ⊤
AllNE (D ∷ Ds) = nonempty D × AllNE Ds

Null : List (𝒫 Value) → Set
Null [] = ⊤
Null (D ∷ Ds) = ⊥

{- the graph model's tuple, of a list of sets -}
𝒯P : List (𝒫 Value) → 𝒫 Value
𝒯P Ds ⟨⟩ = Null Ds
𝒯P Ds (tup[ i ] d) = At i Ds d × AllNE Ds
𝒯P Ds _ = ⊥

{- bind a list of sets, left to right -}
bindL : List (𝒫 Value) → (List (𝒫 Value) → 𝒫 Value) → 𝒫 Value
bindL [] K = K []
bindL (D ∷ Ds) K = D ≫= λ X → bindL Ds (λ Xs → K (X ∷ Xs))

𝒯L : List (𝒫 Value) → 𝒫 Value
𝒯L Ds = bindL Ds 𝒯P

infix 4 _⊆L_
_⊆L_ : List (𝒫 Value) → List (𝒫 Value) → Set
[] ⊆L [] = ⊤
(D ∷ Ds) ⊆L (E ∷ Es) = D ⊆ E × Ds ⊆L Es
_ ⊆L _ = ⊥

⊆L-refl : ∀ Ds → Ds ⊆L Ds
⊆L-refl [] = tt
⊆L-refl (D ∷ Ds) = ⟨ (λ d z → z) , ⊆L-refl Ds ⟩

bindL-mono : ∀ Ds Es {K K'} → Ds ⊆L Es → (∀ {Xs Ys} → Xs ⊆L Ys → K Xs ⊆ K' Ys) → bindL Ds K ⊆ bindL Es K'
bindL-mono [] [] _ mK = mK tt
bindL-mono (D ∷ Ds) (E ∷ Es) ⟨ D⊆ , s ⟩ mK = ≫=-mono D⊆ (λ X⊆ → bindL-mono Ds Es s (λ s' → mK ⟨ X⊆ , s' ⟩))

At-mono : ∀ {n} (i : Fin n) Ds Es d → Ds ⊆L Es → At i Ds d → At i Es d
At-mono {suc n} zero (D ∷ Ds) (E ∷ Es) d ⟨ D⊆ , Ds⊆ ⟩ ⟨ len , d∈ ⟩ = ⟨ len' Ds Es Ds⊆ len , D⊆ d d∈ ⟩
  where
  len' : ∀ {m} Ds Es → Ds ⊆L Es → length Ds ≡ m → length Es ≡ m
  len' [] [] _ refl = refl
  len' (D ∷ Ds) (E ∷ Es) ⟨ _ , s ⟩ refl = cong suc (len' Ds Es s refl)
At-mono (suc i) (D ∷ Ds) (E ∷ Es) d ⟨ _ , Ds⊆ ⟩ a = At-mono i Ds Es d Ds⊆ a

AllNE-mono : ∀ Ds Es → Ds ⊆L Es → AllNE Ds → AllNE Es
AllNE-mono [] [] _ _ = tt
AllNE-mono (D ∷ Ds) (E ∷ Es) ⟨ D⊆ , s ⟩ ⟨ ⟨ d , d∈ ⟩ , ne ⟩ = ⟨ ⟨ d , D⊆ d d∈ ⟩ , AllNE-mono Ds Es s ne ⟩

𝒯P-mono : ∀ {Ds Es} → Ds ⊆L Es → 𝒯P Ds ⊆ 𝒯P Es
𝒯P-mono {[]} {[]} s ⟨⟩ tt = tt
𝒯P-mono {Ds} {Es} s (tup[ i ] d) ⟨ a , ne ⟩ = ⟨ At-mono i Ds Es d s a , AllNE-mono Ds Es s ne ⟩

{- every component has values and no error -}
Vals : List (𝒫 Value) → Set
Vals [] = ⊤
Vals (D ∷ Ds) = Valᴰ D × Vals Ds

bindL-β : ∀ Ds {K} → (∀ {Xs Ys} → Xs ⊆L Ys → K Xs ⊆ K Ys) → Vals Ds → bindL Ds K ≃ K Ds
bindL-β [] mK _ = ≃-refl
bindL-β (D ∷ Ds) {K} mK ⟨ ⟨ c , ne ⟩ , vs ⟩ =
  ≃-trans (≫=-β {F = λ X → bindL Ds (λ Xs → K (X ∷ Xs))}
                (λ X⊆ → bindL-mono Ds Ds (⊆L-refl Ds) (λ s → mK ⟨ X⊆ , s ⟩)) c ne)
          (bindL-β Ds (λ s → mK ⟨ (λ d z → z) , s ⟩) vs)

𝒯L-β : ∀ Ds → Vals Ds → 𝒯L Ds ≃ 𝒯P Ds
𝒯L-β Ds = bindL-β Ds 𝒯P-mono

{- an error in the components, left to right -}
errsL : List (𝒫 Value) → Set
errsL [] = ⊥
errsL (D ∷ Ds) = ω ∈ D ⊎ (Conv D × errsL Ds)

errsL-ω : ∀ Ds {K} → errsL Ds → ω ∈ bindL Ds K
errsL-ω (D ∷ Ds) (inj₁ ω∈) = inj₁ ⟨ refl , ω∈ ⟩
errsL-ω (D ∷ Ds) (inj₂ ⟨ c , e ⟩) = inj₂ ⟨ c , errsL-ω Ds e ⟩

At-length : ∀ {m} (i : Fin m) Ds d → At i Ds d → length Ds ≡ m
At-length {suc m} zero (D ∷ Ds) d ⟨ len , _ ⟩ = cong suc len
At-length (suc i) (D ∷ Ds) d a = cong suc (At-length i Ds d a)

At-[] : ∀ {n} (i : Fin n) {d} → At i [] d → ⊥
At-[] zero ()
At-[] (suc i) ()

𝒯P-kind : ∀ Ds d → d ∈ 𝒯P Ds → kind d ≡ tup (length Ds)
𝒯P-kind [] ⟨⟩ _ = refl
𝒯P-kind Ds (tup[ i ] d) ⟨ a , _ ⟩ = cong tup (sym (At-length i Ds d a))

{- Denotations of values, environments, continuations and states ------------}

𝒱 : Val → 𝒫 Value
𝒱s : List Val → List (𝒫 Value)
𝓔 : Env → VEnv

𝒱 (clo N γ) = Λᵐ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩
𝒱 (const B k) = ℬ B k ptt
𝒱 (tup vs) = 𝒯L (𝒱s vs)
𝒱 (T.inl v) = inlᵐ ⟨ 𝒱 v , ptt ⟩
𝒱 (T.inr v) = inrᵐ ⟨ 𝒱 v , ptt ⟩

𝒱s [] = []
𝒱s (v ∷ vs) = 𝒱 v ∷ 𝒱s vs

𝓔 [] x = ⌈ ω ⌉
𝓔 (v ∷ γ) zero = 𝒱 v
𝓔 (v ∷ γ) (suc x) = 𝓔 γ x

rev𝒱 : List Val → List (𝒫 Value) → List (𝒫 Value)
rev𝒱 [] Ds = Ds
rev𝒱 (v ∷ vs) Ds = rev𝒱 vs (𝒱 v ∷ Ds)

⟦_⟧* : List AST → VEnv → List (𝒫 Value)
⟦ [] ⟧* ρ = []
⟦ M ∷ Ms ⟧* ρ = ⟦ M ⟧ ρ ∷ ⟦ Ms ⟧* ρ

𝒦 : Cont → 𝒫 Value → 𝒫 Value
𝒦 halt D = D
𝒦 (appL M γ κ) D = 𝒦 κ (⋆ᵐ ⟨ D , ⟨ ⟦ M ⟧ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (appR v κ) D = 𝒦 κ (⋆ᵐ ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
𝒦 (tupK vs Ms γ κ) D = 𝒦 κ (𝒯L (rev𝒱 vs (D ∷ ⟦ Ms ⟧* (𝓔 γ))))
𝒦 (getK i κ) D = 𝒦 κ (projᵐ i ⟨ D , ptt ⟩)
𝒦 (inlK κ) D = 𝒦 κ (inlᵐ ⟨ D , ptt ⟩)
𝒦 (inrK κ) D = 𝒦 κ (inrᵐ ⟨ D , ptt ⟩)
𝒦 (caseK M N γ κ) D =
  𝒦 κ (𝒞ᵐ ⟨ D , ⟨ (λ X → ⟦ M ⟧ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩)
𝒦 (primL p M γ κ) D = 𝒦 κ (primᵐ p ⟨ D , ⟨ ⟦ M ⟧ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (primR p v κ) D = 𝒦 κ (primᵐ p ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
𝒦 (letK N γ κ) D = 𝒦 κ (⋆ᵐ ⟨ 𝒱 (clo N γ) , ⟨ D , ptt ⟩ ⟩)

𝒮 : State → 𝒫 Value
𝒮 (eval M γ κ) = 𝒦 κ (⟦ M ⟧ (𝓔 γ))
𝒮 (ret v κ) = 𝒦 κ (𝒱 v)

{- Monotonicity of the continuations -----------------------------------------}

rev𝒱-mono : ∀ vs Ds Es → Ds ⊆L Es → rev𝒱 vs Ds ⊆L rev𝒱 vs Es
rev𝒱-mono [] Ds Es s = s
rev𝒱-mono (v ∷ vs) Ds Es s = rev𝒱-mono vs (𝒱 v ∷ Ds) (𝒱 v ∷ Es) ⟨ (λ d z → z) , s ⟩

𝒦-mono : ∀ κ {D E} → D ⊆ E → 𝒦 κ D ⊆ 𝒦 κ E
𝒦-mono halt D⊆ = D⊆
𝒦-mono (appL M γ κ) D⊆ = 𝒦-mono κ (lower (mono (⋆ᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ⟨ lift (λ d z → z) , ptt ⟩ ⟩))
𝒦-mono (appR v κ) D⊆ = 𝒦-mono κ (lower (mono (⋆ᵐ-good {⊤}) _ _ ⟨ lift (λ d z → z) , ⟨ lift D⊆ , ptt ⟩ ⟩))
𝒦-mono (tupK vs Ms γ κ) {D} {E} D⊆ =
  𝒦-mono κ (bindL-mono _ _ (rev𝒱-mono vs (D ∷ _) (E ∷ _) ⟨ D⊆ , ⊆L-refl _ ⟩) 𝒯P-mono)
𝒦-mono (getK i κ) D⊆ = 𝒦-mono κ (lower (mono (projᵐ-good {⊤} i) _ _ ⟨ lift D⊆ , ptt ⟩))
𝒦-mono (inlK κ) D⊆ = 𝒦-mono κ (lower (mono (inlᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ptt ⟩))
𝒦-mono (inrK κ) D⊆ = 𝒦-mono κ (lower (mono (inrᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ptt ⟩))
𝒦-mono (caseK M N γ κ) D⊆ =
  𝒦-mono κ (lower (mono (𝒞ᵐ-good {⊤}) _ _ ⟨ lift D⊆ , ⟨ (λ X Y X⊆ → lift (body-mono M (𝓔 γ) X⊆)) ,
                                                         ⟨ (λ X Y X⊆ → lift (body-mono N (𝓔 γ) X⊆)) , ptt ⟩ ⟩ ⟩))
𝒦-mono (primL p M γ κ) D⊆ = 𝒦-mono κ (lower (mono (primᵐ-good {⊤} p) _ _ ⟨ lift D⊆ , ⟨ lift (λ d z → z) , ptt ⟩ ⟩))
𝒦-mono (primR p v κ) D⊆ = 𝒦-mono κ (lower (mono (primᵐ-good {⊤} p) _ _ ⟨ lift (λ d z → z) , ⟨ lift D⊆ , ptt ⟩ ⟩))
𝒦-mono (letK N γ κ) D⊆ = 𝒦-mono κ (lower (mono (⋆ᵐ-good {⊤}) _ _ ⟨ lift (λ d z → z) , ⟨ lift D⊆ , ptt ⟩ ⟩))

{- Values denote consistent sets of values of their kind ----------------------}

length-𝒱s : ∀ vs → length (𝒱s vs) ≡ length vs
length-𝒱s [] = refl
length-𝒱s (v ∷ vs) = cong suc (length-𝒱s vs)

Vals⇒AllNE : ∀ Ds → Vals Ds → AllNE Ds
Vals⇒AllNE [] _ = tt
Vals⇒AllNE (D ∷ Ds) ⟨ ⟨ _ , ne ⟩ , vs ⟩ = ⟨ ne , Vals⇒AllNE Ds vs ⟩

shape-ω : ∀ o → ShapeOf o ω → ⊥
shape-ω (o-const B k) ()

𝒱-val : ∀ v → Valᴰ (𝒱 v)
𝒱-shape : ∀ v → Σ[ d ∈ Value ] d ∈ 𝒱 v × ShapeOf (obs v) d
𝒱s-vals : ∀ vs → Vals (𝒱s vs)
𝒱-val (clo N γ) = ⟨ Λᵐ-clean , ⟨ ν , ⟨ tt , tt ⟩ ⟩ ⟩
𝒱-val (const B k) = ⟨ (λ { .ω () refl }) , ⟨ dconst k , ⟨ refl , refl ⟩ ⟩ ⟩
𝒱-val (tup vs) = ⟨ (λ { d d∈ refl → shape-ω' (proj₁ (𝒯L-β (𝒱s vs) (𝒱s-vals vs)) d d∈) }) , ⟨ _ , proj₁ (proj₂ (𝒱-shape (tup vs))) ⟩ ⟩
  where shape-ω' : ω ∈ 𝒯P (𝒱s vs) → ⊥
        shape-ω' ()
𝒱-val (T.inl v) = inlᵐ-val (𝒱-val v)
𝒱-val (T.inr v) = inrᵐ-val (𝒱-val v)
𝒱-shape (clo N γ) = ⟨ ν , ⟨ ⟨ tt , tt ⟩ , tt ⟩ ⟩
𝒱-shape (const B k) = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩
𝒱-shape (tup []) = ⟨ ⟨⟩ , ⟨ tt , refl ⟩ ⟩
𝒱-shape (tup (v ∷ vs)) =
  ⟨ tup[_]_ {suc (length vs)} zero (proj₁ (𝒱-shape v))
  , ⟨ proj₂ (𝒯L-β (𝒱s (v ∷ vs)) vs′) _ ⟨ ⟨ length-𝒱s vs , proj₁ (proj₂ (𝒱-shape v)) ⟩ , Vals⇒AllNE _ vs′ ⟩
    , ⟨ length-obs-list vs , proj₂ (proj₂ (𝒱-shape v)) ⟩ ⟩ ⟩
  where vs′ = ⟨ 𝒱-val v , 𝒱s-vals vs ⟩
𝒱-shape (T.inl v) with 𝒱-shape v
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ left d , ⟨ inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , ⟨ d∈ , d≢ ⟩ ⟩ , sh ⟩ ⟩
  where d≢ = λ { refl → shape-ω (obs v) sh }
𝒱-shape (T.inr v) with 𝒱-shape v
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ right d , ⟨ inj₂ ⟨ ⟨ d , ⟨ d∈ , d≢ ⟩ ⟩ , ⟨ d∈ , d≢ ⟩ ⟩ , sh ⟩ ⟩
  where d≢ = λ { refl → shape-ω (obs v) sh }
𝒱s-vals [] = tt
𝒱s-vals (v ∷ vs) = ⟨ 𝒱-val v , 𝒱s-vals vs ⟩

𝒱-conv : ∀ v → Conv (𝒱 v)
𝒱-conv v = Val⇒Conv (𝒱-val v)

{- the kind of a machine value -}
vkind : Val → Kind
vkind (clo N γ) = fun
vkind (const B k) = base B
vkind (tup vs) = tup (length vs)
vkind (T.inl v) = inj
vkind (T.inr v) = inj

𝒱-kind : ∀ v d → d ∈ ⌊ 𝒱 v ⌋ → kind d ≡ vkind v
𝒱-kind (clo N γ) d ⟨ d∈ , _ ⟩ = Λᵐ-fun d d∈
𝒱-kind (const B k) (dconst k') ⟨ ⟨ refl , _ ⟩ , _ ⟩ = refl
𝒱-kind (tup vs) d ⟨ d∈ , _ ⟩ =
  trans (𝒯P-kind (𝒱s vs) d (proj₁ (𝒯L-β (𝒱s vs) (𝒱s-vals vs)) d d∈)) (cong tup (length-𝒱s vs))
𝒱-kind (T.inl v) d ⟨ inj₁ ⟨ refl , _ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
𝒱-kind (T.inl v) (left d) ⟨ inj₂ _ , _ ⟩ = refl
𝒱-kind (T.inr v) d ⟨ inj₁ ⟨ refl , _ ⟩ , d≢ ⟩ = ⊥-elim (d≢ refl)
𝒱-kind (T.inr v) (right d) ⟨ inj₂ _ , _ ⟩ = refl

{- the check of a kind fails on a value of another kind -}
𝒱-bad : ∀ v {k} → vkind v ≢ k → Bad k ⌊ 𝒱 v ⌋
𝒱-bad v ne with 𝒱-conv v
... | ⟨ d , d∈ ⟩ = ⟨ d , ⟨ d∈ , (λ eq → ne (trans (sym (𝒱-kind v d d∈)) eq)) ⟩ ⟩

AllCon : List (𝒫 Value) → Set
AllCon [] = ⊤
AllCon (D ∷ Ds) = Con D × AllCon Ds

At-con : ∀ {n} (i : Fin n) Ds {d d'} → AllCon Ds → At i Ds d → At i Ds d' → d ~ d'
At-con {suc n} zero (D ∷ Ds) ⟨ c , _ ⟩ ⟨ _ , d∈ ⟩ ⟨ _ , d'∈ ⟩ = c _ _ d∈ d'∈
At-con (suc i) (D ∷ Ds) ⟨ _ , cs ⟩ a a' = At-con i Ds cs a a'

𝒯P-con : ∀ Ds → AllCon Ds → Con (𝒯P Ds)
𝒯P-con Ds cs ⟨⟩ ⟨⟩ _ _ = tt
𝒯P-con Ds cs (tup[ i ] d) (tup[ j ] d') ⟨ a , _ ⟩ ⟨ a' , _ ⟩
    with trans (sym (At-length i Ds d a)) (At-length j Ds d' a')
... | refl with i fin≟ j
... | yes refl = ⟨ refl , inj₂ ⟨ refl , At-con i Ds cs a a' ⟩ ⟩
... | no neq = ⟨ refl , inj₁ neq ⟩
𝒯P-con [] cs ⟨⟩ (tup[ i ] d) _ ⟨ a , _ ⟩ = ⊥-elim (At-[] i a)
𝒯P-con [] cs (tup[ i ] d) ⟨⟩ ⟨ a , _ ⟩ _ = ⊥-elim (At-[] i a)

𝒱-con : ∀ v → Con (𝒱 v)
𝒱s-con : ∀ vs → AllCon (𝒱s vs)
𝓔-con : ∀ γ → Con-env (𝓔 γ)
𝒱-con (clo N γ) = lower (consis (Λᵐ-good {⊤}) tt _ _
  ⟨ (λ X X' X~ → lift (ISWIMᵐ-con-env N (proof.Framework.GraphModel.Env.•-~ (Every _~_) (𝓔-con γ) X~))) , ptt ⟩)
𝒱-con (const B k) = lower (ℬ-consis B k ptt ptt ptt)
𝒱-con (tup vs) = Con-⊆ (𝒯P-con (𝒱s vs) (𝒱s-con vs)) (proj₁ (𝒯L-β (𝒱s vs) (𝒱s-vals vs)))
𝒱-con (T.inl v) = lower (consis (inlᵐ-good {⊤}) tt _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱-con (T.inr v) = lower (consis (inrᵐ-good {⊤}) tt _ _ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱s-con [] = tt
𝒱s-con (v ∷ vs) = ⟨ 𝒱-con v , 𝒱s-con vs ⟩
𝓔-con [] x = Con-⌈⌉ ω
𝓔-con (v ∷ γ) zero = 𝒱-con v
𝓔-con (v ∷ γ) (suc x) = 𝓔-con γ x

{- Environments -----------------------------------------------------------------}

𝓔-nonempty : ∀ γ → proof.Framework.GraphModel.Env.nonempty-env (𝓔 γ)
𝓔-nonempty [] x = ⟨ ω , refl ⟩
𝓔-nonempty (v ∷ γ) zero = proj₂ (𝒱-val v)
𝓔-nonempty (v ∷ γ) (suc x) = 𝓔-nonempty γ x

𝓔-lookup : ∀ γ x {v} → γ ‼ x ≡ just v → 𝒱 v ⊆ 𝓔 γ x
𝓔-lookup (v ∷ γ) zero refl d d∈ = d∈
𝓔-lookup (v ∷ γ) (suc x) eq = 𝓔-lookup γ x eq

{- an unbound variable means {ω} -}
𝓔-nothing : ∀ γ x → γ ‼ x ≡ nothing → ω ∈ 𝓔 γ x
𝓔-nothing [] x _ = refl
𝓔-nothing (v ∷ γ) (suc x) eq = 𝓔-nothing γ x eq

𝓔-ext : ∀ v γ x → 𝓔 (v ∷ γ) x ⊆ (𝒱 v • 𝓔 γ) x
𝓔-ext v γ zero d d∈ = d∈
𝓔-ext v γ (suc x) d d∈ = d∈

{- Tuples ------------------------------------------------------------------------}

𝒱s-reverseAcc : ∀ acc vs → 𝒱s (reverseAcc acc vs) ≡ rev𝒱 vs (𝒱s acc)
𝒱s-reverseAcc acc [] = refl
𝒱s-reverseAcc acc (v ∷ vs) = 𝒱s-reverseAcc (v ∷ acc) vs

tuple-next-𝒮 : ∀ vs Ms γ κ → 𝒮 (tuple-next vs Ms γ κ) ⊆ 𝒦 κ (𝒯L (rev𝒱 vs (⟦ Ms ⟧* (𝓔 γ))))
tuple-next-𝒮 vs [] γ κ d d∈ = subst (λ Ds → 𝒦 κ (𝒯L Ds) d) (𝒱s-reverseAcc [] vs) d∈
tuple-next-𝒮 vs (M ∷ Ms) γ κ d d∈ = d∈

{- the tuple of a list of operands is the tuple of the operands -}
𝒯L-args : ∀ {n} (args : Args (replicate n ■)) ρ → 𝒯L (⟦ args→list args ⟧* ρ) ⊆ 𝒯ᵐ n (⟦ args ⟧₊ ρ)
𝒯L-args {n} args ρ = go args (tup⊆ n)
  where
  open import proof.Framework.GraphModel.Ops using (𝒯)
  {- the bound operands, as a list and as a tuple -}
  Rel : ∀ m → List (𝒫 Value) → Results (𝒫 Value) (replicate m ■) → Set
  Rel zero [] _ = ⊤
  Rel (suc m) (X ∷ Xs) ⟨ Y , Ys ⟩ = X ⊆ Y × Rel m Xs Ys
  Rel _ _ _ = ⊥
  Rel-len : ∀ {m Xs Ys} → Rel m Xs Ys → length Xs ≡ m
  Rel-len {zero} {[]} _ = refl
  Rel-len {suc m} {X ∷ Xs} ⟨ _ , r ⟩ = cong suc (Rel-len r)
  Rel-At : ∀ {m Xs Ys} (i : Fin m) {d} → Rel m Xs Ys → At i Xs d → d ∈ nthD Ys i
  Rel-At {suc m} {X ∷ Xs} zero ⟨ X⊆ , _ ⟩ ⟨ _ , d∈ ⟩ = X⊆ _ d∈
  Rel-At {suc m} {X ∷ Xs} (suc i) ⟨ _ , r ⟩ a = Rel-At i r a
  Rel-ne : ∀ {m Xs Ys} → Rel m Xs Ys → AllNE Xs → ∀ j → nonempty (nthD Ys j)
  Rel-ne {suc m} {X ∷ Xs} ⟨ X⊆ , _ ⟩ ⟨ ⟨ d , d∈ ⟩ , _ ⟩ zero = ⟨ d , X⊆ d d∈ ⟩
  Rel-ne {suc m} {X ∷ Xs} ⟨ _ , r ⟩ ⟨ _ , ne ⟩ (suc j) = Rel-ne r ne j
  tup⊆ : ∀ m {Xs Ys} → Rel m Xs Ys → 𝒯P Xs ⊆ 𝒯 m Ys
  tup⊆ zero {[]} _ ⟨⟩ _ = tt
  tup⊆ zero {[]} _ (tup[ i ] d) ⟨ a , _ ⟩ = ⊥-elim (At-[] i a)
  tup⊆ (suc m) {X ∷ Xs} _ ⟨⟩ ()
  tup⊆ (suc m) {Xs} r (tup[ i ] d) ⟨ a , ne ⟩ with trans (sym (At-length i Xs d a)) (Rel-len r)
  ... | refl = ⟨ refl , ⟨ Rel-At i r a , Rel-ne r ne ⟩ ⟩
  go : ∀ {m} (as : Args (replicate m ■)) {K K'} → (∀ {Xs Ys} → Rel m Xs Ys → K Xs ⊆ K' Ys)
    → bindL (⟦ args→list as ⟧* ρ) K ⊆ binds m (⟦ as ⟧₊ ρ) K'
  go {zero} Nil h = h tt
  go {suc m} (M ,, as) h = ≫=-mono (λ d z → z) (λ X⊆ → go as (λ r → h ⟨ X⊆ , r ⟩))

proj-𝒱s : ∀ {n} (i : Fin n) vs {v} → proj i vs ≡ just v → ∀ d → d ∈ 𝒱 v → At i (𝒱s vs) d
proj-𝒱s {suc n} zero (v ∷ vs) eq d d∈ with has-length n vs in h
proj-𝒱s {suc n} zero (v ∷ vs) refl d d∈ | true =
  ⟨ trans (length-𝒱s vs) (has-length→length n vs h) , d∈ ⟩
proj-𝒱s {suc n} zero (v ∷ vs) () d d∈ | false
proj-𝒱s (suc i) (v ∷ vs) eq d d∈ = proj-𝒱s i vs eq d d∈

{- a projection succeeds on a tuple of the right size -}
proj-length : ∀ {n} (i : Fin n) vs → length vs ≡ n → Σ[ v ∈ Val ] proj i vs ≡ just v
proj-length {suc n} zero (v ∷ vs) refl rewrite length→has-length n vs refl = ⟨ v , refl ⟩
proj-length {suc n} (suc i) (v ∷ vs) refl = proj-length i vs refl

proj-nothing : ∀ {n} (i : Fin n) vs → proj i vs ≡ nothing → length vs ≢ n
proj-nothing i vs eq len with proj-length i vs len
... | ⟨ v , eq' ⟩ with trans (sym eq) eq'
... | ()

{- Primitives -------------------------------------------------------------------}

int-in : ∀ v {n} → obs v ≡ o-const Int n → dconst {Int} n ∈ ⌊ 𝒱 v ⌋
int-in (const B k) refl = ⟨ ⟨ refl , refl ⟩ , (λ ()) ⟩

𝒱-out : ∀ r d → d ∈ 𝒱 (out r) → d ≡ dout r
𝒱-out (int k) (dconst k') ⟨ refl , refl ⟩ = refl
𝒱-out (bool true) d (inj₁ ⟨ refl , () ⟩)
𝒱-out (bool true) (left ⟨⟩) (inj₂ _) = refl
𝒱-out (bool true) (left (tup[ i ] d)) (inj₂ ⟨ _ , ⟨ ⟨ a , _ ⟩ , _ ⟩ ⟩) = ⊥-elim (At-[] i a)
𝒱-out (bool false) d (inj₁ ⟨ refl , () ⟩)
𝒱-out (bool false) (right ⟨⟩) (inj₂ _) = refl
𝒱-out (bool false) (right (tup[ i ] d)) (inj₂ ⟨ _ , ⟨ ⟨ a , _ ⟩ , _ ⟩ ⟩) = ⊥-elim (At-[] i a)

prim-⊆ : ∀ p v w r → δ? p (obs v) (obs w) ≡ just r → 𝒱 (out r) ⊆ primᵐ p ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
prim-⊆ p v w r e d d∈ with δ?-inv p (obs v) (obs w) e
... | ⟨ n , ⟨ m , ⟨ ov , ⟨ ow , refl ⟩ ⟩ ⟩ ⟩ =
  inj₂ ⟨ 𝒱-conv v , inj₂ ⟨ 𝒱-conv w , inj₂ (inj₂ ⟨ n , ⟨ m , ⟨ int-in v ov , ⟨ int-in w ow , 𝒱-out (δ p n m) d d∈ ⟩ ⟩ ⟩ ⟩) ⟩ ⟩

{- a value whose observation is not an integer is not of the kind of one -}
notint-kind : ∀ v → (∀ n → obs v ≢ o-const Int n) → vkind v ≢ base Int
notint-kind (const .Int k) f refl = f k refl

{- a primitive is undefined when one operand is not an integer -}
δ?-none : ∀ p o₁ o₂ → δ? p o₁ o₂ ≡ nothing
  → (∀ n → o₁ ≢ o-const Int n) ⊎ (∀ m → o₂ ≢ o-const Int m)
δ?-none p (o-const Int n) (o-const Int m) ()
δ?-none p (o-const Int n) o₂ eq = inj₂ (λ m e → G (trans (sym eq) (cong (δ? p (o-const Int n)) e)))
  where
  G : ∀ {r : Out} → nothing ≡ just r → ⊥
  G ()
δ?-none p (o-const Nat k) o₂ eq = inj₁ (λ n ())
δ?-none p (o-const 𝔹 k) o₂ eq = inj₁ (λ n ())
δ?-none p (o-const Unit k) o₂ eq = inj₁ (λ n ())
δ?-none p (o-const Void k) o₂ eq = inj₁ (λ n ())
δ?-none p (o-const Blame k) o₂ eq = inj₁ (λ n ())
δ?-none p o-fun o₂ eq = inj₁ (λ n ())
δ?-none p (o-tuple os) o₂ eq = inj₁ (λ n ())
δ?-none p (o-inl o) o₂ eq = inj₁ (λ n ())
δ?-none p (o-inr o) o₂ eq = inj₁ (λ n ())
δ?-none p o-error o₂ eq = inj₁ (λ n ())

prim-ω : ∀ p v w → δ? p (obs v) (obs w) ≡ nothing → ω ∈ primᵐ p ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
prim-ω p v w e with δ?-none p (obs v) (obs w) e
... | inj₁ ni = inj₂ ⟨ 𝒱-conv v , inj₂ ⟨ 𝒱-conv w , inj₁ ⟨ refl , 𝒱-bad v (notint-kind v ni) ⟩ ⟩ ⟩
... | inj₂ ni = inj₂ ⟨ 𝒱-conv v , inj₂ ⟨ 𝒱-conv w , inj₂ (inj₁ ⟨ refl , 𝒱-bad w (notint-kind w ni) ⟩) ⟩ ⟩

{- Steps shrink the denotation of the state --------------------------------}

{- β: the body of a function, run on a value -}
app-β : ∀ N γ w → ⟦ N ⟧ (𝓔 (w ∷ γ)) ⊆ ⋆ᵐ ⟨ 𝒱 (clo N γ) , ⟨ 𝒱 w , ptt ⟩ ⟩
app-β N γ w d d∈ =
  proj₂ (letᵐ-β (body-mono N (𝓔 γ)) (body-continuous N (𝓔 γ) (𝓔-nonempty γ) (𝒱 w) (proj₂ (𝒱-val w)))
                (𝒱-con w) (𝒱-val w)) d (⟦⟧-monotone N (𝓔-ext w γ) d d∈)

case-inl-β : ∀ M N γ v → ⟦ M ⟧ (𝓔 (v ∷ γ))
  ⊆ 𝒞ᵐ ⟨ inlᵐ ⟨ 𝒱 v , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
case-inl-β M N γ v d d∈ =
  proj₂ (𝒞ᵐ-inl-β {G = λ X → ⟦ N ⟧ (X • 𝓔 γ)} (body-mono M (𝓔 γ))
           (body-continuous M (𝓔 γ) (𝓔-nonempty γ) (𝒱 v) (proj₂ (𝒱-val v))) (𝒱-con v) (𝒱-val v))
        d (⟦⟧-monotone M (𝓔-ext v γ) d d∈)

case-inr-β : ∀ M N γ v → ⟦ N ⟧ (𝓔 (v ∷ γ))
  ⊆ 𝒞ᵐ ⟨ inrᵐ ⟨ 𝒱 v , ptt ⟩ , ⟨ (λ X → ⟦ M ⟧ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩
case-inr-β M N γ v d d∈ =
  proj₂ (𝒞ᵐ-inr-β {F = λ X → ⟦ M ⟧ (X • 𝓔 γ)} (body-mono N (𝓔 γ))
           (body-continuous N (𝓔 γ) (𝓔-nonempty γ) (𝒱 v) (proj₂ (𝒱-val v))) (𝒱-con v) (𝒱-val v))
        d (⟦⟧-monotone N (𝓔-ext v γ) d d∈)

step-⊆ : ∀ s {s'} → step s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
step-⊆ (eval (` x) γ κ) eq with γ ‼ x in look
step-⊆ (eval (` x) γ κ) refl | just v = 𝒦-mono κ (𝓔-lookup γ x look)
step-⊆ (eval (` x) γ κ) () | nothing
step-⊆ (eval (lam ⦅ ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (app ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (lit B k ⦅ Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (tuple n ⦅ args ⦆) γ κ) refl d d∈ =
  𝒦-mono κ (𝒯L-args args (𝓔 γ)) d (tuple-next-𝒮 [] (args→list args) γ κ d d∈)
step-⊆ (eval (get i ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (ret (clo N γ) (appL M γ' κ)) refl d d∈ = d∈
step-⊆ (ret w (appR (clo N γ) κ)) refl = 𝒦-mono κ (app-β N γ w)
step-⊆ (ret v (tupK vs Ms γ κ)) refl = tuple-next-𝒮 (v ∷ vs) Ms γ κ
step-⊆ (ret (tup vs) (getK i κ)) eq with proj i vs in p
step-⊆ (ret (tup vs) (getK i κ)) refl | just v =
  𝒦-mono κ λ d d∈ → inj₂ ⟨ 𝒱-conv (tup vs) , inj₂ ⟨ proj₂ (𝒯L-β (𝒱s vs) (𝒱s-vals vs)) _
                      ⟨ proj-𝒱s i vs p d d∈ , Vals⇒AllNE _ (𝒱s-vals vs) ⟩ , (λ ()) ⟩ ⟩
step-⊆ (ret (tup vs) (getK i κ)) () | nothing
step-⊆ (ret v (inlK κ)) refl d d∈ = d∈
step-⊆ (ret v (inrK κ)) refl d d∈ = d∈
step-⊆ (ret (T.inl v) (caseK M N γ κ)) refl = 𝒦-mono κ (case-inl-β M N γ v)
step-⊆ (ret (T.inr v) (caseK M N γ κ)) refl = 𝒦-mono κ (case-inr-β M N γ v)
step-⊆ (ret v (primL p M γ κ)) refl d d∈ = d∈
step-⊆ (ret w (primR p v κ)) eq with δ? p (obs v) (obs w) in e
step-⊆ (ret w (primR p v κ)) refl | just r = 𝒦-mono κ (prim-⊆ p v w r e)
step-⊆ (ret w (primR p v κ)) () | nothing
step-⊆ (ret w (letK N γ κ)) refl = 𝒦-mono κ (app-β N γ w)

↠-⊆ : ∀ {s t} → s ↠ t → 𝒮 t ⊆ 𝒮 s
↠-⊆ done d d∈ = d∈
↠-⊆ {s} (st ∷↠ σ) d d∈ = step-⊆ s st d (↠-⊆ σ d d∈)

{- Errors: a continuation passes on ω -----------------------------------------}

errsL-rev : ∀ vs Ds → errsL Ds → errsL (rev𝒱 vs Ds)
errsL-rev [] Ds e = e
errsL-rev (v ∷ vs) Ds e = errsL-rev vs (𝒱 v ∷ Ds) (inj₂ ⟨ 𝒱-conv v , e ⟩)

𝒦-ω : ∀ κ {D} → ω ∈ D → ω ∈ 𝒦 κ D
𝒦-ω halt ω∈ = ω∈
𝒦-ω (appL M γ κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
𝒦-ω (appR v κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv v , inj₂ (inj₁ ⟨ refl , ω∈ ⟩) ⟩)
𝒦-ω (tupK vs Ms γ κ) {D} ω∈ = 𝒦-ω κ (errsL-ω _ (errsL-rev vs (D ∷ _) (inj₁ ω∈)))
𝒦-ω (getK i κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
𝒦-ω (inlK κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
𝒦-ω (inrK κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
𝒦-ω (caseK M N γ κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
𝒦-ω (primL p M γ κ) ω∈ = 𝒦-ω κ (inj₁ ⟨ refl , ω∈ ⟩)
𝒦-ω (primR p v κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv v , inj₁ ⟨ refl , ω∈ ⟩ ⟩)
𝒦-ω (letK N γ κ) ω∈ = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (clo N γ) , inj₂ (inj₁ ⟨ refl , ω∈ ⟩) ⟩)

{- Final states ----------------------------------------------------------------}

{- a state that stops with an error denotes a set that holds ω -}
final-err : ∀ s → step s ≡ stop o-error → ω ∈ 𝒮 s
final-err (eval (` x) γ κ) eq with γ ‼ x in look
final-err (eval (` x) γ κ) () | just v
final-err (eval (` x) γ κ) refl | nothing = 𝒦-ω κ (𝓔-nothing γ x look)
final-err (eval (lam ⦅ ⟩ N ,, Nil ⦆) γ κ) ()
final-err (eval (app ⦅ L ,, M ,, Nil ⦆) γ κ) ()
final-err (eval (lit B k ⦅ Nil ⦆) γ κ) ()
final-err (eval (tuple n ⦅ args ⦆) γ κ) ()
final-err (eval (get i ⦅ M ,, Nil ⦆) γ κ) ()
final-err (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) ()
final-err (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) ()
final-err (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) ()
final-err (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) ()
final-err (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) ()
final-err (ret (const B k) (appL M γ' κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (const B k) , inj₁ ⟨ refl , 𝒱-bad (const B k) (λ ()) ⟩ ⟩)
final-err (ret (tup vs) (appL M γ' κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (tup vs) , inj₁ ⟨ refl , 𝒱-bad (tup vs) (λ ()) ⟩ ⟩)
final-err (ret (T.inl v) (appL M γ' κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inl v) , inj₁ ⟨ refl , 𝒱-bad (T.inl v) (λ ()) ⟩ ⟩)
final-err (ret (T.inr v) (appL M γ' κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inr v) , inj₁ ⟨ refl , 𝒱-bad (T.inr v) (λ ()) ⟩ ⟩)
final-err (ret w (appR (const B k) κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (const B k) , inj₁ ⟨ refl , 𝒱-bad (const B k) (λ ()) ⟩ ⟩)
final-err (ret w (appR (tup vs) κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (tup vs) , inj₁ ⟨ refl , 𝒱-bad (tup vs) (λ ()) ⟩ ⟩)
final-err (ret w (appR (T.inl v) κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inl v) , inj₁ ⟨ refl , 𝒱-bad (T.inl v) (λ ()) ⟩ ⟩)
final-err (ret w (appR (T.inr v) κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inr v) , inj₁ ⟨ refl , 𝒱-bad (T.inr v) (λ ()) ⟩ ⟩)
final-err (ret (tup vs) (getK i κ)) eq with proj i vs in p
final-err (ret (tup vs) (getK i κ)) () | just v
final-err (ret (tup vs) (getK i κ)) refl | nothing = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (tup vs) , inj₁ ⟨ refl , 𝒱-bad (tup vs) (λ { refl → proj-nothing i vs p refl }) ⟩ ⟩)
final-err (ret (clo N γ) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (clo N γ) , inj₁ ⟨ refl , 𝒱-bad (clo N γ) (λ ()) ⟩ ⟩)
final-err (ret (const B k) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (const B k) , inj₁ ⟨ refl , 𝒱-bad (const B k) (λ ()) ⟩ ⟩)
final-err (ret (T.inl v) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inl v) , inj₁ ⟨ refl , 𝒱-bad (T.inl v) (λ ()) ⟩ ⟩)
final-err (ret (T.inr v) (getK i κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (T.inr v) , inj₁ ⟨ refl , 𝒱-bad (T.inr v) (λ ()) ⟩ ⟩)
final-err (ret (clo N' γ') (caseK M N γ κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (clo N' γ') , inj₁ ⟨ refl , 𝒱-bad (clo N' γ') (λ ()) ⟩ ⟩)
final-err (ret (const B k) (caseK M N γ κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (const B k) , inj₁ ⟨ refl , 𝒱-bad (const B k) (λ ()) ⟩ ⟩)
final-err (ret (tup vs) (caseK M N γ κ)) refl = 𝒦-ω κ (inj₂ ⟨ 𝒱-conv (tup vs) , inj₁ ⟨ refl , 𝒱-bad (tup vs) (λ ()) ⟩ ⟩)
final-err (ret w (primR p v κ)) eq with δ? p (obs v) (obs w) in e
final-err (ret w (primR p v κ)) () | just r
final-err (ret w (primR p v κ)) refl | nothing = 𝒦-ω κ (prim-ω p v w e)

{- a state that stops with an answer has an element of that shape -}
final-shape : ∀ s {o} → step s ≡ stop o → Answer o → Σ[ d ∈ Value ] d ∈ 𝒮 s × ShapeOf o d
final-shape (ret v halt) refl ans = 𝒱-shape v
final-shape (eval (` x) γ κ) {o} eq ans with γ ‼ x
final-shape (eval (` x) γ κ) () ans | just v
final-shape (eval (` x) γ κ) refl ans | nothing = ⊥-elim (ans refl)
final-shape (eval (lam ⦅ ⟩ N ,, Nil ⦆) γ κ) () ans
final-shape (eval (app ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
final-shape (eval (lit B k ⦅ Nil ⦆) γ κ) () ans
final-shape (eval (tuple n ⦅ args ⦆) γ κ) () ans
final-shape (eval (get i ⦅ M ,, Nil ⦆) γ κ) () ans
final-shape (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) () ans
final-shape (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) () ans
final-shape (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
final-shape (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
final-shape (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
final-shape (ret (const B k) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (tup vs) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inl v) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inr v) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (const B k) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (tup vs) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (T.inl v) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (T.inr v) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (tup vs) (getK i κ)) eq ans with proj i vs
final-shape (ret (tup vs) (getK i κ)) () ans | just v
final-shape (ret (tup vs) (getK i κ)) refl ans | nothing = ⊥-elim (ans refl)
final-shape (ret (clo N γ) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (const B k) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inl v) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inr v) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (clo N' γ') (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (const B k) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (tup vs) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (primR p v κ)) eq ans with δ? p (obs v) (obs w)
final-shape (ret w (primR p v κ)) () ans | just r
final-shape (ret w (primR p v κ)) refl ans | nothing = ⊥-elim (ans refl)

{- Soundness ------------------------------------------------------------------}

soundness : ∀ M {o} → Terminates (sem M) o → Answer o
  → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × ShapeOf o d
soundness M (⟨ s , ⟨ σ , fin ⟩ ⟩) ans
    with final-shape s fin ans
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
  ⟨ d , ⟨ ⟦⟧-monotone M (λ x d z → z) d (↠-⊆ (star→↠ σ) d d∈) , sh ⟩ ⟩

sound-error : ∀ M → Terminates (sem M) o-error → ω ∈ ⟦ M ⟧ ρ₀
sound-error M ⟨ s , ⟨ σ , fin ⟩ ⟩ =
  ⟦⟧-monotone M (λ x d z → z) ω (↠-⊆ (star→↠ σ) ω (final-err s fin))
