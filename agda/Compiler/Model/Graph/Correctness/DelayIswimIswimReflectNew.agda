open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Compiler.Lang.Clos3 as L3
open import Compiler.Lang.Clos4 as L4
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ast to ast'; bind to bind'; clear to clear')
open import Compiler.Model.Graph.Sem.Clos3Iswim 
open import Compiler.Model.Graph.Sem.Clos4Iswim renaming 
  (⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊')
open import Compiler.Compile.Delay using (delay; del-map-args)
open import NewEnv
open import Primitives
import Fold2



open import Data.Nat using (ℕ; zero; suc; _≟_; _≤_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Induction using (CRec; cRec)
open import Data.Fin using (Fin; zero; suc; fromℕ)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Data.List using (List; []; _∷_; _++_; replicate; length; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
  renaming (map to anymap)
open import Data.List.Relation.Unary.All using (All; []; _∷_; head; tail; reduce; construct; tabulate)
open import Data.List.Relation.Unary.Any.Properties using (map⁺; map⁻)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax; swap)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst; cong; trans; inspect; [_])
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.Core using (Rel)
open import Data.Bool using (Bool; true; false)

module Compiler.Model.Graph.Correctness.DelayIswimIswimReflectNew where

  {- 
  likely required adjustments : 
    + add consistency as a condition to fro (esp. arrow case premise)
      ++ remove this condition as a parameter, but leave it in premises in the appropriate places
    + need to add membership to fro (esp. need for the V used to be an element of the arguments in arrow case premise)
      ++ again, see if it's possible to remove this and leave it only as a condition in appropriate places

  possible adjustments?
    + change every instance of ≢ []  to 'nonempty'  (exists v. v ∈ V )

  -}

{- Some helpers for list construction -}

  All→∈ : ∀ {A : Set} (P : A → Set) (xs : List A) → All P xs → (∀ x → x ∈ mem xs → P x)
  All→∈ P (_ ∷ _) (Px ∷ Pxs) x (here refl) = Px
  All→∈ P (x ∷ xs) (Px ∷ Pxs) y (there y∈) = All→∈ P xs Pxs y y∈

  ∈→All : ∀ {A : Set} (P : A → Set) (xs : List A) → (∀ x → x ∈ mem xs → P x) → All P xs
  ∈→All P [] Pxs = []
  ∈→All P (x ∷ xs) Pxs = Pxs x (here refl) ∷ ∈→All P xs (λ x z → Pxs x (there z))

  ∈-construct : ∀ {A B : Set} (Q : B → Set) (xs : List A) 
              → (∀ x → x ∈ mem xs → Σ[ y ∈ B ] Q y) → Σ[ ys ∈ List B ] All Q ys
  ∈-construct Q [] Qxs = ⟨ [] , [] ⟩
  ∈-construct Q (x ∷ xs) Qxs with (Qxs x (here refl)) | ∈-construct Q xs (λ z z∈ → Qxs z (there z∈))
  ... | ⟨ y , Qy ⟩ | ⟨ ys , Qys ⟩ = ⟨ y ∷ ys , Qy ∷ Qys ⟩


{- shorthand properties -}
  consis : (D : 𝒫 Value) → Set
  consis D = ∀ u v → u ∈ D → v ∈ D → u ~ v

  consis-⊆ : ∀ S D → S ⊆ D → consis D → consis S
  consis-⊆ S D S⊆D D~ u v u∈D v∈D = D~ u v (S⊆D u u∈D) (S⊆D v v∈D)

{- shorthand operators, and eliminations -}
  


  _●_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
  D ● E = ⋆ ⟨ D , ⟨ E , ptt ⟩ ⟩

  ●-consis : ∀ D E → consis D → consis E → consis (D ● E)
  ●-consis D E D~ E~ = lower (⋆-consis ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D , ⟨ E , ptt ⟩ ⟩  ⟨ lift D~ , ⟨ lift E~ , ptt ⟩ ⟩)

  
  ƛ : (𝒫 Value → 𝒫 Value) → 𝒫 Value
  ƛ F = Λ ⟨ F , ptt ⟩

  Car : 𝒫 Value → 𝒫 Value
  Car D = car ⟨ D , ptt ⟩

  Car-consis : ∀ D → consis D → consis (Car D)
  Car-consis D D~ = lower (car-consis ⟨ D , ptt ⟩ ⟨ D , ptt ⟩ ⟨ lift D~ , ptt ⟩)

  Cdr : 𝒫 Value → 𝒫 Value
  Cdr D = cdr ⟨ D , ptt ⟩

  Pair : 𝒫 Value → 𝒫 Value → 𝒫 Value
  Pair D E = pair ⟨ D , ⟨ E , ptt ⟩ ⟩

  Cdr-consis : ∀ D → consis D → consis (Cdr D)
  Cdr-consis D D~ = lower (cdr-consis ⟨ D , ptt ⟩ ⟨ D , ptt ⟩ ⟨ lift D~ , ptt ⟩)

  Cdr-∈ : ∀ {FV} D → ∣ FV ⦆ ∈ D → mem FV ⊆ Cdr D
  Cdr-∈ {FV} D ∣FV⦆∈D fv fv∈FV = ⟨ FV , ⟨ ∣FV⦆∈D , fv∈FV ⟩ ⟩

  Left : 𝒫 Value → 𝒫 Value
  Left D = ℒ ⟨ D , ptt ⟩

  Right : 𝒫 Value → 𝒫 Value
  Right D = ℛ ⟨ D , ptt ⟩

  GetLeft : 𝒫 Value → 𝒫 Value
  GetLeft D = 𝒞 ⟨ D , ⟨ (λ D' → D') , ⟨ (λ D' d → False) , ptt ⟩ ⟩ ⟩

  GetLeft-∈ : ∀ {d} D → (left d) ∈ D → d ∈ GetLeft D
  GetLeft-∈ {d} D leftd∈D = inj₁ ⟨ d , ⟨ [] , ⟨ (λ d → λ { (here refl) → leftd∈D }) , here refl ⟩ ⟩ ⟩

  GetLeft-consis : ∀ D → consis D → consis (GetLeft D)
  GetLeft-consis D D~ = 
    lower (𝒞-consis ⟨ D , ⟨ (λ X → X) , ⟨ (λ X v → False) , ptt ⟩ ⟩ ⟩ ⟨ D , ⟨ (λ X → X) , ⟨ (λ X v → False) , ptt ⟩ ⟩ ⟩
                    ⟨ lift D~ , ⟨ (λ a1 a2 → lift) , ⟨ (λ a1 a2 _ → lift (λ x x₁ x₂ ())) , ptt ⟩ ⟩ ⟩)

  GetLeft-ℒ : ∀ D → GetLeft (ℒ ⟨ D , ptt ⟩) ≃ D
  GetLeft-ℒ D = ⟨ (λ d d∈ → [ (λ d∈₁ → proj₁ (proj₂ (proj₂ d∈₁)) d (proj₂ (proj₂ (proj₂ d∈₁)))) 
                            , (λ d∈₂ → ⊥-elim (proj₂ (proj₂ (proj₂ d∈₂)))) ] d∈) 
                , (λ d d∈ → inj₁ ⟨ d , ⟨ [] , ⟨ (λ z → λ { (here refl) → d∈ }) , here refl ⟩ ⟩ ⟩) ⟩

  GetRight : 𝒫 Value → 𝒫 Value
  GetRight D = 𝒞 ⟨ D , ⟨ (λ D' d → False) , ⟨ (λ D' → D') , ptt ⟩ ⟩ ⟩

  GetRight-∈ : ∀ {d} D → (right d) ∈ D → d ∈ GetRight D
  GetRight-∈ {d} D rightd∈D = inj₂ ⟨ d , ⟨ [] , ⟨ (λ d → λ { (here refl) → rightd∈D }) , here refl ⟩ ⟩ ⟩

  GetRight-consis : ∀ D → consis D → consis (GetRight D)
  GetRight-consis D D~ = 
    lower (𝒞-consis ⟨ D , ⟨ (λ X v → False) , ⟨ (λ X → X) , ptt ⟩ ⟩ ⟩ ⟨ D , ⟨ (λ X v → False) , ⟨ (λ X → X) , ptt ⟩ ⟩ ⟩
                    ⟨ lift D~ , ⟨ (λ a1 a2 _ → lift (λ x x₁ x₂ ())) , ⟨ (λ a1 a2 → lift) , ptt ⟩ ⟩ ⟩)

  GetRight-ℛ : ∀ D → GetRight (ℛ ⟨ D , ptt ⟩) ≃ D
  GetRight-ℛ D = ⟨ (λ d d∈ → [ (λ d∈₂ → ⊥-elim (proj₂ (proj₂ (proj₂ d∈₂)))) 
                            , (λ d∈₁ → proj₁ (proj₂ (proj₂ d∈₁)) d (proj₂ (proj₂ (proj₂ d∈₁)))) ] d∈) 
                , (λ d d∈ → inj₂ ⟨ d , ⟨ [] , ⟨ (λ z → λ { (here refl) → d∈ }) , here refl ⟩ ⟩ ⟩) ⟩

  Case : 𝒫 Value → (𝒫 Value → 𝒫 Value) → (𝒫 Value → 𝒫 Value) → 𝒫 Value
  Case L M N = 𝒞 ⟨ L , ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟩

  Fst : ∀ n → 𝒫 Value → 𝒫 Value
  Fst n D = proj {suc n} zero ⟨ D , ptt ⟩

  Rst : 𝒫 Value → 𝒫 Value
  Rst D (tup[ i ] d) = tup[ suc i ] d ∈ D
  Rst D d = False

  Nth : ∀ {n} (i : Fin n) → 𝒫 Value → 𝒫 Value
  Nth i D = proj i ⟨ D , ptt ⟩

  Nth-consis : ∀ {n} (i : Fin n) D → consis D → consis (Nth i D)
  Nth-consis i D D~ = {! !} {- proj-consis i ⟨ D , ptt ⟩ ⟨ D , ptt ⟩ ⟨ D~ , ptt ⟩ -}


  fro : ∀ (dₜ : Value) → (Dₜ : 𝒫 Value) → (Dₛ : 𝒫 Value) → Set₁
  froList : ∀ (Vₜ : List Value) → (Dₜ : 𝒫 Value) → (Dₛ : 𝒫 Value) → Set₁
  froList [] _ _ = Lift (lsuc lzero) False
  froList (v ∷ []) Dₜ Dₛ = fro v Dₜ Dₛ
  froList (v ∷ (v' ∷ V)) Dₜ Dₛ = fro v Dₜ Dₛ × froList (v' ∷ V) Dₜ Dₛ
  fro (const k) Dₜ Dₛ = Lift (lsuc lzero) (Dₜ ≃ Dₛ)
  fro (V ↦ dₜ) Dₜ Dₛ = Lift (lsuc lzero) False {- will never come up -}
  fro ν Dₜ Dₛ = Lift (lsuc lzero) False {- will never come up -}
  fro ω Dₜ Dₛ = Lift (lsuc lzero) (Dₜ ≃ Dₛ) {- similar to const case -}
  {- next two cases... ??? ...can't survive self-app -}
  fro ⦅ ν ∣ Dₜ Dₛ = Lift (lsuc lzero) True
  fro ⦅ FV ↦ ν ∣ Dₜ Dₛ = Lift (lsuc lzero) True  
  fro ⦅ [] ↦ (V ↦ w) ∣ Dₜ Dₛ = Lift (lsuc lzero) False {- will never come up -}
  fro ⦅ (fv ∷ FV) ↦ ([] ↦ w) ∣ Dₜ Dₛ = Lift (lsuc lzero) False {- will never come up -}
  fro ⦅ (fv ∷ FV) ↦ ((v ∷ V) ↦ w) ∣ Dₜ Dₛ = ∀ Eₜ Eₛ (Eₜ~ : consis Eₜ) (Eₛ~ : consis Eₛ) (v∷V⊆Eₜ : mem (v ∷ V) ⊆ Eₜ)
                → (froE : froList (v ∷ V) Eₜ Eₛ)
               {- the next premise is a bit odd
                   ... how are we handling the case where this fails? -}
                {- is there something besides membership that we can use 
                   to constrain the given value and denotations?
                   Is this fine, or is it too strict and we need to go back to 'Type's? -}
                → (fv∷FV⊆CdrDₜ : mem (fv ∷ FV) ⊆ Cdr Dₜ)  
                → fro w (((Car Dₜ)  ● (Cdr Dₜ)) ● Eₜ) (Dₛ ● Eₛ)
  fro ⦅ d ∣ Dₜ Dₛ = Lift (lsuc lzero) False {- will never come up -}
  fro ∣ [] ⦆ Dₜ Dₛ = Lift (lsuc lzero) False {- will never come up -}
  fro ∣ (v ∷ V) ⦆ Dₜ Dₛ = froList (v ∷ V) (Cdr Dₜ) (Cdr Dₛ)
  fro (tup[_]_ {n} i dₜ) Dₜ Dₛ = fro dₜ (Nth i Dₜ) (Nth i Dₛ)
  fro (left dₜ) Dₜ Dₛ = fro dₜ (GetLeft Dₜ) (GetLeft Dₛ)
  fro (right dₜ) Dₜ Dₛ = fro dₜ (GetRight Dₜ) (GetRight Dₛ)

  postulate
    ⟦⟧-consis : ∀ M ρ → (∀ i → consis (ρ i)) → consis (⟦ M ⟧ ρ)
    ⟦⟧'-consis : ∀ M' ρ' → (∀ i → consis (ρ' i)) → consis (⟦ M' ⟧' ρ')
    fro-cong : ∀ D' D E' E → D' ≃ E' → D ≃ E → ∀ d' → fro d' D' D → fro d' E' E


  delay-reflect : ∀ M ρ ρ' (ρ~ : ∀ i → consis (ρ i)) (ρ'~ : ∀ i → consis (ρ' i))
     → (ρfro : ∀ i d' → (d'∈ : d' ∈ (ρ' i)) 
           → Σ[ d ∈ Value ] d ∈ ρ i × fro d' (ρ' i) (ρ i))
     → ∀ d' → (d'∈ : d' ∈ ⟦ delay M ⟧' ρ') 
     → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ × fro d' (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
  delay-reflect-⊆ : ∀ M ρ ρ' (ρ~ : ∀ i → consis (ρ i)) (ρ'~ : ∀ i → consis (ρ' i))
     → (ρfro : ∀ i d' → (d'∈ : d' ∈ (ρ' i)) 
           → Σ[ d ∈ Value ] d ∈ ρ i × fro d' (ρ' i) (ρ i))
     → ∀ V' → (V'⊆ : mem V' ⊆ ⟦ delay M ⟧' ρ') → V' ≢ []
     → Σ[ V ∈ List Value ] (mem V ⊆ ⟦ M ⟧ ρ × V ≢ [] ) × froList V' (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
  delay-reflect-⊆ M ρ ρ' ρ~ ρ'~ ρfro [] v'∷V'⊆ neV = ⊥-elim (neV refl)
  delay-reflect-⊆ M ρ ρ' ρ~ ρ'~ ρfro (v ∷ []) v'∷V'⊆ neV
    with delay-reflect M ρ ρ' ρ~ ρ'~ ρfro v (v'∷V'⊆ v (here refl))
  ... | ⟨ v , ⟨ v∈ , frov ⟩ ⟩ = ⟨ v ∷ [] , ⟨ ⟨ (λ d → λ { (here refl) → v∈ }) , (λ ()) ⟩ , frov ⟩ ⟩
  delay-reflect-⊆ M ρ ρ' ρ~ ρ'~ ρfro (v ∷ (v' ∷ V')) v'∷V'⊆ neV
    with delay-reflect M ρ ρ' ρ~ ρ'~ ρfro v (v'∷V'⊆ v (here refl)) 
       | delay-reflect-⊆ M ρ ρ' ρ~ ρ'~ ρfro (v' ∷ V') (λ d z → v'∷V'⊆ d (there z)) (λ ())
  ... | ⟨ v , ⟨ v∈ , frov ⟩ ⟩ | ⟨ V , ⟨ ⟨ V⊆ , neV ⟩ , froV ⟩ ⟩ = 
    ⟨ v ∷ V , ⟨ ⟨ (λ d → λ {(here refl) → v∈ ; (there d∈) → V⊆ d d∈ }) , (λ ()) ⟩
            , ⟨ frov , froV ⟩ ⟩ ⟩
  del-map-args-reflect : ∀ {n} args ρ ρ' (ρ~ : ∀ i → consis (ρ i)) (ρ'~ : ∀ i → consis (ρ' i))
     → (ρfro : ∀ i d' → (d'∈ : d' ∈ (ρ' i)) 
           → Σ[ d ∈ Value ] d ∈ ρ i × fro d' (ρ' i) (ρ i))     
     {- → ∀ d' → (d'∈ : d' ∈ ⟦ delay M ⟧' ρ') 
         → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ × fro d' (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ) -}
     → results-rel-pres-1 (λ D' D → ∀ d' → d' ∈ D' → Σ[ d ∈ Value ] d ∈ D × fro d' D' D) 
                          (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ') (⟦ args ⟧₊ ρ)
  del-map-args-reflect {zero} Nil ρ ρ' ρ~ ρ'~ ρfro = ptt
  del-map-args-reflect {suc n} (M ,, args) ρ ρ' ρ~ ρ'~ ρfro = 
    ⟨ lift (delay-reflect M ρ ρ' ρ~ ρ'~ ρfro) , del-map-args-reflect args ρ ρ' ρ~ ρ'~ ρfro ⟩
 
  delay-reflect (` x) ρ ρ' ρ~ ρ'~ ρfro = ρfro x
  delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
    ρ ρ' ρ~ ρ'~ ρfro ⦅ [] ↦ (V' ↦ d') ∣ 
    ⟨ FV'' , ⟨ ⟨ ⟨ d'∈N' , neV' ⟩ , neFV' ⟩ , ⟨ FV''⊆fvs' , neFV'' ⟩ ⟩ ⟩ = 
    ⊥-elim (neFV' refl)
  delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
    ρ ρ' ρ~ ρ'~ ρfro ⦅ (fv' ∷ FV') ↦ ([] ↦ d') ∣ 
    ⟨ FV'' , ⟨ ⟨ ⟨ d'∈N' , neV' ⟩ , neFV' ⟩ , ⟨ FV''⊆fvs' , neFV'' ⟩ ⟩ ⟩ = 
    ⊥-elim (neV' refl)
  delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
    ρ ρ' ρ~ ρ'~ ρfro ⦅ (fv' ∷ FV') ↦ ((v' ∷ V') ↦ d') ∣ 
    ⟨ FV'' , ⟨ ⟨ ⟨ d'∈N' , neV' ⟩ , neFV' ⟩ , ⟨ FV''⊆fvs' , neFV'' ⟩ ⟩ ⟩ = 
    ⟨ {!  !} , ⟨ {!   !} , {! cond' !} ⟩ ⟩
    where
    fun' = ƛ (λ X → (ƛ (λ Y → (⟦ delay N ⟧' (Y • X • λ x w → w ≡ ω)))))
    env' = 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ')
    closure' = (Pair fun' env')
    self-app' = (Car closure') ● (Cdr closure')
    fun = ƛ (λ X → (ƛ (λ Y → (⟦ N ⟧ (Y • X • λ x w → w ≡ ω)))))
    env = 𝒯 n (⟦ fvs ⟧₊ ρ)
    early-app = fun ● env
    cond : ∀ Eₜ Eₛ → consis Eₜ → consis Eₛ → mem (v' ∷ V') ⊆ Eₜ
         → froList (v' ∷ V') Eₜ Eₛ 
         → mem (fv' ∷ FV') ⊆ env' 
         → fro d' self-app' early-app
    cond Eₜ Eₛ Eₜ~ Eₛ~ V'⊆Eₜ froE FV'⊆fvs' = {!   !}
    H : Cdr closure' ⊆ env'
    H d ⟨ FV , ⟨ ⟨ _ , ⟨ _ , ⟨ FV⊆𝒯 , _ ⟩ ⟩ ⟩ , d∈FV ⟩ ⟩ = FV⊆𝒯 d d∈FV
    cond' : ∀ Eₜ Eₛ → consis Eₜ → consis Eₛ → mem (v' ∷ V') ⊆ Eₜ
         → froList (v' ∷ V') Eₜ Eₛ 
         → mem (fv' ∷ FV') ⊆ Cdr (Pair (ƛ (λ X → (ƛ (λ Y → (⟦ delay N ⟧' (Y • X • λ x w → w ≡ ω)))))) (𝒯 n (⟦ del-map-args fvs ⟧₊' ρ')))
         → fro d' self-app' early-app
    cond' Eₜ Eₛ Eₜ~ Eₛ~ V'⊆Eₜ froE FV'⊆cdrpair = cond Eₜ Eₛ Eₜ~ Eₛ~ V'⊆Eₜ froE (λ d d∈ → H d (FV'⊆cdrpair d d∈))
    IHFV : {!   !}
    IHFV = {!   !}
    IHFV'' : ∀ n fvs d' → d' ∈ 𝒯 n (⟦ del-map-args fvs ⟧₊' ρ') 
          → Σ[ d ∈ Value ] d ∈ 𝒯 n (⟦ fvs ⟧₊ ρ) 
                         × (fro d' (𝒯 n (⟦ del-map-args fvs ⟧₊' ρ')) (𝒯 n (⟦ fvs ⟧₊ ρ)))
    IHFV'' (suc n) (fv ,, fvs) (tup[ zero ] d') ⟨ refl , d'∈ ⟩
      with delay-reflect fv ρ ρ' ρ~ ρ'~ ρfro d' d'∈
    ... | ⟨ d , ⟨ d∈ , frod ⟩ ⟩ = ⟨ tup[ zero ] d , ⟨ ⟨ refl , d∈ ⟩ , {! frod   !} ⟩ ⟩
    IHFV'' (suc n) (fv ,, fvs) (tup[ suc i ] d') ⟨ refl , d'∈ ⟩ = {! IHFV' n fvs (tup[ i ] d')  !}
    {- then we have to map this to different results 
       depending on whether it would succeed at self-application or not -}
  {-
  IHV' : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV' zero fvs d refl = refl
  IHV' (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , IHV' n fvs ∥ ds ∥ ds∈ ⟩
  IHV : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = IHV' n fvs a (FV⊆𝒯fvs a a∈)
  -}
  delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
    ρ ρ' ρ~ ρ'~ ρfro ⦅ FV' ↦ ν ∣ 
    ⟨ FV'' , ⟨ ⟨ tt , neFV' ⟩ , ⟨ FV''⊆fvs' , neFV'' ⟩ ⟩ ⟩ = ⟨ ν , ⟨ {!    !} , {!   !} ⟩ ⟩
  delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
    ρ ρ' ρ~ ρ'~ ρfro ⦅ ν ∣ 
    ⟨ FV'' , ⟨ tt , ⟨ FV''⊆fvs' , neFV'' ⟩ ⟩ ⟩ = ⟨ ν , ⟨ {!  !} , {!   !} ⟩ ⟩
  delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
    ρ ρ' ρ~ ρ'~ ρfro ∣ V ⦆ d'∈ = ⟨ ν , ⟨ {!   !} , {!   !} ⟩ ⟩
  delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ ρ' ρ~ ρ'~ ρfro d' 
    ⟨ [] , ⟨ ⟨ FV' , ⟨ ⦅FV'↦V'↦d'∣∈M' , ⟨ FV'⊆cdrM' , neFV' ⟩ ⟩ ⟩ , ⟨ V'⊆N' , neV' ⟩ ⟩ ⟩ = ⊥-elim (neV' refl)
  delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ ρ' ρ~ ρ'~ ρfro d' 
    ⟨ (v' ∷ V') , ⟨ ⟨ [] , ⟨ ⦅FV'↦V'↦d'∣∈M' , ⟨ FV'⊆cdrM' , neFV' ⟩ ⟩ ⟩ , ⟨ V'⊆N' , neV' ⟩ ⟩ ⟩ = ⊥-elim (neFV' refl)
  delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ ρ' ρ~ ρ'~ ρfro d' 
    ⟨ (v' ∷ V') , ⟨ ⟨ (fv' ∷ FV') , ⟨ ⦅FV'↦V'↦d'∣∈M' , ⟨ FV'⊆cdrM' , neFV' ⟩ ⟩ ⟩ , ⟨ V'⊆N' , neV' ⟩ ⟩ ⟩ = 
    ⟨ {!   !} , ⟨ ⟨ proj₁ IHN , ⟨ {!    !} , proj₁ (proj₂ IHN) ⟩ ⟩ , IH ⟩ ⟩
    where
    IHcarM : Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ × fro (⦅ ((fv' ∷ FV') ↦ ((v' ∷ V') ↦ d')) ∣) (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
    IHcarM = delay-reflect M ρ ρ' ρ~ ρ'~ ρfro (⦅ ((fv' ∷ FV') ↦ ((v' ∷ V') ↦ d')) ∣) ⦅FV'↦V'↦d'∣∈M'
    d = proj₁ IHcarM
    d∈ = proj₁ (proj₂ IHcarM)
    cond = proj₂ (proj₂ IHcarM)
    IHN : Σ[ V ∈ List Value ] (mem V ⊆ ⟦ N ⟧ ρ × V ≢ []) × froList (v' ∷ V') (⟦ delay N ⟧' ρ') (⟦ N ⟧ ρ)
    IHN = delay-reflect-⊆ N ρ ρ' ρ~ ρ'~ ρfro (v' ∷ V') V'⊆N' neV'
    IH = cond (⟦ delay N ⟧' ρ') (⟦ N ⟧ ρ) (⟦⟧'-consis (delay N) ρ' ρ'~) (⟦⟧-consis N ρ ρ~) V'⊆N' (proj₂ (proj₂ IHN)) FV'⊆cdrM'
    {-
    where
    carM∶T' : Σ[ n ∈ ℕ ] Σ[ FVTs ∈ Vec Type' n ] (hasType' (Clos n FVTs) ⦅ FV' ↦ (V' ↦ d') ∣)
    carM∶T' = {!   !}
    n' : ℕ
    n' = proj₁ carM∶T'
    FVTs : Vec Type' n'
    FVTs = proj₁ (proj₂ carM∶T')
    IHcarM : Σ[ f ∈ Value ] f ∈ ⟦ M ⟧ ρ × hasType Fun f
           × Σ[ c ∈ ℕ ] fro c (Clos n' FVTs) (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
    IHcarM = delay-reflect M ρ ρ' ρ~ ρ'~ ρfro (Clos n' FVTs) (⦅ (FV' ↦ (V' ↦ d')) ∣) ⦅FV'↦V'↦d'∣∈M' tt
    IHcdrM : {! ∀ fv' → fv' ∈ mem FV'
           → Σ[ fv ∈ Value ] ∣ fv ⦆ ∈ ⟦ N ⟧ ρ × hasType ? ∣ fv ⦆ 
           × Σ[ c ∈ ℕ ] fro c ? (⟦ delay N ⟧' ρ') (⟦ N ⟧ ρ)  !}
    IHcdrM = {!   !}
    V'∶T' : ∀ v' → v' ∈ mem V' → Σ[ Tv' ∈ Type' ] hasType' Tv' v'
    V'∶T' v' v'∈V' = {!   !}
    IHN : ∀ v' → (v'∈V' : v' ∈ mem V') 
        → Σ[ v ∈ Value ] v ∈ ⟦ N ⟧ ρ × hasType (froT (proj₁ (V'∶T' v' v'∈V'))) v 
        × Σ[ c ∈ ℕ ] fro c (proj₁ (V'∶T' v' v'∈V')) (⟦ delay N ⟧' ρ') (⟦ N ⟧ ρ)
    IHN v' v'∈V' = delay-reflect N ρ ρ' ρ~ ρ'~ ρfro (proj₁ (V'∶T' v' v'∈V')) v' 
                                 (V'⊆N' v' v'∈V') (proj₂ (V'∶T' v' v'∈V'))
    -}
  delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ' ρ~ ρ'~ ρfro (const k'') ⟨ refl , refl ⟩ = 
    ⟨ const k , ⟨ ⟨ refl , refl ⟩ , lift ⟨ (λ d z → z) , (λ d z → z) ⟩ ⟩ ⟩
  delay-reflect (tuple n ⦅ args ⦆) ρ ρ' ρ~ ρ'~ ρfro d' d'∈ = {!   !}
  delay-reflect (get i ⦅ M ,, Nil ⦆) ρ ρ' ρ~ ρ'~ ρfro d' d'∈ = {!   !}
  delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ ρ'~ ρfro (left d') d'∈ 
    with delay-reflect M ρ ρ' ρ~ ρ'~ ρfro d' d'∈
  ... | ⟨ d , ⟨ d∈ , frod ⟩ ⟩ = ⟨ left d , ⟨ d∈ , frod' ⟩ ⟩
    where
    frod' = fro-cong (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ) 
                     (GetLeft (Left (⟦ delay M ⟧' ρ'))) (GetLeft (Left (⟦ M ⟧ ρ))) 
                     (≃-sym (GetLeft-ℒ (⟦ delay M ⟧' ρ'))) (≃-sym (GetLeft-ℒ (⟦ M ⟧ ρ))) 
                     d' frod
  delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ ρ'~ ρfro (right d') d'∈
    with delay-reflect M ρ ρ' ρ~ ρ'~ ρfro d' d'∈
  ... | ⟨ d , ⟨ d∈ , frod ⟩ ⟩ = ⟨ right d , ⟨ d∈ , frod' ⟩ ⟩
    where
    frod' = fro-cong (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ) 
                     (GetRight (Right (⟦ delay M ⟧' ρ'))) (GetRight (Right (⟦ M ⟧ ρ))) 
                     (≃-sym (GetRight-ℛ (⟦ delay M ⟧' ρ'))) (≃-sym (GetRight-ℛ (⟦ M ⟧ ρ))) 
                     d' frod
  delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ ρ' ρ~ ρ'~ ρfro d' 
    (inj₁ ⟨ v' , ⟨ V' , ⟨ V'⊆L' , d'∈M ⟩ ⟩ ⟩)
      = ⟨ proj₁ IHM , ⟨ inj₁ ⟨ v , ⟨ V , ⟨ V⊆L , proj₁ (proj₂ IHM) ⟩ ⟩ ⟩ , frod ⟩ ⟩
    where
    IHv : ∀ v'' → v'' ∈ mem (v' ∷ V') → Σ[ v ∈ Value ] left v ∈ ⟦ L ⟧ ρ 
    IHv v'' v''∈ with delay-reflect L ρ ρ' ρ~ ρ'~ ρfro (left v'') (V'⊆L' v'' v''∈)
    ... | ⟨ v , ⟨ v∈ , vfro ⟩ ⟩ = {!   !}
    IHL : Σ[ v ∈ Value ] Σ[ V ∈ List Value ] All (λ v'' → left v'' ∈ ⟦ L ⟧ ρ) (v ∷ V)
    IHL with ∈-construct (λ z → left z ∈ ⟦ L ⟧ ρ) (v' ∷ V') IHv | inspect (∈-construct (λ z → left z ∈ ⟦ L ⟧ ρ) (v' ∷ V')) IHv
    ... | ⟨ [] , V⊆ ⟩ | [ () ]
    ... | ⟨ v ∷ V , v∈ ∷ V⊆ ⟩ | _ = ⟨ v , ⟨ V , v∈ ∷ V⊆ ⟩ ⟩
    v = proj₁ IHL
    V = proj₁ (proj₂ IHL)
    V⊆L = All→∈ (λ v'' → left v'' ∈ ⟦ L ⟧ ρ) (v ∷ V) (proj₂ (proj₂ IHL))
    IHM : Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ((mem (v ∷ V)) • ρ) 
        × fro d' (⟦ delay M ⟧' (mem (v' ∷ V') • ρ')) (⟦ M ⟧ (mem (v ∷ V) • ρ))
    IHM = delay-reflect M ((mem (v ∷ V)) • ρ) ((mem (v' ∷ V')) • ρ')
         {!   !} {!   !} {!   !} d' d'∈M
    case' = Case (⟦ delay L ⟧' ρ') (λ X → ⟦ delay M ⟧' (X • ρ')) (λ X → ⟦ delay N ⟧' (X • ρ'))
    case = Case (⟦ L ⟧ ρ) (λ X → ⟦ M ⟧ (X • ρ)) (λ X → ⟦ N ⟧ (X • ρ))
    frod : fro d' case' case
    frod = fro-cong (⟦ delay M ⟧' (mem (v' ∷ V') • ρ')) (⟦ M ⟧ (mem (v ∷ V) • ρ)) case' case {!   !} {!   !} d' (proj₂ (proj₂ IHM))
{-  with delay-reflect-⊆ L ρ ρ' ρ~ ρ'~ ρfro (v' ∷ V') {! V'⊆L'  !} {!   !} 
  ... | ⟨ V , ⟨ ⟨ V⊆L , neV ⟩ , froV ⟩ ⟩ 
  
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → left d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect L ρ (left b) (LV∈ b b∈)  
  
  
  
  
  -}
  delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ ρ' ρ~ ρ'~ ρfro d' 
    (inj₂ ⟨ v' , ⟨ V' , ⟨ V'⊆L' , d'∈N ⟩ ⟩ ⟩)
    with delay-reflect-⊆ L ρ ρ' ρ~ ρ'~ ρfro (v' ∷ V') {!   !} {!   !}
  ... | ⟨ V , ⟨ ⟨ V⊆L , neV ⟩ , froV ⟩ ⟩ 
    = {!   !}


{-
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → left d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect L ρ (left b) (LV∈ b b∈)
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → right d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect L ρ (right b) (RV∈ b b∈)

-}







{-
 Σ[ V ∈ List Value ] (mem V ⊆ ⟦ M ⟧ ρ × V ≢ [] ) × froList V' (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
-}
{-
fro : ∀ (dₜ : Value) → (Dₜ : 𝒫 Value) → (Dₛ : 𝒫 Value) → consis Dₜ → consis Dₛ → dₜ ∈ Dₜ → Set₁
  froList : ∀ (Vₜ : List Value) → (Dₜ : 𝒫 Value) → (Dₛ : 𝒫 Value) → consis Dₜ → consis Dₛ → (mem Vₜ) ⊆ Dₜ → Vₜ ≢ [] → Set₁
  froList [] _ _ _ _ _ neq = ⊥-elim (neq refl)
  froList (v ∷ []) Dₜ Dₛ Dₜ~ Dₛ~ [v]⊆Dₜ _ = fro v Dₜ Dₛ Dₜ~ Dₛ~ ([v]⊆Dₜ v (here refl)) 
  froList (v ∷ (v' ∷ V)) Dₜ Dₛ Dₜ~ Dₛ~ v∷V⊆Dₜ ne-v∷v'∷V = 
      fro v Dₜ Dₛ Dₜ~ Dₛ~ (v∷V⊆Dₜ v (here refl)) 
    × froList (v' ∷ V) Dₜ Dₛ Dₜ~ Dₛ~ (λ d z → v∷V⊆Dₜ d (there z)) (λ ())
  fro (const k) Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) (Dₜ ≃ Dₛ)
  fro (V ↦ dₜ) Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) False {- will never come up -}
  fro ν Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) False {- will never come up -}
  fro ω Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) (Dₜ ≃ Dₛ) {- similar to const case -}
  {- next two cases... ??? ...can't survive self-app -}
  fro ⦅ ν ∣ Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) True
  fro ⦅ FV ↦ ν ∣ Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) True  
  fro ⦅ [] ↦ (V ↦ w) ∣ Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) False {- will never come up -}
  fro ⦅ (fv ∷ FV) ↦ ([] ↦ w) ∣ Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) False {- will never come up -}
  fro ⦅ (fv ∷ FV) ↦ ((v ∷ V) ↦ w) ∣ Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = ∀ Eₜ Eₛ Eₜ~ Eₛ~ v∷V⊆Eₜ
                → (froE : froList (v ∷ V) Eₜ Eₛ Eₜ~ Eₛ~ v∷V⊆Eₜ (λ ()))
               {- the next premise is a bit odd
                   ... how are we handling the case where this fails? -}
                {- is there something besides membership that we can use 
                   to constrain the given value and denotations?
                   Is this fine, or is it too strict and we need to go back to 'Type's? -}
                → (fv∷FV⊆CdrDₜ : mem (fv ∷ FV) ⊆ Cdr Dₜ)  
                → fro w (((Car Dₜ)  ● (Cdr Dₜ)) ● Eₜ) (Dₛ ● Eₛ) 
                        (●-consis ((Car Dₜ)  ● (Cdr Dₜ)) Eₜ 
                                  (●-consis (Car Dₜ) (Cdr Dₜ) (Car-consis Dₜ Dₜ~) (Cdr-consis Dₜ Dₜ~)) Eₜ~) 
                        (●-consis Dₛ Eₛ Dₛ~ Eₛ~) 
                        ⟨ (v ∷ V) , ⟨ ⟨ (fv ∷ FV) , ⟨ d∈Dₜ , ⟨ fv∷FV⊆CdrDₜ , (λ ()) ⟩ ⟩ ⟩ , ⟨ v∷V⊆Eₜ , (λ ()) ⟩ ⟩ ⟩
  fro ⦅ d ∣ Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) False {- will never come up -}
  fro ∣ [] ⦆ Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = Lift (lsuc lzero) False {- will never come up -}
  fro ∣ (v ∷ V) ⦆ Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = 
     froList (v ∷ V) (Cdr Dₜ) (Cdr Dₛ) (Cdr-consis Dₜ Dₜ~) (Cdr-consis Dₛ Dₛ~) 
               (Cdr-∈ Dₜ d∈Dₜ) (λ ()) {- is this how to handle lists of values? -}
  fro (tup[_]_ {n} i dₜ) Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = fro dₜ (Nth i Dₜ) (Nth i Dₛ) (Nth-consis i Dₜ Dₜ~) (Nth-consis i Dₛ Dₛ~) d∈Dₜ
  fro (left dₜ) Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = fro dₜ (GetLeft Dₜ) (GetLeft Dₛ) (GetLeft-consis Dₜ Dₜ~) (GetLeft-consis Dₛ Dₛ~) (GetLeft-∈ Dₜ d∈Dₜ)
  fro (right dₜ) Dₜ Dₛ Dₜ~ Dₛ~ d∈Dₜ = fro dₜ (GetRight Dₜ) (GetRight Dₛ) (GetRight-consis Dₜ Dₜ~) (GetRight-consis Dₛ Dₛ~) (GetRight-∈ Dₜ d∈Dₜ)


-}


{- 


  fro-cong : ∀ Dₜ Dₛ Dₜ' Dₛ' → Dₛ ≃ Dₛ' → Dₜ ≃ Dₜ' → ∀ d → fro d Dₜ Dₛ → fro d Dₜ' Dₛ'
  froList-cong : ∀ Dₜ Dₛ Dₜ' Dₛ' → Dₛ ≃ Dₛ' → Dₜ ≃ Dₜ' → ∀ V → froList V Dₜ Dₛ → froList V Dₜ' Dₛ'
  froList-cong Dₜ Dₛ Dₜ' Dₛ' Dₛ≃ Dₜ≃ [] fro-V = lift tt
  froList-cong Dₜ Dₛ Dₜ' Dₛ' Dₛ≃ Dₜ≃ (v ∷ V) ⟨ fro-v , fro-V ⟩ = 
    ⟨ fro-cong Dₜ Dₛ Dₜ' Dₛ' Dₛ≃ Dₜ≃ v fro-v , froList-cong Dₜ Dₛ Dₜ' Dₛ' Dₛ≃ Dₜ≃ V fro-V ⟩
  fro-cong Dₜ Dₛ Dₜ' Dₛ' ⟨ Dₛ⊆ , ⊆Dₛ ⟩ ⟨ Dₜ⊆ , ⊆Dₜ ⟩ (const k) (lift ⟨ Dₜ⊆Dₛ , Dₛ⊆Dₜ ⟩) = 
    lift ⟨ (λ d z → Dₛ⊆ d (Dₜ⊆Dₛ d (⊆Dₜ d z))) , (λ d z → Dₜ⊆ d (Dₛ⊆Dₜ d (⊆Dₛ d z))) ⟩
  fro-cong Dₜ Dₛ Dₜ' Dₛ' ⟨ Dₛ⊆ , ⊆Dₛ ⟩ ⟨ Dₜ⊆ , ⊆Dₜ ⟩ ω (lift ⟨ Dₜ⊆Dₛ , Dₛ⊆Dₜ ⟩) = 
    lift ⟨ (λ x x₁ → Dₛ⊆ x (Dₜ⊆Dₛ x (⊆Dₜ x x₁))) , (λ x x₁ → Dₜ⊆ x (Dₛ⊆Dₜ x (⊆Dₛ x x₁))) ⟩
  fro-cong Dₜ Dₛ Dₜ' Dₛ' Dₛ≃ Dₜ≃ ⦅ V ↦ (V₁ ↦ d) ∣ fro-d Eₛ Eₜ froE = 
    fro-cong ((Car Dₜ ● Cdr Dₜ) ● Eₜ) (Dₛ ● Eₛ) ((Car Dₜ' ● Cdr Dₜ') ● Eₜ) (Dₛ' ● Eₛ) 
             (lower (⋆-cong ⟨ Dₛ , ⟨ Eₛ , ptt ⟩ ⟩ ⟨ Dₛ' , ⟨ Eₛ , ptt ⟩ ⟩ ⟨ lift Dₛ≃ , ⟨ lift ≃-refl , ptt ⟩ ⟩)) 
             (lower (⋆-cong ⟨ Car Dₜ ● Cdr Dₜ , ⟨ Eₜ , ptt ⟩ ⟩ ⟨ Car Dₜ' ● Cdr Dₜ' , ⟨ Eₜ , ptt ⟩ ⟩ 
                            ⟨ ⋆-cong ⟨ Car Dₜ , ⟨ Cdr Dₜ , ptt ⟩ ⟩ ⟨ Car Dₜ' , ⟨ Cdr Dₜ' , ptt ⟩ ⟩ 
                                    ⟨ car-cong ⟨ Dₜ , ptt ⟩ ⟨ Dₜ' , ptt ⟩ ⟨ lift Dₜ≃ , ptt ⟩ 
                                    , ⟨ cdr-cong ⟨ Dₜ , ptt ⟩ ⟨ Dₜ' , ptt ⟩ ⟨ lift Dₜ≃ , ptt ⟩ , ptt ⟩ ⟩ 
                    , ⟨ lift ≃-refl , ptt ⟩ ⟩)) d (fro-d Eₛ Eₜ froE)
  fro-cong Dₜ Dₛ Dₜ' Dₛ' ⟨ Dₛ⊆ , ⊆Dₛ ⟩ ⟨ Dₜ⊆ , ⊆Dₜ ⟩ ⦅ V ↦ ν ∣ fro-d = lift tt
  fro-cong Dₜ Dₛ Dₜ' Dₛ' ⟨ Dₛ⊆ , ⊆Dₛ ⟩ ⟨ Dₜ⊆ , ⊆Dₜ ⟩ ⦅ ν ∣ fro-d = lift tt
  fro-cong Dₜ Dₛ Dₜ' Dₛ' Dₛ≃ Dₜ≃ ∣ V ⦆ fro-d = 
    froList-cong (Cdr Dₜ) (Cdr Dₛ) (Cdr Dₜ') (Cdr Dₛ') 
                 (lower (cdr-cong ⟨ Dₛ , ptt ⟩  ⟨ Dₛ' , ptt ⟩ ⟨ lift Dₛ≃ ,  ptt ⟩))
                 (lower (cdr-cong ⟨ Dₜ , ptt ⟩ ⟨ Dₜ' , ptt ⟩ ⟨ lift Dₜ≃ , ptt ⟩ ))
                 V fro-d
  fro-cong Dₜ Dₛ Dₜ' Dₛ' ⟨ Dₛ⊆ , ⊆Dₛ ⟩ ⟨ Dₜ⊆ , ⊆Dₜ ⟩ (tup[ i ] d) fro-d = {!   !}
  fro-cong Dₜ Dₛ Dₜ' Dₛ' ⟨ Dₛ⊆ , ⊆Dₛ ⟩ ⟨ Dₜ⊆ , ⊆Dₜ ⟩ (left d) fro-d = {!   !}
  fro-cong Dₜ Dₛ Dₜ' Dₛ' ⟨ Dₛ⊆ , ⊆Dₛ ⟩ ⟨ Dₜ⊆ , ⊆Dₜ ⟩ (right d) fro-d = {!   !} 







  fro-mono-down : ∀ {Dₜ Dₛ Dₜ' Dₛ'} → consis Dₜ → consis Dₛ → Dₜ' ⊆ Dₜ → Dₛ' ⊆ Dₛ 
                → ∀ d → d ∈ Dₜ → fro d Dₜ Dₛ → fro d Dₜ' Dₛ'
  froList-mono-down : ∀ {Dₜ Dₛ Dₜ' Dₛ'} → consis Dₜ → consis Dₛ → Dₜ' ⊆ Dₜ → Dₛ' ⊆ Dₛ 
                    → ∀ V → (mem V) ⊆ Dₜ → froList V Dₜ Dₛ → froList V Dₜ' Dₛ'
  froList-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ [] _ _ = ptt
  froList-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ (v' ∷ V') v'∷V'⊆Dₜ ⟨ froDv' , froDV' ⟩ = 
    ⟨ fro-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ v' (v'∷V'⊆Dₜ v' (here refl)) froDv' 
    , froList-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ V' (λ d z → v'∷V'⊆Dₜ d (there z)) froDV' ⟩
  fro-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ (const k) d∈Dₜ froD = {!  !}
  fro-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ ω d∈Dₜ froD = {!   !}
  fro-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ ⦅ FV ↦ (V ↦ w) ∣ d∈Dₜ froD Eₛ Eₜ froE = 
    fro-mono-down {!   !} {!  !} {!   !} {!   !} w {!  !} (froD Eₛ Eₜ froE)
  fro-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ ⦅ FV ↦ ν ∣ d∈Dₜ froD = ptt
  fro-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ ⦅ ν ∣ d∈Dₜ froD = ptt
  fro-mono-down {Dₜ}{Dₛ}{Dₜ'}{Dₛ'} Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ ∣ FV ⦆ d∈Dₜ froD =
    froList-mono-down {Cdr Dₜ}{Cdr Dₛ}{Cdr Dₜ'}{Cdr Dₛ'} 
      (lower (cdr-consis ⟨ Dₜ , ptt ⟩ ⟨ Dₜ , ptt ⟩ ⟨ lift Dₜ~ , ptt ⟩)) 
      (lower (cdr-consis ⟨ Dₛ , ptt ⟩ ⟨ Dₛ , ptt ⟩ ⟨ lift Dₛ~ , ptt ⟩)) 
      (lower (cdr-mono ⟨ Dₜ' , ptt ⟩ ⟨ Dₜ , ptt ⟩ ⟨ lift Dₜ'⊆ , ptt ⟩)) 
      (lower (cdr-mono ⟨ Dₛ' , ptt ⟩ ⟨ Dₛ , ptt ⟩ ⟨ lift Dₛ'⊆ , ptt ⟩)) 
      FV (Cdr-∈ Dₜ d∈Dₜ) froD 
  fro-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ (tup[ i ] d) d∈Dₜ froD = {!   !}
  fro-mono-down {Dₜ}{Dₛ}{Dₜ'}{Dₛ'} Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ (left d) d∈Dₜ froD = 
    fro-mono-down {GetLeft Dₜ}{GetLeft Dₛ}{GetLeft Dₜ'}{GetLeft Dₛ'} 
      {!   !} 
      {!   !} 
      {!   !} 
      {!   !} 
      d {! d∈Dₜ  !} froD
  fro-mono-down Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ (right d) d∈Dₜ froD = {!   !}

  fro-mono-up : ∀ {Dₜ Dₛ Dₜ' Dₛ'} → consis Dₜ → consis Dₛ → Dₜ' ⊆ Dₜ → Dₛ' ⊆ Dₛ 
              → ∀ d → d ∈ Dₜ → fro d Dₜ' Dₛ' → fro d Dₜ Dₛ
  froList-mono-up : ∀ {Dₜ Dₛ Dₜ' Dₛ'} → consis Dₜ → consis Dₛ → Dₜ' ⊆ Dₜ → Dₛ' ⊆ Dₛ 
                  → ∀ V → (mem V) ⊆ Dₜ → froList V Dₜ' Dₛ' → froList V Dₜ Dₛ
  froList-mono-up Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ V V⊆Dₜ froD' = {!   !}
  fro-mono-up Dₜ~ Dₛ~ Dₜ'⊆ Dₛ'⊆ d' d'∈Dₜ froD' = {!   !}

-}

{-
  fro-⊆ : ∀ d' D' D → fro d' D' D → ∀ S' → S' ⊆ D' → Σ[ S ∈ 𝒫 Value ] S ⊆ D × fro d' S' S
  froList-⊆ : ∀ V' D' D → froList V' D' D → ∀ S' → S' ⊆ D' → Σ[ S ∈ 𝒫 Value ] S ⊆ D × froList V' S' S
  froList-⊆ [] D' D froD S' S'⊆ = ⟨ (λ v → False) , ⟨ ? , ptt ⟩ ⟩
  froList-⊆ (v' ∷ V') D' D ⟨ froDv' , froDV' ⟩ S' S'⊆ 
    with froList-⊆ V' D' D froDV' S' S'⊆
  ... | ⟨ SV , ⟨ SV⊆ , froSV ⟩ ⟩ with fro-⊆ v' S' SV froSV S' (λ d z → z)
  ... | ⟨ Sv , ⟨ Sv⊆ , froSv ⟩ ⟩ = ⟨ Sv , ⟨ ? , {!   !} ⟩ ⟩
  fro-⊆ (const k) D' D froD S' S'⊆ = ⟨ S' , ⟨ ? , lift ≃-refl ⟩ ⟩
  fro-⊆ ω D' D froD S' S'⊆ = ⟨ S' , ⟨ ? , lift ≃-refl ⟩ ⟩
  fro-⊆ ⦅ V ↦ (V₁ ↦ d') ∣ D' D froD S' S'⊆ = {! froD  !}
  fro-⊆ ⦅ V ↦ ν ∣ D' D froD S' S'⊆ = ⟨ ⌈ ν ⌉ , ⟨ ? , ptt ⟩ ⟩
  fro-⊆ ⦅ ν ∣ D' D froD S' S'⊆ = ⟨ ⌈ ν ⌉ , ⟨ ? , ptt ⟩ ⟩
  fro-⊆ ∣ [] ⦆ D' D froD S' S'⊆ = ⟨ ⌈ ν ⌉ , ⟨ ? , ptt ⟩ ⟩
  fro-⊆ ∣ x ∷ V ⦆ D' D froD S' S'⊆ = {!  !}
  fro-⊆ (tup[ i ] d') D' D froD S' S'⊆ = {!   !}
  fro-⊆ (left d') D' D froD S' S'⊆ = 
     ⟨ ℒ ⟨ (proj₁ IH) , ptt ⟩ 
     , ⟨ ? , 
        fro-cong (GetLeft S') (proj₁ IH) (GetLeft S') (GetLeft (ℒ ⟨ proj₁ IH , ptt ⟩)) 
                (swap (GetLeft-ℒ (proj₁ IH))) ≃-refl d' (proj₂ IH) ⟩ ⟩
    where
    IH : Σ[ S ∈ 𝒫 Value ] fro d' (GetLeft S') S
    IH = fro-⊆ d' (GetLeft D') (GetLeft D) froD (GetLeft S') 
                  (lower (𝒞-mono ⟨ S' , ⟨ (λ X → X) , ⟨ (λ X v → False) , ptt ⟩ ⟩ ⟩ 
                                 ⟨ D' , ⟨ (λ X → X) , ⟨ (λ X v → False) , ptt ⟩ ⟩ ⟩ 
                                 ⟨ lift S'⊆ , ⟨ (λ a1 a2 → lift) , ⟨ (λ a1 a2 _ → lift (λ x x₁ → x₁)) , ptt ⟩ ⟩ ⟩))
  fro-⊆ (right d') D' D froD S' S'⊆ = {!   !}




  delay-reflect' : ∀ M ρ ρ' → (ρ~ : ∀ i d' → d' ∈ ρ' i → fro d' (ρ' i) (ρ i)) 
                 → ∀ d' → d' ∈ ⟦ delay M ⟧' ρ' → fro d' (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
  delay-reflect' (` x) ρ ρ' ρ~ = ρ~ x
  delay-reflect' (clos-op x ⦅ ! (clear (bind (bind (ast N)))) ,, fvs ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect' (lit B k ⦅ Nil ⦆) ρ ρ' ρ~ (const k') d'∈ = lift ⟨ (λ d z → z) , (λ d z → z) ⟩
  delay-reflect' (tuple n ⦅ args ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ (left d') d'∈ = 
    fro-cong (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ) 
             (GetLeft (ℒ ⟨ ⟦ delay M ⟧' ρ' , ptt ⟩)) (GetLeft (ℒ ⟨ ⟦ M ⟧ ρ , ptt ⟩)) 
             (swap (GetLeft-ℒ (⟦ M ⟧ ρ))) (swap (GetLeft-ℒ (⟦ delay M ⟧' ρ'))) d' IHM
    where
    IHM : fro d' (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
    IHM = delay-reflect' M ρ ρ' ρ~ d' d'∈
  delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect' (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ ρ' ρ~ d' (inj₁ ⟨ v , ⟨ V , ⟨ V⊆L' , d'∈M' ⟩ ⟩ ⟩) 
    = {! IHd'  !}
    where
    IHV : ∀ d → d ∈ mem (v ∷ V) → fro (left d) (⟦ delay L ⟧' ρ') (⟦ L ⟧ ρ) 
    IHV d d∈ = delay-reflect' L ρ ρ' ρ~ (left d) (V⊆L' d d∈)
    IHd' : fro d' (⟦ delay M ⟧' ((mem V) • ρ')) (⟦ M ⟧ ((⟦ L ⟧ ρ) • ρ))
    IHd' = {!   !}
  delay-reflect' (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ ρ' ρ~ d' (inj₂ ⟨ v , ⟨ V , ⟨ V⊆L' , d'∈N' ⟩ ⟩ ⟩) 
    = {!   !}

  delay-reflect : ∀ M ρ ρ' 
     → (ρ~ : ∀ i d' → d' ∈ (ρ' i) 
           → Σ[ d ∈ Value ] d ∈ ρ i × fro d' (ρ' i) (ρ i))
     → ∀ d' → d' ∈ ⟦ delay M ⟧' ρ' 
     → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ × fro d' (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
  delay-reflect (` x) ρ ρ' ρ~ = ρ~ x
  delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ ρ' ρ~ d' 
    ⟨ V' , ⟨ ⟨ FV' , ⟨ ⦅FV'↦V'↦d'∣∈M' , ⟨ FV'⊆cdrM' , neFV' ⟩ ⟩ ⟩ , ⟨ V'⊆N' , neV' ⟩ ⟩ ⟩
    = {!   !}
    {-
    where
    carM∶T' : Σ[ n ∈ ℕ ] Σ[ FVTs ∈ Vec Type' n ] (hasType' (Clos n FVTs) ⦅ FV' ↦ (V' ↦ d') ∣)
    carM∶T' = {!   !}
    n' : ℕ
    n' = proj₁ carM∶T'
    FVTs : Vec Type' n'
    FVTs = proj₁ (proj₂ carM∶T')
    IHcarM : Σ[ f ∈ Value ] f ∈ ⟦ M ⟧ ρ × hasType Fun f
           × Σ[ c ∈ ℕ ] fro c (Clos n' FVTs) (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
    IHcarM = delay-reflect M ρ ρ' ρ~ (Clos n' FVTs) (⦅ (FV' ↦ (V' ↦ d')) ∣) ⦅FV'↦V'↦d'∣∈M' tt
    IHcdrM : {! ∀ fv' → fv' ∈ mem FV'
           → Σ[ fv ∈ Value ] ∣ fv ⦆ ∈ ⟦ N ⟧ ρ × hasType ? ∣ fv ⦆ 
           × Σ[ c ∈ ℕ ] fro c ? (⟦ delay N ⟧' ρ') (⟦ N ⟧ ρ)  !}
    IHcdrM = {!   !}
    V'∶T' : ∀ v' → v' ∈ mem V' → Σ[ Tv' ∈ Type' ] hasType' Tv' v'
    V'∶T' v' v'∈V' = {!   !}
    IHN : ∀ v' → (v'∈V' : v' ∈ mem V') 
        → Σ[ v ∈ Value ] v ∈ ⟦ N ⟧ ρ × hasType (froT (proj₁ (V'∶T' v' v'∈V'))) v 
        × Σ[ c ∈ ℕ ] fro c (proj₁ (V'∶T' v' v'∈V')) (⟦ delay N ⟧' ρ') (⟦ N ⟧ ρ)
    IHN v' v'∈V' = delay-reflect N ρ ρ' ρ~ (proj₁ (V'∶T' v' v'∈V')) v' 
                                 (V'⊆N' v' v'∈V') (proj₂ (V'∶T' v' v'∈V'))
    -}
  delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ' ρ~ (const k'') ⟨ refl , refl ⟩ = 
    ⟨ const k , ⟨ ⟨ refl , refl ⟩ , lift ⟨ (λ d z → z) , (λ d z → z) ⟩ ⟩ ⟩
  delay-reflect (tuple n ⦅ args ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (get i ⦅ M ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}

  -}

{-

  fro-∅ : ∀ d (tvd : targetValue d) → fro d ∅ ∅
  froList-∅ : ∀ V (tvsV : targetValues V) → froList V ∅ ∅
  froList-∅ [] tt = ptt
  froList-∅ (v ∷ V) ⟨ tvv , tvsV ⟩ = ⟨ fro-∅ v tvv , froList-∅ V tvsV ⟩
  fro-∅ (const k) tt = lift ⟨ (λ x x₁ → x₁) , (λ x x₁ → x₁) ⟩
  fro-∅ ω tt = {!   !}
  fro-∅ ⦅ ν ∣ tt = {!   !}
  fro-∅ ⦅ FV ↦ ν ∣ tvsFV = {!   !}
  fro-∅ ⦅ FV ↦ (V ↦ w) ∣ ⟨ tvsFV , ⟨ tvsV , tvw ⟩ ⟩ Eₛ Eₜ froE = {! fro-∅ w tvw  !}
  fro-∅ ∣ V ⦆ tvsV = {!   !}
  fro-∅ (tup[ i ] d) tvd = {!   !}
  fro-∅ (left d) tvd = {!   !}
  fro-∅ (right d) tvd = {!   !}

  -}

  {- data Type' : Set where
    Const : ∀ {B : Base} → (k : base-rep B) → Type'
    Clos : ∀ (n : ℕ) → (FVTs : Vec Type' n) → Type'   {- Clos =  Prod Fun Tup  -}
    LSum : (T : Type') → Type'
    RSum : (T : Type') → Type'
    Tup : ∀ (n : ℕ) → (Ts : Vec Type' n) → Type'
    Err : Type'

  data Type : Set where
    Const : ∀ {B : Base} → (k : base-rep B) → Type
    Fun : Type
    LSum : (T : Type) → Type
    RSum : (T : Type) → Type
    Tup : ∀ (n : ℕ) → (Ts : Vec Type n) → Type
    Err : Type 
    

  froT : Type' → Type
  froTs : ∀ n → Vec Type' n → Vec Type n
  froTs zero [] = []
  froTs (suc n) (T ∷ Ts) = froT T ∷ froTs n Ts
  froT (Const k) = Const k
  froT (Clos n FVTs) = Fun
  froT (LSum T) = LSum (froT T)
  froT (RSum T) = RSum (froT T)
  froT (Tup n Ts) = Tup n (froTs n Ts)
  froT Err = Err


  hasType' : Type' → Value → Set
  hasType'List : Type' → List Value → Set
  hasType'List T [] = True
  hasType'List T (d ∷ ds) = hasType' T d × hasType'List T ds
  hasType' (Clos n FVTs) ⦅ ν ∣ = True
  hasType' (Clos n FVTs) ⦅ FV ↦ ν ∣ = True
  hasType' (Clos n FVTs) ⦅ FV ↦ (V ↦ w) ∣ = True
  hasType' (Clos n FVTs) ∣ V ⦆ = hasType'List (Tup n FVTs) V 
  hasType' (Clos n FVTs) d = False
  hasType' (Const k) d = d ≡ const k
  hasType' (LSum T) (left d) = hasType' T d
  hasType' (LSum T) d = False
  hasType' (RSum T) (right d) = hasType' T d
  hasType' (RSum T) d = False
  hasType' (Tup n Ts) (tup[_]_ {n'} i d) with n ≟ n'
  ... | yes refl = hasType' (lookup Ts i) d
  ... | no neq = False
  hasType' (Tup n Ts) d = False
  hasType' Err ω = True
  hasType' Err d = False


  hasType : Type → Value → Set
  hasTypeList : Type → List Value → Set
  hasTypeList T [] = True
  hasTypeList T (d ∷ ds) = hasType T d × hasTypeList T ds
  hasType Fun ν = True
  hasType Fun (v ↦ w) = True 
  hasType Fun d = False
  hasType (Const k) d = d ≡ const k
  hasType (LSum T) (left d) = hasType T d
  hasType (LSum T) d = False
  hasType (RSum T) (right d) = hasType T d
  hasType (RSum T) d = False
  hasType (Tup n Ts) (tup[_]_ {n'} i d) with n ≟ n'
  ... | yes refl = hasType (lookup Ts i) d
  ... | no neq = False
  hasType (Tup n Ts) d = False
  hasType Err ω = True
  hasType Err d = False



  {- well-typed denotations -}
  _∶_ : 𝒫 Value → Type' → Set
  D ∶ T = ∀ d → d ∈ D → hasType' T d




{-
rest : DOp (𝒫 Value) (■ ∷ [])
rest ⟨ D , _ ⟩ ∥ vs ∥ = Σ[ v ∈ Value ] ∥ v ∷ vs ∥ ∈ D
rest ⟨ D , _ ⟩ _ = False
-}


  {- for Termination -}
  projₙ : ∀ {ℓ P k} → CRec ℓ P (suc k) → (n : ℕ) → n ≤′ k → P n
  projₙ {l} rec n ≤′-refl = proj₁ rec
  projₙ {l} rec n (≤′-step n≤k) = projₙ (proj₂ rec) n n≤k

  fro-step : ∀ (c : ℕ) → CRec (lsuc (lsuc lzero)) (λ i → Type' → 𝒫 Value → 𝒫 Value → Set₁) c 
             → (T : Type') → (Dₜ : 𝒫 Value) → (Dₛ : 𝒫 Value) → Set₁
  fro-step c rec (Const k) Dₜ Dₛ = Lift (lsuc lzero) (Dₜ ≃ Dₛ)
  fro-step zero rec (Clos n FVTs) Dₜ Dₛ = Lift (lsuc lzero) False
  fro-step (suc c) rec (Clos n FVTs) Dₜ Dₛ = 
     (∀ j → (j≤c : j ≤′ c) → ∀ TE Eₛ Eₜ → projₙ rec j j≤c TE Eₛ Eₜ
             → Σ[ Tapp ∈ Type' ] projₙ rec j j≤c Tapp (((Car Dₜ)  ● (Cdr Dₜ)) ● Eₜ) (Dₛ ● Eₛ))
  fro-step c rec (LSum T) Dₜ Dₛ = fro-step c rec T (GetLeft Dₜ) (GetLeft Dₛ)
  fro-step c rec (RSum T) Dₜ Dₛ = fro-step c rec T (GetRight Dₜ) (GetRight Dₛ)
  fro-step c rec (Tup zero Ts) Dₜ Dₛ = Lift (lsuc lzero) False
  fro-step c rec (Tup (suc n) Ts) Dₜ Dₛ = fro-step-tup (suc n) (fromℕ n) Ts Dₜ Dₛ
     where
     fro-step-tup : ∀ n (i : Fin n) → Vec Type' n → 𝒫 Value → 𝒫 Value → Set₁
     fro-step-tup (suc n) zero (T ∷ Ts) Dₜ Dₛ = fro-step c rec T (Fst n Dₜ) (Fst n Dₛ)
     fro-step-tup (suc n) (suc i) (T ∷ Ts) Dₜ Dₛ = fro-step-tup n i Ts (Rst Dₜ) (Rst Dₛ)
  fro-step c rec Err Dₜ Dₛ = Lift (lsuc lzero) (Dₜ ≃ Dₛ)
  
  fro : ∀ (c : ℕ) → (T' : Type') → (Dₜ : 𝒫 Value) → (Dₛ : 𝒫 Value) → Set₁
  fro = cRec (λ _ → Type' → 𝒫 Value → 𝒫 Value → Set₁) fro-step


  {-
  wishlist: 
  for each intro operator, we need to eliminate on its typing to fix the type
  -}


  {- this works for everything but function elimination, 
     for which we need more information -}
  delay-reflect-T : ∀ M ρ' ρ
     → (ρ~ : ∀ i d' d T' T → ρ' i d' → ρ i d → hasType' T' d' → hasType T d → froT T' ≡ T)
     → ∀ d' d T' T
     → d' ∈ ⟦ delay M ⟧' ρ' → d ∈ ⟦ M ⟧ ρ 
     → hasType' T' d' → hasType T d
     → froT T' ≡ T
  delay-reflect-T (` x) ρ' ρ ρ~ = ρ~ x
  delay-reflect-T (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ' ρ ρ~ 
    ⦅ d' ∣ (V ↦ d) (Clos n' FVTs) Fun d'∈ d∈ d'∶T' d∶T = refl
  delay-reflect-T (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ' ρ ρ~ 
    ∣ V₁ ⦆ (V ↦ d) (Clos n' FVTs) Fun d'∈ d∈ d'∶T' d∶T = refl
  delay-reflect-T (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ' ρ ρ~ 
    ⦅ d' ∣ ν (Clos n' FVTs) Fun d'∈ d∈ d'∶T' d∶T = refl
  delay-reflect-T (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ' ρ ρ~ 
    ∣ V ⦆ ν (Clos n' FVTs) Fun d'∈ d∈ d'∶T' d∶T = refl
  delay-reflect-T (app ⦅ M ,, N ,, Nil ⦆) ρ' ρ ρ~ d' d T' T
     ⟨ V' , ⟨ ⟨ FV' , ⟨ FV'↦V'↦d'∈carM' , FV'∈cdrM' ⟩ ⟩ , V'∈N' ⟩ ⟩
     ⟨ V , ⟨ V↦d∈M , V∈N ⟩ ⟩  d'∶T' d∶T = {!   !}
  delay-reflect-T (lit B k ⦅ Nil ⦆) ρ' ρ ρ~ (const {B₁} k₁) (const {B₂} k₂) 
    (Const {B₃} k₃) (Const {B₄} k₄) ⟨ refl , refl ⟩ ⟨ refl , refl ⟩ refl refl = refl
  delay-reflect-T (tuple x ⦅ args ⦆) ρ' ρ ρ~ d' d T' T d'∈ d∈ d'∶T' d∶T = {!   !}
  delay-reflect-T (get i ⦅ args ⦆) ρ' ρ ρ~ d' d T' T d'∈ d∈ d'∶T' d∶T = {!   !}
  delay-reflect-T (inl-op ⦅ args ⦆) ρ' ρ ρ~ d' d T' T d'∈ d∈ d'∶T' d∶T = {!   !}
  delay-reflect-T (inr-op ⦅ args ⦆) ρ' ρ ρ~ d' d T' T d'∈ d∈ d'∶T' d∶T = {!   !}
  delay-reflect-T (case-op ⦅ args ⦆) ρ' ρ ρ~ d' d T' T d'∈ d∈ d'∶T' d∶T = {!   !}

  delay-reflect : ∀ M ρ ρ' 
     → (ρ~ : ∀ i T' d' → d' ∈ (ρ' i) → hasType' T' d' 
           → Σ[ d ∈ Value ] d ∈ ρ i × hasType (froT T') d
           × Σ[ c ∈ ℕ ] fro c T' (ρ' i) (ρ i))
     → (Σ[ T' ∈ Type' ] Σ[ c ∈ ℕ ] fro c T' (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ))
       × ∀ d' → d' ∈ ⟦ delay M ⟧' ρ' → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ
  delay-reflect (` x) ρ ρ' ρ~ = ρ~ x
  delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ ρ' ρ~ T' d' 
    ⟨ V' , ⟨ ⟨ FV' , ⟨ ⦅FV'↦V'↦d'∣∈M' , ⟨ FV'⊆cdrM' , neFV' ⟩ ⟩ ⟩ , ⟨ V'⊆N' , neV' ⟩ ⟩ ⟩ d'∶T' 
    = {!   !}
    where
    carM∶T' : Σ[ n ∈ ℕ ] Σ[ FVTs ∈ Vec Type' n ] (hasType' (Clos n FVTs) ⦅ FV' ↦ (V' ↦ d') ∣)
    carM∶T' = {!   !}
    n' : ℕ
    n' = proj₁ carM∶T'
    FVTs : Vec Type' n'
    FVTs = proj₁ (proj₂ carM∶T')
    IHcarM : Σ[ f ∈ Value ] f ∈ ⟦ M ⟧ ρ × hasType Fun f
           × Σ[ c ∈ ℕ ] fro c (Clos n' FVTs) (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
    IHcarM = delay-reflect M ρ ρ' ρ~ (Clos n' FVTs) (⦅ (FV' ↦ (V' ↦ d')) ∣) ⦅FV'↦V'↦d'∣∈M' tt
    IHcdrM : {! ∀ fv' → fv' ∈ mem FV'
           → Σ[ fv ∈ Value ] ∣ fv ⦆ ∈ ⟦ N ⟧ ρ × hasType ? ∣ fv ⦆ 
           × Σ[ c ∈ ℕ ] fro c ? (⟦ delay N ⟧' ρ') (⟦ N ⟧ ρ)  !}
    IHcdrM = {!   !}
    V'∶T' : ∀ v' → v' ∈ mem V' → Σ[ Tv' ∈ Type' ] hasType' Tv' v'
    V'∶T' v' v'∈V' = {!   !}
    IHN : ∀ v' → (v'∈V' : v' ∈ mem V') 
        → Σ[ v ∈ Value ] v ∈ ⟦ N ⟧ ρ × hasType (froT (proj₁ (V'∶T' v' v'∈V'))) v 
        × Σ[ c ∈ ℕ ] fro c (proj₁ (V'∶T' v' v'∈V')) (⟦ delay N ⟧' ρ') (⟦ N ⟧ ρ)
    IHN v' v'∈V' = delay-reflect N ρ ρ' ρ~ (proj₁ (V'∶T' v' v'∈V')) v' 
                                 (V'⊆N' v' v'∈V') (proj₂ (V'∶T' v' v'∈V'))
  delay-reflect (lit B k ⦅ Nil ⦆) ρ ρ' ρ~ (Const k') (const k'') ⟨ refl , refl ⟩ refl = 
    ⟨ const k , ⟨ ⟨ refl , refl ⟩ , ⟨ refl , ⟨ suc zero , lift ⟨ (λ d z → z) , (λ d z → z) ⟩ ⟩ ⟩ ⟩ ⟩
  delay-reflect (tuple n ⦅ args ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (get i ⦅ M ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}
  delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ ρ' ρ~ d' d'∈ = {!   !}



  delay-reflect' : ∀ M ρ ρ' → (ρ~ : ∀ i T → (ρ' i) ∶ T → Σ[ c ∈ ℕ ] fro c T (ρ' i) (ρ i)) 
                → Σ[ T ∈ Type' ] Σ[ c ∈ ℕ ] fro c T (⟦ delay M ⟧' ρ') (⟦ M ⟧ ρ)
  delay-reflect' (` x) ρ ρ' ρ~ T M'∶T = ρ~ x T M'∶T
  delay-reflect' (clos-op x ⦅ ! (clear (bind (bind (ast N)))) ,, fvs ⦆) ρ ρ' ρ~ T M'∶T = {!   !}
  delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ ρ' ρ~ T M'∶T = {!   !}
  delay-reflect' (lit B k ⦅ Nil ⦆) ρ ρ' ρ~ T M'∶T = {! !}
  delay-reflect' (tuple x ⦅ args ⦆) ρ ρ' ρ~ T M'∶T = {!   !}
  delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ ρ' ρ~ T M'∶T = {!   !}
  delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ T M'∶T = {!   !}
  delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ ρ' ρ~ T M'∶T = {!   !}
  delay-reflect' (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ ρ' ρ~ T M'∶T = {!   !}



-}
{-
  fro : (c : ℕ) → (T : Type') → (Dₜ : 𝒫 Value) → (Dₛ : 𝒫 Value) → Set₁
  fro c (Const k) Dₜ Dₛ = Lift (lsuc lzero) (Dₜ ≃ Dₛ)
  fro zero (Clos n FVTs) Dₜ Dₛ = {!   !}
  fro (suc c) (Clos n FVTs) Dₜ Dₛ = 
     (∀ j → j ≤ c → ∀ TE Eₛ Eₜ → fro j TE Eₛ Eₜ 
             → Σ[ Tapp ∈ Type' ] fro j Tapp (((Car Dₜ)  ● (Cdr Dₜ)) ● Eₜ) (Dₛ ● Eₛ))
  fro c (LSum T) Dₜ Dₛ = fro c T (GetLeft Dₜ) (GetLeft Dₛ)
  fro c (RSum T) Dₜ Dₛ = fro c T (GetRight Dₜ) (GetRight Dₛ)
  fro c (Tup n Ts) Dₜ Dₛ = ∀ (i : Fin n) → fro c (lookup Ts i) (proj i ⟨ Dₜ , ptt ⟩) (proj i ⟨ Dₛ , ptt ⟩)
  -}
  
  {- data fro : ∀ D T → D ∶ T → (D' : 𝒫 Value) → Set₁ where
    fro-const : ∀ {B k D D∶T} → fro D (Const {B} k) D∶T D
    fro-clos : 
             → (∀ j<k TE Es Et → fro j TE Et Es
                 → ∃ Tapp . fro j Tapp ((car Dt ⋆ cdr Dt) ⋆ Et) (Ds ⋆ Es))
             → fro k (Clos stuff) Dt Dt∶T Ds



  hasType' : Type' → Value → Set
  hasType'List : Type' → List Value → Set
  hasType'List T [] = True
  hasType'List T (d ∷ ds) = hasType' T d × hasType'List T ds
  hasType' Fun ν = True
  hasType' Fun (V ↦ w) = True
  hasType' Fun d = False
  hasType' (Const k) d = d ≡ const k
  hasType' (Prod Type'₁ Type'₂) ⦅ d ∣ = hasType' Type'₁ d
  hasType' (Prod Type'₁ Type'₂) ∣ V ⦆ = hasType'List Type'₂ V
  hasType' (Prod Type'₁ Type'₂) d = False
  hasType' (LSum T) (left d) = hasType' T d
  hasType' (LSum T) d = False
  hasType' (RSum T) (right d) = hasType' T d
  hasType' (RSum T) d = False
  hasType' (Tup n Ts) (tup[_]_ {n'} i d) with n ≟ n'
  ... | yes refl = hasType' (lookup Ts i) d
  ... | no neq = False
  hasType' (Tup n Ts) d = False



  ~-Type' : ∀ {T} u v → u ~ v → hasType' T u → hasType' T v
  ~-Type' {T} (const {B} k) (const {B'} k₁) u~v u∶T with base-eq? B B'
  ... | no neq = ⊥-elim u~v
  ... | yes refl rewrite u~v = u∶T
  ~-Type' {Fun} (V ↦ u) (V₁ ↦ v) u~v u∶T = tt
  ~-Type' {Fun} (V ↦ u) ν u~v u∶T = tt
  ~-Type' {Fun} ν (V ↦ v) u~v u∶T = tt
  ~-Type' {Fun} ν ν u~v u∶T = tt
  ~-Type' {T} ω ω u~v u∶T = u∶T
  ~-Type' {T} ⦅ u ∣ ⦅ v ∣ u~v u∶T = {!   !}
  ~-Type' {T} ⦅ u ∣ ∣ V ⦆ u~v u∶T = {!   !}
  ~-Type' {T} ∣ V ⦆ v u~v u∶T = {!   !}
  ~-Type' {T} (tup[ i ] u) v u~v u∶T = {!   !}
  ~-Type' {T} (left u) v u~v u∶T = {!   !}
  ~-Type' {T} (right u) v u~v u∶T = {!   !}

  {- well-typed denotations -}
  _∶_ : 𝒫 Value → Type' → Set
  D ∶ T = ∀ d → d ∈ D → hasType' T d


  {-
  

  clos 0 (λ env a. clos 1 (λ env b. env[0])  [ a ]) []
  
  


  arrows that need recursion:

   V' -> w'   ~~> V -> w


  
  -}
     {- add step indexing -}
                    {- remove D∶T -}
  data fro : ∀ D T → D ∶ T → (D' : 𝒫 Value) → Set₁ where
    fro-const : ∀ {B k D D∶T} → fro D (Const {B} k) D∶T D
    fro-clos : 
             → (∀ j<k TE Es Et → fro j TE Et Es
                 → ∃ Tapp . fro j Tapp ((car Dt ⋆ cdr Dt) ⋆ Et) (Ds ⋆ Es))
             → fro k (Clos stuff) Dt Dt∶T Ds
    
    {- ∀ {D T1 T2 D∶T D1∶T1 D2∶T2 F E}   {-    ⦅ FV ↦ V ↦ w , FV' ⦆   -}
       → fro (car ⟨ D , ptt ⟩) T1 D1∶T1 F
       → fro (cdr ⟨ D , ptt ⟩) T2 D2∶T2 E
       → fro D (Prod T1 T2) D∶T (⋆ ⟨ F , ⟨ E , ptt ⟩ ⟩) -}
      {-could probably replace D1∶T1 and D2∶T2 with lemmas -}
    fro-fun : ∀ {D D∶T}
       → fro D Fun D∶T ?
    fro-sum : ∀ {D T1 T2 D∶T DL∶T1 DR∶T2 DL' DR'}
        → fro (case ⟨ D , ⟨ λ D' → D' , ⟨ λ D' v → False , ptt ⟩ ⟩ ⟩) T1 DL∶T1 DL'
        → fro (case ⟨ D , ⟨ λ D' v → False , ⟨ λ D' → D' , ptt ⟩ ⟩ ⟩) T2 DR∶T2 DR'
        → 
    
    {- Fro T Dt Ds -}
    
    {-  ∀ M d ...  d ∈ ⟦ M ⟧ ... (∀ i ∃ T. fro T (ρ' i) (ρ i)) → 
       ∃ T. ⟦ delay M ⟧ ∶ T  ×  fro T (⟦ delay M ⟧ ρ') (⟦ M ⟧ ρ) ×  ∃ d'. d' ∈ ⟦ delay M ⟧ ρ' -}

    {- 
    fro D Fun D∶T = D
    fro D (Prod T T₁) D∶T = ⋆ ⟨ car ⟨ D , ptt ⟩ , ⟨ cdr ⟨ D , ptt ⟩ , ptt ⟩ ⟩
    fro D (Sum T T₁) D∶T = {!   !}
    fro D (Tup n x) D∶T = {!   !}
    -}


-}

{-
tos : List Value → List Value'
to : Value → Value'
to (const x) = const x
to (FV ⊢ V ↦ w) = ⦅ (tos FV ↦ (tos V ↦ to w)) ∣
to (FV ⊢ν) = ⦅ (tos FV ↦ ν) ∣
to (FV ⊢ V ↦' w) = ∣ tos FV ⦆
to (FV ⊢ν') = ∣ tos FV ⦆
to ω = ω
to ∥ vs ∥ = ∥ tos vs ∥
to (left v) = left (to v)
to (right v) = right (to v)
tos List.[] = []
tos (d List.∷ ds) = to d ∷ tos ds

to-set : 𝒫 Value → 𝒫 Value'
to-set S v = Σ[ d ∈ Value ] d ∈ S × v ≡ to d

_to-⊆_ : 𝒫 Value → 𝒫 Value' → Set
A to-⊆ B = ∀ d → d ∈ A → to d ∈ B

env-map : ∀ {A B : Set} → (A → B) → (ℕ → 𝒫 A) → (ℕ → 𝒫 B)
env-map {A} {B} f ρ x b = Σ[ a ∈ A ] a ∈ (ρ x) × b ≡ f a

to-ne : ∀ V → V ≢ [] → tos V ≢ []
to-ne [] neV = ⊥-elim (neV refl)
to-ne (x ∷ V) neV ()

tos-length : ∀ V → length (tos V) ≡ length V
tos-length [] = refl
tos-length (x ∷ V) = cong suc (tos-length V)

tos-nth : ∀ V i → to (Op3.nth V i) ≡ Op4.nth (tos V) i
tos-nth [] zero = refl
tos-nth (x ∷ V) zero = refl
tos-nth [] (suc i) = refl
tos-nth (x ∷ V) (suc i) = tos-nth V i

to-∈-mem : ∀ {a}{V} → a ∈ (mem V) → to a ∈ mem (tos V)
to-∈-mem (here px) = here (cong to px)
to-∈-mem (there a∈) = there (to-∈-mem a∈)

∈-mem-tos : ∀ {d}{V} → d ∈ mem (tos V) → Σ[ a ∈ Value ] a ∈ mem V × d ≡ to a
∈-mem-tos {d} {x ∷ V} (here px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
∈-mem-tos {d} {x ∷ V} (there d∈) with ∈-mem-tos d∈
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ there a∈ , refl ⟩ ⟩

to-mem-rewrite : ∀ V ρ → env-map to (mem V • ρ) ⊆ₑ (mem (tos V)) • env-map to ρ
to-mem-rewrite V ρ zero d ⟨ a , ⟨ a∈V , refl ⟩ ⟩ = to-∈-mem a∈V
to-mem-rewrite V ρ (suc x) d d∈ρx = d∈ρx

delay-preserve : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → to d ∈ ⟦ delay M ⟧' (env-map to ρ)
del-map-args-preserve : ∀ {n} args ρ → results-rel-pres' _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ))
delay-preserve-⊆ : ∀ M ρ V → mem V ⊆ ⟦ M ⟧ ρ → mem (tos V) ⊆ ⟦ delay M ⟧' (env-map to ρ)

delay-preserve (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d  
  ⟨ [] , ⟨ FV , ⟨ [] ⊢ν , ⟨ ⟨ w∈N , neV ⟩ , ⟨ ⟨ w'∈N , neV' ⟩ 
        , ⟨ FV⊆𝒯fvs , ⟨ neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ tos FV , ⟨ ⟨ tt , to-ne FV neFV ⟩ , ⟨ IHV , to-ne FV neFV ⟩ ⟩ ⟩
  where
  IHV' : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV' zero fvs d refl = refl
  IHV' (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , IHV' n fvs ∥ ds ∥ ds∈ ⟩
  IHV : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = IHV' n fvs a (FV⊆𝒯fvs a a∈)
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d  
  ⟨ [] , ⟨ FV , ⟨ [] ⊢ V ↦ w , ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ ⟨ ⟨ w'∈N , neV' ⟩ , neFV'' ⟩ 
         , ⟨ FV⊆𝒯fvs , ⟨ neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = 
  ⟨ tos FV , ⟨ ⟨ ⟨ stepN , to-ne V neV ⟩ , to-ne FV neFV ⟩ , ⟨ IHfvs , to-ne FV neFV ⟩ ⟩ ⟩
  where
  IHV' : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV' zero fvs d refl = refl
  IHV' (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , IHV' n fvs ∥ ds ∥ ds∈ ⟩
  IHfvs : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHfvs d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = IHV' n fvs a (FV⊆𝒯fvs a a∈)
  IHN : to w ∈ ⟦ delay N ⟧' (env-map to (mem V • mem FV • (λ _ x → x ≡ ω)))
  IHN = delay-preserve N (mem V • mem FV • (λ _ x → x ≡ ω)) w w∈N
  H : env-map to (mem V • mem FV • (λ x → L3.init))
         ⊆ₑ mem (tos V) • mem (tos FV) • (λ x → L4.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  stepN : to w ∈ ⟦ delay N ⟧' (mem (tos V) • mem (tos FV) • (λ x → L4.init))
  stepN = L4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to w) IHN
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d  
  ⟨ [] , ⟨ FV , ⟨ [] ⊢ν' , ⟨ ⟨ w∈N , neV ⟩ , ⟨ ⟨ w'∈N , neV' ⟩ 
         , ⟨ FV⊆𝒯fvs , ⟨ neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ =
    ⟨ ν , ⟨ tt , ⟨ IHV , to-ne FV neFV ⟩ ⟩ ⟩
  where
  IHV' : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV' zero fvs d refl = refl
  IHV' (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , IHV' n fvs ∥ ds ∥ ds∈ ⟩
  IHV : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = IHV' n fvs a (FV⊆𝒯fvs a a∈)
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d  
  ⟨ [] , ⟨ FV , ⟨ [] ⊢ V ↦' w , ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ ⟨ ⟨ w'∈N , neV' ⟩ , neFV'' ⟩ 
         , ⟨ FV⊆𝒯fvs , ⟨ neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ = 
  ⟨ ν , ⟨ tt , ⟨ IHfvs , to-ne FV neFV ⟩ ⟩ ⟩
  where
  IHV' : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHV' zero fvs d refl = refl
  IHV' (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , IHV' n fvs ∥ ds ∥ ds∈ ⟩
  IHfvs : mem (tos FV) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  IHfvs d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = IHV' n fvs a (FV⊆𝒯fvs a a∈)
  IHN : to w ∈ ⟦ delay N ⟧' (env-map to (mem V • mem FV • (λ _ x → x ≡ ω)))
  IHN = delay-preserve N (mem V • mem FV • (λ _ x → x ≡ ω)) w w∈N
  H : env-map to (mem V • mem FV • (λ x → L3.init))
         ⊆ₑ mem (tos V) • mem (tos FV) • (λ x → L4.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  stepN : to w ∈ ⟦ delay N ⟧' (mem (tos V) • mem (tos FV) • (λ x → L4.init))
  stepN = L4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to w) IHN
delay-preserve (app ⦅ M ,, N ,, Nil ⦆) ρ d 
  ⟨ FV , ⟨ neFV , ⟨ V , ⟨ FV⊢V↦d∈M , ⟨ FV⊢V↦'d∈M , ⟨ V⊆N , neV ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  with delay-preserve M ρ (FV ⊢ V ↦ d) FV⊢V↦d∈M 
    | delay-preserve M ρ (FV ⊢ V ↦' d) FV⊢V↦'d∈M
    | delay-preserve-⊆ N ρ V V⊆N
... | clos∈M' | clos'∈M' | V'⊆N' = 
  ⟨ tos V , ⟨ ⟨ tos FV , ⟨ clos∈M' , ⟨ second , to-ne FV neFV ⟩ ⟩ ⟩ 
  , ⟨ V'⊆N' , to-ne V neV ⟩ ⟩ ⟩
   where
   second : ∀ d' → d' ∈ mem (tos FV) → d' ∈ cdr ⟨ ⟦ delay M ⟧' (env-map to ρ) , ptt ⟩
   second d' d'∈ = ⟨ tos FV , ⟨ clos'∈M' , d'∈ ⟩ ⟩
delay-preserve (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-preserve (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ ρ → to d ∈ ⟦ delay (tuple n ⦅ args ⦆ ) ⟧' (env-map to ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-preserve arg ρ d d∈ , ds'∈ ⟩  
delay-preserve (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ tos ds , ⟨ subst (Data.Nat._<_ i) (sym (tos-length ds)) i≤ 
  , ⟨ delay-preserve M ρ ∥ ds ∥ ds∈ , tos-nth ds i ⟩ ⟩ ⟩
delay-preserve (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-preserve M ρ v v∈
delay-preserve (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-preserve M ρ v v∈ 
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
     inj₁ ⟨ to v , ⟨ tos V , ⟨ G , G2 ⟩ ⟩ ⟩
  where
  H : ∀ V' → (∀ d' → d' ∈ mem V' → left d' ∈ ⟦ L ⟧ ρ) → mem (Data.List.map left V') ⊆ ⟦ L ⟧ ρ
  H (x ∷ V') H' .(left x) (here refl) = H' x (here refl)
  H (x ∷ V') H' d' (there d'∈) = H V' (λ d' z → H' d' (there z)) d' d'∈
  H0 : ∀ {x : Value'} v V → x ∈ mem (tos (v ∷ V)) → left x ∈ mem (left (to v) ∷ tos (Data.List.map left V))
  H0 v V (here refl) = here refl
  H0 v (x ∷ V) (there (here refl)) = there (here refl)
  H0 v (x ∷ V) (there (there x∈)) = there (H0 x V (there x∈))
  G : ∀ d' → d' ∈ mem (tos (v ∷ V)) → left d' ∈ ⟦ delay L ⟧' (env-map to ρ)
  G d' d'∈ = delay-preserve-⊆ L ρ (Data.List.map left (v ∷ V)) (H (v ∷ V) LV∈) (left d') (H0 v V d'∈)
  H2 : env-map to (mem (v ∷ V) • ρ)
         ⊆ₑ mem (tos (v ∷ V)) • env-map to ρ
  H2 zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H2 (suc i) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ a∈ , refl ⟩ ⟩
  G2 : to d ∈ ⟦ delay M ⟧' (mem (tos (v ∷ V)) • env-map to ρ)
  G2 = L4.⟦⟧-monotone {{Clos4-Semantics}} (delay M) H2 (to d) 
                             (delay-preserve M (mem (v ∷ V) • ρ) d d∈)
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = inj₂ ⟨ to v , ⟨ tos V , ⟨ G , G2 ⟩ ⟩ ⟩
     where
  H : ∀ V' → (∀ d' → d' ∈ mem V' → right d' ∈ ⟦ L ⟧ ρ) → mem (Data.List.map right V') ⊆ ⟦ L ⟧ ρ
  H (x ∷ V') H' .(right x) (here refl) = H' x (here refl)
  H (x ∷ V') H' d' (there d'∈) = H V' (λ d' z → H' d' (there z)) d' d'∈
  H0 : ∀ {x : Value'} v V → x ∈ mem (tos (v ∷ V)) → right x ∈ mem (right (to v) ∷ tos (Data.List.map right V))
  H0 v V (here refl) = here refl
  H0 v (x ∷ V) (there (here refl)) = there (here refl)
  H0 v (x ∷ V) (there (there x∈)) = there (H0 x V (there x∈))
  G : ∀ d' → d' ∈ mem (tos (v ∷ V)) → right d' ∈ ⟦ delay L ⟧' (env-map to ρ)
  G d' d'∈ = delay-preserve-⊆ L ρ (Data.List.map right (v ∷ V)) (H (v ∷ V) RV∈) (right d') (H0 v V d'∈)
  H2 : env-map to (mem (v ∷ V) • ρ)
         ⊆ₑ mem (tos (v ∷ V)) • env-map to ρ
  H2 zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H2 (suc i) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ a∈ , refl ⟩ ⟩
  G2 : to d ∈ ⟦ delay N ⟧' (mem (tos (v ∷ V)) • env-map to ρ)
  G2 = L4.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H2 (to d) 
                             (delay-preserve N (mem (v ∷ V) • ρ) d d∈)

delay-preserve-⊆ M ρ [] V⊆ = λ d ()
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-preserve M ρ d (V⊆ d (here refl))
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈tosV) = 
  delay-preserve-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈tosV
del-map-args-preserve {zero} args ρ = lift tt
del-map-args-preserve {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-preserve M ρ) , del-map-args-preserve args ρ ⟩




{- ============================================================================
    Reverse Direction
 ============================================================================ -}


fros : List Value' → List Value
fro : Value' → Value
fro (const x) = const x
fro (V ↦ w) = ω
fro ν = ω
fro ω = ω
fro ∣ FV ⦆ = fros FV ⊢ν
fro ⦅ ν ∣ = [] ⊢ν
fro ⦅ FV ↦ ν ∣ = fros FV ⊢ν
fro ⦅ FV ↦ (V ↦ w) ∣ = fros FV ⊢ fros V ↦ fro w
fro ⦅ u ∣ = ω
fro ∥ xs ∥ = ∥ fros xs ∥
fro (left v) = left (fro v)
fro (right v) = right (fro v)
fros List.[] = []
fros (d List.∷ ds) = fro d List.∷ fros ds


fro-set : 𝒫 Value' → 𝒫 Value
fro-set S v = Σ[ d ∈ Value' ] d ∈ S × v ≡ fro d

_fro-⊆_ : 𝒫 Value' → 𝒫 Value → Set
A fro-⊆ B = ∀ d → d ∈ A → fro d ∈ B

fro-ne : ∀ V → V ≢ [] → fros V ≢ []
fro-ne [] neV = ⊥-elim (neV refl)
fro-ne (x ∷ V) neV ()

fros-length : ∀ V → length (fros V) ≡ length V
fros-length [] = refl
fros-length (x ∷ V) = cong suc (fros-length V)

fros-nth : ∀ V i → fro (Op4.nth V i) ≡ Op3.nth (fros V) i
fros-nth [] zero = refl
fros-nth (x ∷ V) zero = refl
fros-nth [] (suc i) = refl
fros-nth (x ∷ V) (suc i) = fros-nth V i

fro-∈-mem : ∀ {a}{V} → a ∈ (mem V) → fro a ∈ mem (fros V)
fro-∈-mem (here px) = here (cong fro px)
fro-∈-mem (there a∈) = there (fro-∈-mem a∈)

∈-mem-fros : ∀ {d}{V} → d ∈ mem (fros V) → Σ[ a ∈ Value' ] a ∈ mem V × d ≡ fro a
∈-mem-fros {d} {x ∷ V} (here px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
∈-mem-fros {d} {x ∷ V} (there d∈) with ∈-mem-fros d∈
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ there a∈ , refl ⟩ ⟩

++-ne₁ : ∀ {A : Set} (FV : List A) {FV'} → FV ≢ [] → FV ++ FV' ≢ []
++-ne₁ [] neFV = ⊥-elim (neFV refl)
++-ne₁ (x ∷ FV) neFV ()

++-⊆₁ : ∀ {A : Set} (FV : List A) {FV'} → mem FV ⊆ (mem (FV ++ FV'))
++-⊆₁ (x ∷ FV) d (here refl) = here refl
++-⊆₁ (x ∷ FV) d (there d∈) = there (++-⊆₁ FV d d∈)


delay-reflect : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect : ∀ {n} args ρ
  → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect-⊆ : ∀ M ρ V
  → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ∣ FV ⦆ 
  ⟨ f , ⟨ f∈ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ = 
  ⟨ [] , ⟨ fros FV , ⟨ [] ⊢ν , ⟨ ⟨ tt , fro-ne FV neFV ⟩ 
  , ⟨ ⟨ tt , fro-ne FV neFV ⟩ , ⟨ G3 , ⟨ fro-ne FV neFV , refl ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ ν ∣
  ⟨ FV , ⟨ tt , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ = 
  ⟨ [] , ⟨ {!   !} , ⟨ [] ⊢ν , ⟨ ⟨ tt , {!   !} ⟩ 
  , ⟨ ⟨ tt , {!   !} ⟩ , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV' ↦ ν ∣ 
  ⟨ FV , ⟨ ⟨ ν∈ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ = 
  ⟨ [] , ⟨ fros FV , ⟨ {!   !} , ⟨ ⟨ {!   !} , fro-ne FV neFV ⟩ 
  , ⟨ ⟨ {!   !} , fro-ne FV neFV ⟩ , ⟨ G3 , ⟨ fro-ne FV neFV , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = 
    ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
{-
  ⟨ ⟨ tt , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
-}
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV' ↦ (V ↦ w) ∣ 
  ⟨ FV , ⟨ ⟨ ⟨ w∈ , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ ⟩ = 
   ⟨ [] , ⟨ fros FV , ⟨ [] ⊢ fros V ↦ fro w , ⟨ ⟨ ⟨ {!   !} , fro-ne V neV ⟩ , fro-ne FV neFV ⟩ 
   , ⟨ ⟨ ⟨ {!   !} , fro-ne V neV ⟩ , fro-ne FV neFV ⟩ , ⟨ {!   !} , ⟨ fro-ne FV neFV , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
{-
 ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ 
  with FV' D4.mem⊆? FV
... | no FV'⊈  = ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ | yes FV'⊆ 
    = ⟨ (λ d z → G3 d (froFV'⊆ d z)) , ⟨ fro-ne FV' neFV' , ⟨ G1 , fro-ne V neV ⟩ ⟩ ⟩
  where
  froFV'⊆ : mem (fros FV') ⊆ mem (fros FV)
  froFV'⊆ d d∈ with ∈-mem-fros d∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem (FV'⊆ b b∈)
  H : env-map fro (mem V • mem FV' • λ x → L4.init)
      ⊆ₑ mem (fros V) • mem (fros FV') • (λ x → L3.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros V) • mem (fros FV') • (λ x → L3.init))
  G1 = L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect N (mem V • mem FV' • (λ _ x → x ≡ ω)) {!   !} w 
                     w∈N)
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
-}
delay-reflect (app ⦅ M ,, N ,, Nil ⦆) ρ d 
   ⟨ V , ⟨ inner-app , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ with inner-app
... | ⟨ FV , ⟨ FV↦[V↦d]∈carM' , ⟨ FV⊆cdrM' , neFV ⟩ ⟩ ⟩ = ⟨ fros FV , ⟨ fro-ne FV neFV 
  , ⟨ fros V , ⟨ IHM , ⟨ {!   !} , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
  where
  IHN : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect-⊆ N ρ V V⊆N'
  IHM : (fros FV ⊢ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM = delay-reflect M ρ ⦅ FV ↦ (V ↦ d) ∣ FV↦[V↦d]∈carM'
{-
  ⟨ fros FV , ⟨ fro-ne FV neFV 
  , ⟨ fros V , ⟨ IHM , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩
  where
  IHN : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect-⊆ N ρ V V⊆N'
  G : ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ ∈ ⟦ delay M ⟧' ρ
  G = keylemma' (⟦ delay M ⟧' ρ) (smash-⟦⟧' (delay M) ρ) FV ⦅FV↦[V↦d],FV'⦆∈M' FV⊆cdrM'
  IHM : (fros FV ⊢ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM with FV D4.mem⊆? (FV ++ FV') | delay-reflect M ρ ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ G
  ... | yes FV⊆FV | IH = IH
  ... | no FV⊈FV | IH = ⊥-elim (FV⊈FV (++-⊆₁ FV))
-}
delay-reflect (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-reflect (tuple n ⦅ args ⦆) ρ d d∈ = G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect arg ρ d d∈ , ds'∈ ⟩
delay-reflect (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-reflect M ρ v v∈
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-reflect M ρ v v∈
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → left d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect L ρ (left b) (LV∈ b b∈)
delay-reflect (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → right d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect L ρ (right b) (RV∈ b b∈)
delay-reflect-⊆ M ρ [] V⊆ = λ d ()
delay-reflect-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect M ρ d (V⊆ d (here refl))
delay-reflect-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect {zero} args ρ = lift tt
del-map-args-reflect {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-reflect M ρ) , del-map-args-reflect args ρ ⟩










{-
Fun : Value' → Set
Fun (V ↦ d) = True
Fun ν = True
Fun d = False

data _⊑_ : Value' → Value' → Set where
  ⊑-ω : ω ⊑ ω
  ⊑-const : ∀ {B k} → const {B} k ⊑ const k
  ⊑-ν : ∀ {d} → Fun d → ν ⊑ d
  ⊑-↦ : ∀ {V w w1} → w ⊑ w1
          → (V ↦ w) ⊑ (V ↦ w1)
  ⊑-nil : ∥ [] ∥ ⊑ ∥ [] ∥
  ⊑-cons : ∀ {d d1 ds ds1} 
          → (d⊑ : d ⊑ d1)
          → (ds⊑ : ∥ ds ∥ ⊑ ∥ ds1 ∥)
          → ∥ d ∷ ds ∥ ⊑ ∥ d1 ∷ ds1 ∥
  ⊑-pair : ∀ {u u1 V V1}
          → (⊑u : u ⊑ u1)
          → (⊑V : ∀ v → v ∈ mem V 
                → Σ[ v1 ∈ Value' ] (mem V1 v1) × v ⊑ v1)
          → ⦅ u , V ⦆ ⊑ ⦅ u1 , V1 ⦆
  ⊑-left : ∀ {d d1} → d ⊑ d1 → left d ⊑ left d1
  ⊑-right : ∀ {d d1} → d ⊑ d1 → right d ⊑ right d1

⊑-refl : ∀ {d} → d ⊑ d
⊑-mem-refl : ∀ V d → d ∈ (mem V) → d ⊑ d
⊑-refl {const k} = ⊑-const
⊑-refl {V ↦ d} = ⊑-↦ ⊑-refl
⊑-refl {ν} = ⊑-ν tt
⊑-refl {ω} = ⊑-ω
⊑-refl {⦅ d , V ⦆} = ⊑-pair ⊑-refl V⊑V
  where
  V⊑V : (x : Value') (x₁ : Any (_≡_ x) V) → Σ Value' (λ z → Σ (Any (_≡_ z) V) (λ _ → x ⊑ z))
  V⊑V v v∈ = ⟨ v , ⟨ v∈ , ⊑-mem-refl V v v∈ ⟩ ⟩
⊑-refl {∥ [] ∥} = ⊑-nil
⊑-refl {∥ x ∷ ds ∥} = ⊑-cons ⊑-refl ⊑-refl
⊑-refl {left d} = ⊑-left ⊑-refl
⊑-refl {right d} = ⊑-right ⊑-refl
⊑-mem-refl (x ∷ V) .x (here refl) = ⊑-refl
⊑-mem-refl (x ∷ V) d (there d∈V) = ⊑-mem-refl V d d∈V


{- This version with infinite sets seems to fail.
   Let's attempt to consider distributivity over finite sets,
   which makes more sense anyway.
   -}
data _⊑'_ : Value' → 𝒫 Value' → Set where
   ⊑'-single : ∀ {u v D} 
              → v ∈ D → u ⊑ v
              → u ⊑' D
   ⊑'-dist-↦ : ∀ {V w D}
              → w ⊑' (Op4.⋆ ⟨ D , ⟨ mem V , ptt ⟩ ⟩)
              → (V ↦ w) ⊑' D
   ⊑'-dist-pair : ∀ {u V D}
              → u ⊑' car ⟨ D , ptt ⟩
              → (∀ v → v ∈ mem V → v ⊑' cdr ⟨ D , ptt ⟩)
              → ⦅ u , V ⦆ ⊑' D           
   ⊑'-left : ∀ {d D}
             → d ⊑' Op4.𝒞 ⟨ D , ⟨ (λ z → z) , ⟨ (λ z → ⌈ ω ⌉) , ptt ⟩ ⟩ ⟩
             → left d ⊑' D
   ⊑'-right : ∀ {d D}
             → d ⊑' Op4.𝒞 ⟨ D , ⟨ (λ z → ⌈ ω ⌉) , ⟨ (λ z → z) , ptt ⟩ ⟩ ⟩
             → right d ⊑' D
   ⊑'-tup : ∀ {ds D}
             → (∀ i → Op4.nth ds i ⊑' Op4.proj i ⟨ D , ptt ⟩)
             → ∥ ds ∥ ⊑' D

{-
data _⊑'_ : Value' → List Value' → Set where
   ⊑'-single : ∀ {u v D} 
              → v ∈ mem D → u ⊑ v
              → u ⊑' D
   ⊑'-dist-↦ : ∀ {V w D}
              → w ⊑' (Op4.⋆ ⟨ mem D , ⟨ mem V , ptt ⟩ ⟩)
              → (V ↦ w) ⊑' mem D
   ⊑'-dist-pair : ∀ {u V D} 
              → u ⊑' car ⟨ D , ptt ⟩
              → (∀ v → v ∈ mem V → v ⊑' cdr ⟨ D , ptt ⟩)
              → ⦅ u , V ⦆ ⊑' D           
   ⊑'-left : ∀ {d D}
             → d ⊑' Op4.𝒞 ⟨ D , ⟨ (λ z → z) , ⟨ (λ z → ⌈ ω ⌉) , ptt ⟩ ⟩ ⟩
             → left d ⊑' D
   ⊑'-right : ∀ {d D}
             → d ⊑' Op4.𝒞 ⟨ D , ⟨ (λ z → ⌈ ω ⌉) , ⟨ (λ z → z) , ptt ⟩ ⟩ ⟩
             → right d ⊑' D
   ⊑'-tup : ∀ {ds D}
             → (∀ i → Op4.nth ds i ⊑' Op4.proj i ⟨ D , ptt ⟩)
             → ∥ ds ∥ ⊑' D
-}

⊑-closed : (𝒫 Value') → Set
⊑-closed D = ∀ u v → v ∈ D → u ⊑ v → u ∈ D

⊑'-closed : (𝒫 Value') → Set
⊑'-closed D = ∀ d → d ⊑' D → d ∈ D

⋆-⊑-closed : op-pred-pres ⊑-closed (■ ∷ ■ ∷ []) Op4.⋆
⋆-⊑-closed ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟨ dcM , ⟨ dcN , ptt ⟩ ⟩ = lift G
  where
  G : ⊑-closed (Op4.⋆ ⟨ M , ⟨ N , ptt ⟩ ⟩)
  G u v ⟨ V , ⟨ u∈ , ⟨ V⊆ , neV ⟩ ⟩ ⟩ u⊑v = 
    ⟨ V , ⟨ lower dcM (V ↦ u) (V ↦ v) u∈ (⊑-↦ u⊑v) , ⟨ V⊆ , neV ⟩ ⟩ ⟩

⋆-⊑'-closed : op-pred-pres ⊑'-closed (■ ∷ ■ ∷ []) Op4.⋆
⋆-⊑'-closed ⟨ M , ⟨ N , ptt ⟩ ⟩ ⟨ dcM , ⟨ dcN , ptt ⟩ ⟩ = lift G
  where
  G : ⊑'-closed (Op4.⋆ ⟨ M , ⟨ N , ptt ⟩ ⟩)
  G d d⊑'⋆MN = ⟨ {!   !} , ⟨ lower dcM {!   !} (⊑'-dist-↦ {!   !}) , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩

{-
  w ⊑' ⋆ ⟨ D , ⟨ mem V , ptt ⟩ ⟩
  -------------------------------
  V ↦ w ⊑' D

  d ⊑' ⋆ ⟨ M , ⟨ N , ptt ⟩ ⟩

-}

⊑-closed-⟦⟧' : ∀ M ρ 
              → (ρ~ : ∀ₑ ⊑-closed ρ)
              → ⊑-closed (⟦ M ⟧' ρ)
⊑-closed-⟦⟧' (# x) ρ ρ~ = ρ~ x
⊑-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .ν v v∈M (⊑-ν x) = tt
⊑-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ 
             (V ↦ w) (V' ↦ ν) ⟨ w'∈ΛM , neV ⟩ (⊑-↦ (⊑-ν x)) = ⟨ tt , neV ⟩
⊑-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ 
             (V ↦ w) (V' ↦ (V'' ↦ w')) ⟨ w'∈ΛM , neV ⟩ (⊑-↦ (⊑-ν x)) = 
  ⟨ tt , neV ⟩
⊑-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ 
             (V ↦ (V' ↦ w)) (V ↦ (V' ↦ w')) ⟨ ⟨ w'∈M , neV'' ⟩ , neV ⟩ (⊑-↦ (⊑-↦ u⊑v)) = 
  ⟨ ⟨ ⊑-closed-⟦⟧' N  (mem V' • mem V • (λ _ x → x ≡ ω)) {!   !} w w' w'∈M u⊑v , neV'' ⟩ , neV ⟩
⊑-closed-⟦⟧' (app ⦅ L ,, M ,, N ,, Nil ⦆') ρ ρ~ u v 
  ⟨ V , ⟨ ⟨ FV , ⟨ w∈L , ⟨ FV⊆M , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N , neV ⟩ ⟩ ⟩ u⊑v =
   ⟨ V , ⟨ ⟨ FV , ⟨ ⊑-closed-⟦⟧' L ρ ρ~ (FV ↦ (V ↦ u)) (FV ↦ (V ↦ v)) w∈L (⊑-↦ (⊑-↦ u⊑v)) , ⟨ FV⊆M , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N , neV ⟩ ⟩ ⟩
⊑-closed-⟦⟧' (lit B k ⦅ Nil ⦆') ρ ρ~ .(const _) .(const _) v∈M ⊑-const = v∈M
⊑-closed-⟦⟧' (lit B k ⦅ Nil ⦆') ρ ρ~ .ν v v∈M (⊑-ν x) = {!   !} {- contradiction -}
⊑-closed-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ ρ~ ⦅ u , V ⦆ ⦅ u' , V' ⦆ 
   ⟨ u'∈M , ⟨ V'⊆N , neV' ⟩ ⟩ (⊑-pair u⊑v ⊑V) = 
   ⟨ ⊑-closed-⟦⟧' M ρ ρ~ u u' u'∈M u⊑v , ⟨ {!   !} , {!   !} ⟩ ⟩
⊑-closed-⟦⟧' (fst-op ⦅ M ,, Nil ⦆') ρ ρ~ u v ⟨ FV , ⟨ p∈ , neFV ⟩ ⟩ u⊑v =
   ⟨ FV , ⟨ ⊑-closed-⟦⟧' M ρ ρ~ ⦅ u , FV ⦆ ⦅ v , FV ⦆ p∈ (⊑-pair u⊑v FV⊑FV) , neFV ⟩ ⟩
  where
  FV⊑FV : (x : Value') (x₁ : Any (_≡_ x) FV) → Σ Value' (λ z → Σ (Any (_≡_ z) FV) (λ _ → x ⊑ z))
  FV⊑FV v v∈ = ⟨ v , ⟨ v∈ , ⊑-mem-refl FV v v∈ ⟩ ⟩
⊑-closed-⟦⟧' (snd-op ⦅ M ,, Nil ⦆') ρ ρ~ u v ⟨ f , ⟨ FV , ⟨ p∈ , v∈FV ⟩ ⟩ ⟩ u⊑v =
   ⟨ f , ⟨ (u ∷ []) , ⟨ ⊑-closed-⟦⟧' M ρ ρ~ ⦅ f , u ∷ [] ⦆ ⦅ f , FV ⦆ p∈ 
                                  (⊑-pair ⊑-refl H) , here refl ⟩ ⟩ ⟩
  where
  H : (x : Value') (x₁ : Any (_≡_ x) (u ∷ [])) →
      Σ Value' (λ z → Σ (Any (_≡_ z) FV) (λ _ → x ⊑ z))
  H d (here refl) = ⟨ v , ⟨ v∈FV , u⊑v ⟩ ⟩
⊑-closed-⟦⟧' (tuple n ⦅ args ⦆') ρ ρ~ u v v∈M u⊑v = {!   !}
⊑-closed-⟦⟧' (get i ⦅ M ,, Nil ⦆') ρ ρ~ u v ⟨ vs , ⟨ i≤ , ⟨ vs∈ , refl ⟩ ⟩ ⟩ u⊑v 
  = ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩
⊑-closed-⟦⟧' (inl-op ⦅ M ,, Nil ⦆') ρ ρ~ (left u) (left v) v∈M (⊑-left u⊑v)= 
  ⊑-closed-⟦⟧' M ρ ρ~ u v v∈M u⊑v
⊑-closed-⟦⟧' (inr-op ⦅ M ,, Nil ⦆') ρ ρ~ (right u) (right v) v∈M (⊑-right u⊑v) = 
  ⊑-closed-⟦⟧' M ρ ρ~ u v v∈M u⊑v
⊑-closed-⟦⟧' (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆') ρ ρ~ u v 
  (inj₁ ⟨ v' , ⟨ V' , ⟨ V'⊆L , v∈M[V'] ⟩ ⟩ ⟩) u⊑v = 
  inj₁ ⟨ v' , ⟨ V' , ⟨ V'⊆L , ⊑-closed-⟦⟧' M (mem (v' ∷ V') • ρ) {!   !} u v v∈M[V'] u⊑v ⟩ ⟩ ⟩
⊑-closed-⟦⟧' (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆') ρ ρ~ u v 
  (inj₂ ⟨ v' , ⟨ V' , ⟨ V'⊆L , v∈N[V'] ⟩ ⟩ ⟩) u⊑v = 
  inj₂ ⟨ v' , ⟨ V' , ⟨ V'⊆L , ⊑-closed-⟦⟧' N (mem (v' ∷ V') • ρ) {!   !}  u v v∈N[V'] u⊑v ⟩ ⟩ ⟩


⊑'-closed⇒⊑-closed : ∀ {D} → ⊑'-closed D → ⊑-closed D
⊑'-closed⇒⊑-closed H u v v∈D u⊑v = H u (⊑'-single v∈D u⊑v)

⊑'-closed-⟦⟧' : ∀ M ρ 
              → (ρ~ : ∀ₑ ⊑'-closed ρ)
              → ⊑'-closed (⟦ M ⟧' ρ)
⊑'-closed-⟦⟧' (# x) ρ ρ~ = ρ~ x
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ u (⊑'-single x x₁) 
  = {! ⊑-closed-⟦⟧' ? ρ   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(_ ↦ _) (⊑'-dist-↦ u⊑'M) 
  = {!   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(⦅ _ , _ ⦆) (⊑'-dist-pair u⊑'M x) 
  = ⊥-elim {!   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(left _) (⊑'-left u⊑'M) 
  = ⊥-elim {!   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(right _) (⊑'-right u⊑'M) 
  = ⊥-elim {!   !}
⊑'-closed-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ ρ~ .(∥ _ ∥) (⊑'-tup x) 
  = ⊥-elim {!   !}
⊑'-closed-⟦⟧' (app ⦅ L ,, M ,, N ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (lit B k ⦅ Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (fst-op ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (snd-op ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (tuple n ⦅ args ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (get i ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (inl-op ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (inr-op ⦅ M ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}
⊑'-closed-⟦⟧' (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆') ρ ρ~ u u⊑'M = {!   !}



{-
⊑'-closed-⟦⟧' : ∀ M ρ 
              → (ρ~ : ∀ₑ ⊑'-closed ρ)
              → ⊑'-closed (⟦ M ⟧' ρ)
⊑'-closed-⟦⟧' M ρ ρ~ u (⊑'-single {u} {v} v∈M u⊑v) = 
  ⊑-closed-⟦⟧' M ρ (λ i → ⊑'-closed⇒⊑-closed (ρ~ i)) u v v∈M u⊑v
⊑'-closed-⟦⟧' M ρ ρ~ (V ↦ w) (⊑'-dist-↦ u⊑'M) = {!   !}
⊑'-closed-⟦⟧' M ρ ρ~ (⦅ u , v ⦆) (⊑'-dist-pair u⊑'M x) = {!   !}
⊑'-closed-⟦⟧' M ρ ρ~ (left u) (⊑'-left u⊑'M) = {!   !}
⊑'-closed-⟦⟧' M ρ ρ~ (right v) (⊑'-right u⊑'M) = {!   !}
⊑'-closed-⟦⟧' M ρ ρ~ (∥ ds ∥) (⊑'-tup x) = {!   !}
-}

keylemma : ∀ {u1 V1 u2 V2 D} → ⊑'-closed D
         → ⦅ u1 , V1 ⦆ ∈ D → ⦅ u2 , V2 ⦆ ∈ D
         → V1 ≢ []
         → ⦅ u1 , V2 ⦆ ∈ D
keylemma {u1}{V1}{u2}{V2}{D} ⊑'-D p1∈ p2∈ neV1 = 
  ⊑'-D ⦅ u1 , V2 ⦆ (⊑'-dist-pair H1 H2)
  where
  H1 : u1 ⊑' car ⟨ D , ptt ⟩
  H1 = ⊑'-single ⟨ V1 , ⟨ p1∈ , neV1 ⟩ ⟩ ⊑-refl
  H2 : ∀ v → v ∈ mem V2 → v ⊑' cdr ⟨ D , ptt ⟩
  H2 v v∈ = ⊑'-single ⟨ u2 , ⟨ V2 , ⟨ p2∈ , v∈ ⟩ ⟩ ⟩ ⊑-refl

{-
data _⊑'_⊔_ : Value' → Value' → Value' → Set where
  ⊑'-⊔-R1 : ∀ {u v} → u ⊑' u ⊔ v
  ⊑'-⊔-R2 : ∀ {u v} → v ⊑' u ⊔ v
  ⊑'-⊔-dist-fun : ∀ {V w w1 w2} 
               → w ⊑' w1 ⊔ w2
               → V ↦ w ⊑' V ↦ w1 ⊔ V ↦ w2
  ⊑'-⊔-dist-pair : ∀ {u u1 u2 V V1 V2}
               → u ⊑' u1 ⊔ u2
               → (∀ v → v ∈ mem V
                 → Σ[ v1 ∈ Value' ] Σ[ v2 ∈ Value' ]
                     (v1 ∈ mem V1 ⊎ v1 ∈ mem V2)
                   × (v2 ∈ mem V1 ⊎ v2 ∈ mem V2)
                   × v ⊑' v1 ⊔ v2)
               → ⦅ u , V ⦆ ⊑' ⦅ u1 , V1 ⦆ ⊔ ⦅ u2 , V2 ⦆
-}



{-
reverse direction explanation and design decisions:

Our values for this direction include annotated pairs.
All pairs represent closures, and they contain a single value followed 
  by a list of values.
⦅ u , V ⦆

The interesting case is when the first part contains a (2-ary) function 
  and the second part contains a rep of the captured local environment.
⦅ FV' ↦ (V ↦ w) , FV ⦆
  When such closures are applied, we apply the first projection 
  to the second projection and then to the argument.
  Given such a value, we can determine that the
  application succeeds if FV' ⊆ FV. However, if FV' ⊈ FV,
  we cannot conclude that the application fails. This is because we take
  first and second projections of the denotation: a set of such pairs.
  What we really need to track is whether,
Given a pair ⦅ FV' ↦ (V ↦ w) , FV ⦆ in a denotation D,
  is FV' ⊆ cdr D or not?
This is something that we can determine when we create the pairs and carry as an annotation.
  ⦅ FV' ↦ (V ↦ w) , FV ⦆ ∈ D
  where 
  b = true when FV' ⊆ cdr D, and
  b = false otherwise (but everything else about the denotation of pair holds)
Intuitively, this means that when a lambda generates a pair that represents
  self-application (of the function in the closure to its captured environment)
  we mark that pair with true. And when it generates a pair based on taking
  some garbage as input (a pair outside of the calling convention), then
  we mark that pair as false.


For the closure case, these annotations are sufficient for us to have a theorem
  written with a function fro : Value → Value such that we get the theorem 
delay-reflect : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ).
  The function is simply based on whether self-application would succeed or fail
  on the value; if it would fail, we map it to the empty function which is
  always in a function declaration.

fro ⦅ ν , FV ⦆) = fros FV ⊢ν
fro ⦅ FV' ↦ ν , FV ⦆) = fros FV ⊢ν
fro ⦅ FV' ↦ (V ↦ w) , FV ⦆) = fros FV' ⊢ fros V ↦ fro w
fro ⦅ FV' ↦ (V ↦ w) , FV ⦆) = fros FV ⊢ν {- NOT for app; this a default value for closure case -}
fro ⦅ u , v ⦆) = ω

app M N ->  ((car M')  (cdr M')) N'
d' ∈ target ==> d ∈ source  (where d' ~ d)

pair : DOp (𝒫 Value) (■ ∷ ■ ∷ [])
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ⦅ u , V ⦆) = u ∈ D₁ × mem V ⊆ D₂ × V ≢ []
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ ⦅ U ↦ w , V ⦆) = 
   (mem U ⊆ D₂ × U ≢ []) × (U ↦ w ∈ D₁) × mem V ⊆ D₂ × V ≢ []
{- could do U ⊆ V also, would get neU for free -}
pair ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ _ = False


let y = 5; let g = λ x. y x; (g 2)
              ν               ν · 2
let y = 5; < λ f. λ x. f[0] x , [ y ] > ; ((g[0] g[1]) 2)
           ⦅ ([ 2 ↦ 3 ]) ↦ (2 ↦ 3) , [ 5 ] ⦆    (([ 2 ↦ 3 ]) ↦ (2 ↦ 3)) · [ 5 ] · 2
           ⦅ ([ 5 ]) ↦ XX , [ 5 ] ⦆                 can we prove ν ∈ g[0] g[1] XX
let d' ∈ delay (application)
  ...  case (looks bad)  -> contradiction
      => bad[0] bad[1] = {ν} ... contradicts that the app succeeds.
  ...  case (looks good) -> straightforward proof

let d' ∈ delay (application)
  - things we know
  -> construct a nice enough pair of values
    FV ↦ V ↦ d ∈ g[0] and FV' ⊆ g[1]
    ⦅ FV ↦ V ↦ d , XX ⦆ ∈ g
     and we know FV ⊆ cdr g
    ∀ fv ∈ FV' → ∃ ?,V → ⦅ XX , V ⦆ ∈ g × fv ∈ V

    then, there must be a single pair that is "good"
    ⦅ FV ↦ V ↦ d , FV' ⦆ ∈ g   -> application succeeds, we get result.
    then fro (construction) ∈ the application
      because 



However, such a function will not be enough for an application case.
While a "false" tag indicates that an application of the arrow should fail,
this information is available at the closure introduction site, but 
this information isn't available at the application site... so we define
a logical relation to carry that information.

...
a potential problem or complication: a "false" tag as currently defined
doesn't actually indicate that the application will fail, but 
is just not a guarantee of success. If we wanted "false" to indicate
the negation of FV' ⊆ FV... then our pair operator may no longer be monotonic.

...
another approach that we can use to tackle this (while using a function)
is to prove that given our compatible first and second projections, there
exists a pair which contains both of those projections in the denotation.
This is a pain, because it essentially requires proving down-closed-ness on
an ordering and union-closed-ness on denotations in our language.
I'll want to do this proof on paper befrore I attempt it, because
I'm not certain at this moment that the approach guarantees success.

...
Another approach might be to prove that
any time a pair is in a denotation and self-application succeeds, then
there exists a true-tagged version of that pair in the denotation as well.
-}

{-
Current attempt:
I'm fairly committed to avoiding ordering and joining, so let's first try
the relational approach, but while sidestepping the monotonicity problem...

The idea is to push all of the info in the annotation into the relation,
and "remove the annotation to permit monotonicity".

...or in our case, we simply ignore the existing annotation, which already
permits monotonicity.

f ∈ car g 
FV ⊆ cdr g
----------------
⦅ f , FV ⦆ ∈ g


g1 ⊔ g2 ⊑ g 



application union-closed

(a ↦ b) union (c ↦ d)  

x , x' ∈ app A B
x union x' ∈ app A B

(a ↦ x) , (a' ↦ x') ∈ A
a , a' ∈ B
a union a' ∈ B
(a union a' ↦ x union x′) ∈ A

we know a ↦ x union a' ↦ x' ∈ A (by IH of union-closed)
a union a' ↦ x union x'  ⊑ a ↦ x union a' ↦ x' is true
... use ⊑-closed to finish the proof.

a ↦ x
a' ↦ x'
a intersection a' ↦ x union x'

a ⊔ b ∈ D =  a ∈ D ∧ b ∈ D

A ↦ (x,Y) ⊔ A ↦ (x',Y')
(or A and A', but A ~ A' guaranteed)
A ↦ (x ⊔ x' , Y ++ Y') 


-}


{-

data add2cdr : Value' → Value' → Value' → Set where
  +cdr-pair : ∀ {u V v}
     → add2cdr ⦅ u , V ⦆ v ⦅ u , v ∷ V ⦆
  +cdr-↦ : ∀ {V w v w+v}
     → add2cdr w v w+v
     → add2cdr (V ↦ w) v (V ↦ w+v)
  +cdr-left : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (left u) v (left u+v)
  +cdr-right : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (right u) v (right u+v)
  +cdr-head : ∀ {u v u+v us}
     → add2cdr u v u+v
     → add2cdr (∥ u ∷ us ∥) v (∥ u+v ∷ us ∥)
  +cdr-tail : ∀ {u us v us+v}
     → add2cdr (∥ us ∥) v (∥ us+v ∥)
     → add2cdr (∥ u ∷ us ∥) v (∥ u ∷ us+v ∥)
  +cdr-car : ∀ {u v u+v V}
     → add2cdr u v u+v
     → add2cdr ⦅ u , V ⦆ v ⦅ u+v , V ⦆
  +cdr-cdr-here : ∀ {u v w v+w V}
     → add2cdr v w v+w
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v+w ∷ V ⦆
  +cdr-cdr-there : ∀ {u V w V+w v}
     → add2cdr ⦅ u , V ⦆ w ⦅ u , V+w ⦆
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v ∷ V+w ⦆

get-cdr : ∀ (D : 𝒫 Value') u {v u+v} → add2cdr u v u+v
        → 𝒫 Value'
get-cdr D u +cdr-pair = cdr ⟨ D , ptt ⟩
get-cdr D (V ↦ w) (+cdr-↦ +cdr) = 
  get-cdr (Op4.⋆ ⟨ D , ⟨ mem V , ptt ⟩ ⟩) w +cdr
get-cdr D (left u) (+cdr-left +cdr) = 
  get-cdr (Op4.𝒞 ⟨ D , ⟨ (λ V v → v ∈ V) , ⟨ (λ V v → v ∈ V) , ptt ⟩ ⟩ ⟩) u +cdr
get-cdr D (right u) (+cdr-right +cdr) =
  get-cdr (Op4.𝒞 ⟨ D , ⟨ (λ V v → v ∈ V) , ⟨ (λ V v → v ∈ V) , ptt ⟩ ⟩ ⟩) u +cdr
get-cdr D ∥ u ∷ us ∥ (+cdr-head +cdr) = 
  get-cdr (Op4.proj 0 ⟨ D , ptt ⟩) u +cdr
get-cdr D ∥ u ∷ us ∥ (+cdr-tail +cdr) = 
  get-cdr (rest ⟨ D , ptt ⟩) ∥ us ∥ +cdr
get-cdr D ⦅ u , V ⦆ (+cdr-car +cdr) = 
  get-cdr (car ⟨ D , ptt ⟩) u +cdr
get-cdr D ⦅ u , v ∷ V ⦆ (+cdr-cdr-here +cdr) = 
  get-cdr (cdr ⟨ D , ptt ⟩) v +cdr
get-cdr D ⦅ u , v ∷ V ⦆ (+cdr-cdr-there +cdr) = 
  get-cdr D ⦅ u , V ⦆ +cdr

get-cdr-mono : ∀ {D D'} u {v u+v} (+cdr : add2cdr u v u+v) 
             → D' ⊆ D' → get-cdr D u +cdr ⊆ get-cdr D u +cdr
get-cdr-mono (V ↦ u) (+cdr-↦ +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ⦅ u , V ⦆ +cdr-pair D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ⦅ u , V ⦆ (+cdr-car +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ⦅ u , .(_ ∷ _) ⦆ (+cdr-cdr-here +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ⦅ u , .(_ ∷ _) ⦆ (+cdr-cdr-there +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ∥ .(_ ∷ _) ∥ (+cdr-head +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono ∥ .(_ ∷ _) ∥ (+cdr-tail +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono (left u) (+cdr-left +cdr) D⊆ u+v u+v∈ = {!   !}
get-cdr-mono (right u) (+cdr-right +cdr) D⊆ u+v u+v∈ = {!   !}

+cdr-closed : (D : 𝒫 Value') → Set
+cdr-closed D = ∀ u v u+v 
              → (+cdr : add2cdr u v u+v)
              → u ∈ D → v ∈ get-cdr D u +cdr
              → u+v ∈ D

cdr-closure-n : ℕ → (D : 𝒫 Value') → 𝒫 Value'
cdr-closure-n zero D = D
cdr-closure-n (suc n) D d+v = 
  Σ[ d ∈ Value' ] Σ[ v ∈ Value' ] Σ[ +cdr ∈ add2cdr d v d+v ] 
     (d ∈ (cdr-closure-n n D) × v ∈ get-cdr (cdr-closure-n n D) d +cdr)

cdr-closure : 𝒫 Value' → 𝒫 Value'
cdr-closure D d = Σ[ n ∈ ℕ ] cdr-closure-n n D d

cdr-closure-closed : ∀ D → +cdr-closed (cdr-closure D)
cdr-closure-closed D u v u+v +cdr ⟨ n , u∈ ⟩ v∈ = 
   ⟨ suc n , ⟨ u , ⟨ v , ⟨ +cdr , ⟨ u∈ , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩

cdr-closure-⊆ : ∀ D → D ⊆ cdr-closure D
cdr-closure-⊆ D d d∈ = ⟨ zero , d∈ ⟩


{-

smash-closure-n-⊆-closed : ∀ n {S U} → smash-closed S → U ⊆ S → smash-closure-n n U ⊆ S
smash-closure-n-⊆-closed zero closedS U⊆S d d∈scnU = U⊆S d d∈scnU
smash-closure-n-⊆-closed (suc n) closedS U⊆S d 
                        ⟨ d1 , ⟨ d2 , ⟨ d1∈ , ⟨ d2∈ , smash ⟩ ⟩ ⟩ ⟩ 
  = closedS d1 d2 d smash (smash-closure-n-⊆-closed n closedS U⊆S d1 d1∈) 
                          (smash-closure-n-⊆-closed n closedS U⊆S d2 d2∈)

smash-closure-⊆-closed : ∀ {S U} → smash-closed S → U ⊆ S → smash-closure U ⊆ S
smash-closure-⊆-closed closedS U⊆S d ⟨ n , d∈scUn ⟩ = 
  smash-closure-n-⊆-closed n closedS U⊆S d d∈scUn

-}   
{-
cdr-closure-n : ∀ (n : ℕ) → (D : 𝒫 Value') → 𝒫 Value'
cdr-closure zero D = D
cdr-closure (suc n) D d+v = 
  Σ[ d ∈ Value' ] Σ[ v ∈ Value' ] Σ[ +cdr ∈ add2cdr d v d+v ] (d ∈ D × v ∈ get-cdr D d +cdr)

smash-closed : (D : 𝒫 Value') → Set
smash-closed D = ∀ v1 v2 v → v1 ▹ v ◃ v2 → v1 ∈ D → v2 ∈ D → v ∈ D

smash-closure-n : ∀ (n : ℕ) (U : 𝒫 Value') → 𝒫 Value'
smash-closure-n zero U = U
smash-closure-n (suc n) U u = Σ[ u1 ∈ Value' ] Σ[ u2 ∈ Value' ] 
  u1 ∈ smash-closure-n n U × u2 ∈ smash-closure-n n U × u1 ▹ u ◃ u2

smash-closure : ∀ (U : 𝒫 Value') → 𝒫 Value'
smash-closure U u = Σ[ n ∈ ℕ ] u ∈ smash-closure-n n U

-}

+cdr-⟦⟧' : ∀ M' ρ' 
         → (ρ'~ : ∀ i → +cdr-closed (ρ' i))
          → +cdr-closed (⟦ M' ⟧' ρ')
+cdr-⟦⟧' (# x) ρ' ρ'~ = ρ'~ x
+cdr-⟦⟧' (lit B k ⦅ Nil ⦆') ρ' ρ'~ (const k') v u+v ()
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , V ⦆ v .(⦅ u , v ∷ V ⦆) 
  +cdr-pair u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , V ⦆ v .(⦅ _ , V ⦆) 
  (+cdr-car +cdr) u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , .(_ ∷ _) ⦆ v .(⦅ u , _ ∷ _ ⦆) 
  (+cdr-cdr-here +cdr) u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (pair-op ⦅ M' ,, N' ,, Nil ⦆') ρ' ρ'~ ⦅ u , .(_ ∷ _) ⦆ v .(⦅ u , _ ∷ _ ⦆) 
  (+cdr-cdr-there +cdr) u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (fst-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (snd-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (inl-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (left u) v (left u+v) (+cdr-left +cdr) 
  u∈⟦M'⟧ v∈cdr = +cdr-⟦⟧' M' ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ {! v∈cdr  !}
+cdr-⟦⟧' (inr-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (right u) v (right u+v) (+cdr-right +cdr) 
  u∈⟦M'⟧ v∈cdr = +cdr-⟦⟧' M' ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ {! v∈cdr  !}
+cdr-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (tuple n ⦅ args' ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (get i ⦅ M' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr u∈⟦M'⟧ v∈cdr = {!   !}
+cdr-⟦⟧' (fun-op ⦅ ! clear' (bind' (bind' (ast' N))) ,, Nil ⦆') ρ' ρ'~ 
  (FV ↦ (V ↦ w)) v (FV ↦ (V ↦ u+v)) (+cdr-↦ (+cdr-↦ +cdr)) ⟨ ⟨ w∈N , neV ⟩ , neFV ⟩ v∈cdr 
  = ⟨ ⟨ +cdr-⟦⟧' N {!   !} {!   !} w v u+v +cdr w∈N {!   !} , neV ⟩ , neFV ⟩
+cdr-⟦⟧' (app ⦅ L' ,, M' ,, N' ,, Nil ⦆') ρ' ρ'~ u v u+v +cdr 
  ⟨ V , ⟨ ⟨ FV , ⟨ u∈L' , ⟨ FV⊆M' , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ v∈cdr = 
  ⟨ V , ⟨ ⟨ FV , ⟨ {!   !}  , ⟨ FV⊆M' , neFV ⟩ ⟩ ⟩ , ⟨ V⊆N' , neV ⟩ ⟩ ⟩
  where
  G : (FV ↦ (V ↦ u+v)) ∈ ⟦ L' ⟧' ρ'
  G = +cdr-⟦⟧' L' ρ' ρ'~ (FV ↦ (V ↦ u)) v (FV ↦ (V ↦ u+v)) (+cdr-↦ (+cdr-↦ +cdr)) 
      u∈L' {!  !}

keylemma : ∀ D → +cdr-closed D
         → ∀ V' {f V} → ⦅ f  , V ⦆ ∈ D
         → mem V' ⊆ cdr ⟨ D , ptt ⟩
         → ⦅ f , V' ++ V ⦆ ∈ D
keylemma D ccD [] ⦅f,V⦆∈D V'⊆cdrD = ⦅f,V⦆∈D
keylemma D ccD (v ∷ V') {f}{V} ⦅f,V⦆∈D V'⊆cdrD = 
  ccD ⦅ f , V' ++ V ⦆ v ⦅ f , v ∷ V' ++ V ⦆ +cdr-pair 
      (keylemma D ccD V' ⦅f,V⦆∈D (λ d z → V'⊆cdrD d (there z))) 
      (V'⊆cdrD v (here refl))


{- =============================================================================
   Current attempt
   =============================================================================
This get-cdr formulation is ugly.  Instead of adding a value to a cdr
and checking elsewhere that the value sits in an appropriate denotation, we'll
join values of similar shape, and this will ensure things sit in the right places.
-}


{- I want to start simple with consistent/joinable arrows... let's not worry 
   just yet about whether there are cases where we can "join" domains of arrows -}

data _≈≈_ : List Value' → List Value' → Set
data _~∥~_ : List Value' → List Value' → Set
data _~~_ : Value' → Value' → Set where
  ~~-const : ∀ {B k} → const {B} k ~~ const k
  ~~-ω : ω ~~ ω
  ~~-ν-ν : ν ~~ ν
  ~~-ν-↦ : ∀ {V w} → ν ~~ (V ↦ w)
  ~~-↦-ν : ∀ {V w} → (V ↦ w) ~~ ν
  ~~-↦-↦ : ∀ {V w w'} 
          → (w~ : w ~~ w')
          → (V ↦ w) ~~ (V ↦ w')
  ~~-left : ∀ {d d'}
          → (d~ : d ~~ d')
          → left d ~~ left d'
  ~~-right : ∀ {d d'}
          → (d~ : d ~~ d')
          → right d ~~ right d'
  ~~-tup : ∀ {ds ds'}
          → (ds~ : ds ~∥~ ds')
          → ∥ ds ∥ ~~ ∥ ds' ∥
  ~~-pair : ∀ {u u' V V'}
          → (u~ : u ~~ u')
          → (V≈ : V ≈≈ V')
          → ⦅ u , V ⦆ ~~ ⦅ u' , V' ⦆
data _~∥~_ where
   [] : [] ~∥~ []
   _∷_ : ∀ {d d' ds ds'}
       → (d~ : d ~~ d')
       → (ds~ : ds ~∥~ ds')
       → (d ∷ ds) ~∥~ (d' ∷ ds')

data _≈≈_ where
  ≈≈[] : ∀ {V'} → [] ≈≈ V'
  ≈≈∷ : ∀ {v V V'}
     → All (v ~~_) V'
     → V ≈≈ V'
     → (v ∷ V) ≈≈ V'

_⊔cdr_[_] : (u v : Value') → u ~~ v → Value'
_⊔cdr∥_[_] : (ds ds' : List Value') → ds ~∥~ ds' → List Value'
_⨆cdr_[_] : (V V' : List Value') → V ≈≈ V' → List Value'
(const k) ⊔cdr .(const _) [ ~~-const ] = const k
.ω ⊔cdr .ω [ ~~-ω ] = ω
.ν ⊔cdr .ν [ ~~-ν-ν ] = ν
.ν ⊔cdr (V ↦ w) [ ~~-ν-↦ ] = V ↦ w
(V ↦ w) ⊔cdr .ν [ ~~-↦-ν ] = V ↦ w
(V ↦ w) ⊔cdr (V ↦ w') [ ~~-↦-↦ w~ ] = V ↦ (w ⊔cdr w' [ w~ ])
(left d) ⊔cdr (left d') [ ~~-left d~ ] = left (d ⊔cdr d' [ d~ ])
(right d) ⊔cdr (right d') [ ~~-right d~ ] = right (d ⊔cdr d' [ d~ ])
(∥ ds ∥) ⊔cdr (∥ ds' ∥) [ ~~-tup ds~ ] = ∥ ds ⊔cdr∥ ds' [ ds~ ] ∥
⦅ u , V ⦆ ⊔cdr ⦅ u' , V' ⦆ [ ~~-pair u~ V≈ ] = 
   ⦅ u ⊔cdr u' [ u~ ] , V ⨆cdr V' [ V≈ ] ⦆
.[] ⊔cdr∥ .[] [ [] ] = []
(d ∷ ds) ⊔cdr∥ (d' ∷ ds') [ d~ ∷ ds~ ] = d ⊔cdr d' [ d~ ] ∷ (ds ⊔cdr∥ ds' [ ds~ ])
.[] ⨆cdr V' [ ≈≈[] ] = V'
(v ∷ V) ⨆cdr V' [ ≈≈∷ v~ V≈ ] = 
   reduce (λ {x} v~~x → v ⊔cdr x [ v~~x ]) v~ ++ (V ⨆cdr V' [ V≈ ]) 

{-
 : Value' → Value' → Value' → Set where
  +cdr-pair : ∀ {u V v}
     → add2cdr ⦅ u , V ⦆ v ⦅ u , v ∷ V ⦆
  +cdr-↦ : ∀ {V w v w+v}
     → add2cdr w v w+v
     → add2cdr (V ↦ w) v (V ↦ w+v)
  +cdr-left : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (left u) v (left u+v)
  +cdr-right : ∀ {u v u+v}
     → add2cdr u v u+v
     → add2cdr (right u) v (right u+v)
  +cdr-head : ∀ {u v u+v us}
     → add2cdr u v u+v
     → add2cdr (∥ u ∷ us ∥) v (∥ u+v ∷ us ∥)
  +cdr-tail : ∀ {u us v us+v}
     → add2cdr (∥ us ∥) v (∥ us+v ∥)
     → add2cdr (∥ u ∷ us ∥) v (∥ u ∷ us+v ∥)
  +cdr-car : ∀ {u v u+v V}
     → add2cdr u v u+v
     → add2cdr ⦅ u , V ⦆ v ⦅ u+v , V ⦆
  +cdr-cdr-here : ∀ {u v w v+w V}
     → add2cdr v w v+w
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v+w ∷ V ⦆
  +cdr-cdr-there : ∀ {u V w V+w v}
     → add2cdr ⦅ u , V ⦆ w ⦅ u , V+w ⦆
     → add2cdr ⦅ u , v ∷ V ⦆ w ⦅ u , v ∷ V+w ⦆
-}


{- =============================================================================
   ACTUAL Current attempt
   =============================================================================
The ~~ relation was not useful on its own, and I don't really want
join to be a function (because the way it maps in the ≈≈ case explodes and is gross).

So we want to define something similar, but that is just join as a relation.
-}



data _▹_◃_ : Value' → Value' → Value' → Set where
    smash-pair-L : ∀ {u1 u2 V1 V2 v2}
            → v2 ∈ mem V2
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u1 , v2 ∷ V1 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-pair-R : ∀ {u1 u2 V1 V2 v1}
            → v1 ∈ mem V1
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u2 , v1 ∷ V2 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-↦ : ∀ {V w1 w2 w} 
            → w1 ▹ w ◃ w2  
            → (V ↦ w1) ▹ (V ↦ w) ◃ (V ↦ w2)
    smash-left : ∀ {v1 v2 v} → v1 ▹ v ◃ v2
            → left v1 ▹ left v ◃ left v2
    smash-right : ∀ {v1 v2 v} → v1 ▹ v ◃ v2
            → right v1 ▹ right v ◃ right v2
    smash-car-L : ∀ {u1 u2 u V1 V2}
            → (u⊔ : u1 ▹ u ◃ u2)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u , V1 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-car-R : ∀ {u1 u2 u V1 V2}
            → (u⊔ : u1 ▹ u ◃ u2)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u , V2 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-cdr-here-L : ∀ {u1 u2 v1 v2 v V1 V2}
            → (v⊔ : v1 ▹ v ◃ v2)
            → (v2∈ : v2 ∈ mem V2)
            → ⦅ u1 , v1 ∷ V1 ⦆ ▹ ⦅ u1 , v ∷ V1 ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-cdr-here-R : ∀ {u1 u2 v1 v2 v V1 V2}
            → (v⊔ : v1 ▹ v ◃ v2)
            → (v1∈ : v1 ∈ mem V1)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u2 , v ∷ V1 ⦆ ◃ ⦅ u2 , v2 ∷ V2 ⦆
    smash-cdr-there-L : ∀ {u1 u2 u v V1 V2 V}
            → (V⨆ : ⦅ u1 , V1 ⦆ ▹ ⦅ u , V ⦆ ◃ ⦅ u2 , V2 ⦆)
            → ⦅ u1 , v ∷ V1 ⦆ ▹ ⦅ u , v ∷ V ⦆ ◃ ⦅ u2 , V2 ⦆
    smash-cdr-there-R : ∀ {u1 u2 u v V1 V2 V}
            → (V⨆ : ⦅ u1 , V1 ⦆ ▹ ⦅ u , V ⦆ ◃ ⦅ u2 , V2 ⦆)
            → ⦅ u1 , V1 ⦆ ▹ ⦅ u , v ∷ V ⦆ ◃ ⦅ u2 , v ∷ V2 ⦆
    smash-nil : ∥ [] ∥ ▹ ∥ [] ∥ ◃ ∥ [] ∥
    smash-cons : ∀ {d1 d2 d ds1 ds2 ds}
            → (d⊔ : d1 ▹ d ◃ d2)
            → (ds⊔ : ∥ ds1 ∥ ▹ ∥ ds ∥ ◃ ∥ ds2 ∥)
            → ∥ d1 ∷ ds1 ∥ ▹ ∥ d ∷ ds ∥ ◃ ∥ d2 ∷ ds2 ∥
  {-
    smash-head : ∀ {v1 v2 v vs} → v1 ▹ v ◃ v2
            → ∥ v1 ∷ vs ∥ ▹ ∥ v ∷ vs ∥ ◃ ∥ v2 ∷ vs ∥
    smash-tail : ∀ {v vs1 vs2 vs} → ∥ vs1 ∥ ▹ ∥ vs ∥ ◃ ∥ vs2 ∥
            → ∥ v ∷ vs1 ∥  ▹ ∥ v ∷ vs ∥ ◃ ∥ v ∷ vs2 ∥
    -}

data _▹[_]◃_ : List Value' → List Value' → List Value' → Set where
    [] : [] ▹[ [] ]◃ []
    _∷_ : ∀ {d1 d2 d ds1 ds2 ds}
        → (d⊔ : d1 ▹ d ◃ d2)
        → (ds⊔ : ds1 ▹[ ds ]◃ ds2)
        → (d1 ∷ ds1) ▹[ (d ∷ ds) ]◃ (d2 ∷ ds2)
data _▹▹_◃◃_ : List Value' → List Value' → List Value' → Set where
    ▹[]◃ : ∀ {V2} → [] ▹▹ V2 ◃◃ V2
    ▹∷◃ : ∀ {v1 V1 V2 V}
        → (V⨆ : V1 ▹▹ V ◃◃ V2)
        → (v1 ∷ V1) ▹▹ V ◃◃ V2


smash-mem : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {FV1 FV2} 
          → d1 ∈ mem FV1 → d2 ∈ mem FV2 → List Value'
smash-mem {d1} {d2} {d} smash {FV1 = d1 ∷ FV1} (here refl) d2∈ = d ∷ FV1
smash-mem {d1} {d2} {d} smash {FV1 = d' ∷ FV1} (there d1∈) d2∈ = 
   d' ∷ smash-mem smash d1∈ d2∈

smash-mem-ne : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {FV1 FV2} 
          → (d1∈ : d1 ∈ mem FV1) → (d2∈ : d2 ∈ mem FV2)
          → d ∈ mem (smash-mem smash d1∈ d2∈)
smash-mem-ne smash (here refl) d2∈ = here refl
smash-mem-ne smash (there d1∈) d2∈ = there (smash-mem-ne smash d1∈ d2∈)

smash-cdr-L : ∀ {d1 d2 d} → (smash : d1 ▹ d ◃ d2)
          → ∀ {u1 u2 FV1 FV2} 
          → (d1∈ : d1 ∈ mem FV1) → (d2∈ : d2 ∈ mem FV2)
          → ⦅ u1 , FV1 ⦆ ▹ ⦅ u1 , smash-mem smash d1∈ d2∈ ⦆ ◃ ⦅ u2 , FV2 ⦆
smash-cdr-L smash (here refl) d2∈ = smash-cdr-here-L smash d2∈
smash-cdr-L smash (there d1∈) d2∈ = smash-cdr-there-L (smash-cdr-L smash d1∈ d2∈)

smash-closed : (D : 𝒫 Value') → Set
smash-closed D = ∀ v1 v2 v → v1 ▹ v ◃ v2 → v1 ∈ D → v2 ∈ D → v ∈ D

smash-closure-n : ∀ (n : ℕ) (U : 𝒫 Value') → 𝒫 Value'
smash-closure-n zero U = U
smash-closure-n (suc n) U u = Σ[ u1 ∈ Value' ] Σ[ u2 ∈ Value' ] 
  u1 ∈ smash-closure-n n U × u2 ∈ smash-closure-n n U × u1 ▹ u ◃ u2

smash-closure : ∀ (U : 𝒫 Value') → 𝒫 Value'
smash-closure U u = Σ[ n ∈ ℕ ] u ∈ smash-closure-n n U

smash-closure-n-⊆-closed : ∀ n {S U} → smash-closed S → U ⊆ S → smash-closure-n n U ⊆ S
smash-closure-n-⊆-closed zero closedS U⊆S d d∈scnU = U⊆S d d∈scnU
smash-closure-n-⊆-closed (suc n) closedS U⊆S d 
                        ⟨ d1 , ⟨ d2 , ⟨ d1∈ , ⟨ d2∈ , smash ⟩ ⟩ ⟩ ⟩ 
  = closedS d1 d2 d smash (smash-closure-n-⊆-closed n closedS U⊆S d1 d1∈) 
                          (smash-closure-n-⊆-closed n closedS U⊆S d2 d2∈)

smash-closure-⊆-closed : ∀ {S U} → smash-closed S → U ⊆ S → smash-closure U ⊆ S
smash-closure-⊆-closed closedS U⊆S d ⟨ n , d∈scUn ⟩ = 
  smash-closure-n-⊆-closed n closedS U⊆S d d∈scUn


smash-⟦⟧' : ∀ M' ρ' 
          → (ρ'~ : ∀ i → smash-closed (ρ' i))
          → smash-closed (⟦ M' ⟧' ρ')
smash-⟦⟧' (# x) ρ' ρ'~ = ρ'~ x
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ u1 , _ ∷ V1 ⦆) 
          (smash-pair-L x) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ u2 , _ ∷ V2 ⦆) 
          (smash-pair-R x) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ _ , V1 ⦆) 
          (smash-car-L smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , V2 ⦆ .(⦅ _ , V2 ⦆) 
          (smash-car-R smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , .(_ ∷ _) ⦆ ⦅ u2 , V2 ⦆ .(⦅ u1 , _ ∷ _ ⦆) 
          (smash-cdr-here-L smash v2∈) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , .(_ ∷ _) ⦆ .(⦅ u2 , _ ∷ V1 ⦆) 
          (smash-cdr-here-R smash v1∈) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , .(_ ∷ _) ⦆ ⦅ u2 , V2 ⦆ .(⦅ _ , _ ∷ _ ⦆) 
          (smash-cdr-there-L smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (pair-op ⦅ M ,, N ,, Nil ⦆') ρ' ρ'~ ⦅ u1 , V1 ⦆ ⦅ u2 , .(_ ∷ _) ⦆ .(⦅ _ , _ ∷ _ ⦆) 
          (smash-cdr-there-R smash) p1∈ p2∈ = {!   !}
smash-⟦⟧' (fst-op ⦅ M ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash
          ⟨ FV1 , ⟨ p1∈ , neFV1 ⟩ ⟩ ⟨ FV2 , ⟨ p2∈ , neFV2 ⟩ ⟩
  with smash-⟦⟧' M ρ' ρ'~ ⦅ d1 , FV1 ⦆ ⦅ d2 , FV2 ⦆ ⦅ d , FV1 ⦆ 
                 (smash-car-L smash) p1∈ p2∈
... | IH
    = ⟨ FV1 , ⟨ IH , neFV1 ⟩ ⟩
smash-⟦⟧' (snd-op ⦅ M ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash
  ⟨ f1 , ⟨ FV1 , ⟨ p1∈ , d1∈ ⟩ ⟩ ⟩  ⟨ f2 , ⟨ FV2 , ⟨ p2∈ , d2∈ ⟩ ⟩ ⟩
  with smash-⟦⟧' M ρ' ρ'~ ⦅ f1 , FV1 ⦆ ⦅ f2 , FV2 ⦆
                 ⦅ f1 , smash-mem smash d1∈ d2∈ ⦆
                 (smash-cdr-L smash d1∈ d2∈) p1∈ p2∈
... | IH
    = ⟨ f1 , ⟨ smash-mem smash d1∈ d2∈ , ⟨ IH , smash-mem-ne smash d1∈ d2∈ ⟩ ⟩ ⟩

smash-⟦⟧' (inl-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (left d1) (left d2) (left d)
    (smash-left smash) d1∈ d2∈ = smash-⟦⟧' M' ρ' ρ'~ d1 d2 d smash d1∈ d2∈
smash-⟦⟧' (inr-op ⦅ M' ,, Nil ⦆') ρ' ρ'~ (right d1) (right d2) (right d)
    (smash-right smash) d1∈ d2∈ = smash-⟦⟧' M' ρ' ρ'~ d1 d2 d smash d1∈ d2∈
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₁ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈M' ⟩ ⟩ ⟩)  (inj₁ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈M' ⟩ ⟩ ⟩)
  with smash-⟦⟧' M' ((mem (v1 ∷ V1 ++ v2 ∷ V2)) • ρ') {!   !} d1 d2 d smash 
                   {! d1∈M'  !} {! d2∈M'  !}
... | IH = inj₁ ⟨ v1 , ⟨ V1 ++ (v2 ∷ V2) , ⟨ {!   !} , IH ⟩ ⟩ ⟩
  {- in the IH, expand each of the environments for the d1∈ d2∈ premises -}
  {- even-worse... we have to extend the environment by the 
     smash-closure of v1 ∷ V1 ++ v2 ∷ V2... -}
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₁ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈M' ⟩ ⟩ ⟩)  (inj₂ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈N' ⟩ ⟩ ⟩)
  = {!   !} {- v1∈ and v2∈ contradict consistency of ⟦L'⟧  -}
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₂ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈N' ⟩ ⟩ ⟩)  (inj₁ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈M' ⟩ ⟩ ⟩)
  = {!   !} {- v1∈ and v2∈ contradict consistency of ⟦L'⟧  -}
smash-⟦⟧' (case-op ⦅ L' ,, ⟩ M' ,, ⟩ N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash 
  (inj₂ ⟨ v1 , ⟨ V1 , ⟨ V1⊆ , d1∈N' ⟩ ⟩ ⟩) (inj₂ ⟨ v2 , ⟨ V2 , ⟨ V2⊆ , d2∈N' ⟩ ⟩ ⟩)
  = inj₂ {!   !}  {- similar to first case -}
smash-⟦⟧' (fun-op ⦅ args ⦆') ρ' ρ'~ = {!   !}
smash-⟦⟧' (app ⦅ L' ,, M' ,, N' ,, Nil ⦆') ρ' ρ'~ d1 d2 d smash d1∈ d2∈ = {!   !}
smash-⟦⟧' (tuple n ⦅ args ⦆') ρ' ρ'~ d1 d2 d smash d1∈ d2∈ = {!   !}
smash-⟦⟧' (get i ⦅ M' ,, Nil ⦆') ρ' ρ'~ d1 d2 smash d1∈ d2∈ = {!   !}



keylemma' : ∀ D → smash-closed D
         → ∀ V' {f V} → ⦅ f  , V ⦆ ∈ D
         → mem V' ⊆ cdr ⟨ D , ptt ⟩
         → ⦅ f , V' ++ V ⦆ ∈ D
keylemma' D scD [] ⦅f,V⦆∈D V'⊆cdrD = ⦅f,V⦆∈D
keylemma' D scD (v ∷ V') {f}{V} ⦅f,V⦆∈D V'⊆cdrD with V'⊆cdrD v (here refl)
... | ⟨ f' , ⟨ FV , ⟨ p∈ , v∈FV ⟩ ⟩ ⟩ = 
  scD ⦅ f' , FV ⦆ ⦅ f , V' ++ V ⦆ ⦅ f , v ∷ V' ++ V ⦆ (smash-pair-R v∈FV) 
      p∈ 
      (keylemma' D scD V' ⦅f,V⦆∈D (λ d z → V'⊆cdrD d (there z))) 


fros : List Value' → List Value
fro : Value' → Value
fro (const x) = const x
fro (V ↦ w) = ω
fro ν = ω
fro ω = ω
fro ⦅ ν , FV ⦆ = fros FV ⊢ν
fro ⦅ V ↦ ν , FV ⦆ = fros FV ⊢ν
fro ⦅ FV' ↦ (V ↦ w) , FV ⦆ with FV' D4.mem⊆? FV
... | yes FV'⊆FV =  fros FV' ⊢ fros V ↦ fro w
... | no FV'⊈FV = fros FV ⊢ν
fro ⦅ u , v ⦆ = ω
fro ∥ xs ∥ = ∥ fros xs ∥
fro (left v) = left (fro v)
fro (right v) = right (fro v)
fros List.[] = []
fros (d List.∷ ds) = fro d List.∷ fros ds


fro-set : 𝒫 Value' → 𝒫 Value
fro-set S v = Σ[ d ∈ Value' ] d ∈ S × v ≡ fro d

_fro-⊆_ : 𝒫 Value' → 𝒫 Value → Set
A fro-⊆ B = ∀ d → d ∈ A → fro d ∈ B

fro-ne : ∀ V → V ≢ [] → fros V ≢ []
fro-ne [] neV = ⊥-elim (neV refl)
fro-ne (x ∷ V) neV ()

fros-length : ∀ V → length (fros V) ≡ length V
fros-length [] = refl
fros-length (x ∷ V) = cong suc (fros-length V)

fros-nth : ∀ V i → fro (Op4.nth V i) ≡ Op3.nth (fros V) i
fros-nth [] zero = refl
fros-nth (x ∷ V) zero = refl
fros-nth [] (suc i) = refl
fros-nth (x ∷ V) (suc i) = fros-nth V i

fro-∈-mem : ∀ {a}{V} → a ∈ (mem V) → fro a ∈ mem (fros V)
fro-∈-mem (here px) = here (cong fro px)
fro-∈-mem (there a∈) = there (fro-∈-mem a∈)

∈-mem-fros : ∀ {d}{V} → d ∈ mem (fros V) → Σ[ a ∈ Value' ] a ∈ mem V × d ≡ fro a
∈-mem-fros {d} {x ∷ V} (here px) = ⟨ x , ⟨ here refl , px ⟩ ⟩
∈-mem-fros {d} {x ∷ V} (there d∈) with ∈-mem-fros d∈
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = ⟨ a , ⟨ there a∈ , refl ⟩ ⟩

++-ne₁ : ∀ {A : Set} (FV : List A) {FV'} → FV ≢ [] → FV ++ FV' ≢ []
++-ne₁ [] neFV = ⊥-elim (neFV refl)
++-ne₁ (x ∷ FV) neFV ()

++-⊆₁ : ∀ {A : Set} (FV : List A) {FV'} → mem FV ⊆ (mem (FV ++ FV'))
++-⊆₁ (x ∷ FV) d (here refl) = here refl
++-⊆₁ (x ∷ FV) d (there d∈) = there (++-⊆₁ FV d d∈)


delay-reflect' : ∀ M ρ
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → ∀ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect'-⊆ : ∀ M ρ 
  → (ρ~ : ∀ i → smash-closed (ρ i))
  → ∀ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' (` x) ρ ρ~ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ ν , FV ⦆ 
  ⟨ tt , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ ν , FV ⦆ 
  ⟨ ⟨ tt , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ = 
  ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ 
  with FV' D4.mem⊆? FV
... | no FV'⊈  = ⟨ G3 , fro-ne FV neFV ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) 
                 → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ρ~ ⦅ FV' ↦ (V ↦ w) , FV ⦆ 
  ⟨ ⟨ ⟨ w∈N , neV ⟩ , neFV' ⟩ , ⟨ FV⊆ , neFV ⟩ ⟩ | yes FV'⊆ 
    = ⟨ (λ d z → G3 d (froFV'⊆ d z)) , ⟨ fro-ne FV' neFV' , ⟨ G1 , fro-ne V neV ⟩ ⟩ ⟩
  where
  froFV'⊆ : mem (fros FV') ⊆ mem (fros FV)
  froFV'⊆ d d∈ with ∈-mem-fros d∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem (FV'⊆ b b∈)
  H : env-map fro (mem V • mem FV' • λ x → L4.init)
      ⊆ₑ mem (fros V) • mem (fros FV') • (λ x → L3.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros V) • mem (fros FV') • (λ x → L3.init))
  G1 = L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect' N (mem V • mem FV' • (λ _ x → x ≡ ω)) {!   !} w 
                     w∈N)
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ ρ~ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a a∈ with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b b∈)
delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ ρ~ d 
   ⟨ V , ⟨ inner-app , ⟨ V⊆N' , neV ⟩ ⟩ ⟩ with inner-app
... | ⟨ FV , ⟨ FV↦[V↦d]∈carM' , ⟨ FV⊆cdrM' , neFV ⟩ ⟩ ⟩ with FV↦[V↦d]∈carM'
... | ⟨ FV' , ⟨ ⦅FV↦[V↦d],FV'⦆∈M' , neFV' ⟩ ⟩ = 
  ⟨ fros FV , ⟨ fro-ne FV neFV 
  , ⟨ fros V , ⟨ IHM , ⟨ IHN , fro-ne V neV ⟩ ⟩ ⟩ ⟩ ⟩
  where
  IHN : mem (fros V) ⊆ ⟦ N ⟧ (env-map fro ρ)
  IHN = delay-reflect'-⊆ N ρ ρ~ V V⊆N'
  G : ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ ∈ ⟦ delay M ⟧' ρ
  G = keylemma' (⟦ delay M ⟧' ρ) (smash-⟦⟧' (delay M) ρ ρ~) FV ⦅FV↦[V↦d],FV'⦆∈M' FV⊆cdrM'
  IHM : (fros FV ⊢ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  IHM with FV D4.mem⊆? (FV ++ FV') | delay-reflect' M ρ ρ~ ⦅ FV ↦ (V ↦ d) , FV ++ FV' ⦆ G
  ... | yes FV⊆FV | IH = IH
  ... | no FV⊈FV | IH = ⊥-elim (FV⊈FV (++-⊆₁ FV))
delay-reflect' (lit B k ⦅ Nil ⦆) ρ ρ~ (const {B'} k') d∈ with base-eq? B B'
... | yes refl = d∈
... | no neq = d∈
delay-reflect' (tuple n ⦅ args ⦆) ρ ρ~ d d∈ = G n args d d∈
  where
  G : ∀ n args d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args d refl = refl
  G (suc n) (arg ,, args) ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect' arg ρ ρ~ d d∈ , ds'∈ ⟩
delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ ρ~ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect' M ρ ρ~ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ ρ~ (left v) v∈ = 
  delay-reflect' M ρ ρ~ v v∈
delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ ρ~ (right v) v∈ = 
  delay-reflect' M ρ ρ~ v v∈
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} M H (fro d) 
            (delay-reflect' M (mem (v ∷ V) • ρ) {!   !} d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → left d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect' L ρ ρ~ (left b) (LV∈ b b∈)
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ ρ~ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = 
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ G 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro d) 
            (delay-reflect' N (mem (v ∷ V) • ρ) {!   !} d d∈) ⟩ ⟩ ⟩
    where
    H : env-map fro (mem (v ∷ V) • ρ) ⊆ₑ mem (fro v ∷ fros V) • env-map fro ρ
    H zero d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = fro-∈-mem b∈
    H (suc n) d ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = ⟨ b , ⟨ b∈ , refl ⟩ ⟩
    G : ∀ d' → d' ∈ mem (fros (v ∷ V))
             → right d' ∈ ⟦ L ⟧ (env-map fro ρ)
    G d' d'∈ with ∈-mem-fros {V = v ∷ V} d'∈
    ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = delay-reflect' L ρ ρ~ (right b) (RV∈ b b∈)
delay-reflect'-⊆ M ρ ρ~ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ ρ~ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ ρ~ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ ρ~ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ ρ~ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect' {zero} args ρ ρ~ = lift tt
del-map-args-reflect' {suc n} (M ,, args) ρ ρ~ = 
  ⟨ lift (delay-reflect' M ρ ρ~) , del-map-args-reflect' args ρ ρ~ ⟩


{-
data _⊢_≈fro_ : 𝒫 Value' → List Value' → List Value → Set₁
data _⊢_~fros_ : 𝒫 Value' → List Value' → List Value → Set₁
data _⊢_~fro_ : 𝒫 Value' → Value' → Value → Set₁ where
  fro-ω : ∀ {D} → D ⊢ ω ~fro ω
  fro-const : ∀ {D B k} → D ⊢ const {B} k ~fro const k
  fro-left : ∀ {d d' D} → (d~ : D ⊢ d ~fro d')
           → Op4.ℒ ⟨ D , ptt ⟩ ⊢ left d ~fro left d'
  fro-right : ∀ {d d' D} → (d~ : D ⊢ d ~fro d')
           → Op4.ℛ ⟨ D , ptt ⟩ ⊢ right d ~fro right d'
  fro-tup : ∀ {ds ds' D} → (ds~ : D ⊢ ds ≈fro ds')
          → D ⊢ ∥ ds ∥ ~fro ∥ ds' ∥
  fro-ν : ∀ {FV FV' b D}
        → (FV~ : D ⊢ FV ~fros FV')
        → D ⊢ ⦅ ν , FV ⦆) ~fro (FV' ⊢ν)
  fro-↦-ν : ∀ {FV FV' V b D}
          → (FV~ : D ⊢ FV ~fros FV')
          → D ⊢ ⦅ V ↦ ν , FV ⦆) ~fro (FV' ⊢ν) 
  fro-clos-true : ∀ {FV FV' V V' w w' FVcdr D}
          → (FV~ : D ⊢ FV ~fros FV')
          → (V~ : D ⊢ V ~fros V')
          → (w~ : D ⊢ w ~fro w')
          → D ⊢ ⦅ FV ↦ (V ↦ w) , FVcdr ⦆) ~fro (FV' ⊢ V' ↦ w')
  fro-clos-false : ∀ {FV FV' dom V w D}
          → (FV~ : D ⊢ FV ~fros FV')
          → D ⊢ ⦅ dom ↦ (V ↦ w) , FV ⦆) ~fro (FV' ⊢ν)


data _⊢_≈fro_ where
  [] : ∀ {D} → D ⊢ [] ≈fro []
  _∷_ : ∀ {d d' ds ds' D}
        → (d~ : D ⊢ d ~fro d')
        → (ds~ : D ⊢ ds ≈fro ds')
        → D ⊢ (d ∷ ds) ≈fro (d' ∷ ds')

data _⊢_~fros_ where
  [] : ∀ {D} → D ⊢ [] ~fros []
  _∷_ : ∀ {d d' ds ds' D}
        → (d~ : D ⊢ d ~fro d')
        → (ds~ : D ⊢ ds ~fros ds')
        → D ⊢ (d ∷ ds) ~fros (d' ∷ ds')




{- 

This has to be existentially quantified on at least D 
... this could become a mess... might need to say something like
∃ d D. d ∈ ⟦ M ⟧ ρ × D ⊢ d' ~fro d      

NOTES:
 - the relation will have to be closed upward on denotations, relying on the monotonicity of the operators
 - [theorem] × D ⊆ ⟦ M ⟧ ρ ??? 
 - 

-}
delay-reflect : ∀ M (ρ' : Env Value') (ρ : Env Value)
              → (∀ {i d'} → d' ∈ ρ' i → Σ[ d ∈ Value ] d ∈ ρ i × Σ[ D ∈ 𝒫 Value' ] D ⊢ d' ~fro d)
              → ∀ d'
              → d' ∈ ⟦ delay M ⟧' ρ' 
              → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ ×
                Σ[ D ∈ 𝒫 Value' ] D ⊢ d' ~fro d
delay-reflect-⊆ : ∀ M ρ' ρ 
              → (∀ {i d'} → d' ∈ ρ' i → Σ[ d ∈ Value ] d ∈ ρ i × Σ[ D ∈ 𝒫 Value' ] D ⊢ d' ~fro d)
              → ∀ V'
              → mem V' ⊆ ⟦ delay M ⟧' ρ'
              → Σ[ V ∈ List Value ] mem V ⊆ ⟦ M ⟧ ρ ×
                Σ[ D ∈ 𝒫 Value' ] D ⊢ V' ~fros V
delay-reflect (` i) ρ' ρ ρ~ d' d'∈ = ρ~ d'∈
delay-reflect (inl-op ⦅ M ,, Nil ⦆) ρ' ρ ρ~ (left d') d'∈ 
  with (delay-reflect M ρ' ρ ρ~ d' d'∈)
... | ⟨ d , ⟨ d∈ , ⟨ D , ~d ⟩ ⟩ ⟩ = ⟨ left d , ⟨ d∈ , ⟨ Op4.ℒ ⟨ D , ptt ⟩ , fro-left ~d ⟩ ⟩ ⟩
delay-reflect (inr-op ⦅ M ,, Nil ⦆) ρ' ρ ρ~ (right d') d'∈
  with (delay-reflect M ρ' ρ ρ~ d' d'∈)
... | ⟨ d , ⟨ d∈ , ⟨ D , ~d ⟩ ⟩ ⟩ = ⟨ right d , ⟨ d∈ , ⟨ Op4.ℛ ⟨ D , ptt ⟩ , fro-right ~d ⟩ ⟩ ⟩
delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ' ρ ρ~ d' 
   (inj₁ ⟨ v' , ⟨ V' , ⟨ V'⊆ , d'∈ ⟩ ⟩ ⟩) 
  with delay-reflect-⊆ L ρ' ρ ρ~ (v' ∷ V') {! V'⊆   !}
... | ⟨ V , ⟨ V⊆ , ⟨ DV , ~V ⟩ ⟩ ⟩
  with (delay-reflect M (mem (v' ∷ V') • ρ') {!   !} {!   !} d' d'∈)
... | ⟨ d , ⟨ d∈ , ⟨ Dd , ~d ⟩ ⟩ ⟩ = 
  ⟨ d , ⟨ inj₁ ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , d∈ ⟩ ⟩ ⟩ , ⟨ Dd , ~d ⟩ ⟩ ⟩
delay-reflect (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) ρ' ρ ρ~ d' 
   (inj₂ ⟨ v' , ⟨ V' , ⟨ V'⊆ , d'∈ ⟩ ⟩ ⟩) = {!   !}
delay-reflect M ρ' ρ ρ~ d' d'∈ = {!   !}
delay-reflect-⊆ M ρ' ρ ρ~ [] V'⊆ = ⟨ [] , ⟨ (λ d ()) , ⟨ ⟦ delay M ⟧' ρ' , [] ⟩ ⟩ ⟩
delay-reflect-⊆ M ρ' ρ ρ~ (d' ∷ V') V'⊆
  with delay-reflect M ρ' ρ ρ~ d' (V'⊆ d' (here refl)) 
     | delay-reflect-⊆ M ρ' ρ ρ~ V' (λ d z → V'⊆ d (there z))
... | ⟨ d , ⟨ d∈ , ⟨ D1 , ~d ⟩ ⟩ ⟩ | ⟨ V , ⟨ V⊆ , ⟨ D2 , ~V ⟩ ⟩ ⟩ 
    = ⟨ d ∷ V , ⟨ G , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩
  where
  G : mem (d ∷ V) ⊆ ⟦ M ⟧ ρ
  G d' (here refl) = d∈
  G d' (there d'∈) = V⊆ d' d'∈

{-
delay-reflect'-⊆ M ρ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
-}







{-
need to check for equality of fv' with fv
and FV' with FV

-}

{-






fro-mem-rewrite : ∀ V ρ → env-map fro (mem V • ρ) ⊆ₑ (mem (fros V)) • env-map fro ρ
fro-mem-rewrite V ρ zero d ⟨ a , ⟨ a∈V , refl ⟩ ⟩ = fro-∈-mem a∈V
fro-mem-rewrite V ρ (suc x) d d∈ρx = d∈ρx

fro-⊆-mem : ∀ {V' V} → mem V' ⊆ mem V → mem (fros V') ⊆ (mem (fros V))
fro-⊆-mem V⊆ d d∈ with ∈-mem-fros d∈ 
... | ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem (V⊆ a a∈)

{-
data _⊑_⊔_ : Value → Value → Value → Set where
  ⊑-clos-L : ∀ {f₁} f₂ {fv₁ fv₂ fv' FV₁ FV₂ FV'}
           → (∀ d → d ∈ mem (fv' ∷ FV') → ((d ∈ mem (fv₁ ∷ FV₁)) 
                                           ⊎ (d ∈ mem (fv₂ ∷ FV₂))))
           → ⦅ f₁ ∣ fv' ∷ fV' ⦆ ⊑ ⦅ f₁ ∣ fv₁ , FV₁ ⦆ ⊔ ⦅ f₂ ∣ fv₂ , FV₂ ⦆
  ⊑-clos-R : ∀ f₁ {f₂ fv₁ fv₂ fv' FV₁ FV₂ FV'}
           → (∀ d → d ∈ mem (fv' ∷ FV') → ((d ∈ mem (fv₁ ∷ FV₁)) 
                                           ⊎ (d ∈ mem (fv₂ ∷ FV₂))))
           → ⦅ f₂ ∣ fv' ∷ fV' ⦆ ⊑ ⦅ f₁ ∣ fv₁ , FV₁ ⦆ ⊔ ⦅ f₂ ∣ fv₂ , FV₂ ⦆
  {- the next case is probably not good enough, 
     but I can workshop it while working on the theorem -}
  ⊑-↦-L : ∀ {v₁ V₁ w₁ v₂ V₂ w₂ w a A b B}
       → w ⊑ w₁ ⊔ w₂
       → (a , A ⊢ v₁ , V₁ ↦ w) ⊑ (a , A ⊢ v₁ , V₁ ↦ w₁) ⊔ (b , B ⊢ v₂ , V₂ ↦ w₂)
  {- also need other cases; will add as needed -}


⊔-⊑-closed : ∀ M ρ v₁ v₂ d
           {- insert same closed condition on ρ -}
            → v₁ ∈ ⟦ delay M ⟧' ρ
            → v₂ ∈ ⟦ delay M ⟧' ρ
            → d ⊑ v₁ ⊔ v₂
            → d ∈ ⟦ delay M ⟧' ρ
⊔-⊑-closed (` x) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) 
  ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (app ⦅ M ,, N ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (lit B k ⦅ Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (tuple zero ⦅ Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (tuple (suc n) ⦅ M ,, Ms ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (get i ⦅ M ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (inl-op ⦅ M ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (inr-op ⦅ M ,, Nil ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
⊔-⊑-closed (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ v₁ v₂ d v₁∈ v₂∈ d⊑v₁⊔v₂ = HOLE
-}

{-crucial lemma: closures-are-products -}
{-
closures-are-products : ∀ M ρ f fv FV fv' FV'
                      → mem FV ⊆ cdr ⟨ ⟦ delay M ⟧' ρ , ptt ⟩ 
                      → ⦅ f ∣ fv' ∷ fV' ⦆ ∈ ⟦ delay M ⟧' ρ
                      → ⦅ f ∣ fv ∷ fV ⦆ ∈ ⟦ delay M ⟧' ρ
closures-are-products M ρ f fv FV fv' FV' FV⊆ f∈ = 
  ⊔-⊑-closed M ρ ⦅ f ∣ fv' ∷ fV' ⦆ ⦅ proj₁ G ∣ fv ∷ fV ⦆ ⦅ f ∣ fv ∷ fV ⦆ 
                  f∈ (proj₂ G) (⊑-clos-R (proj₁ G) (λ d d∈ → inj₂ d∈))
  where 
  G : Σ[ f' ∈ Value ] ⦅ f' ∣ fv ∷ fV ⦆ ∈ ⟦ delay M ⟧' ρ
  G = HOLE
  {- this proof is bad so far... just need to recur on FV and use f directly as the f'
    with base case using ⦅ f ∣ fv' ∷ fV' ⦆ -}
-}


delay-reflect' : ∀ M ρ d → d ∈ ⟦ delay M ⟧' ρ → fro d ∈ ⟦ M ⟧ (env-map fro ρ)
del-map-args-reflect' : ∀ {n} args ρ → results-rel-pres' _fro-⊆_ (replicate n ■) (⟦ del-map-args {n} args ⟧₊' ρ) (⟦ args ⟧₊ (env-map fro ρ))
delay-reflect'-⊆ : ∀ M ρ V → mem V ⊆ ⟦ delay M ⟧' ρ → mem (fros V) ⊆ ⟦ M ⟧ (env-map fro ρ)

delay-reflect' (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ d d∈ = {!   !}

{-
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ ( ⦅ ν , fv' ⦆) ⟨ FV⊆ , ⟨ f∈ , fv'∈ ⟩ ⟩ 
  = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv ∷ FV ⊢⦅ fv' ∷ FV' ↦ ν , fv'' ⦆) ⟨ FV⊆ , ⟨ f∈ , fv''∈ ⟩ ⟩
  = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
   (fv ∷ FV ⊢⦅ fv' ∷ FV' ↦ (v ∷ V ↦ w) , fv'' ⦆) ⟨ FV⊆ , ⟨ w∈ , fv''∈ ⟩ ⟩
   with (fv' ∷ FV') D4.mem⊆? FV
... | no FV'⊈ = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
   (fv ∷ FV ⊢⦅ fv' ∷ FV' ↦ (v ∷ V ↦ w) , fv'' ⦆) ⟨ FV⊆ , ⟨ w∈ , fv''∈ ⟩ ⟩ | yes FV'⊆ = 
   ⟨ G3 (fro fv') (fro-∈-mem (FV'⊆ fv' (here refl))) , ⟨ (λ d' d'∈ → G3 d' (fro-⊆-mem FV'⊆ d' (there d'∈))) , G1 ⟩ ⟩
  where
  H : env-map fro (mem (v ∷ V) • mem (fv' ∷ FV') • λ x → L4.init)
      ⊆ₑ mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → L3.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → L3.init))
  G1 = L3.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect' N (mem (v ∷ V) • mem (fv' ∷ FV') • (λ _ x → x ≡ ω)) w 
                     w∈)
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros FV) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
-}
delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ d 
   ⟨ v , ⟨ V , ⟨ inner-app , V⊆N' ⟩ ⟩ ⟩ with inner-app
... | ⟨ v' , ⟨ V' , ⟨ q , V'⊆sndM' ⟩ ⟩ ⟩    = {!  q !}

{-
   with delay-reflect' M ρ (fv' ∷ FV' ⊢⦅ fv ∷ FV ↦ (v ∷ V ↦ d) , fv'' ⦆) ⦅FV↦V↦d∣FV'⦆∈M
... | IHM with FV D4.mem⊆? (fv' ∷ FV')
... | yes FV⊆ =
   ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ IHM , delay-reflect'-⊆ N ρ (v ∷ V) V⊆N' ⟩ ⟩ ⟩ ⟩ ⟩
... | no ¬FV⊆ = HOLE
-}
{- should be a contradiction -}
   {- the codomain isn't a subset of the annotation -}
   {- not a contradiction, but we know that this can't ALWAYS be true -}  

   
   
     {-
  ⟨ fro v , ⟨ fros V , ⟨ G1+IH , G2 ⟩ ⟩ ⟩
  where
  G1 : (fv ∷ FV ⊢⦅ ( fv ∷ FV ↦ (v ∷ V ↦ d)) , fv ⦆) ∈ ⟦ delay M ⟧' ρ
  G1 = {! FV⊆sndM' !}
  G1+IH : (fro v ∷ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  G1+IH with delay-reflect' M ρ (fv ∷ FV ⊢⦅ ( fv ∷ FV ↦ ( v ∷ V ↦ d)) , fv ⦆) G1 
  ... | ihres with FV D4.mem⊆? FV
  ... | no neq = ⊥-elim (neq λ z z∈ → z∈)
  ... | yes eq = ihres
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N'
  -}

{-



-}


{-
    with FV mem⊆? (fv' ∷ FV') | delay-reflect' M ρ ⦅ ( fv ∷ FV ↦ ( v ∷ V ↦ d) ∣ fv' ∷ fV' ⦆ U∈M'
... | no FV⊈ |  q = ⊥-elim (FV⊈ G)
   {- ⟨ fro v , ⟨ fros V , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ -}
  where
  G : mem FV ⊆ (mem (fv' ∷ FV'))
  G d' d'∈ with FV⊆sndM' d' d'∈ 
  ... | ⟨ q , ⟨ p , ⟨ P , ⟨ qP∈M , d'∈P ⟩ ⟩ ⟩ ⟩ = HOLE
  {-
  G1 : {!   !}
  G1 = {! delay-reflect' M   !}
  -}
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N'
... | yes FV⊆ | q
  =  ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ HOLE , G2 ⟩ ⟩ ⟩ ⟩ ⟩ 
  where
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N' {- delay-reflect' M ρ ⦅ (fv' ∷ fV' ⊢ fv ∷ FV ↦ (fvouter , FVouter ⊢ V ↦ d)) , U₂ ⦆ U∈M' -}
-}

{- need two things:
need to split U₂ up 
and need to split on whether fv ∷ FV is a subset of U₂ or not.

fro ⦅ _ , _ ⊢ FV ↦ (_ , _ ⊢ V ↦ w) , (fv' ∷ FV') ⦆ 
   with FV mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv , fros FV ⊢ fros V ↦ fro w
... | no FV⊈FV' = fro fv' , fros FV' ⊢ν


-}

delay-reflect' (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ = {! d∈   !}
delay-reflect' (tuple n ⦅ args ⦆) ρ d d∈ = G n args ρ d d∈
  where
  G : ∀ n args ρ d → d ∈ ⟦ delay (tuple n ⦅ args ⦆) ⟧' ρ → fro d ∈ ⟦ tuple n ⦅ args ⦆ ⟧ (env-map fro ρ) 
  G zero args ρ d refl = refl
  G (suc n) (arg ,, args) ρ ∥ d ∷ ds ∥ ⟨ d∈ , ds∈ ⟩ with G n args ρ ∥ ds ∥ ds∈
  ... | ds'∈ = ⟨ delay-reflect' arg ρ d d∈ , ds'∈ ⟩
delay-reflect' (get i ⦅ M ,, Nil ⦆) ρ d ⟨ ds , ⟨ i≤ , ⟨ ds∈ , refl ⟩ ⟩ ⟩ = 
  ⟨ fros ds , ⟨ subst (Data.Nat._<_ i) (sym (fros-length ds)) i≤ 
  , ⟨ delay-reflect' M ρ ∥ ds ∥ ds∈ , fros-nth ds i ⟩ ⟩ ⟩
delay-reflect' (inl-op ⦅ M ,, Nil ⦆) ρ (left v) v∈ = 
  delay-reflect' M ρ v v∈
delay-reflect' (inr-op ⦅ M ,, Nil ⦆) ρ (right v) v∈ = 
  delay-reflect' M ρ v v∈
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = {!   !}
   {-
   inj₁ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (left v) LV∈ 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
                               -}
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = {!   !}
   {-
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (right v) RV∈ 
        , L3.⟦⟧-monotone {{Clos3-Semantics}} N  
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩ -}
delay-reflect'-⊆ M ρ [] V⊆ = λ d ()
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-reflect' M ρ d (V⊆ d (here refl))
delay-reflect'-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈frosV) = 
  delay-reflect'-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈frosV
del-map-args-reflect' {zero} args ρ = lift tt
del-map-args-reflect' {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-reflect' M ρ) , del-map-args-reflect' args ρ ⟩


-}

-}

-}
-}

-}