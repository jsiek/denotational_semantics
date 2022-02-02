open import NewSigUtil
open import NewSyntaxUtil
open import SetsAsPredicates
open import NewDOpSig
open import NewDenotProperties
open import NewDomainSingleAnnLam as D3
open import NewDomainSingleAnnPair as D4
  renaming (Value to Value')
open import NewDOpSingleAnnLam as Op3
open import NewDOpSingleAnnPair as Op4
open import NewClos3Single
open import NewClos4Single
  renaming (AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
            _⦅_⦆ to _⦅_⦆'; ⟦_⟧ to ⟦_⟧'; ⟦_⟧ₐ to ⟦_⟧ₐ'; ⟦_⟧₊ to ⟦_⟧₊';
            ast to ast'; bind to bind'; clear to clear')
open import NewCompilerSingle using (delay; del-map-args)
open import NewEnv
open import Primitives
import Fold2



open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate; length; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Data.Unit.Polymorphic using () renaming (tt to ptt; ⊤ to pTrue)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst; cong; trans)
open import Level using (Level; Lift; lift; lower)
    renaming (zero to lzero; suc to lsuc; _⊔_ to _l⊔_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.Core using (Rel)


tos : List Value → List Value'
to : Value → Value'
to (const x) = const x
to (fv ∷ FV ⊢ v ∷ V ↦ w) = (to fv ∷ tos FV ⊢⦅ (to fv ∷ tos FV ↦ (to v ∷ tos V ↦ to w)) , to fv ⦆)
to (fv ∷ FV ⊢ν) = (to fv ∷ tos FV ⊢⦅ (to fv ∷ tos FV ↦ ν) , to fv ⦆)
to ω = ω
to ∥ xs ∥ = ∥ tos xs ∥
to (left v) = left (to v)
to (right v) = right (to v)
tos List.[] = []
tos (d List.∷ ds) = to d List.∷ tos ds

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

{-
pair-denot-inv : ∀ M ρ {fv FV u v} 
             → (∀ i {fv' FV' u' v'} → (fv' ∷ FV' ⊢⦅ u' , v' ⦆) ∈ ρ i 
                 → Σ[ M' ∈ AST' ] Σ[ ρ' ∈ Env Value' ] mem (fv ∷ FV) ⊆ Op4.cdr ⟨ ⟦ M' ⟧' ρ' , ptt ⟩)
             → (fv ∷ FV ⊢⦅ u , v ⦆) ∈ ⟦ delay M ⟧' ρ 
             → Σ[ M' ∈ AST' ] Σ[ ρ' ∈ Env Value' ] mem (fv ∷ FV) ⊆ Op4.cdr ⟨ ⟦ M' ⟧' ρ' , ptt ⟩
pair-denot-inv (` x) ρ Hρ uv∈ = Hρ x uv∈
pair-denot-inv (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆)
  ρ {fv} {FV} Hρ ⟨ FV⊆ , ⟨ u∈ , v∈ ⟩ ⟩ = 
  ⟨  delay (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆)
  , ⟨ ρ , (λ d d∈ → G d (FV⊆ d d∈)) ⟩ ⟩
   where
   G : Op4.𝒯 n ( ⟦ del-map-args fvs ⟧₊' ρ) ⊆ Op4.cdr ⟨ ⟦ delay (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ⟧' ρ , ptt ⟩
   G d d∈ = ⟨ fv , ⟨ FV , ⟨ ν , ⟨ FV⊆ , ⟨ tt , d∈ ⟩ ⟩ ⟩ ⟩ ⟩ 
pair-denot-inv (app ⦅ M ,, N ,, Nil ⦆) ρ Hρ uv∈ = HOLE
pair-denot-inv (lit B k ⦅ Nil ⦆) ρ Hρ ()
pair-denot-inv (tuple zero ⦅ Nil ⦆) ρ Hρ ()
pair-denot-inv (tuple (suc n) ⦅ M ,, Ms ⦆) ρ Hρ ()
pair-denot-inv (get i ⦅ M ,, Nil ⦆) ρ Hρ uv∈ = HOLE
pair-denot-inv (inl-op ⦅ M ,, Nil ⦆) ρ Hρ ()
pair-denot-inv (inr-op ⦅ M ,, Nil ⦆) ρ Hρ ()
pair-denot-inv (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ Hρ (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , p∈ ⟩ ⟩ ⟩) 
  with pair-denot-inv M (mem (v ∷ V) • ρ) HOLE p∈
... | ⟨ M' , ⟨ ρ' , IH ⟩ ⟩ = ⟨ M' , ⟨ ρ' , IH ⟩  ⟩
pair-denot-inv (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ Hρ (inj₂ y) = HOLE

pair-annot : ∀ M' ρ {fv FV u v} 
             → (∀ i {fv' FV' u' v'} → (fv' ∷ FV' ⊢⦅ u' , v' ⦆) ∈ ρ i 
                 → mem (fv' ∷ FV') ⊆ Op4.cdr ⟨ ρ i , ptt ⟩)
             → (fv ∷ FV ⊢⦅ u , v ⦆) ∈ ⟦ M' ⟧' ρ 
           → mem (fv ∷ FV) ⊆ Op4.cdr ⟨ ⟦ M' ⟧' ρ , ptt ⟩
pair-annot (# x) ρ Hρ uv∈ = Hρ x uv∈
pair-annot (fun-op ⦅ ! (clear' (bind' (bind' (ast' N)))) ,, Nil ⦆') ρ Hρ ()
pair-annot (app ⦅ F ,, M ,, N ,, Nil ⦆') ρ Hρ ⟨ v , ⟨ V , ⟨ inner-app , V⊆ ⟩ ⟩ ⟩ d d∈ with inner-app 
... | ⟨ v' , ⟨ V' , ⟨ V'↦V↦uv , V'⊆ ⟩ ⟩ ⟩ = 
      ⟨ HOLE , ⟨ HOLE , ⟨ HOLE , ⟨ v , ⟨ V , ⟨ ⟨ v' , ⟨ V' , ⟨ HOLE , V'⊆ ⟩ ⟩ ⟩ , V⊆ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pair-annot (lit B k ⦅ Nil ⦆') ρ Hρ ()
pair-annot (tuple zero ⦅ Nil ⦆') ρ Hρ ()
pair-annot (tuple (suc n) ⦅ M ,, Ms ⦆') ρ Hρ ()
pair-annot (get i ⦅ M ,, Nil ⦆') ρ Hρ uv∈ = HOLE
pair-annot (inl-op ⦅ M ,, Nil ⦆') ρ Hρ ()
pair-annot (inr-op ⦅ M ,, Nil ⦆') ρ Hρ ()
pair-annot (pair-op ⦅ M ,, N ,, Nil ⦆') ρ Hρ uv∈ = HOLE
pair-annot (fst-op ⦅ M ,, Nil ⦆') ρ Hρ uv∈ = HOLE
pair-annot (snd-op ⦅ M ,, Nil ⦆') ρ Hρ uv∈ = HOLE
pair-annot (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆') ρ Hρ (inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , p∈ ⟩ ⟩ ⟩)
  d d∈FV with pair-annot M (mem (v ∷ V) • ρ) HOLE p∈ 
... | FV⊆  with FV⊆ d d∈FV 
... | ⟨ fv' , ⟨ FV' , ⟨ u , ud∈M' ⟩ ⟩ ⟩ = ⟨ fv' , ⟨ FV' , ⟨ u , inj₁ ⟨ v , ⟨ V , ⟨ V⊆ , ud∈M' ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pair-annot (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆') ρ Hρ (inj₂ y) = HOLE
-}

delay-preserve : ∀ M ρ d → d ∈ ⟦ M ⟧ ρ → to d ∈ ⟦ delay M ⟧' (env-map to ρ)
del-map-args-preserve : ∀ {n} args ρ → results-rel-pres' _to-⊆_ (replicate n ■) (⟦ args ⟧₊ ρ) (⟦ del-map-args {n} args ⟧₊' (env-map to ρ))
delay-preserve-⊆ : ∀ M ρ V → mem V ⊆ ⟦ M ⟧ ρ → mem (tos V) ⊆ ⟦ delay M ⟧' (env-map to ρ)

delay-preserve (` x) ρ d d∈ = ⟨ d , ⟨ d∈ , refl ⟩ ⟩
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv ∷ FV ⊢ν) ⟨ fv∈𝒯fvs , FV⊆𝒯fvs ⟩ = 
  ⟨ G3 , ⟨ tt , G3 (to fv) (here refl) ⟩ ⟩
  where
  G1 : (to fv ∷ tos FV ↦ ν) ∈ Op4.Λ ⟨ (λ X → Op4.Λ ⟨ (λ Y → ⟦ delay N ⟧' (Y • X • (λ _ x → x ≡ ω))) , ptt ⟩) , ptt ⟩
  G1 = tt
  G2 : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (tos (fv ∷ FV)) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ here refl , refl ⟩ ⟩ = G2 n fvs a fv∈𝒯fvs
  ... | ⟨ a , ⟨ there a∈ , refl ⟩ ⟩ = G2 n fvs a (FV⊆𝒯fvs a a∈)
delay-preserve (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv ∷ FV ⊢ v ∷ V ↦ w) ⟨ fv∈𝒯 , ⟨ FV⊆𝒯 , w∈N ⟩ ⟩
  = ⟨ G3 , ⟨ G1 , G3 (to fv) (here refl) ⟩ ⟩
  where
  H : env-map to (mem (v ∷ V) • mem (fv ∷ FV) • (λ x → NewClos3Single.init))
         ⊆ₑ mem (tos (v ∷ V)) • mem (tos (fv ∷ FV)) • (λ x → NewClos4Single.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = to-∈-mem a∈
  H (suc (suc x)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : (to fv ∷ tos FV ↦ (to v ∷ tos V ↦ to w)) 
     ∈ Op4.Λ ⟨ (λ X → Op4.Λ ⟨ ⟦ clear' (bind' (bind' (ast' (delay N)))) ⟧ₐ' (env-map to ρ) X 
          , ptt ⟩) , ptt ⟩
  G1 = NewClos4Single.⟦⟧-monotone {{Clos4-Semantics}} (delay N) H (to w) 
                (delay-preserve N (mem (v ∷ V) • mem (fv ∷ FV) • (λ _ x → x ≡ ω)) w w∈N)
  G2 : ∀ n fvs d → d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ ρ) → to d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-preserve fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (tos (fv ∷ FV)) ⊆ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' (env-map to ρ))
  G3 d d∈ with ∈-mem-tos d∈
  ... | ⟨ a , ⟨ here refl , refl ⟩ ⟩ = G2 n fvs a fv∈𝒯
  ... | ⟨ a , ⟨ there a∈ , refl ⟩ ⟩ = G2 n fvs a (FV⊆𝒯 a a∈)
delay-preserve (app ⦅ M ,, N ,, Nil ⦆) ρ d ⟨ v , ⟨ V , ⟨ fv , ⟨ FV , ⟨ FV⊢V↦d∈M , V⊆N ⟩ ⟩ ⟩ ⟩ ⟩ 
  with delay-preserve M ρ (fv ∷ FV ⊢ v ∷ V ↦ d) FV⊢V↦d∈M | delay-preserve-⊆ N ρ (v ∷ V) V⊆N
... | clos∈M' | V'⊆N' = ⟨ to v , ⟨ tos V , ⟨ ⟨ to fv , ⟨ tos FV , ⟨ ⟨ to fv , ⟨ tos FV , ⟨ to fv , clos∈M' ⟩ ⟩ ⟩ , second ⟩ ⟩ ⟩ , V'⊆N' ⟩ ⟩ ⟩
   {- ⟨ to v , ⟨ tos V , ⟨ ⟨ to fv , ⟨ tos FV , 
     ⟨ ⟨ to fv , ⟨ tos FV , clos∈M' ⟩ ⟩ , second ⟩ ⟩ ⟩ , V'⊆N' ⟩ ⟩ ⟩ -}
   where
   second : ∀ d' → d' ∈ mem (to fv ∷ tos FV) → d' ∈ cdr ⟨ ⟦ delay M ⟧' (env-map to ρ) , ptt ⟩
   second d' d'∈tosFV = ⟨ to fv , ⟨ tos FV , ⟨ to fv ∷ tos FV ↦ (to v ∷ tos V ↦ to d) , {! clos∈M'  !} ⟩ ⟩ ⟩ 
{- this whole requirement is only to satisfy info about annotations, which could be removed from this pass, in theory -}
{- it also might be possible to just prove, I just need to spend a little time with it. -}
   {- ⟨ to fv ∷ tos FV ↦ (to v ∷ tos V ↦ to d) , ⟨ tos (fv ∷ FV) , ⟨ clos∈M' , d'∈tosFV ⟩ ⟩ ⟩ -}
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
  (inj₁ ⟨ v , ⟨ V , ⟨ LV∈ , d∈ ⟩ ⟩ ⟩) = inj₁ ⟨ to v , ⟨ tos V , ⟨ G , {! delay-preserve M ? d d∈   !} ⟩ ⟩ ⟩
{- All the holes in the case-op cases can be filled with some appeals to 
   monotonicity with respect to environments and some properties of List.Map -}
  where
  H : mem (Data.List.map left (v ∷ V)) ⊆ ⟦ L ⟧ ρ
  H d' d'∈ = {!   !}
  G : ∀ d' → d' ∈ mem (tos (v ∷ V)) → left d' ∈ ⟦ delay L ⟧' (env-map to ρ)
  G d' d'∈ = delay-preserve-⊆ L ρ (Data.List.map left (v ∷ V)) H (left d') {!   !}
   {- inj₁ ⟨ to v , ⟨ tos V , ⟨ delay-preserve L ρ (left v) LV∈ 
        , NewClos4Single.⟦⟧-monotone {{Clos4-Semantics}} (delay M) 
                               (to-mem-rewrite (v ∷ V) ρ) (to d) 
                               (delay-preserve M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩ -}
delay-preserve (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = inj₂ ⟨ to v , ⟨ tos V , ⟨ {!   !} , {!   !} ⟩ ⟩ ⟩
   {- inj₂ ⟨ to v , ⟨ tos V , ⟨ delay-preserve L ρ (right v) RV∈ 
        , NewClos4Single.⟦⟧-monotone {{Clos4-Semantics}} (delay N) 
                               (to-mem-rewrite (v ∷ V) ρ) (to d) 
                               (delay-preserve N (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩ -}
delay-preserve-⊆ M ρ [] V⊆ = λ d ()
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (here refl) = 
  delay-preserve M ρ d (V⊆ d (here refl))
delay-preserve-⊆ M ρ (d ∷ V) V⊆ d' (there d'∈tosV) = 
  delay-preserve-⊆ M ρ V (λ x x∈ → V⊆ x (there x∈)) d' d'∈tosV
del-map-args-preserve {zero} args ρ = lift tt
del-map-args-preserve {suc n} (M ,, args) ρ = 
  ⟨ lift (delay-preserve M ρ) , del-map-args-preserve args ρ ⟩





{-
need to check for equality of fv' with fv
and FV' with FV

-}

fros : List Value' → List Value
fro : Value' → Value
fro (const x) = const x
fro (v ∷ V ↦ w) = ω
fro ν = ω
fro ω = ω
fro (fv ∷ FV ⊢⦅ ν , fv' ⦆) = fro fv ∷ fros FV ⊢ν
fro (fv ∷ FV ⊢⦅ v ∷ V ↦ ν , fv' ⦆) = fro fv ∷ fros FV ⊢ν
fro (fv' ∷ FV' ⊢⦅ fv ∷ FV ↦ ( v ∷ V ↦ w) , fv'' ⦆)
   with (fv ∷ FV) D4.mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv ∷ fros FV ⊢ fro v ∷ fros V ↦ fro w
... | no FV⊈FV' = fro fv' ∷ fros FV' ⊢ν
fro (fv ∷ FV ⊢⦅ u , v ⦆) = ω
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
                      → mem (fv ∷ FV) ⊆ cdr ⟨ ⟦ delay M ⟧' ρ , ptt ⟩ 
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
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv ∷ FV ⊢⦅ ν , fv' ⦆) ⟨ FV⊆ , ⟨ f∈ , fv'∈ ⟩ ⟩ 
  = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv ∷ FV)) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ (fv ∷ FV ⊢⦅ fv' ∷ FV' ↦ ν , fv'' ⦆) ⟨ FV⊆ , ⟨ f∈ , fv''∈ ⟩ ⟩
  = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv ∷ FV)) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
   (fv ∷ FV ⊢⦅ fv' ∷ FV' ↦ (v ∷ V ↦ w) , fv'' ⦆) ⟨ FV⊆ , ⟨ w∈ , fv''∈ ⟩ ⟩
   with (fv' ∷ FV') D4.mem⊆? (fv ∷ FV)
... | no FV'⊈ = ⟨ G2 n fvs fv (FV⊆ fv (here refl)) , (λ d' d'∈ → G3 d' (there d'∈)) ⟩
  where
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv ∷ FV)) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))
delay-reflect' (clos-op n ⦅ ! clear (bind (bind (ast N))) ,, fvs ⦆) ρ 
   (fv ∷ FV ⊢⦅ fv' ∷ FV' ↦ (v ∷ V ↦ w) , fv'' ⦆) ⟨ FV⊆ , ⟨ w∈ , fv''∈ ⟩ ⟩ | yes FV'⊆ = 
   ⟨ G3 (fro fv') (fro-∈-mem (FV'⊆ fv' (here refl))) , ⟨ (λ d' d'∈ → G3 d' (fro-⊆-mem FV'⊆ d' (there d'∈))) , G1 ⟩ ⟩
  where
  H : env-map fro (mem (v ∷ V) • mem (fv' ∷ FV') • λ x → NewClos4Single.init)
      ⊆ₑ mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → NewClos3Single.init)
  H zero d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc zero) d ⟨ a , ⟨ a∈ , refl ⟩ ⟩ = fro-∈-mem a∈
  H (suc (suc n)) d ⟨ a , ⟨ refl , refl ⟩ ⟩ = refl
  G1 : fro w ∈ ⟦ N ⟧ (mem (fros (v ∷ V)) • mem (fros (fv' ∷ FV')) • (λ x → NewClos3Single.init))
  G1 = NewClos3Single.⟦⟧-monotone {{Clos3-Semantics}} N H (fro w) 
          (delay-reflect' N (mem (v ∷ V) • mem (fv' ∷ FV') • (λ _ x → x ≡ ω)) w 
                     w∈)
  G2 : ∀ n fvs d → d ∈ Op4.𝒯 n (⟦ del-map-args fvs ⟧₊' ρ) → fro d ∈ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G2 zero fvs d refl = refl
  G2 (suc n) (fv ,, fvs) (∥ d ∷ ds ∥) ⟨ d∈ , ds∈ ⟩ = ⟨ delay-reflect' fv ρ d d∈ , G2 n fvs ∥ ds ∥ ds∈ ⟩
  G3 : mem (fros (fv ∷ FV)) ⊆ Op3.𝒯 n (⟦ fvs ⟧₊ (env-map fro ρ))
  G3 a (here refl) = G2 n fvs fv (FV⊆ fv (here refl))
  G3 a (there a∈) with ∈-mem-fros a∈
  ... | ⟨ b , ⟨ b∈ , refl ⟩ ⟩ = G2 n fvs b (FV⊆ b (there b∈))


delay-reflect' (app ⦅ M ,, N ,, Nil ⦆) ρ d 
   ⟨ v , ⟨ V , ⟨ inner-app , V⊆N' ⟩ ⟩ ⟩ with inner-app
... | ⟨ fv , ⟨ FV , ⟨ ⟨ fv' , ⟨ FV' , ⟨ fv'' , ⦅FV↦V↦d∣FV'⦆∈M ⟩ ⟩ ⟩ , FV⊆sndM' ⟩ ⟩ ⟩
   with delay-reflect' M {!   !} (fv' ∷ FV' ⊢⦅ fv ∷ FV ↦ (v ∷ V ↦ d) , fv'' ⦆) ⦅FV↦V↦d∣FV'⦆∈M | (fv ∷ FV) D4.mem⊆? (fv' ∷ FV')
... | IHM | no ¬FV⊆ = {! FV⊆sndM'   !}
... | IHM | yes FV⊆ =
   ⟨ fro v , ⟨ fros V , ⟨ fro fv , ⟨ fros FV , ⟨ {!  !} , {!   !} ⟩ ⟩ ⟩ ⟩ ⟩
   {-
  ⟨ fro v , ⟨ fros V , ⟨ G1+IH , G2 ⟩ ⟩ ⟩
  where
  G1 : (fv ∷ FV ⊢⦅ ( fv ∷ FV ↦ (v ∷ V ↦ d)) , fv ⦆) ∈ ⟦ delay M ⟧' ρ
  G1 = {! FV⊆sndM' !}
  G1+IH : (fro v ∷ fros V ↦ fro d) ∈ ⟦ M ⟧ (env-map fro ρ)
  G1+IH with delay-reflect' M ρ (fv ∷ FV ⊢⦅ ( fv ∷ FV ↦ ( v ∷ V ↦ d)) , fv ⦆) G1 
  ... | ihres with (fv ∷ FV) D4.mem⊆? (fv ∷ FV)
  ... | no neq = ⊥-elim (neq λ z z∈ → z∈)
  ... | yes eq = ihres
  G2 : mem (fros (v ∷ V)) ⊆ ⟦ N ⟧ (env-map fro ρ)
  G2 = delay-reflect'-⊆ N ρ (v ∷ V) V⊆N'
  -}

{-



-}


{-
    with (fv ∷ FV) mem⊆? (fv' ∷ FV') | delay-reflect' M ρ ⦅ ( fv ∷ FV ↦ ( v ∷ V ↦ d) ∣ fv' ∷ fV' ⦆ U∈M'
... | no FV⊈ |  q = ⊥-elim (FV⊈ G)
   {- ⟨ fro v , ⟨ fros V , ⟨ {!   !} , ⟨ {!   !} , ⟨ {!   !} , G2 ⟩ ⟩ ⟩ ⟩ -}
  where
  G : mem (fv ∷ FV) ⊆ (mem (fv' ∷ FV'))
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

fro ⦅ _ , _ ⊢ (fv ∷ FV) ↦ (_ , _ ⊢ V ↦ w) , (fv' ∷ FV') ⦆ 
   with (fv ∷ FV) mem⊆? (fv' ∷ FV')
... | yes FV⊆FV' = fro fv , fros FV ⊢ fros V ↦ fro w
... | no FV⊈FV' = fro fv' , fros FV' ⊢ν


-}

delay-reflect' (lit B k ⦅ Nil ⦆) ρ (const {B'} k') d∈ = {!   !}
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
        , NewClos3Single.⟦⟧-monotone {{Clos3-Semantics}} M 
                               (fro-mem-rewrite (v ∷ V) ρ) (fro d) 
                               (delay-reflect' M (mem (v ∷ V) • ρ) d d∈) ⟩ ⟩ ⟩
                               -}
delay-reflect' (case-op ⦅ L ,, (⟩ M ,, (⟩ N ,, Nil)) ⦆) ρ d 
  (inj₂ ⟨ v , ⟨ V , ⟨ RV∈ , d∈ ⟩ ⟩ ⟩) = {!   !}
   {-
   inj₂ ⟨ fro v , ⟨ fros V , ⟨ delay-reflect' L ρ (right v) RV∈ 
        , NewClos3Single.⟦⟧-monotone {{Clos3-Semantics}} N  
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

