{-

  Forward (preserve) direction of the correctness of typed delay
  (Clos3ᵀ → Clos4ᵀ) in the graph model with errors, by the logical
  relation of proof/Correctness/GraphErr/DelayPreserve.agda between
  single source values and target sets (v ⊑ D'), by recursion on the
  value: a source function is exhibited by a target closure (a pair of
  values, whose environment gives the length for unpack) whose
  applications (⊙, the call of unpack) are related to its own.

  The relation lifts through the monad (≫=-lift, binds-lift), so each
  construct is its kernel. The types remove the checks but that of
  project (⊑-proj); a value of type ⟪ fun ⟫ is a function (fun-val), so
  an application whose argument errs has a closure to unpack.

-}

open import proof.Framework.GraphModel.SetsAsPredicates
open import Framework.Primitives
open import proof.Framework.GraphModel.Domain
open import proof.Framework.GraphModel.OpsBase
open import proof.Framework.GraphModel.DOpSig
open import proof.Framework.GraphModel.Ops using (⋆; Λ; 𝒯; proj; inl; inr; 𝒞; pair; car; cdr; 𝒞-left; 𝒞-right; ⋆₂-mono)
open import proof.Framework.GraphModel.DomainUtilBase
open import proof.Framework.GraphModel.ErrorMonad
open import proof.Framework.GraphModel.Env using (Env; nonempty-env; extend-nonempty-env)
open import proof.Semantics.GraphErr.Prim using (primD; out)
open import Semantics.GraphErr.Typed.Ops using (kindᶠ; checkedᵠ)
open import Language.Typed.Type using (Any; ⟪_⟫; tup; fun; _∋_; Z; S; idx)
open import Language.Typed.Clos3 as L3 using (Tm; `_; clos; app; lit; tuple; get; case; prim; let′; inject; project)
import Language.Typed.Clos4 as T
import proof.Semantics.GraphErr.Typed.Clos3 as S3
open S3 using (⟦_⟧; ⟦_⟧s)
import proof.Semantics.GraphErr.Typed.Clos4 as S4
open S4 using (fin₁; fin₂; ΛΛᵐ-call; kind₄) renaming (⟦_⟧ to ⟦_⟧'; ⟦_⟧s to ⟦_⟧s')
open import Compiler.Typed.Delay using (Ren; ext; delay; delays; delay-program)
open import proof.Correctness.Typed.GraphErr.DelayRel using (_●_; out-data)

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec using (Vec; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (tt; ⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using () renaming (⊤ to pTrue; tt to ptt)
open import Level using (Lift; lift; lower) renaming (suc to lsuc; zero to lzero)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Language.Prim using (δ; sub; eq)

module proof.Correctness.Typed.GraphErr.DelayPreserve where

{- The relation -----------------------------------------------------------------}

{- the call of the closures P on E': unpack's body -}
⋆⋆ : 𝒫 Value → 𝒫 Value → 𝒫 Value → 𝒫 Value
⋆⋆ C Y X = ⋆ ⟨ ⋆ ⟨ C , ⟨ Y , ptt ⟩ ⟩ , ⟨ X , ptt ⟩ ⟩

⋆⋆-mono : ∀ {C C' Y Y' X X'} → C ⊆ C' → Y ⊆ Y' → X ⊆ X' → ⋆⋆ C Y X ⊆ ⋆⋆ C' Y' X'
⋆⋆-mono {C} {C'} {Y} {Y'} {X} {X'} C⊆ Y⊆ X⊆ =
  lower (⋆₂-mono ⟨ C , ⟨ Y , ⟨ X , ptt ⟩ ⟩ ⟩ ⟨ C' , ⟨ Y' , ⟨ X' , ptt ⟩ ⟩ ⟩ ⟨ lift C⊆ , ⟨ lift Y⊆ , ⟨ lift X⊆ , ptt ⟩ ⟩ ⟩)

_⊙_ : 𝒫 Value → 𝒫 Value → 𝒫 Value
P ⊙ E' = car ⟨ P , ptt ⟩ ≫= λ C → cdr ⟨ P , ptt ⟩ ≫= λ Y → E' ≫= λ X → ⋆⋆ C Y X

⊙-mono : ∀ {D₁ D₂ E} → (∀ u v → ⦅ u , v ⦆ ∈ D₁ → ⦅ u , v ⦆ ∈ D₂) → (D₁ ⊙ E) ⊆ (D₂ ⊙ E)
⊙-mono {D₁} {D₂} {E} s =
  ≫=-mono {F = λ C → cdr ⟨ D₁ , ptt ⟩ ≫= λ Y → E ≫= ⋆⋆ C Y} {F' = λ C → cdr ⟨ D₂ , ptt ⟩ ≫= λ Y → E ≫= ⋆⋆ C Y}
    (λ { u ⟨ v , p ⟩ → ⟨ v , s u v p ⟩ }) λ {C} {C'} C⊆ →
  ≫=-mono {F = λ Y → E ≫= ⋆⋆ C Y} {F' = λ Y → E ≫= ⋆⋆ C' Y} (λ { v ⟨ u , p ⟩ → ⟨ u , s u v p ⟩ }) λ {Y} {Y'} Y⊆ →
  ≫=-mono {F = ⋆⋆ C Y} {F' = ⋆⋆ C' Y'} (λ d z → z) λ X⊆ → ⋆⋆-mono C⊆ Y⊆ X⊆

{- a closure: a pair of values, whose environment has a length -}
PairV : 𝒫 Value → Set
PairV D' = Σ[ u ∈ Value ] Σ[ t ∈ Value ] Σ[ n ∈ ℕ ] ⦅ u , t ⦆ ∈ D' × u ≢ ω × kind t ≡ tup n

infix 4 _⊑_ _⊑*_
_⊑_ : Value → 𝒫 Value → Set₁
_⊑*_ : List Value → 𝒫 Value → Set₁
ν ⊑ D' = Lift (lsuc lzero) (PairV D')
(U ↦ w) ⊑ D' = Lift (lsuc lzero) (PairV D') × (∀ E' → Con E' → U ⊑* E' → w ⊑ D' ⊙ E')
(tup[ i ] d) ⊑ D' = d ⊑ Nth i D'
left d ⊑ D' = d ⊑ Lefts D'
right d ⊑ D' = d ⊑ Rights D'
⦅ u , v ⦆ ⊑ D' = Lift (lsuc lzero) ⊥
v ⊑ D' = Lift (lsuc lzero) (v ∈ D')
[] ⊑* E' = pTrue
(u ∷ U) ⊑* E' = u ⊑ E' × U ⊑* E'

PairV-mono : ∀ {D₁ D₂} → (∀ u v → ⦅ u , v ⦆ ∈ D₁ → ⦅ u , v ⦆ ∈ D₂) → PairV D₁ → PairV D₂
PairV-mono s ⟨ u , ⟨ t , ⟨ n , ⟨ p∈ , r ⟩ ⟩ ⟩ ⟩ = ⟨ u , ⟨ t , ⟨ n , ⟨ s u t p∈ , r ⟩ ⟩ ⟩ ⟩

⊑-mono : ∀ v {D₁ D₂} → D₁ ⊆ D₂ → v ⊑ D₁ → v ⊑ D₂
⊑-mono ν {D₁} {D₂} D⊆ (lift p) = lift (PairV-mono {D₁} {D₂} (λ u v → D⊆ _) p)
⊑-mono (U ↦ w) {D₁} {D₂} D⊆ ⟨ lift p , f ⟩ =
  ⟨ lift (PairV-mono {D₁} {D₂} (λ u v → D⊆ _) p) , (λ E' cE U⊑ → ⊑-mono w (⊙-mono {D₁} {D₂} (λ u v → D⊆ _)) (f E' cE U⊑)) ⟩
⊑-mono (tup[ i ] d) D⊆ = ⊑-mono d (λ d → D⊆ (tup[ i ] d))
⊑-mono (left d) D⊆ = ⊑-mono d (λ d → D⊆ (left d))
⊑-mono (right d) D⊆ = ⊑-mono d (λ d → D⊆ (right d))
⊑-mono (const k) D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ω D⊆ (lift v∈) = lift (D⊆ _ v∈)
⊑-mono ⦅ u , v ⦆ D⊆ (lift ())
⊑-mono ⟨⟩ D⊆ (lift v∈) = lift (D⊆ _ v∈)

{- a source value other than ω is exhibited by a target value of its kind -}
⊑-wit : ∀ v {D'} → v ⊑ D' → v ≢ ω → Σ[ d' ∈ Value ] d' ∈ ⌊ D' ⌋ × kind₄ (kind d') ≡ kind v
⊑-ne : ∀ v {D'} → v ⊑ D' → nonempty D'
⊑-ne v {D'} v⊑ with ω? v
... | inj₁ refl = ⟨ ω , lower v⊑ ⟩
... | inj₂ v≢ = let ⟨ d' , ⟨ d'∈ , _ ⟩ ⟩ = ⊑-wit v v⊑ v≢ in ⟨ d' , proj₁ d'∈ ⟩
⊑-wit ν (lift ⟨ u , ⟨ t , ⟨ _ , ⟨ p∈ , _ ⟩ ⟩ ⟩ ⟩) _ = ⟨ _ , ⟨ ⟨ p∈ , (λ ()) ⟩ , refl ⟩ ⟩
⊑-wit (U ↦ w) ⟨ lift ⟨ u , ⟨ t , ⟨ _ , ⟨ p∈ , _ ⟩ ⟩ ⟩ ⟩ , _ ⟩ _ = ⟨ _ , ⟨ ⟨ p∈ , (λ ()) ⟩ , refl ⟩ ⟩
⊑-wit (tup[ i ] d) d⊑ _ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ tup[ i ] d' , ⟨ ⟨ d'∈ , (λ ()) ⟩ , refl ⟩ ⟩
⊑-wit (left d) d⊑ _ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ left d' , ⟨ ⟨ d'∈ , (λ ()) ⟩ , refl ⟩ ⟩
⊑-wit (right d) d⊑ _ = let ⟨ d' , d'∈ ⟩ = ⊑-ne d d⊑ in ⟨ right d' , ⟨ ⟨ d'∈ , (λ ()) ⟩ , refl ⟩ ⟩
⊑-wit (const k) (lift v∈) _ = ⟨ _ , ⟨ ⟨ v∈ , (λ ()) ⟩ , refl ⟩ ⟩
⊑-wit ω _ ne = ⊥-elim (ne refl)
⊑-wit ⦅ u , v ⦆ (lift ())
⊑-wit ⟨⟩ (lift v∈) _ = ⟨ _ , ⟨ ⟨ v∈ , (λ ()) ⟩ , refl ⟩ ⟩

⊑-val : ∀ {v D'} → v ≢ ω → v ⊑ D' → Conv D'
⊑-val {v} v≢ v⊑ = let ⟨ d' , ⟨ d'∈ , _ ⟩ ⟩ = ⊑-wit v v⊑ v≢ in ⟨ d' , d'∈ ⟩

⊑-lift : LiftRel _⊑_
⊑-lift = record { ω→ = lower ; →ω = lift ; S-mono = λ {d} → ⊑-mono d ; S-val = ⊑-val }

{- project: the check, and the values of the right kind -}
⊑-restrict : ∀ v {X'} → v ⊑ X' → v ⊑ (X' ⇂ λ d → kind₄ (kind d) ≡ kind v)
⊑-restrict ν {X'} (lift p) = lift (PairV-mono {X'} {X' ⇂ λ d → kind₄ (kind d) ≡ fun} (λ u v p∈ → ⟨ p∈ , refl ⟩) p)
⊑-restrict (U ↦ w) {X'} ⟨ lift p , f ⟩ =
  ⟨ lift (PairV-mono {X'} {X' ⇂ λ d → kind₄ (kind d) ≡ fun} (λ u v p∈ → ⟨ p∈ , refl ⟩) p)
  , (λ E' cE U⊑ → ⊑-mono w (⊙-mono {X'} {X' ⇂ λ d → kind₄ (kind d) ≡ fun} (λ u v p∈ → ⟨ p∈ , refl ⟩)) (f E' cE U⊑)) ⟩
⊑-restrict (tup[ i ] d) d⊑ = ⊑-mono d (λ e e∈ → ⟨ e∈ , refl ⟩) d⊑
⊑-restrict (left d) d⊑ = ⊑-mono d (λ e e∈ → ⟨ e∈ , refl ⟩) d⊑
⊑-restrict (right d) d⊑ = ⊑-mono d (λ e e∈ → ⟨ e∈ , refl ⟩) d⊑
⊑-restrict (const k) (lift v∈) = lift ⟨ v∈ , refl ⟩
⊑-restrict ω (lift v∈) = lift ⟨ v∈ , refl ⟩
⊑-restrict ⦅ u , v ⦆ (lift ())
⊑-restrict ⟨⟩ (lift v∈) = lift ⟨ v∈ , refl ⟩

⊑-proj : ∀ k {X X'} → Clean X → Lifted _⊑_ X X'
  → Lifted _⊑_ (checked k X (X ⇂ λ d → kind d ≡ k)) (checkedᵠ kind₄ k X' (X' ⇂ λ d → kind₄ (kind d) ≡ k))
⊑-proj k clX h w (inj₁ ⟨ refl , ⟨ s , ⟨ s∈ , sk ⟩ ⟩ ⟩) with ⊑-wit s (h s s∈) (clX s s∈)
... | ⟨ d' , ⟨ d'∈ , dk ⟩ ⟩ = lift (inj₁ ⟨ refl , ⟨ d' , ⟨ proj₁ d'∈ , (λ e → sk (trans (sym dk) e)) ⟩ ⟩ ⟩)
⊑-proj k clX h w (inj₂ ⟨ w∈ , wk ⟩) = ⊑-mono w (λ { d ⟨ d∈ , e ⟩ → inj₂ ⟨ d∈ , trans e wk ⟩ }) (⊑-restrict w (h w w∈))

data-⊑ : ∀ v {D'} → Data v → v ∈ D' → v ⊑ D'
data-⊑ (left d) dd v∈ = data-⊑ d dd v∈
data-⊑ (right d) dd v∈ = data-⊑ d dd v∈
data-⊑ (const k) _ v∈ = lift v∈
data-⊑ ω _ v∈ = lift v∈
data-⊑ ⟨⟩ _ v∈ = lift v∈

⊑*-intro : ∀ U {D E'} → mem U ⊆ D → Lifted _⊑_ D E' → U ⊑* E'
⊑*-intro [] U⊆ f = ptt
⊑*-intro (u ∷ U) U⊆ f = ⟨ f u (U⊆ u (here refl)) , ⊑*-intro U (λ d d∈ → U⊆ d (there d∈)) f ⟩

⊑*-elim : ∀ {U E'} → U ⊑* E' → Lifted _⊑_ (mem U) E'
⊑*-elim ⟨ u⊑ , _ ⟩ u (here refl) = u⊑
⊑*-elim ⟨ _ , U⊑ ⟩ u (there u∈) = ⊑*-elim U⊑ u u∈

{- a function exhibited by D' gives a closure -}
fun-pair : ∀ f {D'} → kind f ≡ fun → f ⊑ D' → PairV D'
fun-pair ν _ (lift p) = p
fun-pair (U ↦ w) _ ⟨ lift p , _ ⟩ = p

{- Facts about Clos3ᵀ and Clos4ᵀ ----------------------------------------------------}

{- the values of a tuple of length n have kind tup n -}
binds-in : ∀ m Ds {K : Results (𝒫 Value) (replicate m ■) → 𝒫 Value} {P : Value → Set}
  → (∀ {Xs} t → t ∈ K Xs → P t) → ∀ t → t ∈ binds m Ds K → t ≢ ω → P t
binds-in zero _ h t t∈ _ = h t t∈
binds-in (suc m) ⟨ D , Ds ⟩ h t (inj₁ ⟨ refl , _ ⟩) t≢ = ⊥-elim (t≢ refl)
binds-in (suc m) ⟨ D , Ds ⟩ h t (inj₂ ⟨ _ , t∈ ⟩) t≢ = binds-in m Ds h t t∈ t≢

𝒯-kind : ∀ n {Xs} t → t ∈ 𝒯 n Xs → kind t ≡ tup n
𝒯-kind zero ⟨⟩ _ = refl
𝒯-kind (suc n) (tup[ i ] d) ⟨ refl , _ ⟩ = refl

𝒯ᵐ-kind : ∀ n {Ds} t → t ∈ ⌊ 𝒯ᵐ n Ds ⌋ → kind t ≡ tup n
𝒯ᵐ-kind n {Ds} t ⟨ t∈ , t≢ ⟩ = binds-in n Ds (𝒯-kind n) t t∈ t≢

kind≢ω : ∀ {t n} → kind t ≡ tup n → t ≢ ω
kind≢ω () refl

{- a value of type ⟪ fun ⟫ is a function -}
FunEnv : ∀ {Γ} → Env Value → Set
FunEnv {Γ} ρ = ∀ (x : Γ ∋ ⟪ fun ⟫) f → f ∈ ρ (idx x) → f ≢ ω → kind f ≡ fun

Λ-fun : ∀ f {G} → f ∈ Λ ⟨ G , ptt ⟩ → kind f ≡ fun
Λ-fun (U ↦ w) _ = refl
Λ-fun ν _ = refl

fun-val : ∀ {Γ G} (L : Tm Γ ⟪ G ⟫) {ρ} → G ≡ fun → FunEnv {Γ} ρ → ∀ f → f ∈ ⌊ ⟦ L ⟧ ρ ⌋ → kind f ≡ fun
fun-val (` x) refl h f ⟨ f∈ , f≢ ⟩ = h x f f∈ f≢
fun-val (clos N Ms) {ρ} _ h f f∈ with ⌊≫=⌋ {𝒯ᵐ _ (⟦ Ms ⟧s ρ)} {λ Y → ⋆ ⟨ ΛΛᵐ ⟨ (λ X Y → ⟦ N ⟧ (Y • X • λ _ → ⌈ ω ⌉)) , ptt ⟩ , ⟨ Y , ptt ⟩ ⟩} f f∈
... | ⟨ V , ⟨ ⟨ ⟨ f∈Λ , _ ⟩ , _ ⟩ , _ ⟩ ⟩ = Λ-fun f f∈Λ
fun-val (project _ M) {ρ} refl h f f∈ =
  proj₂ (⌊checked⌋ {fun} {⌊ ⟦ M ⟧ ρ ⌋} {⌊ ⟦ M ⟧ ρ ⌋ ⇂ λ d → kind d ≡ fun} f ⟨ ⌊≫=⌋ {⟦ M ⟧ ρ} {λ X → checked fun X (X ⇂ λ d → kind d ≡ fun)} f f∈ , proj₂ f∈ ⟩)
fun-val (prim sub L M) ()
fun-val (prim eq L M) ()

{- The fundamental lemma ------------------------------------------------------}

record Envs {Γ Δ} (r : Ren Γ Δ) (ρ ρ' : Env Value) : Set₁ where
  constructor envs
  field
    NE' : nonempty-env ρ'
    ρ'~ : Con-env ρ'
    ρ⊑ : ∀ {A} (x : Γ ∋ A) → Lifted _⊑_ (ρ (idx x)) (ρ' (idx (r x)))
    funs : FunEnv {Γ} ρ

ext-envs : ∀ {Γ Δ} {r : Ren Γ Δ} {ρ ρ' X X'} → Envs r ρ ρ' → nonempty X' → Con X' → Lifted _⊑_ X X'
  → Envs (ext {B = Any} r) (X • ρ) (X' • ρ')
ext-envs (envs NE' ρ'~ ρ⊑ funs) ne c h =
  envs (extend-nonempty-env NE' ne) (Con-• c ρ'~) (λ { Z → h ; (S x) → ρ⊑ x }) (λ { (S x) → funs x })

preserve : ∀ {Γ Δ A} (M : Tm Γ A) {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ' → Lifted _⊑_ (⟦ M ⟧ ρ) (⟦ delay r M ⟧' ρ')
preserve-nth : ∀ {Γ Δ n} (Ms : Vec (Tm Γ Any) n) {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → ∀ i → Lifted _⊑_ (nthD (⟦ Ms ⟧s ρ) i) (nthD (⟦ delays r Ms ⟧s' ρ') i)
preserve-𝒯 : ∀ {Γ Δ n} (Ms : Vec (Tm Γ Any) n) {r : Ren Γ Δ} {ρ ρ'} → Envs r ρ ρ'
  → Lifted _⊑_ (𝒯ᵐ n (⟦ Ms ⟧s ρ)) (𝒯ᵐ n (⟦ delays r Ms ⟧s' ρ'))

args-con' : ∀ {Γ Δ n} (Ms : Vec (Tm Γ Any) n) {r : Ren Γ Δ} {ρ} → Con-env ρ → ∀ i → Con (nthD (⟦ delays r Ms ⟧s' ρ) i)
args-con' (M ∷ Ms) c zero = S4.con (delay _ M) c
args-con' (M ∷ Ms) c (suc i) = args-con' Ms c i

clean⌊⌋ : ∀ {D} → Clean ⌊ D ⌋
clean⌊⌋ d d∈ = proj₂ d∈

preserve (` x) E = Envs.ρ⊑ E x

preserve (lit B k) E (const k') v∈ = lift v∈

preserve (prim p L M) {r} {ρ} {ρ'} E =
  ≫=-lift {F = λ X → ⟦ M ⟧ ρ ≫= K X} {F' = λ X → ⟦ delay r M ⟧' ρ' ≫= K X} ⊑-lift (S4.con (delay r L) ρ'~) (preserve L E)
    λ _ _ hX → ≫=-lift {F = K ⌊ ⟦ L ⟧ ρ ⌋} {F' = K ⌊ ⟦ delay r L ⟧' ρ' ⌋} ⊑-lift (S4.con (delay r M) ρ'~) (preserve M E)
    λ _ _ hY → kernel hX hY
  where
  open Envs E
  K = λ X Y → primD p ⟨ X , ⟨ Y , ptt ⟩ ⟩
  kernel : ∀ {X X' Y Y'} → Lifted _⊑_ X X' → Lifted _⊑_ Y Y' → Lifted _⊑_ (K X Y) (K X' Y')
  kernel hX hY _ ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , refl ⟩ ⟩ ⟩ ⟩ =
    data-⊑ (out (δ p n m)) (out-data (δ p n m)) ⟨ n , ⟨ m , ⟨ lower (hX _ n∈) , ⟨ lower (hY _ m∈) , refl ⟩ ⟩ ⟩ ⟩

preserve (tuple Ms) = preserve-𝒯 Ms

preserve (get i M) {r} E =
  ≫=-lift {F = λ X → proj i ⟨ X , ptt ⟩} {F' = λ X → proj i ⟨ X , ptt ⟩} ⊑-lift (S4.con (delay r M) (Envs.ρ'~ E)) (preserve M E)
    λ _ _ hX v t∈ → hX _ t∈

preserve (L3.inl M) {r} E =
  ≫=-lift {F = λ X → inl ⟨ X , ptt ⟩} {F' = λ X → inl ⟨ X , ptt ⟩} ⊑-lift (S4.con (delay r M) (Envs.ρ'~ E)) (preserve M E)
    λ { _ _ hX (left v) v∈ → hX v v∈ }

preserve (L3.inr M) {r} E =
  ≫=-lift {F = λ X → inr ⟨ X , ptt ⟩} {F' = λ X → inr ⟨ X , ptt ⟩} ⊑-lift (S4.con (delay r M) (Envs.ρ'~ E)) (preserve M E)
    λ { _ _ hX (right v) v∈ → hX v v∈ }

preserve {Γ} (case L M N) {r} {ρ} {ρ'} E =
  ≫=-lift {F = λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩} {F' = λ X → 𝒞 ⟨ X ⇂ ValPayload , ⟨ F₁' , ⟨ F₂' , ptt ⟩ ⟩ ⟩}
    ⊑-lift (S4.con (delay r L) ρ'~) (preserve L E) λ _ _ hX → kernel hX
  where
  open Envs E
  F₁ = λ Y → ⟦ M ⟧ (Y • ρ)
  F₂ = λ Y → ⟦ N ⟧ (Y • ρ)
  F₁' = λ Y → ⟦ delay (ext r) M ⟧' (Y • ρ')
  F₂' = λ Y → ⟦ delay (ext r) N ⟧' (Y • ρ')
  X' = ⌊ ⟦ delay r L ⟧' ρ' ⌋ ⇂ ValPayload
  cX' : Con X'
  cX' = Con-⊆ (S4.con (delay r L) ρ'~) (λ d d∈ → proj₁ (proj₁ d∈))
  {- the branch B on the side s of the scrutinee -}
  branch : ∀ (s : Tag) (B : Tm (Any ∷ Γ) Any) {Cs} → (∀ {a b} → tag s a ~ tag s b → a ~ b)
    → (∀ {y} → y ≢ ω → ValPayload (tag s y))
    → (nonempty (Untag s X') → Con (Untag s X') → ⟦ delay (ext r) B ⟧' (Untag s X' • ρ') ⊆ Cs)
    → ∀ u U → (∀ d → d ∈ mem (u ∷ U) → d ⊑ Untag s ⌊ ⟦ delay r L ⟧' ρ' ⌋) → NoErr (u ∷ U)
    → ∀ v → v ∈ ⟦ B ⟧ (mem (u ∷ U) • ρ) → v ⊑ Cs
  branch s B {Cs} s~ vp B⊆ u U u⊑ nU v v∈ = ⊑-mono v (B⊆ ne cS) (preserve B (ext-envs E ne cS u⊑') v v∈)
    where
    cS = Untag-con s s~ cX'
    clU : Clean (Untag s ⌊ ⟦ delay r L ⟧' ρ' ⌋)
    clU = con-clean (Untag-con s s~ (Con-⊆ (S4.con (delay r L) ρ'~) ⌊⌋-⊆))
                    (⊑-val {u} (λ { refl → nU (here refl) }) (u⊑ u (here refl)))
    u⊑' : Lifted _⊑_ (mem (u ∷ U)) (Untag s X')
    u⊑' d d∈ = ⊑-mono d (λ y y∈ → ⟨ y∈ , vp (clU y y∈) ⟩) (u⊑ d d∈)
    ne : nonempty (Untag s X')
    ne = let ⟨ y , y∈ ⟩ = ⊑-val {u} {Untag s X'} (λ { refl → nU (here refl) }) (u⊑' u (here refl)) in ⟨ y , proj₁ y∈ ⟩
  kernel : Lifted _⊑_ ⌊ ⟦ L ⟧ ρ ⌋ ⌊ ⟦ delay r L ⟧' ρ' ⌋
    → Lifted _⊑_ (𝒞 ⟨ ⌊ ⟦ L ⟧ ρ ⌋ ⇂ ValPayload , ⟨ F₁ , ⟨ F₂ , ptt ⟩ ⟩ ⟩) (𝒞 ⟨ X' , ⟨ F₁' , ⟨ F₂' , ptt ⟩ ⟩ ⟩)
  kernel hX v (inj₁ ⟨ u , ⟨ U , ⟨ all , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
    branch leftT M (λ c → c) (λ y≢ → y≢) (λ ne c → 𝒞-left {X'} {F₁'} {F₂'} (fin₁ (S4.ok (delay (ext r) M)) NE' ne) c)
      u U (λ d d∈ → hX (left d) (proj₁ (all d d∈))) (λ ω∈ → proj₂ (all ω ω∈) refl) v v∈
  kernel hX v (inj₂ ⟨ u , ⟨ U , ⟨ all , ⟨ v∈ , _ ⟩ ⟩ ⟩ ⟩) =
    branch rightT N (λ c → c) (λ y≢ → y≢) (λ ne c → 𝒞-right {X'} {F₁'} {F₂'} (fin₁ (S4.ok (delay (ext r) N)) NE' ne) c)
      u U (λ d d∈ → hX (right d) (proj₁ (all d d∈))) (λ ω∈ → proj₂ (all ω ω∈) refl) v v∈

preserve (let′ M N) {r} {ρ} {ρ'} E =
  ≫=-lift {F = λ X → ⟦ N ⟧ (X • ρ)} {F' = λ X → ⟦ delay (ext r) N ⟧' (X • ρ')} ⊑-lift (S4.con (delay r M) ρ'~) (preserve M E)
    λ _ c' hX → preserve N (ext-envs E c' (Con-⊆ (S4.con (delay r M) ρ'~) ⌊⌋-⊆) hX)
  where open Envs E

preserve (inject G M) E = preserve M E

preserve (project G M) {r} E =
  ≫=-lift {F = λ X → checked (kindᶠ G) X (X ⇂ λ d → kind d ≡ kindᶠ G)} {F' = λ X → checkedᵠ kind₄ (kindᶠ G) X (X ⇂ λ d → kind₄ (kind d) ≡ kindᶠ G)}
    ⊑-lift (S4.con (delay r M) (Envs.ρ'~ E)) (preserve M E) λ _ _ hX → ⊑-proj (kindᶠ G) clean⌊⌋ hX

preserve (app L M) {r} {ρ} {ρ'} E =
  ≫=-lift {F = λ Xs → Xs ● ⟦ M ⟧ ρ} {F' = S4.Unpack Body ρ'} ⊑-lift (S4.con (delay r L) ρ'~) (preserve L E) APP
  where
  open Envs E
  Body : ∀ n → Env Value → 𝒫 Value
  Body n = ⟦ T.call {n = n} (T.` S Z) (T.` Z) (delay (λ x → S (S (r x))) M) ⟧'
  P = ⌊ ⟦ delay r L ⟧' ρ' ⌋
  cP : Con P
  cP = Con-⊆ (S4.con (delay r L) ρ'~) ⌊⌋-⊆
  APP : Conv (⟦ L ⟧ ρ) → Conv (⟦ delay r L ⟧' ρ') → Lifted _⊑_ ⌊ ⟦ L ⟧ ρ ⌋ P
    → Lifted _⊑_ (⌊ ⟦ L ⟧ ρ ⌋ ● ⟦ M ⟧ ρ) (S4.Unpack Body ρ' P)
  APP ⟨ f , f∈ ⟩ _ hX with fun-pair f (fun-val L refl funs f f∈) (hX f f∈)
  ... | ⟨ u , ⟨ t , ⟨ n , ⟨ p∈ , ⟨ u≢ , tk ⟩ ⟩ ⟩ ⟩ ⟩ = G
    where
    E'' : Envs (λ x → S (S (r x))) ρ (cdr ⟨ P , ptt ⟩ • car ⟨ P , ptt ⟩ • ρ')
    E'' = envs (extend-nonempty-env (extend-nonempty-env NE' ⟨ u , ⟨ t , p∈ ⟩ ⟩) ⟨ t , ⟨ u , p∈ ⟩ ⟩)
      (Con-• (λ a b a∈ b∈ → proj₂ (cP _ _ (proj₂ a∈) (proj₂ b∈))) (Con-• (λ a b a∈ b∈ → proj₁ (cP _ _ (proj₂ a∈) (proj₂ b∈))) ρ'~))
      ρ⊑ funs
    Arg = ⟦ delay (λ x → S (S (r x))) M ⟧' (cdr ⟨ P , ptt ⟩ • car ⟨ P , ptt ⟩ • ρ')
    into : P ⊙ Arg ⊆ S4.Unpack Body ρ' P
    into x x∈ = ⟨ n , ⟨ ⟨ t , ⟨ ⟨ u , p∈ ⟩ , tk ⟩ ⟩ , x∈ ⟩ ⟩
    G : Lifted _⊑_ (⌊ ⟦ L ⟧ ρ ⌋ ● ⟦ M ⟧ ρ) (S4.Unpack Body ρ' P)
    G w (inj₁ ⟨ refl , ω∈ ⟩) = lift (into ω (inj₂ ⟨ ⟨ u , ⟨ ⟨ t , p∈ ⟩ , u≢ ⟩ ⟩ , inj₂ ⟨ ⟨ t , ⟨ ⟨ u , p∈ ⟩ , kind≢ω tk ⟩ ⟩
      , inj₁ ⟨ refl , lower (preserve M E'' ω ω∈) ⟩ ⟩ ⟩))
    G w (inj₂ ⟨ _ , ⟨ U , ⟨ e∈ , ⟨ U⊆ , _ ⟩ ⟩ ⟩ ⟩) =
      ⊑-mono w into (proj₂ (hX (U ↦ w) e∈) Arg (S4.con (delay (λ x → S (S (r x))) M) (Envs.ρ'~ E''))
        (⊑*-intro U (λ d d∈ → proj₁ (U⊆ d d∈)) (preserve M E'')))

preserve (clos {n = n} N Ms) {r} {ρ} {ρ'} E v v∈ =
  ⊑-mono v (proj₂ (≫=-val-β {F = λ C → T' ≫= λ Y → pair ⟨ C , ⟨ Y , ptt ⟩ ⟩} ΛΛᵐ-val))
    (≫=-lift {F = λ Y → ⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ Y , ptt ⟩ ⟩} {F' = λ Y → pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ Y , ptt ⟩ ⟩}
       ⊑-lift cT' (preserve-𝒯 Ms E) kernel v v∈)
  where
  open Envs E
  F = λ X Y → ⟦ N ⟧ (Y • X • (λ _ → ⌈ ω ⌉))
  F' = λ X Y → ⟦ delay (λ x → x) N ⟧' (Y • X • (λ _ → ⌈ ω ⌉))
  T = 𝒯ᵐ n (⟦ Ms ⟧s ρ)
  T' = 𝒯ᵐ n (⟦ delays r Ms ⟧s' ρ')
  cT' = S4.con (T.tuple (delays r Ms)) ρ'~
  kernel : Conv T → Conv T' → Lifted _⊑_ ⌊ T ⌋ ⌊ T' ⌋
    → Lifted _⊑_ (⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ ⌊ T ⌋ , ptt ⟩ ⟩) (pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ ⌊ T' ⌋ , ptt ⟩ ⟩)
  kernel _ ⟨ t' , t'∈ ⟩ hT = G
    where
    Pp = pair ⟨ ⌊ ΛΛᵐ ⟨ F' , ptt ⟩ ⌋ , ⟨ ⌊ T' ⌋ , ptt ⟩ ⟩
    PV : PairV Pp
    PV = ⟨ ν , ⟨ t' , ⟨ n , ⟨ ⟨ ⟨ ⟨ tt , tt ⟩ , (λ ()) ⟩ , t'∈ ⟩ , ⟨ (λ ()) , 𝒯ᵐ-kind n t' t'∈ ⟩ ⟩ ⟩ ⟩ ⟩
    C⊆ : ΛΛᵐ ⟨ F' , ptt ⟩ ⊆ ⌊ car ⟨ Pp , ptt ⟩ ⌋
    C⊆ c c∈ = ⟨ ⟨ t' , ⟨ ⟨ c∈ , proj₁ ΛΛᵐ-val c c∈ ⟩ , t'∈ ⟩ ⟩ , proj₁ ΛΛᵐ-val c c∈ ⟩
    T⊆ : ⌊ T' ⌋ ⊆ ⌊ cdr ⟨ Pp , ptt ⟩ ⌋
    T⊆ y y∈ = ⟨ ⟨ ν , ⟨ ⟨ ⟨ tt , tt ⟩ , (λ ()) ⟩ , y∈ ⟩ ⟩ , proj₂ y∈ ⟩
    G : Lifted _⊑_ (⋆ ⟨ ΛΛᵐ ⟨ F , ptt ⟩ , ⟨ ⌊ T ⌋ , ptt ⟩ ⟩) Pp
    G ν _ = lift PV
    G (U ↦ w) ⟨ FV , ⟨ ⟨ ⟨ ⟨ w∈ , ⟨ neU , _ ⟩ ⟩ , _ ⟩ , ⟨ _ , nU ⟩ ⟩ , ⟨ FV⊆ , _ ⟩ ⟩ ⟩ = ⟨ lift PV , call ⟩
      where
      call : ∀ E' → Con E' → U ⊑* E' → w ⊑ Pp ⊙ E'
      call E' cE' U⊑ = ⊑-mono w β (preserve N Eb w w∈)
        where
        u₀ = proj₁ (ne-mem neU (λ d d∈ → d∈))
        u₀∈ = proj₂ (ne-mem neU (λ d d∈ → d∈))
        vE' = con-val cE' (⊑-val (λ eq → nU (subst (λ x → x ∈ mem U) eq u₀∈)) (⊑*-elim U⊑ u₀ u₀∈))
        Eb : Envs (λ x → x) (mem U • mem FV • λ _ → ⌈ ω ⌉) (E' • ⌊ T' ⌋ • λ _ → ⌈ ω ⌉)
        Eb = envs (extend-nonempty-env (extend-nonempty-env (λ _ → ⟨ ω , refl ⟩) ⟨ t' , t'∈ ⟩) (proj₂ vE'))
                  (Con-• cE' (Con-• (Con-⊆ cT' ⌊⌋-⊆) (λ _ → Con-⌈⌉ ω)))
                  (λ { Z → ⊑*-elim U⊑ ; (S Z) d d∈ → hT d (FV⊆ d d∈) }) (λ { (S (S ())) })
        β : F' ⌊ T' ⌋ E' ⊆ Pp ⊙ E'
        β x x∈ = inj₂ ⟨ ⟨ ν , C⊆ ν ⟨ tt , tt ⟩ ⟩ , inj₂ ⟨ ⟨ t' , T⊆ t' t'∈ ⟩ , inj₂ ⟨ Val⇒Conv vE'
          , ⋆⋆-mono C⊆ T⊆ (⌊⌋-clean (proj₁ vE')) x
              (ΛΛᵐ-call {F'} (Con-⊆ cT' ⌊⌋-⊆) cE' clean⌊⌋ (proj₁ vE') (fin₂ (S4.ok (delay (λ x → x) N)) ⟨ t' , t'∈ ⟩ (proj₂ vE')) x x∈) ⟩ ⟩ ⟩

preserve-nth (M ∷ Ms) E zero = preserve M E
preserve-nth (M ∷ Ms) E (suc i) = preserve-nth Ms E i

preserve-𝒯 {n = n} Ms E =
  binds-lift n ⊑-lift (args-con' Ms (Envs.ρ'~ E)) (preserve-nth Ms E) (kernel n)
  where
  kernel : ∀ m {Xs Xs'} → (∀ i → Clean (nthD Xs i)) → (∀ i → Lifted _⊑_ (nthD Xs i) (nthD Xs' i))
    → Lifted _⊑_ (𝒯 m Xs) (𝒯 m Xs')
  kernel zero cl hs ⟨⟩ tt = lift tt
  kernel (suc m) cl hs (tup[ i ] d) ⟨ refl , ⟨ d∈ , ne ⟩ ⟩ =
    ⊑-mono d (λ d' d'∈ → ⟨ refl , ⟨ d'∈ , ne' ⟩ ⟩) (hs i d d∈)
    where
    ne' = λ j → let ⟨ e , e∈ ⟩ = ne j ; ⟨ e' , e'∈ ⟩ = ⊑-val (cl j e e∈) (hs j e e∈) in ⟨ e' , proj₁ e'∈ ⟩

{- The end theorem (forward half) ------------------------------------------------}

Envs₀ : ∀ (r : Ren [] []) → Envs r ρ₀ ρ₀
Envs₀ r = envs (λ _ → ⟨ ω , refl ⟩) (λ _ → Con-⌈⌉ ω) (λ ()) (λ ())

preserve₀ : ∀ (M : Tm [] Any) → Lifted _⊑_ (⟦ M ⟧ ρ₀) (⟦ delay-program M ⟧' ρ₀)
preserve₀ M = preserve M (Envs₀ _)
