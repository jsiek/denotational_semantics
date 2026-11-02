{-

  Assurance (not in the totals): what the erasure proof
  (proof/Assurance/X86Erasure.agda) relates X86ᵀ and X86 states by,
  kept from the proof of select into untyped X86 that preceded X86ᵀ
  (PR #58).

  An X86 value is the erasure of a typed value (⌊_⌋): a code pointer is
  its definition's level, a closure a pair, and an injection into Any
  the value itself. The X86 frame holds the erasure of slot x of the
  typed frame at the level of x (Agree); reading an atom (arg-ok) and
  writing a slot (write) keep it. X86's proj finds component i of a
  tuple when the tuple has the length its type says (proj-ok), and
  fails otherwise (proj-bad).

-}

module proof.Assurance.X86Agree where

open import Language.Typed.Type hiding (_≟_)
open import Framework.Membership using (_⊑_; ⊑-∋)
open import Framework.Lookup using (_!_; forget)
open import Framework.ListUtil using (_‼_; has-length; proj)
import Language.Typed.Imp as Imp
open import Compiler.SelectX86 using (select-atm)
open import proof.Framework.Lookup using (lvl-<; lvl-⊑; forget-!)
open import Semantics.Observation using (Obs; o-tuple; o-inl; o-inr)
import Semantics.CEK.X86 as X
import Semantics.CEK.Values as XV
import Semantics.CEK.Typed.Clos5 as V
import Semantics.CEK.Typed.CFG as G
open G using (atom)

open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mmap)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
import Data.Nat as N
open import Data.Nat.Properties using (<⇒≢)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

{- Erasure ---------------------------------------------------------------------}

⌊_⌋ : ∀ {Σ A} → V.Val Σ A → X.Val
⌊_⌋* : ∀ {Σ n} → Vec (V.Val Σ Any) n → List X.Val
⌊ V.code f ⌋ = X.code (lvl f)
⌊ V.pack c e ⌋ = X.pair ⌊ c ⌋ ⌊ e ⌋
⌊ V.const {B} c ⌋ = X.const B c
⌊ V.tup vs ⌋ = X.tup ⌊ vs ⌋*
⌊ V.inl v ⌋ = X.inl ⌊ v ⌋
⌊ V.inr v ⌋ = X.inr ⌊ v ⌋
⌊ V.dyn G v ⌋ = ⌊ v ⌋
⌊ [] ⌋* = []
⌊ v ∷ vs ⌋* = ⌊ v ⌋ ∷ ⌊ vs ⌋*

obs-⌊⌋ : ∀ {Σ A} (v : V.Val Σ A) → X.obs ⌊ v ⌋ ≡ V.obs v
obs-⌊⌋* : ∀ {Σ n} (vs : Vec (V.Val Σ Any) n) → XV.obs-list ⌊ vs ⌋* ≡ V.obs-vec vs
obs-⌊⌋ (V.code f) = refl
obs-⌊⌋ (V.pack c e) = refl
obs-⌊⌋ (V.const c) = refl
obs-⌊⌋ (V.tup vs) = cong o-tuple (obs-⌊⌋* vs)
obs-⌊⌋ (V.inl v) = cong o-inl (obs-⌊⌋ v)
obs-⌊⌋ (V.inr v) = cong o-inr (obs-⌊⌋ v)
obs-⌊⌋ (V.dyn G v) = obs-⌊⌋ v
obs-⌊⌋* [] = refl
obs-⌊⌋* (v ∷ vs) = cong₂′ (obs-⌊⌋ v) (obs-⌊⌋* vs)
  where cong₂′ : ∀ {a b : Obs} {as bs} → a ≡ b → as ≡ bs → a ∷ as ≡ b ∷ bs
        cong₂′ refl refl = refl

len-⌊⌋ : ∀ {Σ n} (vs : Vec (V.Val Σ Any) n) → length ⌊ vs ⌋* ≡ n
len-⌊⌋ [] = refl
len-⌊⌋ (v ∷ vs) = cong suc (len-⌊⌋ vs)

has-len : ∀ {A : Set} (vs : List A) n → length vs ≡ n → has-length n vs ≡ true
has-len [] zero e = refl
has-len (v ∷ vs) (suc n) e = has-len vs n (cong N.pred e)

{- component i of a tuple, in X86 -}
proj-ok : ∀ {Σ n} (vs : Vec (V.Val Σ Any) n) (i : Fin n) → proj i ⌊ vs ⌋* ≡ just ⌊ lookup vs i ⌋
proj-ok {n = suc n} (v ∷ vs) zero = cong (λ b → if b then just ⌊ v ⌋ else nothing) (has-len _ n (len-⌊⌋ vs))
proj-ok (v ∷ vs) (suc i) = proj-ok vs i

has-len⁻ : ∀ {A : Set} (vs : List A) n → has-length n vs ≡ true → length vs ≡ n
has-len⁻ [] zero e = refl
has-len⁻ [] (suc n) ()
has-len⁻ (v ∷ vs) zero ()
has-len⁻ (v ∷ vs) (suc n) e = cong suc (has-len⁻ vs n e)

proj-bad : ∀ {A : Set} (vs : List A) {k} (i : Fin k) → length vs ≢ k → proj i vs ≡ nothing
proj-bad [] zero ne = refl
proj-bad [] (suc i) ne = refl
proj-bad (v ∷ vs) {suc k} zero ne with has-length k vs in e
... | true = ⊥-elim (ne (cong suc (has-len⁻ vs k e)))
... | false = refl
proj-bad (v ∷ vs) (suc i) ne = proj-bad vs i (ne ∘ cong suc)

{- Frames ----------------------------------------------------------------------}

module _ {Σ : List ℕ} where

  {- the X86 frame holds slot x at the level of x -}
  record Agree {Δ} (φ : G.Frame Σ Δ) (φₓ : X.Frame) : Set where
    constructor agree
    field at : ∀ {B} (x : Δ ∋ B) → φₓ ‼ lvl x ≡ just ⌊ φ ! x ⌋

  arg-ok : ∀ {Δ A} {φ : G.Frame Σ Δ} {φₓ ρ} → Agree φ φₓ → ∀ (a : Imp.Atm Σ Δ A)
    → X.arg φₓ ρ (select-atm a) ≡ just ⌊ atom φ a ⌋
  arg-ok ag (Imp.var x) = Agree.at ag x
  arg-ok ag (Imp.lit B c) = refl
  arg-ok ag (Imp.ref f) = refl

upd : ∀ (φ : X.Frame) k w → k < length φ
  → Σ[ φ' ∈ X.Frame ] φ X.[ k ]≔ w ≡ just φ' × φ' ‼ k ≡ just w × (∀ j → j ≢ k → φ' ‼ j ≡ φ ‼ j) × length φ' ≡ length φ
upd (u ∷ φ) zero w _ = w ∷ φ , refl , refl , (λ { zero ne → ⊥-elim (ne refl) ; (suc j) _ → refl }) , refl
upd (u ∷ φ) (suc k) w (s≤s lt) with upd φ k w lt
... | φ' , e , r , o , l = u ∷ φ' , cong (mmap (u ∷_)) e , r , (λ { zero _ → refl ; (suc j) ne → o j (ne ∘ cong suc) }) , cong suc l

{- slot |Δ'| := v, forgetting the slots from |Δ'| on -}
write : ∀ {Σ Δ Δ' A} {φ : G.Frame Σ Δ} {φₓ} → Agree φ φₓ → (p : Δ' ⊑ Δ) → length Δ' < length φₓ → (v : V.Val Σ A)
  → Σ[ φₓ' ∈ X.Frame ] φₓ X.[ length Δ' ]≔ ⌊ v ⌋ ≡ just φₓ' × Agree (v ∷ forget p φ) φₓ' × length φₓ' ≡ length φₓ
write {φ = φ} {φₓ} ag p lt v with upd φₓ _ ⌊ v ⌋ lt
... | φₓ' , e , r , o , l = φₓ' , e , agree ag' , l
  where
  ag' : ∀ {B} (x : _ ∋ B) → φₓ' ‼ lvl x ≡ just ⌊ (v ∷ forget p φ) ! x ⌋
  ag' Z = r
  ag' (S y) = trans (o (lvl y) (<⇒≢ (lvl-< y)))
    (trans (cong (φₓ ‼_) (sym (lvl-⊑ p y)))
      (trans (Agree.at ag (⊑-∋ p y)) (cong (just ∘ ⌊_⌋) (sym (forget-! p φ y)))))

