{-

  Lift locals (Monμ → Impμ), as typed lift locals
  (ISWIM/Compiler/LiftLocals.agda), into a fixed frame: every variable
  that a let or a case of a body binds gets a slot of its own, and the
  frame of the body has a slot for each of them and for each parameter.
  A let becomes an assignment to its variable's slot, and a case writes
  the payload to the slot of the variable that the branch binds. An
  atom reads the slot of its variable.

  binds e D lists the types of the variables that e binds in front of
  D, the oldest last: for let x = e₁ in e₂, those of e₁, then x, then
  those of e₂. The frame of a body with parameters Γ is binds e Γ, the
  slots of the parameters being its suffix Γ. lift e q ρ translates e,
  whose variables are in the slots ρ, and whose bound variables are in
  the part binds e D of the frame that q places (D being older); where
  e starts, the variables in scope are initialized (ρ x ∈ I) and only
  the slots of D are (Only). The slot of a bound variable is therefore
  not initialized where the variable is bound, as Impμ requires.

-}

module FPC.Compiler.LiftLocals where

open import FPC.Language.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
import FPC.Language.Mon as M
open import FPC.Language.Imp
open import FPC.Framework.AllUtil using (All; []; _∷_) renaming (map to All-map)

open import Data.List using (List; []; _∷_)

{- the types of the variables that e binds, in front of D -}
binds : ∀ {Σ Γ A} → M.Exp Σ Γ A → Ctx → Ctx
binds (M.case {A} {B} a e₁ e₂) D = binds e₂ (B ∷ binds e₁ (A ∷ D))
binds (M.let′ {A} e₁ e₂) D = binds e₂ (A ∷ binds e₁ D)
binds e D = D

{- D is a suffix of binds e D -}
binds-⊒ : ∀ {Σ Γ A} (e : M.Exp Σ Γ A) D → D ⊑ binds e D
binds-⊒ (M.case {A} {B} a e₁ e₂) D =
  ⊑-trans (⊑-trans (there⊑ here⊑) (binds-⊒ e₁ (A ∷ D)))
    (⊑-trans (there⊑ here⊑) (binds-⊒ e₂ (B ∷ binds e₁ (A ∷ D))))
binds-⊒ (M.let′ {A} e₁ e₂) D =
  ⊑-trans (binds-⊒ e₁ D) (⊑-trans (there⊑ here⊑) (binds-⊒ e₂ _))
binds-⊒ (M.atm a) D = here⊑
binds-⊒ (M.pair a b) D = here⊑
binds-⊒ (M.callc a b) D = here⊑
binds-⊒ (M.tuple as) D = here⊑
binds-⊒ (M.get i a) D = here⊑
binds-⊒ (M.inl a) D = here⊑
binds-⊒ (M.inr a) D = here⊑
binds-⊒ (M.prim p a b) D = here⊑
binds-⊒ (M.fold a) D = here⊑
binds-⊒ (M.unfold a) D = here⊑

{- the slots of the variables of Γ -}
Slots : Ctx → Ctx → Set
Slots Γ Δ = ∀ {B} → Γ ∋ B → Δ ∋ B

{- the slots ρ of the variables in scope are initialized -}
Inited : ∀ {Γ Δ} → Slots Γ Δ → Inits Δ → Set
Inited {Γ} ρ I = ∀ {B} (x : Γ ∋ B) → ρ x ∈ I

ext : ∀ {Γ Δ A} → Δ ∋ A → Slots Γ Δ → Slots (A ∷ Γ) Δ
ext s ρ Z = s
ext s ρ (S x) = ρ x

inited-ext : ∀ {Γ Δ A} {I : Inits Δ} (s : Δ ∋ A) (ρ : Slots Γ Δ)
  → Inited ρ I
  → Inited (ext s ρ) (I ⊕ s)
inited-ext {I = I} s ρ ok Z = ∈-⊕ {I = I} s
inited-ext {I = I} s ρ ok (S x) = ∈-⊕ʳ {I = I} s (ρ x) (ok x)

atom : ∀ {Σ Γ Δ A} {I : Inits Δ} (ρ : Slots Γ Δ)
  → .(Inited ρ I)
  → M.Atm Σ Γ A
  → Atm Σ Δ I A
atom ρ ok (M.var x) = var (ρ x) (ok x)
atom ρ ok (M.lit B c) = lit B c
atom ρ ok (M.ref f) = ref f

atoms : ∀ {Σ Γ Δ Δs} {I : Inits Δ} (ρ : Slots Γ Δ)
  → .(Inited ρ I)
  → All (M.Atm Σ Γ) Δs
  → All (Atm Σ Δ I) Δs
atoms ρ ok [] = []
atoms ρ ok (a ∷ as) = atom ρ ok a ∷ atoms ρ ok as

{- the slot of the variable bound at the head of the suffix A ∷ D -}
slot : ∀ {Δ D : Ctx} {A} → (A ∷ D) ⊑ Δ → Δ ∋ A
slot q = ⊑-∋ q Z

{- the slot x of the variable that let e₁ e₂ binds, the part q₁ of the
   frame for the variables of e₁, and the facts about the initialized
   slots that lift needs (P places D) -}
module Let {Σ Γ Δ D A B} {I : Inits Δ} (e₁ : M.Exp Σ Γ A)
  (e₂ : M.Exp Σ (A ∷ Γ) B) (q : binds (M.let′ e₁ e₂) D ⊑ Δ) where

  P : D ⊑ Δ
  P = ⊑-trans (binds-⊒ (M.let′ e₁ e₂) D) q

  q₂ : (A ∷ binds e₁ D) ⊑ Δ
  q₂ = ⊑-trans (binds-⊒ e₂ (A ∷ binds e₁ D)) q

  q₁ : binds e₁ D ⊑ Δ
  q₁ = ⊑-tail q₂

  x : Δ ∋ A
  x = slot q₂

  fresh : Only P I → x ∉ I
  fresh o = only-fresh {I = I} q₂ (only-up {I = I} P (binds-⊒ e₁ D) q₁ o)

  only₁ : Only P I → Only (⊑-trans (binds-⊒ e₁ D) q₁) I
  only₁ o = only-⊑ {I = I} P _ o

  only₂ : Only P I → Only q₂ (I ⊕ x)
  only₂ o =
    only-⊕ {I = I} q₂ Z
      (only-up {I = I} P (⊑-trans (binds-⊒ e₁ D) (there⊑ here⊑)) q₂ o)

{- the slots x and y of the variables that case a e₁ e₂ binds, the part
   q₁ of the frame for the variables of e₁, and the facts that lift
   needs -}
module Case {Σ Γ Δ D A B C} {I : Inits Δ} (a : M.Atm Σ Γ (A ⊹ B))
  (e₁ : M.Exp Σ (A ∷ Γ) C) (e₂ : M.Exp Σ (B ∷ Γ) C)
  (q : binds (M.case a e₁ e₂) D ⊑ Δ) where

  P : D ⊑ Δ
  P = ⊑-trans (binds-⊒ (M.case a e₁ e₂) D) q

  q₂ : (B ∷ binds e₁ (A ∷ D)) ⊑ Δ
  q₂ = ⊑-trans (binds-⊒ e₂ (B ∷ binds e₁ (A ∷ D))) q

  q₁ : binds e₁ (A ∷ D) ⊑ Δ
  q₁ = ⊑-tail q₂

  qA : (A ∷ D) ⊑ Δ
  qA = ⊑-trans (binds-⊒ e₁ (A ∷ D)) q₁

  g : D ⊑ binds e₁ (A ∷ D)
  g = ⊑-trans (there⊑ here⊑) (binds-⊒ e₁ (A ∷ D))

  x : Δ ∋ A
  x = slot qA

  y : Δ ∋ B
  y = slot q₂

  fresh₁ : Only P I → x ∉ I
  fresh₁ o = only-fresh {I = I} qA (only-⊑ {I = I} P (⊑-tail qA) o)

  fresh₂ : Only P I → y ∉ I
  fresh₂ o = only-fresh {I = I} q₂ (only-up {I = I} P g q₁ o)

  only₁ : Only P I → Only qA (I ⊕ x)
  only₁ o = only-⊕ {I = I} qA Z (only-up {I = I} P (there⊑ here⊑) qA o)

  only₂ : Only P I → Only q₂ (I ⊕ y)
  only₂ o =
    only-⊕ {I = I} q₂ Z (only-up {I = I} P (⊑-trans g (there⊑ here⊑)) q₂ o)

lift : ∀ {Σ Γ Δ D A} {I : Inits Δ} (e : M.Exp Σ Γ A)
  → (q : binds e D ⊑ Δ)
  → (ρ : Slots Γ Δ)
  → .(Inited ρ I)
  → .(Only (⊑-trans (binds-⊒ e D) q) I)
  → Exp Σ Δ I A
lift (M.atm a) q ρ ok o = simple (atm (atom ρ ok a))
lift (M.pair a b) q ρ ok o = simple (pair (atom ρ ok a) (atom ρ ok b))
lift (M.callc a b) q ρ ok o = simple (callc (atom ρ ok a) (atom ρ ok b))
lift (M.tuple as) q ρ ok o = simple (tuple (atoms ρ ok as))
lift (M.get i a) q ρ ok o = simple (get i (atom ρ ok a))
lift (M.inl a) q ρ ok o = simple (inl (atom ρ ok a))
lift (M.inr a) q ρ ok o = simple (inr (atom ρ ok a))
lift (M.prim p a b) q ρ ok o = simple (prim p (atom ρ ok a) (atom ρ ok b))
lift (M.fold a) q ρ ok o = simple (fold (atom ρ ok a))
lift (M.unfold a) q ρ ok o = simple (unfold (atom ρ ok a))
lift {I = I} (M.let′ e₁ e₂) q ρ ok o =
  assign x (fresh o) (lift e₁ q₁ ρ ok (only₁ o))
    (lift e₂ q (ext x ρ) (inited-ext {I = I} x ρ ok) (only₂ o))
  where open Let {I = I} e₁ e₂ q
lift {I = I} (M.case a e₁ e₂) q ρ ok o =
  case (atom ρ ok a) x (fresh₁ o) y (fresh₂ o)
    (lift e₁ q₁ (ext x ρ) (inited-ext {I = I} x ρ ok) (only₁ o))
    (lift e₂ q (ext y ρ) (inited-ext {I = I} y ρ ok) (only₂ o))
  where open Case {I = I} a e₁ e₂ q

{- a body: its frame has the slots of the variables it binds, in front
   of those of its parameters -}
lift-body : ∀ {Σ Γ A} → M.Exp Σ Γ A → Body Σ Γ A
lift-body {Γ = Γ} e =
  body (binds e Γ) p (lift e here⊑ (⊑-∋ p) (fill-∈ (⊑-∋ p)) (only-initial p))
  where p = binds-⊒ e Γ

{- the pass, for a whole program -}
lift-program : ∀ {A} → M.Program A → Program A
lift-program (M.program ds e) = program (All-map lift-body ds) (lift-body e)
