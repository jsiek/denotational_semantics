{-

  GlobalFunμ: GlobalFun, intrinsically typed, with recursive types. The output
  of globalize (Mu/Compiler/Globalize.agda); as Clos5ᵀ
  (Language/Typed/Clos5.agda), with the types of PairClosμ.

  The code of every function is a global definition. A program has a
  table Σ, the signatures of its definitions (newest first): a
  signature sig Δ A B is the types Δ of the environment, the type A of
  the argument and the type B of the result, and the code of such a
  definition has type code Δ A B. A term is indexed by the table as
  well as by its context: fun-ref f, for f : Σ ∋ sig Δ A B, is the code
  of definition f. Every definition is typed over the whole table
  (globalize makes only references to older ones). A program has the
  type of its main term.

-}

module Mu.Language.GlobalFun where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (Prim)
open import Mu.Language.Type
open import Mu.Framework.AllUtil using (All; []; _∷_)

open import Data.List using (List; []; _∷_)

{- the signature of a definition: environment, argument, result -}
record DSig : Set where
  constructor sig
  field
    env : Ctx
    dom cod : Type

data Tm (Σ : List DSig) (Γ : Ctx) : Type → Set where
  `_ : ∀ {A} → Γ ∋ A → Tm Σ Γ A
  fun-ref : ∀ {Δ A B} → Σ ∋ sig Δ A B → Tm Σ Γ (code Δ A B)
  pair : ∀ {Δ A B} → Tm Σ Γ (code Δ A B) → Tm Σ Γ (tup Δ) → Tm Σ Γ (A ⇒ B)
  callc : ∀ {A B} → Tm Σ Γ (A ⇒ B) → Tm Σ Γ A → Tm Σ Γ B
  lit : (B : Base) → base-rep B → Tm Σ Γ (base B)
  tuple : ∀ {Δ} → All (Tm Σ Γ) Δ → Tm Σ Γ (tup Δ)
  get : ∀ {Δ A} → Δ ∋ A → Tm Σ Γ (tup Δ) → Tm Σ Γ A
  inl : ∀ {A B} → Tm Σ Γ A → Tm Σ Γ (A ⊹ B)
  inr : ∀ {A B} → Tm Σ Γ B → Tm Σ Γ (A ⊹ B)
  case : ∀ {A B C} → Tm Σ Γ (A ⊹ B) → Tm Σ (A ∷ Γ) C → Tm Σ (B ∷ Γ) C → Tm Σ Γ C
  prim : (p : Prim) → Tm Σ Γ (base Int) → Tm Σ Γ (base Int) → Tm Σ Γ (out-ty p)
  let′ : ∀ {A B} → Tm Σ Γ A → Tm Σ (A ∷ Γ) B → Tm Σ Γ B
  fold : ∀ {A} → Tm Σ Γ (unroll A) → Tm Σ Γ (μ A)
  unfold : ∀ {A} → Tm Σ Γ (μ A) → Tm Σ Γ (unroll A)

{- the context of the code of a definition: the argument is variable 0,
   the environment variable 1 -}
Args : DSig → Ctx
Args s = DSig.dom s ∷ tup (DSig.env s) ∷ []

Code : List DSig → DSig → Set
Code Σ s = Tm Σ (Args s) (DSig.cod s)

record Program (A : Type) : Set where
  constructor program
  field
    {table} : List DSig
    defs : All (Code table) table
    main : Tm table [] A

{- a term over a smaller table, over a bigger one -}
wk : ∀ {Σ Σ' Γ A} → (∀ {s} → Σ ∋ s → Σ' ∋ s) → Tm Σ Γ A → Tm Σ' Γ A
wks : ∀ {Σ Σ' Γ Δ} → (∀ {s} → Σ ∋ s → Σ' ∋ s) → All (Tm Σ Γ) Δ → All (Tm Σ' Γ) Δ
wk r (` x) = ` x
wk r (fun-ref f) = fun-ref (r f)
wk r (pair L M) = pair (wk r L) (wk r M)
wk r (callc L M) = callc (wk r L) (wk r M)
wk r (lit B c) = lit B c
wk r (tuple Ms) = tuple (wks r Ms)
wk r (get i M) = get i (wk r M)
wk r (inl M) = inl (wk r M)
wk r (inr M) = inr (wk r M)
wk r (case L M N) = case (wk r L) (wk r M) (wk r N)
wk r (prim p L M) = prim p (wk r L) (wk r M)
wk r (let′ M N) = let′ (wk r M) (wk r N)
wk r (fold M) = fold (wk r M)
wk r (unfold M) = unfold (wk r M)
wks r [] = []
wks r (M ∷ Ms) = wk r M ∷ wks r Ms
