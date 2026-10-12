{-

  A counterexample: explicate control does not preserve denotations (≃)
  in the graph model, for the semantics of Imp (Sem/Imp.agda) and CFG
  (Sem/CFG.agda).

  The Clos5 program

    def 0 = λ fv. λ Y. let y = case Y of inl _ ⇒ ⟨1,1⟩ | inr _ ⇒ ⟨2,2⟩ in
                       let a = fst y in let b = snd y in ⟨a,b⟩
    main  = ref 0

  is monadic, and P below is its image under lift locals. Explicate turns
  the case on the right of the assignment into a case whose branches jump
  to a join block. Λ admits an inconsistent argument such as
  Y = {left ν, right ν}; then y, in Clos5 and in Imp alike, is bound to
  finite subsets of {⟨1,1⟩, ⟨2,2⟩} that mix the two branches (⋆ ⟨ Λ … , 𝒞 … ⟩),
  so ⟨1,2⟩ is a result of the function; in CFG each branch reaches the
  join on its own (𝒞 ⟨ … , Λ … ⟩, the commuting conversion), and ⟨1,2⟩ is
  not. So the main of P denotes an entry that the main of explicate P
  does not.

-}

open import SetsAsPredicates
open import Compiler.Model.Graph.Domain.ISWIM.Domain
open import Compiler.Model.Graph.Domain.ISWIM.Ops
open import Primitives using (Int)
open import Compiler.Lang.Imp as I using (Simple; simple; var; lit; fun-ref; atm; fst; snd; assign)
import Compiler.Lang.CFG as C
open import Compiler.Compile.Explicate using (explicate)
import Compiler.Model.Graph.Sem.Imp as SI
import Compiler.Model.Graph.Sem.CFG as SC

open import Data.Integer using (+_)
import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

module Compiler.Model.Graph.Correctness.ExplicateCounterExample where

n : Data.Nat.ℕ → I.Atm
n k = lit Int (+ k)

c : Data.Nat.ℕ → Value
c k = const {Int} (+ k)

e : I.Exp
e = assign 2 (I.case (var 1) 2 (simple (I.pair (n 1) (n 1))) (simple (I.pair (n 2) (n 2))))
      (assign 3 (simple (fst (var 2))) (assign 4 (simple (snd (var 2)))
        (simple (I.pair (var 3) (var 4)))))

P : I.Program
P = I.program (I.body 5 e ∷ []) (I.body 0 (simple (atm (fun-ref 0))))

W : List Value
W = left ν ∷ right ν ∷ []

{- the entry ν ↦ (W ↦ ⟨1,2⟩) -}
w : Value
w = (ν ∷ []) ↦ (W ↦ ⦅ c 1 , c 2 ⦆)

ℬ-refl : ∀ k → c k ∈ ℬ Int (+ k) _
ℬ-refl k = ⟨ refl , refl ⟩

in-Imp : w ∈ SI.⟦ P ⟧ₚ
in-Imp = ⟨ ⟨ ⟨ V , ⟨ ⟨ E∈ , (λ ()) ⟩ , ⟨ V⊆ , (λ ()) ⟩ ⟩ ⟩ , (λ ()) ⟩ , (λ ()) ⟩
  where
  V = ⦅ c 1 , c 1 ⦆ ∷ ⦅ c 2 , c 2 ⦆ ∷ []
  V⊆ : mem V ⊆ _
  V⊆ _ (here refl) = inj₁ ⟨ ν , ⟨ [] , ⟨ (λ { _ (here refl) → here refl ; _ (there ()) }) , ⟨ ℬ-refl 1 , ℬ-refl 1 ⟩ ⟩ ⟩ ⟩
  V⊆ _ (there (here refl)) =
    inj₂ ⟨ ν , ⟨ [] , ⟨ (λ { _ (here refl) → there (here refl) ; _ (there ()) }) , ⟨ ℬ-refl 2 , ℬ-refl 2 ⟩ ⟩ ⟩ ⟩
  E₂∈ = ⟨ c 2 ∷ [] , ⟨ ⟨ ⟨ here refl , here refl ⟩ , (λ ()) ⟩
                     , ⟨ (λ { _ (here refl) → ⟨ c 2 , there (here refl) ⟩ ; _ (there ()) }) , (λ ()) ⟩ ⟩ ⟩
  E∈ = ⟨ c 1 ∷ [] , ⟨ ⟨ E₂∈ , (λ ()) ⟩ , ⟨ (λ { _ (here refl) → ⟨ c 1 , here refl ⟩ ; _ (there ()) }) , (λ ()) ⟩ ⟩ ⟩

not-in-CFG : ¬ (w ∈ SC.⟦ explicate P ⟧ₚ)
not-in-CFG ⟨ ⟨ inj₁ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ X , ⟨ ⟨ ⟨ A , ⟨ ⟨ ⟨ B , ⟨ ⟨ ⟨ a∈ , b∈ ⟩ , _ ⟩ , ⟨ B⊆ , _ ⟩ ⟩ ⟩ , _ ⟩ , ⟨ A⊆ , _ ⟩ ⟩ ⟩ , _ ⟩ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ , _ ⟩ , _ ⟩
  with B⊆ _ b∈
... | ⟨ u , ub∈ ⟩ with X⊆ _ ub∈
... | ⟨ _ , ⟨ refl , () ⟩ ⟩
not-in-CFG ⟨ ⟨ inj₂ ⟨ _ , ⟨ _ , ⟨ _ , ⟨ X , ⟨ ⟨ ⟨ A , ⟨ ⟨ ⟨ B , ⟨ ⟨ ⟨ a∈ , b∈ ⟩ , _ ⟩ , ⟨ B⊆ , _ ⟩ ⟩ ⟩ , _ ⟩ , ⟨ A⊆ , _ ⟩ ⟩ ⟩ , _ ⟩ , ⟨ X⊆ , _ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ , _ ⟩ , _ ⟩
  with A⊆ _ a∈
... | ⟨ u , au∈ ⟩ with X⊆ _ au∈
... | ⟨ ⟨ refl , () ⟩ , _ ⟩

explicate-not-≃ : ¬ (SC.⟦ explicate P ⟧ₚ ≃ SI.⟦ P ⟧ₚ)
explicate-not-≃ eq = not-in-CFG (proj₂ eq w in-Imp)
