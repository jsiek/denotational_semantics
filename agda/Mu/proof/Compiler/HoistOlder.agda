{-

  Hoist makes only references to older definitions, for FPC
  (agda/Mu/), as for the typed pipeline (proof/Compiler/HoistOlder.agda);
  X86μ adequacy needs it (Mu/proof/Adequacy/X86Compiled.agda).

  A GlobalFunμ definition is typed over the whole table, but a graph
  semantics gives each definition the meanings of the older ones only
  (as Untyped/Semantics/Graph/Clos5Iswim.agda does), so it needs that a
  definition refers only to older ones. Older k M: every reference f in
  M has a level (its position from the oldest definition, lvl) below k.
  OlderDefs ds: each definition refers only to the definitions after
  it in the list (the older ones). hoist-older: the definitions of
  every program that hoist produces do.

-}

module Mu.proof.Compiler.HoistOlder where

open import Mu.Language.Type
open import Framework.Membership using (_⊑_; here⊑; there⊑; ⊑-∋; ⊑-trans)
open import Mu.Language.GlobalFun
open import Mu.Compiler.Hoist using (Made; []; _▷_; out; glob; close; hoist)

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; _<_)
open import proof.Framework.Lookup using (lvl-<)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
import Mu.Language.PairClos as S

Older : ∀ {Σ Γ A} → ℕ → Tm Σ Γ A → Set
Olders : ∀ {Σ Γ Δ} → ℕ → All (Tm Σ Γ) Δ → Set
Older k (` x) = ⊤
Older k (fun-ref f) = lvl f < k
Older k (pair L M) = Older k L × Older k M
Older k (callc L M) = Older k L × Older k M
Older k (lit B c) = ⊤
Older k (tuple Ms) = Olders k Ms
Older k (get i M) = Older k M
Older k (inl M) = Older k M
Older k (inr M) = Older k M
Older k (case L M N) = Older k L × Older k M × Older k N
Older k (prim p L M) = Older k L × Older k M
Older k (let′ M N) = Older k M × Older k N
Older k (fold M) = Older k M
Older k (unfold M) = Older k M
Olders k [] = ⊤
Olders k (M ∷ Ms) = Older k M × Olders k Ms

{- each definition refers only to the ones after it (the older ones) -}
OlderDefs : ∀ {Σ ss} → All (Code Σ) ss → Set
OlderDefs [] = ⊤
OlderDefs {ss = _ ∷ ss} (d ∷ ds) = Older (length ss) d × OlderDefs ds

{- a level stays below the length of the list as it grows at the front -}
⊑-lvl< : ∀ {A : Set} {Γ Γ' : List A} {a} (s : Γ ⊑ Γ') (x : Γ ∋ a) → lvl (⊑-∋ s x) < length Γ
⊑-lvl< here⊑ x = lvl-< x
⊑-lvl< (there⊑ s) x = ⊑-lvl< s x

{- a weakening whose references are below k -}
wk-older : ∀ {Σ Σ' Γ A k} (r : ∀ {s} → Σ ∋ s → Σ' ∋ s) → (∀ {s} (f : Σ ∋ s) → lvl (r f) < k)
  → (M : Tm Σ Γ A) → Older k (wk r M)
wks-older : ∀ {Σ Σ' Γ Δ k} (r : ∀ {s} → Σ ∋ s → Σ' ∋ s) → (∀ {s} (f : Σ ∋ s) → lvl (r f) < k)
  → (Ms : All (Tm Σ Γ) Δ) → Olders k (wks r Ms)
wk-older r h (` x) = tt
wk-older r h (fun-ref f) = h f
wk-older r h (pair L M) = wk-older r h L , wk-older r h M
wk-older r h (callc L M) = wk-older r h L , wk-older r h M
wk-older r h (lit B c) = tt
wk-older r h (tuple Ms) = wks-older r h Ms
wk-older r h (get i M) = wk-older r h M
wk-older r h (inl M) = wk-older r h M
wk-older r h (inr M) = wk-older r h M
wk-older r h (case L M N) = wk-older r h L , wk-older r h M , wk-older r h N
wk-older r h (prim p L M) = wk-older r h L , wk-older r h M
wk-older r h (let′ M N) = wk-older r h M , wk-older r h N
wk-older r h (fold M) = wk-older r h M
wk-older r h (unfold M) = wk-older r h M
wks-older r h [] = tt
wks-older r h (M ∷ Ms) = wk-older r h M , wks-older r h Ms

close-older : ∀ {Σ Σ'} (D : Made Σ') (s : Σ' ⊑ Σ) → OlderDefs (close D s)
close-older [] s = tt
close-older (D ▷ N) s =
  wk-older (⊑-∋ s') (⊑-lvl< s') N , close-older D s'
  where
  s' = ⊑-trans (there⊑ here⊑) s

hoist-older : ∀ {A} (M : S.Tm [] A) → OlderDefs (Program.defs (hoist M))
hoist-older M with glob M []
... | out _ D _ = close-older D here⊑
