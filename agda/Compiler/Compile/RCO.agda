module Compiler.Compile.RCO where
{-

 The remove-complex-operands pass (Clos5 → Clos5), after Essentials of
 Compilation: every complex operand is bound to a fresh variable by a
 let, so that the result is in monadic normal form (Lang/Mon.agda).

 Evaluation order. The operands of a construct are bound left to right:
 atomize turns the operands M₁ … Mₙ into a chain of lets, one for each
 complex operand, in order, and the atoms A₁ … Aₙ under that chain, where
 Aᵢ is the variable bound to Mᵢ if Mᵢ is complex and Mᵢ itself (shifted)
 if it is an atom. Atoms evaluate without effect, so evaluating the
 chain and then the construct on A₁ … Aₙ evaluates the complex operands
 in the same order as the construct on M₁ … Mₙ; let does not tick the
 clock of the interpreters. Going wrong is preserved too: app checks
 that its operator is code only at the call, after all its operands.

 Shifts. Each let puts what comes after it under one more binder, so
 after binding Mᵢ the operands Mᵢ₊₁ … Mₙ are shifted by one; an atom Mᵢ
 is shifted by the number of lets after it, and the variable for a
 complex Mᵢ is that number (the lets after it bind 0, 1, …). The
 branches of case are shifted by the number of lets in the chain.

-}

open import Compiler.Lang.Clos5
open import Compiler.Lang.Mon
open import Framework.Syntax.Rename Op sig using (rename; rename-args; ext)
open import Framework.Syntax.SyntaxUtil using (_,,_; ⟩_,,_; Nil)

open import Data.List using (List; []; _∷_; length; replicate; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no)

atom? : ∀ M → Dec (Atom M)
atom? (` x) = yes (var x)
atom? (fun-ref k ⦅ nil ⦆) = yes (ref k)
atom? (lit B k ⦅ nil ⦆) = yes (lit B k)
atom? (app ⦅ _ ⦆) = no λ ()
atom? (pair-op ⦅ _ ⦆) = no λ ()
atom? (fst-op ⦅ _ ⦆) = no λ ()
atom? (snd-op ⦅ _ ⦆) = no λ ()
atom? (tuple n ⦅ _ ⦆) = no λ ()
atom? (get i ⦅ _ ⦆) = no λ ()
atom? (inl-op ⦅ _ ⦆) = no λ ()
atom? (inr-op ⦅ _ ⦆) = no λ ()
atom? (case-op ⦅ _ ⦆) = no λ ()
atom? (prim p ⦅ _ ⦆) = no λ ()
atom? (let-op ⦅ _ ⦆) = no λ ()

{- let x₀ = M₀ in let x₁ = M₁ in … N -}
lets : List AST → AST → AST
lets [] N = N
lets (M ∷ Ms) N = let-op ⦅ M ,, ⟩ lets Ms N ,, Nil ⦆

{- the right-hand sides of a chain of lets, and n atoms under it -}
record Bound (n : ℕ) : Set where
  constructor bound
  field
    binds : List AST
    atoms : Args (replicate n ■)
open Bound public

{- an atom A for the first operand, in front of the atoms of the rest -}
keep : ∀ {n} → AST → Bound n → Bound (suc n)
keep A (bound bs As) = bound bs (rename (length bs +_) A ,, As)

{- a let for the complex first operand M, in front of the lets of the rest -}
bind-let : ∀ {n} → AST → Bound n → Bound (suc n)
bind-let M (bound bs As) = bound (M ∷ bs) (` length bs ,, As)

atomize : ∀ {n} → Args (replicate n ■) → Bound n
atomize {zero} Nil = bound [] Nil
atomize {suc n} (M ,, Ms) with atom? M
... | yes _ = keep M (atomize Ms)
... | no _ = bind-let M (atomize (rename-args suc Ms))

{- f k on the atoms for the operands Ms, under the k lets for the
   complex ones -}
lift : ∀ {n} → (ℕ → Args (replicate n ■) → AST) → Args (replicate n ■) → AST
lift f Ms = lets (binds (atomize Ms)) (f (length (binds (atomize Ms))) (atoms (atomize Ms)))

{- case on an atom, with the branches M and N under k more lets -}
case-on : AST → AST → ℕ → Args (■ ∷ []) → AST
case-on M N k (A ,, Nil) =
  case-op ⦅ A ,, ⟩ rename (ext (k +_)) M ,, ⟩ rename (ext (k +_)) N ,, Nil ⦆

rco : AST → AST
rco-args : ∀ {n} → Args (replicate n ■) → Args (replicate n ■)

rco (` x) = ` x
rco (fun-ref k ⦅ Nil ⦆) = fun-ref k ⦅ Nil ⦆
rco (app ⦅ Ms ⦆) = lift {3} (λ _ → app ⦅_⦆) (rco-args Ms)
rco (lit B k ⦅ Nil ⦆) = lit B k ⦅ Nil ⦆
rco (pair-op ⦅ Ms ⦆) = lift {2} (λ _ → pair-op ⦅_⦆) (rco-args Ms)
rco (fst-op ⦅ Ms ⦆) = lift {1} (λ _ → fst-op ⦅_⦆) (rco-args Ms)
rco (snd-op ⦅ Ms ⦆) = lift {1} (λ _ → snd-op ⦅_⦆) (rco-args Ms)
rco (tuple n ⦅ Ms ⦆) = lift {n} (λ _ → tuple n ⦅_⦆) (rco-args Ms)
rco (get i ⦅ Ms ⦆) = lift {1} (λ _ → get i ⦅_⦆) (rco-args Ms)
rco (inl-op ⦅ Ms ⦆) = lift {1} (λ _ → inl-op ⦅_⦆) (rco-args Ms)
rco (inr-op ⦅ Ms ⦆) = lift {1} (λ _ → inr-op ⦅_⦆) (rco-args Ms)
rco (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = lift (case-on (rco M) (rco N)) (rco L ,, Nil)
rco (prim p ⦅ Ms ⦆) = lift {2} (λ _ → prim p ⦅_⦆) (rco-args Ms)
rco (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = let-op ⦅ rco M ,, ⟩ rco N ,, Nil ⦆

rco-args {zero} Nil = Nil
rco-args {suc n} (M ,, Ms) = rco M ,, rco-args Ms

{- the pass, for a whole program -}
rco-program : Program → Program
rco-program (program ds M) = program (map rco ds) (rco M)

{- The result is in monadic normal form ---------------------------------------}

Mons : ∀ {n} → Args (replicate n ■) → Set
Mons {zero} Nil = ⊤
Mons {suc n} (M ,, Ms) = Mon M × Mons Ms

mons-rename : ∀ r {n} (Ms : Args (replicate n ■)) → Mons Ms → Mons (rename-args r Ms)
mons-rename r {zero} Nil tt = tt
mons-rename r {suc n} (M ,, Ms) ⟨ m , ms ⟩ = ⟨ mon-rename r m , mons-rename r Ms ms ⟩

{- the lets bind monadic terms, and the atoms are atoms -}
Good : ∀ {n} → Bound n → Set
Good B = All Mon (binds B) × Atoms (atoms B)

atomize-mon : ∀ {n} (Ms : Args (replicate n ■)) → Mons Ms → Good (atomize Ms)
atomize-mon {zero} Nil tt = ⟨ [] , [] ⟩
atomize-mon {suc n} (M ,, Ms) ⟨ m , ms ⟩ with atom? M
... | yes a = keep-good (atomize-mon Ms ms)
  where keep-good : ∀ {B : Bound n} → Good B → Good (keep M B)
        keep-good ⟨ bs , as ⟩ = ⟨ bs , atom-rename _ a ∷ as ⟩
... | no _ = let-good (atomize-mon (rename-args suc Ms) (mons-rename suc Ms ms))
  where let-good : ∀ {B : Bound n} → Good B → Good (bind-let M B)
        let-good ⟨ bs , as ⟩ = ⟨ m ∷ bs , var _ ∷ as ⟩

lets-mon : ∀ {bs N} → All Mon bs → Mon N → Mon (lets bs N)
lets-mon [] n = n
lets-mon (m ∷ ms) n = let′ m (lets-mon ms n)

lift-mon : ∀ {n} {f : ℕ → Args (replicate n ■) → AST}
  → (∀ k {As} → Atoms As → Mon (f k As))
  → (Ms : Args (replicate n ■)) → Mons Ms → Mon (lift f Ms)
lift-mon mf Ms ms with atomize-mon Ms ms
... | ⟨ bs , as ⟩ = lets-mon bs (mf _ as)

case-on-mon : ∀ {M N} k {As} → Mon M → Mon N → Atoms As → Mon (case-on M N k As)
case-on-mon k m n (a ∷ []) = case a (mon-rename _ m) (mon-rename _ n)

rco-mon : ∀ M → Mon (rco M)
rco-args-mon : ∀ {n} (Ms : Args (replicate n ■)) → Mons (rco-args Ms)

rco-mon (` x) = atom (var x)
rco-mon (fun-ref k ⦅ Nil ⦆) = atom (ref k)
rco-mon (app ⦅ Ms ⦆) = lift-mon (λ _ → app) _ (rco-args-mon Ms)
rco-mon (lit B k ⦅ Nil ⦆) = atom (lit B k)
rco-mon (pair-op ⦅ Ms ⦆) = lift-mon (λ _ → pair) _ (rco-args-mon Ms)
rco-mon (fst-op ⦅ Ms ⦆) = lift-mon (λ _ → fst) _ (rco-args-mon Ms)
rco-mon (snd-op ⦅ Ms ⦆) = lift-mon (λ _ → snd) _ (rco-args-mon Ms)
rco-mon (tuple n ⦅ Ms ⦆) = lift-mon (λ _ → tuple) _ (rco-args-mon Ms)
rco-mon (get i ⦅ Ms ⦆) = lift-mon (λ _ → get) _ (rco-args-mon Ms)
rco-mon (inl-op ⦅ Ms ⦆) = lift-mon (λ _ → inl) _ (rco-args-mon Ms)
rco-mon (inr-op ⦅ Ms ⦆) = lift-mon (λ _ → inr) _ (rco-args-mon Ms)
rco-mon (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) =
  lift-mon (λ k → case-on-mon k (rco-mon M) (rco-mon N)) _ ⟨ rco-mon L , tt ⟩
rco-mon (prim p ⦅ Ms ⦆) = lift-mon (λ _ → prim) _ (rco-args-mon Ms)
rco-mon (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = let′ (rco-mon M) (rco-mon N)

rco-args-mon {zero} Nil = tt
rco-args-mon {suc n} (M ,, Ms) = ⟨ rco-mon M , rco-args-mon Ms ⟩

rco-program-mon : ∀ P → MonProgram (rco-program P)
rco-program-mon (program ds M) = ⟨ defs-mon ds , rco-mon M ⟩
  where defs-mon : ∀ ds → All Mon (map rco ds)
        defs-mon [] = []
        defs-mon (D ∷ ds) = rco-mon D ∷ defs-mon ds
