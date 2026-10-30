open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; replicate)

open import Framework.abt.AbstractBindingTree
open import Framework.Syntax.SyntaxUtil
open import Framework.Syntax.SigUtil

module Untyped.Compiler.Split where
  open import Untyped.Language.Clos3 as Source
  open import Untyped.Language.Clos4 as Target
    renaming (clear to clear'; bind to bind'; ast to ast';
              AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
              _⦅_⦆ to _⦅_⦆')
  open import Framework.Syntax.Rename Target.Op Target.sig using (shift)
              

  split : (M : Source.AST) → Target.AST
  del-map-args : ∀ {n} → Source.Args (replicate n ■) → Target.Args (replicate n ■)
  split (` x) = ABT.` x
  split (clos-op n ⦅ ! (clear (bind (bind (ast N)))) ,, FVs ⦆) = 
    pair-op ABT.⦅ (fun-op ABT.⦅ ! (clear' (bind' (bind' (ast' (split N))))) ,, Nil ⦆) 
               ,, (tuple n ABT.⦅ del-map-args FVs ⦆) ,, Nil ⦆
  {- the closure M is computed once and bound by a let, so that both its
     code (fst) and its environment (snd) come from the same value -}
  split (app ⦅ M ,, N ,, Nil ⦆) =
    let-op ABT.⦅ split M ,,
                 ⟩ (app ABT.⦅ (fst-op ABT.⦅ # 0 ,, Nil ⦆) ,,
                              (snd-op ABT.⦅ # 0 ,, Nil ⦆) ,,
                              shift (split N) ,, Nil ⦆) ,, Nil ⦆
  split (lit B k ⦅ Nil ⦆) = lit B k ABT.⦅ Nil ⦆
  split (tuple n ⦅ Ms ⦆) = tuple n ABT.⦅ del-map-args Ms ⦆
  split (get n ⦅ M ,, Nil ⦆) = get n ABT.⦅ split M ,, Nil ⦆
  split (inl-op ⦅ M ,, Nil ⦆) = inl-op ABT.⦅ split M ,, Nil ⦆
  split (inr-op ⦅ M ,, Nil ⦆) = inr-op ABT.⦅ split M ,, Nil ⦆
  split (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = case-op ABT.⦅ split L ,, ⟩ split M ,, ⟩ split N ,, Nil ⦆
  split (prim p ⦅ L ,, M ,, Nil ⦆) = prim p ABT.⦅ split L ,, split M ,, Nil ⦆
  split (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) = let-op ABT.⦅ split M ,, ⟩ split N ,, Nil ⦆

  del-map-args {zero} Nil = Nil
  del-map-args {suc n} (M ,, args) = split M ,, del-map-args args
  
