open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; replicate)

open import AbstractBindingTree
open import NewSyntaxUtil
open import NewSigUtil

module Compiler.Compile.Delay where
  open import Compiler.Lang.Clos3 as Source
  open import Compiler.Lang.Clos4 as Target
    renaming (clear to clear'; bind to bind'; ast to ast';
              AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
              _⦅_⦆ to _⦅_⦆')
              

  delay : (M : Source.AST) → Target.AST
  del-map-args : ∀ {n} → Source.Args (replicate n ■) → Target.Args (replicate n ■)
  delay (` x) = ABT.` x
  delay (clos-op n ⦅ ! (clear (bind (bind (ast N)))) ,, FVs ⦆) = 
    pair-op ABT.⦅ (fun-op ABT.⦅ ! (clear' (bind' (bind' (ast' (delay N))))) ,, Nil ⦆) 
               ,, (tuple n ABT.⦅ del-map-args FVs ⦆) ,, Nil ⦆
  delay (app ⦅ M ,, N ,, Nil ⦆) = 
    app ABT.⦅ (fst-op ABT.⦅ delay M ,, Nil ⦆) ,, 
              (snd-op ABT.⦅ delay M ,, Nil ⦆) ,, 
              delay N ,, Nil ⦆
  delay (lit B k ⦅ Nil ⦆) = lit B k ABT.⦅ Nil ⦆
  delay (tuple n ⦅ Ms ⦆) = tuple n ABT.⦅ del-map-args Ms ⦆
  delay (get n ⦅ M ,, Nil ⦆) = get n ABT.⦅ delay M ,, Nil ⦆
  delay (inl-op ⦅ M ,, Nil ⦆) = inl-op ABT.⦅ delay M ,, Nil ⦆
  delay (inr-op ⦅ M ,, Nil ⦆) = inr-op ABT.⦅ delay M ,, Nil ⦆
  delay (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = case-op ABT.⦅ delay L ,, ⟩ delay M ,, ⟩ delay N ,, Nil ⦆

  del-map-args {zero} Nil = Nil
  del-map-args {suc n} (M ,, args) = delay M ,, del-map-args args
  
