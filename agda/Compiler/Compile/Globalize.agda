open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

open import NewSyntaxUtil
open import NewSigUtil

module Compiler.Compile.Globalize where
  {-
   The globalize pass (Clos4 → Clos5): the code of every function becomes
   a global definition, as in the hoisting step of
   siek.blogspot.com/2012/07/essence-of-closure-conversion.html.

   In Clos4 the code of a function, fun-op ⦅ ∁ (X. Y. N) ⦆, is already
   closed (∁), so it can be moved to the top level as is. The pass threads
   the list of definitions made so far (newest first) through the term,
   from left to right. For fun-op it first globalizes the body N, so the
   functions nested in N become definitions first, then adds N as a new
   definition and replaces the code by a reference to it.
  -}
  open import Compiler.Lang.Clos4 as Source
  open import Compiler.Lang.Clos5 as Target
    renaming (clear to clear'; bind to bind'; ast to ast';
              AST to AST'; Arg to Arg'; Args to Args'; `_ to #_;
              _⦅_⦆ to _⦅_⦆'; nil to nil'; cons to cons')

  {- the definitions made so far, newest first -}
  Defs : Set
  Defs = List AST'

  glob : AST → Defs → AST' × Defs
  glob-arg : ∀ {b} → Arg b → Defs → Arg' b × Defs
  glob-args : ∀ {bs} → Args bs → Defs → Args' bs × Defs

  glob (` x) ds = ⟨ # x , ds ⟩
  glob (fun-op ⦅ cons (clear (bind (bind (ast N)))) nil ⦆) ds =
    ⟨ fun-ref (length (proj₂ (glob N ds))) ⦅ nil' ⦆'
    , proj₁ (glob N ds) ∷ proj₂ (glob N ds) ⟩
  glob (app ⦅ args ⦆) ds = ⟨ app ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩
  glob (lit B k ⦅ args ⦆) ds =
    ⟨ lit B k ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩
  glob (pair-op ⦅ args ⦆) ds =
    ⟨ pair-op ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩
  glob (fst-op ⦅ args ⦆) ds =
    ⟨ fst-op ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩
  glob (snd-op ⦅ args ⦆) ds =
    ⟨ snd-op ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩
  glob (tuple n ⦅ args ⦆) ds =
    ⟨ tuple n ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩
  glob (get i ⦅ args ⦆) ds =
    ⟨ get i ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩
  glob (inl-op ⦅ args ⦆) ds =
    ⟨ inl-op ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩
  glob (inr-op ⦅ args ⦆) ds =
    ⟨ inr-op ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩
  glob (case-op ⦅ args ⦆) ds =
    ⟨ case-op ⦅ proj₁ (glob-args args ds) ⦆' , proj₂ (glob-args args ds) ⟩

  glob-arg (ast M) ds = ⟨ ast' (proj₁ (glob M ds)) , proj₂ (glob M ds) ⟩
  glob-arg (bind a) ds = ⟨ bind' (proj₁ (glob-arg a ds)) , proj₂ (glob-arg a ds) ⟩
  glob-arg (clear a) ds = ⟨ clear' (proj₁ (glob-arg a ds)) , proj₂ (glob-arg a ds) ⟩

  glob-args nil ds = ⟨ nil' , ds ⟩
  glob-args (cons a args) ds =
    ⟨ cons' (proj₁ (glob-arg a ds)) (proj₁ (glob-args args (proj₂ (glob-arg a ds))))
    , proj₂ (glob-args args (proj₂ (glob-arg a ds))) ⟩

  {- the pass, for a whole program -}
  globalize : AST → Program
  globalize M = program (proj₂ (glob M [])) (proj₁ (glob M []))
