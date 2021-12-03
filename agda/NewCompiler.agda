
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; replicate)

open import AbstractBindingTree
open import NewSyntaxUtil
open import NewSigUtil

module NewCompiler where
  open import NewISWIM 
    {- renaming (AST to AST0; cons to cons0; nil to nil0; ast to ast0) -}
  open import NewClos1 
   {- renaming (AST to AST1; cons to cons1; nil to nil1; ast to ast1) -}
  open import NewClos2 
   {- renaming (AST to NewClos2.AST; cons to cons2; nil to nil2; ast to NewClos2.AST) -}
  open import NewClos3 
   {- renaming (AST to NewClos3.AST; cons to cons3; nil to nil3; ast to NewClos3.AST) -}
  open import NewClos4 
    renaming (clear to clear4; bind to bind4; ast to ast4)
    {- renaming (AST to NewClos4.AST; cons to cons4; nil to nil4; ast to NewClos4.AST) -}

  var-range-desc : ∀ {Op sig} (m : ℕ) → AbstractBindingTree.Args Op sig (replicate m ■)
  var-range-desc zero = Nil
  var-range-desc (suc m) = (ABT.` m) ,, var-range-desc m

  annotate : (M : NewISWIM.AST) → NewClos1.AST
  annotate (` x) = NewClos1.AST.` x
  annotate (lam ABT.⦅ ⟩ N ,, Nil ⦆) = 
    clos-op m ABT.⦅ ⟩ N' ,, var-range-desc m ⦆
      where
      N' : NewClos1.AST
      N' = annotate N
      m : ℕ
      m = NewClos1.ASTMod.max-var N'
  annotate (app ABT.⦅ M ,, N ,, Nil ⦆) = 
    app ABT.⦅ (annotate M) ,, (annotate M) ,, Nil ⦆
  annotate (lit B k ABT.⦅ Nil ⦆) = lit B k ABT.⦅ Nil ⦆
  annotate (pair-op ABT.⦅ M ,, N ,, Nil ⦆) = 
    pair-op ABT.⦅ annotate M ,, annotate N ,, Nil ⦆
  annotate (fst-op ABT.⦅ M ,, Nil ⦆) = fst-op ABT.⦅  annotate M ,, Nil ⦆
  annotate (snd-op ABT.⦅ N ,, Nil ⦆) = snd-op ABT.⦅ annotate N ,, Nil ⦆
  annotate (tuple n ABT.⦅ Ms ⦆) = tuple n ABT.⦅ ann-map-args Ms ⦆
    where
    ann-map-arg : ∀ {b} → NewISWIM.Arg b → NewClos1.Arg b
    ann-map-arg (ast x) = NewClos1.ast (annotate x)
    ann-map-arg (bind arg) = NewClos1.bind (ann-map-arg arg)
    ann-map-arg (clear arg) = NewClos1.clear (ann-map-arg arg)
    ann-map-args : ∀ {bs} → NewISWIM.Args bs → NewClos1.Args bs
    ann-map-args Nil = Nil
    ann-map-args (! x ,, args) = ! ann-map-arg x ,, ann-map-args args
  annotate (get n ABT.⦅ M ,, Nil ⦆) = get n ABT.⦅ annotate M ,, Nil ⦆
  annotate (inl-op ABT.⦅ M ,, Nil ⦆) = inl-op ABT.⦅ annotate M ,, Nil ⦆
  annotate (inr-op ABT.⦅ M ,, Nil ⦆) = inr-op ABT.⦅ annotate M ,, Nil ⦆
  annotate (case-op ABT.⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = 
    case-op ABT.⦅ annotate L ,, ⟩ annotate M ,, ⟩ annotate N ,, Nil ⦆

  data annotated : (M : NewClos1.AST) → Set where
    temp : ∀ M → annotated M

  
  enclose : (M : NewClos1.AST) → NewClos2.AST
  enclose (` x) = ABT.` x
  enclose (clos-op n ABT.⦅ ! (bind (ast N)) ,, FVS ⦆) = 
    clos-op n ABT.⦅ ! NewClos2.clear (bind-n n (NewClos2.bind 
                      (NewClos2.ast (enclose N)))) 
                    ,, enc-map-args FVS ⦆
    where
    enc-map-arg : ∀ {b} → NewClos1.Arg b → NewClos2.Arg b
    enc-map-arg (ast x) = NewClos2.ast (enclose x)
    enc-map-arg (bind arg) = NewClos2.bind (enc-map-arg arg)
    enc-map-arg (clear arg) = NewClos2.clear (enc-map-arg arg)
    enc-map-args : ∀ {bs} → NewClos1.Args bs → NewClos2.Args bs
    enc-map-args Nil = Nil
    enc-map-args (! x ,, args) = ! enc-map-arg x ,, enc-map-args args
  enclose (app ABT.⦅ M ,, N ,, Nil ⦆) = 
    app ABT.⦅ (enclose M) ,, (enclose M) ,, Nil ⦆
  enclose (lit B k ABT.⦅ Nil ⦆) = lit B k ABT.⦅ Nil ⦆
  enclose (pair-op ABT.⦅ M ,, N ,, Nil ⦆) = 
    pair-op ABT.⦅ enclose M ,, enclose N ,, Nil ⦆
  enclose (fst-op ABT.⦅ M ,, Nil ⦆) = fst-op ABT.⦅  enclose M ,, Nil ⦆
  enclose (snd-op ABT.⦅ N ,, Nil ⦆) = snd-op ABT.⦅ enclose N ,, Nil ⦆
  enclose (tuple n ABT.⦅ Ms ⦆) = tuple n ABT.⦅ enc-map-args Ms ⦆
    where
    enc-map-arg : ∀ {b} → NewClos1.Arg b → NewClos2.Arg b
    enc-map-arg (ast x) = NewClos2.ast (enclose x)
    enc-map-arg (bind arg) = NewClos2.bind (enc-map-arg arg)
    enc-map-arg (clear arg) = NewClos2.clear (enc-map-arg arg)
    enc-map-args : ∀ {bs} → NewClos1.Args bs → NewClos2.Args bs
    enc-map-args Nil = Nil
    enc-map-args (! x ,, args) = ! enc-map-arg x ,, enc-map-args args
  enclose (get n ABT.⦅ M ,, Nil ⦆) = get n ABT.⦅ enclose M ,, Nil ⦆
  enclose (inl-op ABT.⦅ M ,, Nil ⦆) = inl-op ABT.⦅ enclose M ,, Nil ⦆
  enclose (inr-op ABT.⦅ M ,, Nil ⦆) = inr-op ABT.⦅ enclose M ,, Nil ⦆
  enclose (case-op ABT.⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = 
    case-op ABT.⦅ enclose L ,, ⟩ enclose M ,, ⟩ enclose N ,, Nil ⦆

  optimize : (M : NewClos2.AST) → NewClos2.AST
  optimize M = {!   !}

  concretize : (M : NewClos2.AST) → NewClos3.AST
  concretize (` x) = ABT.` x
  concretize (clos-op n ⦅ x ⦆) = clos-op n ABT.⦅ {!   !} ⦆
  concretize (app ⦅ x ⦆) = {!   !}
  concretize (lit B k ⦅ x ⦆) = {!   !}
  concretize (pair-op ⦅ x ⦆) = {!   !}
  concretize (fst-op ⦅ x ⦆) = {!   !}
  concretize (snd-op ⦅ x ⦆) = {!   !}
  concretize (tuple n ⦅ x ⦆) = {!   !}
  concretize (get n ⦅ x ⦆) = {!   !}
  concretize (inl-op ⦅ x ⦆) = {!   !}
  concretize (inr-op ⦅ x ⦆) = {!   !}
  concretize (case-op ⦅ x ⦆) = {!   !}

  delay : (M : NewClos3.AST) → NewClos4.AST
  del-map-args : ∀ {n} → NewClos3.Args (replicate n ■) → NewClos4.Args (replicate n ■)
  delay (` x) = ABT.` x
  delay (clos-op n ⦅ ! (clear (bind (bind (ast N)))) ,, FVs ⦆) = 
    pair-op ABT.⦅ (fun-op ABT.⦅ ! (clear4 (bind4 (bind4 (ast4 (delay N))))) ,, Nil ⦆) 
               ,, (tuple n ABT.⦅ del-map-args FVs ⦆) ,, Nil ⦆
  delay (app ⦅ M ,, N ,, Nil ⦆) = 
    app ABT.⦅ (fst-op ABT.⦅ delay M ,, Nil ⦆) ,, 
              (snd-op ABT.⦅ delay M ,, Nil ⦆) ,, 
              delay N ,, Nil ⦆
  delay (lit B k ⦅ Nil ⦆) = lit B k ABT.⦅ Nil ⦆
  delay (pair-op ⦅ M ,, N ,, Nil ⦆) = pair-op ABT.⦅ delay M ,, delay N ,, Nil ⦆
  delay (fst-op ⦅ M ,, Nil ⦆) = fst-op ABT.⦅ delay M ,, Nil ⦆
  delay (snd-op ⦅ M ,, Nil ⦆) = snd-op ABT.⦅ delay M ,, Nil ⦆
  delay (tuple n ⦅ Ms ⦆) = tuple n ABT.⦅ del-map-args Ms ⦆
  delay (get n ⦅ M ,, Nil ⦆) = get n ABT.⦅ delay M ,, Nil ⦆
  delay (inl-op ⦅ M ,, Nil ⦆) = inl-op ABT.⦅ delay M ,, Nil ⦆
  delay (inr-op ⦅ M ,, Nil ⦆) = inr-op ABT.⦅ delay M ,, Nil ⦆
  delay (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = case-op ABT.⦅ delay L ,, ⟩ delay M ,, ⟩ delay N ,, Nil ⦆

  del-map-args {zero} Nil = Nil
  del-map-args {suc n} (M ,, args) = delay M ,, del-map-args args
  
{-

  enclose : (M : NewClos1.AST) → NewClos2.AST
  enclose (` x) = ABT.` x
  enclose (clos-op n ABT.⦅ ! (bind (ast N)) ,, FVS ⦆) = 
    clos-op n ABT.⦅ ! NewClos2.clear (bind-n n (NewClos2.bind 
                      (NewClos2.ast (enclose N)))) 
                    ,, enc-map-args FVS ⦆
    where
    enc-map-arg : ∀ {b} → NewClos1.Arg b → NewClos2.Arg b
    enc-map-arg (ast x) = NewClos2.ast (enclose x)
    enc-map-arg (bind arg) = NewClos2.bind (enc-map-arg arg)
    enc-map-arg (clear arg) = NewClos2.clear (enc-map-arg arg)
    enc-map-args : ∀ {bs} → NewClos1.Args bs → NewClos2.Args bs
    enc-map-args Nil = Nil
    enc-map-args (! x ,, args) = ! enc-map-arg x ,, enc-map-args args
  enclose (app ABT.⦅ M ,, N ,, Nil ⦆) = 
    app ABT.⦅ (enclose M) ,, (enclose M) ,, Nil ⦆
  enclose (lit B k ABT.⦅ Nil ⦆) = lit B k ABT.⦅ Nil ⦆
  enclose (pair-op ABT.⦅ M ,, N ,, Nil ⦆) = 
    pair-op ABT.⦅ enclose M ,, enclose N ,, Nil ⦆
  enclose (fst-op ABT.⦅ M ,, Nil ⦆) = fst-op ABT.⦅  enclose M ,, Nil ⦆
  enclose (snd-op ABT.⦅ N ,, Nil ⦆) = snd-op ABT.⦅ enclose N ,, Nil ⦆
  enclose (tuple n ABT.⦅ Ms ⦆) = tuple n ABT.⦅ enc-map-args Ms ⦆
    where
    enc-map-arg : ∀ {b} → NewClos1.Arg b → NewClos2.Arg b
    enc-map-arg (ast x) = NewClos2.ast (enclose x)
    enc-map-arg (bind arg) = NewClos2.bind (enc-map-arg arg)
    enc-map-arg (clear arg) = NewClos2.clear (enc-map-arg arg)
    enc-map-args : ∀ {bs} → NewClos1.Args bs → NewClos2.Args bs
    enc-map-args Nil = Nil
    enc-map-args (! x ,, args) = ! enc-map-arg x ,, enc-map-args args
  enclose (get n ABT.⦅ M ,, Nil ⦆) = get n ABT.⦅ enclose M ,, Nil ⦆
  enclose (inl-op ABT.⦅ M ,, Nil ⦆) = inl-op ABT.⦅ enclose M ,, Nil ⦆
  enclose (inr-op ABT.⦅ M ,, Nil ⦆) = inr-op ABT.⦅ enclose M ,, Nil ⦆
  enclose (case-op ABT.⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) = 
    case-op ABT.⦅ enclose L ,, ⟩ enclose M ,, ⟩ enclose N ,, Nil ⦆

-}


