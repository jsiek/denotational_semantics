{-

  Select instructions (Compiler/Select.agda) emits the instructions of
  select into untyped X86 (Compiler/SelectX86.agda), once the types are
  erased (Language/Typed/X86Erase.agda; Theorems/Erasure.agda): the
  same blocks, the same frame sizes, the same
  code for every statement, chk being the test of project and the move.

-}

module proof.Compiler.SelectErase where

open import Language.Typed.Type
open import Framework.Membership using (_⊑_; here⊑)
import Language.Typed.CFG as C
open C using (Tail; return; seq; goto; case; _▷_)
import Language.Typed.Imp as I
import Language.Prim
import Data.Nat
open import Language.Typed.X86
open import Language.Typed.X86Erase
import Language.X86 as L
import Compiler.SelectX86 as U
import Compiler.Select as T
open T using (Out; ret; to)

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.All using (All; []; _∷_) renaming (map to All-map)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Maybe using (nothing)
open import Data.Bool using (false)
open import Data.Vec using (Vec; []; _∷_; toList; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; trans)

{- where the value of a simple expression goes, in X86 -}
out : ∀ {n Δ A Δ''} → Out n Δ A Δ'' → L.Loc
out ret = L.reg L.rax
out (to {Δ'} p _) = L.var (length Δ')

dst-e : ∀ {n Δ A Δ''} (o : Out n Δ A Δ'') {Γ O F} → eDst (T.dst o {Γ} {O} {F}) ≡ out o
dst-e ret = refl
dst-e (to p _) = refl

atms-e : ∀ {Σ Δ m Γ O F} (as : Vec (Atm Σ Δ Any) m)
  → toList (map eArg (T.atms {Γ = Γ} {O} {F} as)) ≡ toList (map U.select-atm as)
atms-e [] = refl
atms-e (a ∷ as) = cong (U.select-atm a ∷_) (atms-e as)

block≡ : ∀ {xs ys : List L.Instr} {b b' : L.Block} → xs ≡ ys → b ≡ b'
  → L.block (xs ++ L.Block.instrs b) (L.Block.jump b) ≡ L.block (ys ++ L.Block.instrs b') (L.Block.jump b')
block≡ refl refl = refl

sel-e : ∀ {Σ n Bs Δ A Δ''} (s : I.Simple Σ Δ A) (o : Out n Δ A Δ'') (k : ∀ {Γ O F} → Seq Σ n Bs (T.after o Γ O F))
  (b : L.Block) → (∀ {Γ O F} → eSeq (k {Γ} {O} {F}) ≡ b)
  → ∀ {Γ O F} → eSeq (T.sel s o k {Γ} {O} {F}) ≡ L.block (U.select-simple s (out o) ++ L.Block.instrs b) (L.Block.jump b)
sel-e (I.atm a) o k b hk = block≡ (cong (λ d → L.movq (U.select-atm a) d ∷ []) (dst-e o)) hk
sel-e (I.pack c e) o k b hk = block≡ (cong (λ d → L.alloc L.pair (U.select-atm c ∷ U.select-atm e ∷ []) d ∷ []) (dst-e o)) hk
sel-e {Δ = Δ} (I.callc (I.var x) a) o k b hk =
  block≡ (cong (λ d → L.load L.fst (L.loc (L.var (lvl x))) (L.reg L.rax) ∷ L.load L.snd (L.loc (L.var (lvl x))) (L.reg L.rdi)
                   ∷ L.movq (U.select-atm a) (L.reg L.rsi) ∷ L.callq (L.loc (L.reg L.rax)) ∷ L.movq (L.loc (L.reg L.rax)) d ∷ [])
              (dst-e o {St.rs (returned Δ)} {nothing} {false})) (hk {St.rs (returned Δ)} {nothing} {false})
sel-e (I.tuple as) o k b hk = block≡ (cong₂ (λ l d → L.alloc L.tuple l d ∷ []) (atms-e as) (dst-e o)) hk
sel-e (I.get i a) o k b hk = block≡ (cong (λ d → L.load (L.get i) (U.select-atm a) d ∷ []) (dst-e o)) hk
sel-e (I.inl a) o k b hk = block≡ (cong (λ d → L.alloc L.inl (U.select-atm a ∷ []) d ∷ []) (dst-e o)) hk
sel-e (I.inr a) o k b hk = block≡ (cong (λ d → L.alloc L.inr (U.select-atm a ∷ []) d ∷ []) (dst-e o)) hk
sel-e (I.prim Language.Prim.sub a c) o k b hk =
  block≡ (cong (λ d → L.movq (U.select-atm a) (L.reg L.rax) ∷ L.subq (U.select-atm c) (L.reg L.rax) ∷ L.movq (L.loc (L.reg L.rax)) d ∷ [])
            (dst-e o)) hk
sel-e (I.prim Language.Prim.eq a c) o k b hk =
  block≡ (cong (λ d → L.cmpq (U.select-atm c) (U.select-atm a) ∷ L.sete d ∷ []) (dst-e o)) hk
sel-e (I.inject G a) o k b hk = block≡ (cong (λ d → L.movq (U.select-atm a) d ∷ []) (dst-e o)) hk
sel-e (I.project t (I.var x)) o k b hk {Γ} {O} {F} =
  block≡ (cong (λ d → U.check t (L.loc (L.var (lvl x))) ++ L.movq (L.loc (L.var (lvl x))) d ∷ [])
              (dst-e o {Γ [ rax ↦ nothing ]} {O} {false})) (hk {Γ [ rax ↦ nothing ]} {O} {false})

depth-e : ∀ {Σ Bs Δ} (t : Tail Σ Bs Δ) → T.depth t ≡ U.depth t
depth-e (return s) = refl
depth-e {Δ = Δ} (seq p s t) = cong (length Δ ⊔_) (depth-e t)
depth-e (goto l) = refl
depth-e (case a p l₁ l₂) = refl

bdepth-e : ∀ {Σ Bs} (bs : C.Blocks Σ Bs) → T.blocks-depth bs ≡ U.blocks-depth bs
bdepth-e C.[] = refl
bdepth-e (bs ▷ t) = cong₂ _⊔_ (depth-e t) (bdepth-e bs)

tail-e : ∀ {Σ n Bs Δ} (t : Tail Σ Bs Δ) .(le : T.depth t Data.Nat.≤ n) {Γ O F} → eSeq (T.tail t le {Γ} {O} {F}) ≡ U.select-tail t
tail-e (return s) le =
  trans (sel-e s ret (retq refl) (L.block [] L.retq) refl) (cong (λ is → L.block is L.retq) (++-identityʳ _))
tail-e (seq p s t) le = sel-e s (to p _) (T.tail t _) (U.select-tail t) (tail-e t _)
tail-e (goto l) le = refl
tail-e (case a p l₁ l₂) le = refl

blocks-e : ∀ {Σ n Bs} (bs : C.Blocks Σ Bs) .(le : T.blocks-depth bs Data.Nat.≤ n) → eBlocks (T.blocks bs le) ≡ U.select-blocks bs
blocks-e C.[] le = refl
blocks-e (bs ▷ t) le = cong₂ _∷_ (tail-e t _) (blocks-e bs _)

body≡ : ∀ {n n' bs bs'} {b b' : L.Block} → n ≡ n' → bs ≡ bs' → b ≡ b' → L.body n bs b ≡ L.body n' bs' b'
body≡ refl refl refl = refl

main-e : ∀ {Σ} (b : C.Body Σ []) → eBody (T.main-body b) ≡ U.select-body [] b
main-e (C.body bs t) = body≡ (cong₂ _⊔_ (bdepth-e bs) (depth-e t)) (blocks-e bs _) (tail-e t _)

def-e : ∀ {Σ m} (b : C.Body Σ (Any ∷ ⟪ tup m ⟫ ∷ [])) → eBody (T.def-body b) ≡ U.select-body U.prologue b
def-e (C.body bs t) =
  body≡ (cong₂ _⊔_ (bdepth-e bs) (depth-e t)) (blocks-e bs _)
    (cong (λ b' → L.block (U.prologue ++ L.Block.instrs b') (L.Block.jump b')) (tail-e t _))

defs-e : ∀ {Σ ms} (ds : All (λ m → C.Body Σ (Any ∷ ⟪ tup m ⟫ ∷ [])) ms) → eDefs (All-map T.def-body ds) ≡ U.select-defs ds
defs-e [] = refl
defs-e (d ∷ ds) = cong₂ _∷_ (def-e d) (defs-e ds)

select-erase : ∀ (P : C.Program) → erase (T.select P) ≡ U.select P
select-erase (C.program ds b) = cong₂ L.program (defs-e ds) (main-e b)
