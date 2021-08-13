module DelayClos where

open import ISWIMClos

open import Data.List using (List; []; _∷_; _++_; length; replicate)
open import Data.Nat using (ℕ; suc ; zero)
open import Data.Product using (_×_; proj₁; proj₂; Σ; Σ-syntax)
  renaming (_,_ to ⟨_,_⟩ )
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit renaming (tt to True)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥-elim)

delay : Term → Term
delay-args : ∀{n} → Args (replicate n ■) → Args (replicate n ■)

delay (` x) = ` x
delay (fun N) = pair {!!} {!!}
delay (L · M) =
   let dL = delay L in
   (fst dL) · (snd dL) · (delay M)
delay ($ P k) = {!!}
delay (pair M N) = pair (delay M) (delay N)
delay (fst M) = fst (delay M)
delay (snd M) = snd (delay M)
delay (tuple n ⦅ args ⦆) = tuple n ⦅ delay-args args ⦆
delay (M ❲ i ❳) = (delay M) ❲ i ❳
delay (inl M) = inl (delay M)
delay (inr M) = inr (delay M)
delay (case L M N) = case (delay L) (delay M) (delay N)

delay-args {zero} nil = nil
delay-args {suc n} (cons (ast M) args) = cons (ast (delay M)) (delay-args args)

