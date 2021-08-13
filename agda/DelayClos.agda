module DelayClos where

open import ISWIMClos1
open import ISWIMClos2
  renaming (Term to Term₂; Args to Args₂; `_ to #_;
      pair to pair₂; fst to fst₂; snd to snd₂; tuple to tuple₂;
      $ to %; _❲_❳ to _❲_❳₂; inl to inl₂; inr to inr₂; case to case₂;
      cons to cons₂; ast to ast₂; nil to nil₂; _⦅_⦆ to _⦅_⦆₂)

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

delay : Term → Term₂
delay-args : ∀{n} → Args (replicate n ■) → Args₂ (replicate n ■)

delay (` x) = # x
delay (clos n N fvs) = pair₂ (fun (delay N)) (tuple₂ n ⦅ delay-args fvs ⦆₂)
delay (L · M) = let dL = delay L in (fst₂ dL) ⦉ snd₂ dL , delay M ⦊
delay ($ P k) = % P k
delay (pair M N) = pair₂ (delay M) (delay N)
delay (fst M) = fst₂ (delay M)
delay (snd M) = snd₂ (delay M)
delay (tuple n ⦅ args ⦆) = tuple₂ n ⦅ delay-args args ⦆₂
delay (M ❲ i ❳) = (delay M) ❲ i ❳₂
delay (inl M) = inl₂ (delay M)
delay (inr M) = inr₂ (delay M)
delay (case L M N) = case₂ (delay L) (delay M) (delay N)

delay-args {zero} nil = nil₂
delay-args {suc n} (cons (ast M) args) =
    cons₂ (ast₂ (delay M)) (delay-args args)

