{-

  Soundness of the ISWIM machine with respect to the graph model: what the
  machine computes is in the denotation of the program.

  Each machine state denotes a set of values (𝒮): a value denotes the
  denotation of the code it came from (𝒱; a closure denotes its λ in the
  denotation of its environment, 𝓔), and a continuation denotes a function
  on sets (𝒦), the context its frame stands for. Every step can only
  shrink the denotation of the state (step-⊆), so the value returned to
  the empty continuation is in the denotation of the program. Steps that
  pass a value to a function body (application, case) need β, which
  needs continuity (ISWIMContinuous.body-continuous) and that values
  denote nonempty sets (𝒱-nonempty).

-}

module Compiler.Operational.Adequacy.Soundness where

open import Primitives using (Base; base-rep; Int)
open import Compiler.Lang.Prim using (Out; int; bool; δ)
open import SetsAsPredicates
open import GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _~_; Con; Con-env; Con-⌈⌉; Con⇒≈)
  renaming (const to dconst)
open import GraphModel.Ops
  using (⋆; ℬ; 𝒯; nthD; inl; inr; 𝒞; Λ; Λ-consis; ℬ-consis; inl-consis; inr-consis)
  renaming (proj to dproj)
open import Compiler.Model.Graph.Prim using (primD) renaming (out to dout)
open import NewDenotProperties using (Every)
open import Data.Fin.Properties using () renaming (_≟_ to _fin≟_)
open import Relation.Nullary using (yes; no)
open import Level using (lift; lower)
open import Compiler.Model.Graph.Correctness.DelayFiniteCommon using (ρ₀; Init)
open import Compiler.Lang.ISWIM
open import Compiler.Model.Graph.Sem.ISWIM using (⟦_⟧; ⟦_⟧₊; ⟦⟧-monotone; ISWIM-con-env)
open import Compiler.Model.Graph.Sem.ISWIMContinuous using (body-continuous)
import NewEnv
open import NewSyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Compiler.Observation
open import Compiler.Operational.Smallstep using (Star; Terminates; next; stop)
open import ListUtil
open import Compiler.Operational.Machine.ISWIM hiding (inl; inr)
import Compiler.Operational.Machine.ISWIM as T using (inl; inr)
open import Compiler.Operational.Adequacy.Common

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate; reverse; map)
open import Data.List.Base using (reverseAcc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

VEnv : Set₁
VEnv = NewEnv.Env Value

{- Tuples of sets ------------------------------------------------------------}

{- d is in component i of a list of n sets -}
At : ∀ {n} → Fin n → List (𝒫 Value) → Value → Set
At {suc n} zero (D ∷ Ds) d = length Ds ≡ n × d ∈ D
At (suc i) (D ∷ Ds) d = At i Ds d
At _ [] d = ⊥

AllNE : List (𝒫 Value) → Set
AllNE [] = ⊤
AllNE (D ∷ Ds) = nonempty D × AllNE Ds

Null : List (𝒫 Value) → Set
Null [] = ⊤
Null (D ∷ Ds) = ⊥

{- the tuple of a list of sets (𝒯, for lists) -}
𝒯L : List (𝒫 Value) → 𝒫 Value
𝒯L Ds ⟨⟩ = Null Ds
𝒯L Ds (tup[ i ] d) = At i Ds d × AllNE Ds
𝒯L Ds _ = ⊥

infix 4 _⊆L_
_⊆L_ : List (𝒫 Value) → List (𝒫 Value) → Set
[] ⊆L [] = ⊤
(D ∷ Ds) ⊆L (E ∷ Es) = D ⊆ E × Ds ⊆L Es
_ ⊆L _ = ⊥

⊆L-refl : ∀ Ds → Ds ⊆L Ds
⊆L-refl [] = tt
⊆L-refl (D ∷ Ds) = ⟨ (λ d z → z) , ⊆L-refl Ds ⟩

At-mono : ∀ {n} (i : Fin n) Ds Es d → Ds ⊆L Es → At i Ds d → At i Es d
At-mono {suc n} zero (D ∷ Ds) (E ∷ Es) d ⟨ D⊆ , Ds⊆ ⟩ ⟨ len , d∈ ⟩ =
  ⟨ len' Ds Es Ds⊆ len , D⊆ d d∈ ⟩
  where
  len' : ∀ {m} Ds Es → Ds ⊆L Es → length Ds ≡ m → length Es ≡ m
  len' [] [] _ refl = refl
  len' (D ∷ Ds) (E ∷ Es) ⟨ _ , s ⟩ refl = cong suc (len' Ds Es s refl)
At-mono (suc i) (D ∷ Ds) (E ∷ Es) d ⟨ _ , Ds⊆ ⟩ a = At-mono i Ds Es d Ds⊆ a

AllNE-mono : ∀ Ds Es → Ds ⊆L Es → AllNE Ds → AllNE Es
AllNE-mono [] [] _ _ = tt
AllNE-mono (D ∷ Ds) (E ∷ Es) ⟨ D⊆ , s ⟩ ⟨ ⟨ d , d∈ ⟩ , ne ⟩ = ⟨ ⟨ d , D⊆ d d∈ ⟩ , AllNE-mono Ds Es s ne ⟩

𝒯L-mono : ∀ Ds Es → Ds ⊆L Es → 𝒯L Ds ⊆ 𝒯L Es
𝒯L-mono [] [] s ⟨⟩ tt = tt
𝒯L-mono Ds Es s (tup[ i ] d) ⟨ a , ne ⟩ = ⟨ At-mono i Ds Es d s a , AllNE-mono Ds Es s ne ⟩

{- Denotations of values, environments, continuations and states ------------}

𝒱 : Val → 𝒫 Value
𝒱s : List Val → List (𝒫 Value)
𝓔 : Env → VEnv

𝒱 (clo N γ) = Λ ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩
𝒱 (const B k) = ℬ B k ptt
𝒱 (tup vs) = 𝒯L (𝒱s vs)
𝒱 (T.inl v) = inl ⟨ 𝒱 v , ptt ⟩
𝒱 (T.inr v) = inr ⟨ 𝒱 v , ptt ⟩

𝒱s [] = []
𝒱s (v ∷ vs) = 𝒱 v ∷ 𝒱s vs

𝓔 [] x = Init
𝓔 (v ∷ γ) zero = 𝒱 v
𝓔 (v ∷ γ) (suc x) = 𝓔 γ x

{- the values so far of a tuple (in reverse), in front of the rest -}
rev𝒱 : List Val → List (𝒫 Value) → List (𝒫 Value)
rev𝒱 [] Ds = Ds
rev𝒱 (v ∷ vs) Ds = rev𝒱 vs (𝒱 v ∷ Ds)

⟦_⟧* : List AST → VEnv → List (𝒫 Value)
⟦ [] ⟧* ρ = []
⟦ M ∷ Ms ⟧* ρ = ⟦ M ⟧ ρ ∷ ⟦ Ms ⟧* ρ

inl-⊆ : ∀ {D E} → D ⊆ E → inl ⟨ D , ptt ⟩ ⊆ inl ⟨ E , ptt ⟩
inl-⊆ D⊆ (left d) d∈ = D⊆ d d∈
inl-⊆ D⊆ (dconst k) ()
inl-⊆ D⊆ (V ↦ w) ()
inl-⊆ D⊆ ν ()
inl-⊆ D⊆ ω ()
inl-⊆ D⊆ ⦅ u , v ⦆ ()
inl-⊆ D⊆ (tup[ i ] d) ()
inl-⊆ D⊆ (right d) ()
inl-⊆ D⊆ ⟨⟩ ()

inr-⊆ : ∀ {D E} → D ⊆ E → inr ⟨ D , ptt ⟩ ⊆ inr ⟨ E , ptt ⟩
inr-⊆ D⊆ (right d) d∈ = D⊆ d d∈
inr-⊆ D⊆ (dconst k) ()
inr-⊆ D⊆ (V ↦ w) ()
inr-⊆ D⊆ ν ()
inr-⊆ D⊆ ω ()
inr-⊆ D⊆ ⦅ u , v ⦆ ()
inr-⊆ D⊆ (tup[ i ] d) ()
inr-⊆ D⊆ (left d) ()
inr-⊆ D⊆ ⟨⟩ ()

𝒦 : Cont → 𝒫 Value → 𝒫 Value
𝒦 halt D = D
𝒦 (appL M γ κ) D = 𝒦 κ (⋆ ⟨ D , ⟨ ⟦ M ⟧ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (appR v κ) D = 𝒦 κ (⋆ ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
𝒦 (tupK vs Ms γ κ) D = 𝒦 κ (𝒯L (rev𝒱 vs (D ∷ ⟦ Ms ⟧* (𝓔 γ))))
𝒦 (getK i κ) D = 𝒦 κ (dproj i ⟨ D , ptt ⟩)
𝒦 (inlK κ) D = 𝒦 κ (inl ⟨ D , ptt ⟩)
𝒦 (inrK κ) D = 𝒦 κ (inr ⟨ D , ptt ⟩)
𝒦 (caseK M N γ κ) D =
  𝒦 κ (𝒞 ⟨ D , ⟨ (λ X → ⟦ M ⟧ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩)

𝒦 (primL p M γ κ) D = 𝒦 κ (primD p ⟨ D , ⟨ ⟦ M ⟧ (𝓔 γ) , ptt ⟩ ⟩)
𝒦 (primR p v κ) D = 𝒦 κ (primD p ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)

𝒮 : State → 𝒫 Value
𝒮 (eval M γ κ) = 𝒦 κ (⟦ M ⟧ (𝓔 γ))
𝒮 (ret v κ) = 𝒦 κ (𝒱 v)

{- Basic properties ----------------------------------------------------------}

rev𝒱-mono : ∀ vs Ds Es → Ds ⊆L Es → rev𝒱 vs Ds ⊆L rev𝒱 vs Es
rev𝒱-mono [] Ds Es s = s
rev𝒱-mono (v ∷ vs) Ds Es s = rev𝒱-mono vs (𝒱 v ∷ Ds) (𝒱 v ∷ Es) ⟨ (λ d z → z) , s ⟩

𝒦-mono : ∀ κ {D E} → D ⊆ E → 𝒦 κ D ⊆ 𝒦 κ E
𝒦-mono halt D⊆ = D⊆
𝒦-mono (appL M γ κ) D⊆ = 𝒦-mono κ λ { w ⟨ V , ⟨ f∈ , rest ⟩ ⟩ → ⟨ V , ⟨ D⊆ _ f∈ , rest ⟩ ⟩ }
𝒦-mono (appR v κ) D⊆ =
  𝒦-mono κ λ { w ⟨ V , ⟨ f∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ → ⟨ V , ⟨ f∈ , ⟨ (λ d d∈ → D⊆ d (V⊆ d d∈)) , ne ⟩ ⟩ ⟩ }
𝒦-mono (tupK vs Ms γ κ) {D} {E} D⊆ =
  𝒦-mono κ (𝒯L-mono _ _ (rev𝒱-mono vs (D ∷ _) (E ∷ _) ⟨ D⊆ , ⊆L-refl _ ⟩))
𝒦-mono (getK i κ) D⊆ = 𝒦-mono κ λ d d∈ → D⊆ _ d∈
𝒦-mono (inlK κ) D⊆ = 𝒦-mono κ (inl-⊆ D⊆)
𝒦-mono (inrK κ) D⊆ = 𝒦-mono κ (inr-⊆ D⊆)
𝒦-mono (caseK M N γ κ) D⊆ = 𝒦-mono κ G
  where
  G : _ ⊆ _
  G w (inj₁ ⟨ u , ⟨ U , ⟨ allL , w∈ ⟩ ⟩ ⟩) = inj₁ ⟨ u , ⟨ U , ⟨ (λ d d∈ → D⊆ _ (allL d d∈)) , w∈ ⟩ ⟩ ⟩
  G w (inj₂ ⟨ u , ⟨ U , ⟨ allR , w∈ ⟩ ⟩ ⟩) = inj₂ ⟨ u , ⟨ U , ⟨ (λ d d∈ → D⊆ _ (allR d d∈)) , w∈ ⟩ ⟩ ⟩
𝒦-mono (primL p M γ κ) D⊆ =
  𝒦-mono κ λ { w ⟨ n , ⟨ m , ⟨ n∈ , rest ⟩ ⟩ ⟩ → ⟨ n , ⟨ m , ⟨ D⊆ _ n∈ , rest ⟩ ⟩ ⟩ }
𝒦-mono (primR p v κ) D⊆ =
  𝒦-mono κ λ { w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , eq ⟩ ⟩ ⟩ ⟩ → ⟨ n , ⟨ m , ⟨ n∈ , ⟨ D⊆ _ m∈ , eq ⟩ ⟩ ⟩ ⟩ }

{- every value denotes a nonempty set, so every environment is nonempty -}
𝒱-nonempty : ∀ v → nonempty (𝒱 v)
𝒱s-nonempty : ∀ vs → AllNE (𝒱s vs)

𝒱-nonempty (clo N γ) = ⟨ ν , tt ⟩
𝒱-nonempty (const B k) = ⟨ dconst k , ⟨ refl , refl ⟩ ⟩
𝒱-nonempty (tup []) = ⟨ ⟨⟩ , tt ⟩
𝒱-nonempty (tup (v ∷ vs)) with 𝒱-nonempty v
... | ⟨ d , d∈ ⟩ =
  ⟨ tup[_]_ {suc (length vs)} zero d , ⟨ ⟨ length-𝒱s vs , d∈ ⟩ , ⟨ ⟨ d , d∈ ⟩ , 𝒱s-nonempty vs ⟩ ⟩ ⟩
  where
  length-𝒱s : ∀ vs → length (𝒱s vs) ≡ length vs
  length-𝒱s [] = refl
  length-𝒱s (v ∷ vs) = cong suc (length-𝒱s vs)
𝒱-nonempty (T.inl v) with 𝒱-nonempty v
... | ⟨ d , d∈ ⟩ = ⟨ left d , d∈ ⟩
𝒱-nonempty (T.inr v) with 𝒱-nonempty v
... | ⟨ d , d∈ ⟩ = ⟨ right d , d∈ ⟩

𝒱s-nonempty [] = tt
𝒱s-nonempty (v ∷ vs) = ⟨ 𝒱-nonempty v , 𝒱s-nonempty vs ⟩

𝓔-nonempty : ∀ γ → NewEnv.nonempty-env (𝓔 γ)
𝓔-nonempty [] x = ⟨ ω , refl ⟩
𝓔-nonempty (v ∷ γ) zero = 𝒱-nonempty v
𝓔-nonempty (v ∷ γ) (suc x) = 𝓔-nonempty γ x

𝓔-lookup : ∀ γ x {v} → γ ‼ x ≡ just v → 𝒱 v ⊆ 𝓔 γ x
𝓔-lookup (v ∷ γ) zero refl d d∈ = d∈
𝓔-lookup (v ∷ γ) (suc x) eq = 𝓔-lookup γ x eq

𝓔-ext : ∀ v γ x → 𝓔 (v ∷ γ) x ⊆ (𝒱 v • 𝓔 γ) x
𝓔-ext v γ zero d d∈ = d∈
𝓔-ext v γ (suc x) d d∈ = d∈

{- β: the body of a function, run on a value, is in the application -}
body-in : ∀ N γ v d → d ∈ ⟦ N ⟧ (𝓔 (v ∷ γ))
  → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ 𝒱 v × d ∈ ⟦ N ⟧ (mem V • 𝓔 γ)
body-in N γ v d d∈ =
  body-continuous N (𝓔 γ) (𝓔-nonempty γ) (𝒱 v) (𝒱-nonempty v) d
    (⟦⟧-monotone N (𝓔-ext v γ) d d∈)

{- Tuples --------------------------------------------------------------------}

𝒱s-reverseAcc : ∀ acc vs → 𝒱s (reverseAcc acc vs) ≡ rev𝒱 vs (𝒱s acc)
𝒱s-reverseAcc acc [] = refl
𝒱s-reverseAcc acc (v ∷ vs) = 𝒱s-reverseAcc (v ∷ acc) vs

{- the denotation of the start of a tuple -}
tuple-next-𝒮 : ∀ vs Ms γ κ → 𝒮 (tuple-next vs Ms γ κ) ⊆ 𝒦 κ (𝒯L (rev𝒱 vs (⟦ Ms ⟧* (𝓔 γ))))
tuple-next-𝒮 vs [] γ κ d d∈ = subst (λ Ds → 𝒦 κ (𝒯L Ds) d) (𝒱s-reverseAcc [] vs) d∈
tuple-next-𝒮 vs (M ∷ Ms) γ κ d d∈ = d∈

At-args : ∀ {n} (args : Args (replicate n ■)) ρ (i : Fin n) d
  → At i (⟦ args→list args ⟧* ρ) d → d ∈ nthD (⟦ args ⟧₊ ρ) i
At-args {suc n} (M ,, args) ρ zero d ⟨ _ , d∈ ⟩ = d∈
At-args {suc n} (M ,, args) ρ (suc i) d a = At-args args ρ i d a

AllNE-args : ∀ {n} (args : Args (replicate n ■)) ρ
  → AllNE (⟦ args→list args ⟧* ρ) → ∀ i → nonempty (nthD (⟦ args ⟧₊ ρ) i)
AllNE-args {suc n} (M ,, args) ρ ⟨ ne , _ ⟩ zero = ne
AllNE-args {suc n} (M ,, args) ρ ⟨ _ , nes ⟩ (suc i) = AllNE-args args ρ nes i

At-length : ∀ {m} (i : Fin m) Ds d → At i Ds d → length Ds ≡ m
At-length {suc m} zero (D ∷ Ds) d ⟨ len , _ ⟩ = cong suc len
At-length (suc i) (D ∷ Ds) d a = cong suc (At-length i Ds d a)

length-args : ∀ {n} (args : Args (replicate n ■)) ρ → length (⟦ args→list args ⟧* ρ) ≡ n
length-args {zero} Nil ρ = refl
length-args {suc n} (M ,, args) ρ = cong suc (length-args args ρ)

𝒯L-args : ∀ {n} (args : Args (replicate n ■)) ρ → 𝒯L (⟦ args→list args ⟧* ρ) ⊆ 𝒯 n (⟦ args ⟧₊ ρ)
𝒯L-args {zero} Nil ρ ⟨⟩ tt = tt
𝒯L-args {zero} Nil ρ (tup[ zero ] d) ⟨ () , _ ⟩
𝒯L-args {zero} Nil ρ (tup[ suc i ] d) ⟨ () , _ ⟩
𝒯L-args {suc n} (M ,, args) ρ ⟨⟩ ()
𝒯L-args {suc n} args ρ (tup[_]_ {m} i d) ⟨ a , ne ⟩
    with At-length i _ d a
... | len with subst (λ k → k ≡ m) (length-args args ρ) len
... | refl = ⟨ refl , ⟨ At-args args ρ i d a , AllNE-args args ρ ne ⟩ ⟩

proj-𝒱s : ∀ {n} (i : Fin n) vs {v} → proj i vs ≡ just v → ∀ d → d ∈ 𝒱 v → At i (𝒱s vs) d
proj-𝒱s {suc n} zero (v ∷ vs) eq d d∈ with has-length n vs in h
proj-𝒱s {suc n} zero (v ∷ vs) refl d d∈ | true =
  ⟨ len vs (has-length→length n vs h) , d∈ ⟩
  where
  len : ∀ vs {m} → length vs ≡ m → length (𝒱s vs) ≡ m
  len [] refl = refl
  len (v ∷ vs) refl = cong suc (len vs refl)
proj-𝒱s {suc n} zero (v ∷ vs) () d d∈ | false
proj-𝒱s (suc i) (v ∷ vs) eq d d∈ = proj-𝒱s i vs eq d d∈

{- every value denotes a consistent set, so every environment is consistent -}
AllCon : List (𝒫 Value) → Set
AllCon [] = ⊤
AllCon (D ∷ Ds) = Con D × AllCon Ds

At-con : ∀ {n} (i : Fin n) Ds {d d'} → AllCon Ds → At i Ds d → At i Ds d' → d ~ d'
At-con {suc n} zero (D ∷ Ds) ⟨ c , _ ⟩ ⟨ _ , d∈ ⟩ ⟨ _ , d'∈ ⟩ = c _ _ d∈ d'∈
At-con (suc i) (D ∷ Ds) ⟨ _ , cs ⟩ a a' = At-con i Ds cs a a'

At-[] : ∀ {n} (i : Fin n) {d} → At i [] d → ⊥
At-[] zero ()
At-[] (suc i) ()

𝒯L-con : ∀ Ds → AllCon Ds → Con (𝒯L Ds)
𝒯L-con Ds cs ⟨⟩ ⟨⟩ _ _ = tt
𝒯L-con Ds cs (tup[ i ] d) (tup[ j ] d') ⟨ a , _ ⟩ ⟨ a' , _ ⟩
    with trans (sym (At-length i Ds d a)) (At-length j Ds d' a')
... | refl with i fin≟ j
... | yes refl = ⟨ refl , inj₂ ⟨ refl , At-con i Ds cs a a' ⟩ ⟩
... | no neq = ⟨ refl , inj₁ neq ⟩
𝒯L-con [] cs ⟨⟩ (tup[ i ] d) _ ⟨ a , _ ⟩ = ⊥-elim (At-[] i a)
𝒯L-con [] cs (tup[ i ] d) ⟨⟩ ⟨ a , _ ⟩ _ = ⊥-elim (At-[] i a)
𝒯L-con (D ∷ Ds) cs ⟨⟩ _ () _
𝒯L-con (D ∷ Ds) cs (tup[ i ] d) ⟨⟩ _ ()
𝒯L-con Ds cs (dconst k) v () _
𝒯L-con Ds cs (V ↦ w) v () _
𝒯L-con Ds cs ν v () _
𝒯L-con Ds cs ω v () _
𝒯L-con Ds cs ⦅ _ , _ ⦆ v () _
𝒯L-con Ds cs (left _) v () _
𝒯L-con Ds cs (right _) v () _
𝒯L-con Ds cs u (dconst k) _ ()
𝒯L-con Ds cs u (V ↦ w) _ ()
𝒯L-con Ds cs u ν _ ()
𝒯L-con Ds cs u ω _ ()
𝒯L-con Ds cs u ⦅ _ , _ ⦆ _ ()
𝒯L-con Ds cs u (left _) _ ()
𝒯L-con Ds cs u (right _) _ ()

𝒱-con : ∀ v → Con (𝒱 v)
𝒱s-con : ∀ vs → AllCon (𝒱s vs)
𝓔-con : ∀ γ → Con-env (𝓔 γ)
𝒱-con (clo N γ) = lower (Λ-consis _ _ ⟨ (λ X X' X~ → lift (ISWIM-con-env N (NewEnv.•-~ (Every _~_) (𝓔-con γ) X~))) , ptt ⟩)
𝒱-con (const B k) = lower (ℬ-consis B k ptt ptt ptt)
𝒱-con (tup vs) = 𝒯L-con (𝒱s vs) (𝒱s-con vs)
𝒱-con (T.inl v) = lower (inl-consis ⟨ 𝒱 v , ptt ⟩ ⟨ 𝒱 v , ptt ⟩ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱-con (T.inr v) = lower (inr-consis ⟨ 𝒱 v , ptt ⟩ ⟨ 𝒱 v , ptt ⟩ ⟨ lift (𝒱-con v) , ptt ⟩)
𝒱s-con [] = tt
𝒱s-con (v ∷ vs) = ⟨ 𝒱-con v , 𝒱s-con vs ⟩
𝓔-con [] x = Con-⌈⌉ ω
𝓔-con (v ∷ γ) zero = 𝒱-con v
𝓔-con (v ∷ γ) (suc x) = 𝓔-con γ x

{- Primitives -------------------------------------------------------------------}

int-in : ∀ v {n} → obs v ≡ o-const Int n → dconst {Int} n ∈ 𝒱 v
int-in (const B k) refl = ⟨ refl , refl ⟩

𝒱-out : ∀ r d → d ∈ 𝒱 (out r) → d ≡ dout r
𝒱-out (int k) (dconst k') ⟨ refl , refl ⟩ = refl
𝒱-out (bool true) (left ⟨⟩) tt = refl
𝒱-out (bool false) (right ⟨⟩) tt = refl
𝒱-out (bool true) (left (tup[ zero ] d)) ⟨ () , _ ⟩
𝒱-out (bool true) (left (tup[ suc i ] d)) ⟨ () , _ ⟩
𝒱-out (bool false) (right (tup[ zero ] d)) ⟨ () , _ ⟩
𝒱-out (bool false) (right (tup[ suc i ] d)) ⟨ () , _ ⟩

prim-⊆ : ∀ p v w r → δ? p (obs v) (obs w) ≡ just r → 𝒱 (out r) ⊆ primD p ⟨ 𝒱 v , ⟨ 𝒱 w , ptt ⟩ ⟩
prim-⊆ p v w r e d d∈ with δ?-inv p (obs v) (obs w) e
... | ⟨ n , ⟨ m , ⟨ ov , ⟨ ow , refl ⟩ ⟩ ⟩ ⟩ = ⟨ n , ⟨ m , ⟨ int-in v ov , ⟨ int-in w ow , 𝒱-out (δ p n m) d d∈ ⟩ ⟩ ⟩ ⟩

{- Steps shrink the denotation of the state --------------------------------}

step-⊆ : ∀ s {s'} → step s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
step-⊆ (eval (` x) γ κ) eq with γ ‼ x in look
step-⊆ (eval (` x) γ κ) refl | just v = 𝒦-mono κ (𝓔-lookup γ x look)
step-⊆ (eval (` x) γ κ) () | nothing
step-⊆ (eval (lam ⦅ ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (app ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (lit B k ⦅ Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (tuple n ⦅ args ⦆) γ κ) refl d d∈ =
  𝒦-mono κ (𝒯L-args args (𝓔 γ)) d (tuple-next-𝒮 [] (args→list args) γ κ d d∈)
step-⊆ (eval (get i ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (ret v halt) ()
step-⊆ (ret (clo N γ) (appL M γ' κ)) refl d d∈ = d∈
step-⊆ (ret (const B k) (appL M γ' κ)) ()
step-⊆ (ret (tup vs) (appL M γ' κ)) ()
step-⊆ (ret (T.inl v) (appL M γ' κ)) ()
step-⊆ (ret (T.inr v) (appL M γ' κ)) ()
step-⊆ (ret w (appR (clo N γ) κ)) refl = 𝒦-mono κ β
  where
  β : ⟦ N ⟧ (𝓔 (w ∷ γ)) ⊆ ⋆ ⟨ 𝒱 (clo N γ) , ⟨ 𝒱 w , ptt ⟩ ⟩
  β d d∈ with body-in N γ w d d∈
  ... | ⟨ V , ⟨ ne , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = ⟨ V , ⟨ ⟨ d∈′ , ⟨ ne , Con⇒≈ V (𝒱-con w) V⊆ ⟩ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩
step-⊆ (ret w (appR (const B k) κ)) ()
step-⊆ (ret w (appR (tup vs) κ)) ()
step-⊆ (ret w (appR (T.inl v) κ)) ()
step-⊆ (ret w (appR (T.inr v) κ)) ()
step-⊆ (ret v (tupK vs Ms γ κ)) refl = tuple-next-𝒮 (v ∷ vs) Ms γ κ
step-⊆ (ret (tup vs) (getK i κ)) eq with proj i vs in p
step-⊆ (ret (tup vs) (getK i κ)) refl | just v =
  𝒦-mono κ λ d d∈ → ⟨ proj-𝒱s i vs p d d∈ , 𝒱s-nonempty vs ⟩
step-⊆ (ret (tup vs) (getK i κ)) () | nothing
step-⊆ (ret (clo N γ) (getK i κ)) ()
step-⊆ (ret (const B k) (getK i κ)) ()
step-⊆ (ret (T.inl v) (getK i κ)) ()
step-⊆ (ret (T.inr v) (getK i κ)) ()
step-⊆ (ret v (inlK κ)) refl d d∈ = d∈
step-⊆ (ret v (inrK κ)) refl d d∈ = d∈
step-⊆ (ret (T.inl v) (caseK M N γ κ)) refl = 𝒦-mono κ β
  where
  β : ⟦ M ⟧ (𝓔 (v ∷ γ)) ⊆ _
  β d d∈ with body-in M γ v d d∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = inj₁ ⟨ u , ⟨ U , ⟨ V⊆ , ⟨ d∈′ , Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ ⟩ ⟩ ⟩ ⟩
step-⊆ (ret (T.inr v) (caseK M N γ κ)) refl = 𝒦-mono κ β
  where
  β : ⟦ N ⟧ (𝓔 (v ∷ γ)) ⊆ _
  β d d∈ with body-in N γ v d d∈
  ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
  ... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = inj₂ ⟨ u , ⟨ U , ⟨ V⊆ , ⟨ d∈′ , Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ ⟩ ⟩ ⟩ ⟩
step-⊆ (ret (clo N' γ') (caseK M N γ κ)) ()
step-⊆ (ret (const B k) (caseK M N γ κ)) ()
step-⊆ (ret (tup vs) (caseK M N γ κ)) ()
step-⊆ (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
step-⊆ (ret v (primL p M γ κ)) refl d d∈ = d∈
step-⊆ (ret w (primR p v κ)) eq with δ? p (obs v) (obs w) in e
step-⊆ (ret w (primR p v κ)) refl | just r = 𝒦-mono κ (prim-⊆ p v w r e)
step-⊆ (ret w (primR p v κ)) () | nothing

↠-⊆ : ∀ {s t} → s ↠ t → 𝒮 t ⊆ 𝒮 s
↠-⊆ done d d∈ = d∈
↠-⊆ {s} (st ∷↠ σ) d d∈ = step-⊆ s st d (↠-⊆ σ d d∈)

{- Final states ----------------------------------------------------------------}

{- the denotation of a value has an element of the shape of its observation -}
𝒱-shape : ∀ v → Σ[ d ∈ Value ] d ∈ 𝒱 v × ShapeOf (obs v) d
𝒱-shape (clo N γ) = ⟨ ν , ⟨ tt , tt ⟩ ⟩
𝒱-shape (const B k) = ⟨ dconst k , ⟨ ⟨ refl , refl ⟩ , refl ⟩ ⟩
𝒱-shape (tup []) = ⟨ ⟨⟩ , ⟨ tt , refl ⟩ ⟩
𝒱-shape (tup (v ∷ vs)) with 𝒱-shape v
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
  ⟨ tup[_]_ {suc (length vs)} zero d
  , ⟨ ⟨ ⟨ len vs , d∈ ⟩ , 𝒱s-nonempty (v ∷ vs) ⟩ , ⟨ length-obs-list vs , sh ⟩ ⟩ ⟩
  where
  len : ∀ vs → length (𝒱s vs) ≡ length vs
  len [] = refl
  len (v ∷ vs) = cong suc (len vs)
𝒱-shape (T.inl v) with 𝒱-shape v
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ left d , ⟨ d∈ , sh ⟩ ⟩
𝒱-shape (T.inr v) with 𝒱-shape v
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ = ⟨ right d , ⟨ d∈ , sh ⟩ ⟩

{- a state that stops with an answer has an element of that shape -}
final-shape : ∀ s {o} → step s ≡ stop o → Answer o → Σ[ d ∈ Value ] d ∈ 𝒮 s × ShapeOf o d
final-shape (eval (` x) γ κ) eq ans with γ ‼ x
final-shape (eval (` x) γ κ) () ans | just v
final-shape (eval (` x) γ κ) refl ans | nothing = ⊥-elim (ans refl)
final-shape (eval (lam ⦅ ⟩ N ,, Nil ⦆) γ κ) () ans
final-shape (eval (app ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
final-shape (eval (lit B k ⦅ Nil ⦆) γ κ) () ans
final-shape (eval (tuple n ⦅ args ⦆) γ κ) () ans
final-shape (eval (get i ⦅ M ,, Nil ⦆) γ κ) () ans
final-shape (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) () ans
final-shape (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) () ans
final-shape (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
final-shape (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
final-shape (ret v halt) refl ans = 𝒱-shape v
final-shape (ret (const B k) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (tup vs) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inl v) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inr v) (appL M γ' κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (const B k) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (tup vs) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (T.inl v) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (appR (T.inr v) κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (tup vs) (getK i κ)) eq ans with proj i vs
final-shape (ret (tup vs) (getK i κ)) () ans | just v
final-shape (ret (tup vs) (getK i κ)) refl ans | nothing = ⊥-elim (ans refl)
final-shape (ret (clo N γ) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (const B k) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inl v) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (T.inr v) (getK i κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (clo N' γ') (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (const B k) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret (tup vs) (caseK M N γ κ)) refl ans = ⊥-elim (ans refl)
final-shape (ret w (primR p v κ)) eq ans with δ? p (obs v) (obs w)
final-shape (ret w (primR p v κ)) () ans | just r
final-shape (ret w (primR p v κ)) refl ans | nothing = ⊥-elim (ans refl)

{- Soundness ------------------------------------------------------------------}

{- a program that terminates with an answer o has an element of the shape
   of o in its denotation -}
soundness : ∀ M {o} → Terminates (sem M) o → Answer o
  → Σ[ d ∈ Value ] d ∈ ⟦ M ⟧ ρ₀ × ShapeOf o d
soundness M (⟨ s , ⟨ σ , fin ⟩ ⟩) ans
    with final-shape s fin ans
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
  ⟨ d , ⟨ ⟦⟧-monotone M (λ x d z → z) d (↠-⊆ (star→↠ σ) d d∈) , sh ⟩ ⟩
