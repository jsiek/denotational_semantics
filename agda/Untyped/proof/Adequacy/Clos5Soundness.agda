{-

  Soundness of the Clos5 machine with respect to the graph model: what the
  machine computes is in the denotation of the (well-formed) program.

  As for ISWIM (Adequacy/Soundness.agda), each machine state denotes a set
  of values (𝒮) and every step can only shrink it (step-⊆). Two things
  are new.

  * Code pointers. A code pointer code k denotes the entry for k in the
    table of definitions. The machine looks every reference up in the
    whole table, while the semantics interprets each definition with the
    table of the older ones; since a definition refers only to older ones
    (RB, part of DefsWF), the two agree (stab, from GlobalizeCorrect).
    Calling code k on an environment e and an argument w (two β steps at
    once) needs the continuity of the Clos5 semantics in the two
    parameters (Semantics/Graph/Clos5IswimContinuous.agda).

  * Values must denote nonempty sets (for β, for pairs and for tuples),
    but a reference past the end of the table denotes ∅. So states are
    interpreted with the table T⁺, which adds ν to every entry; for a
    program whose references all exist, T⁺ agrees with the table on
    them, so the final value is in the denotation of the program.

-}

module Untyped.proof.Adequacy.Clos5Soundness where

open import Framework.Primitives using (Base; base-rep; Int)
open import Language.Prim using (int; bool; δ)
open import proof.Framework.GraphModel.SetsAsPredicates
open import proof.Framework.GraphModel.Domain
  using (Value; _↦_; ν; ω; ⦅_,_⦆; tup[_]_; left; right; ⟨⟩; _~_; Con; Con-env; Con-⌈⌉; Con⇒≈)
  renaming (const to dconst)
open import proof.Framework.GraphModel.Ops
  using (⋆; ℬ; 𝒯; nthD; inl; inr; 𝒞; Λ; car; cdr; pair-mono)
  renaming (proj to dproj; pair to dpair)
open import proof.Semantics.Graph.Prim using (primD) renaming (out to dout)
open import Untyped.Language.Clos5
open import Untyped.Semantics.Graph.Clos5Iswim
  using (Table; ⟦_⟧[_]; ⟦_⟧₊[_]; ⟦_⟧ₚ; table; init) renaming (code to codeD)
open import Untyped.proof.Correctness.Graph.GlobalizeCorrect using (stab; Agree)
import proof.Framework.GraphModel.Env
open import Framework.Syntax.SyntaxUtil using (_,,_; Nil; ⟩_,,_)
open import Semantics.Observation
open import proof.Semantics.CEK.Smallstep using (Star; Terminates; next; stop)
open import proof.Framework.ListUtil
open import Untyped.Semantics.CEK.Clos5 hiding (inl; inr)
import Untyped.Semantics.CEK.Clos5 as T using (inl; inr)
open import Untyped.proof.Compiler.GlobalizeTable using (_⊑_; ∷-⊑)
open import proof.Adequacy.Common using (ShapeOf)
open import proof.Adequacy.Soundness
  using (At; AllNE; 𝒯L; _⊆L_; ⊆L-refl; 𝒯L-mono; At-length; inl-⊆; inr-⊆)
open import Untyped.proof.Adequacy.Clos5WF using (WF; DefsWF)
open import Untyped.proof.Semantics.Graph.Clos5IswimContinuous using (⟦⟧[]-monotone; term-continuous; table-con)
import Untyped.proof.Adequacy.Clos5Common as Common
open import proof.Adequacy.Values using (module Den)

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_; length; replicate; reverse)
open import Data.List.Base using (reverseAcc)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _<_; _≟_)
open import Relation.Nullary using (yes; no)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ptt)
open import Level using (lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)

VEnv : Set₁
VEnv = proof.Framework.GraphModel.Env.Env Value

≡→⊆ : ∀ {D E : 𝒫 Value} → D ≡ E → D ⊆ E
≡→⊆ refl d d∈ = d∈

pair-⊆ : ∀ {D D' E E'} → D ⊆ D' → E ⊆ E' → dpair ⟨ D , ⟨ E , ptt ⟩ ⟩ ⊆ dpair ⟨ D' , ⟨ E' , ptt ⟩ ⟩
pair-⊆ {D} {D'} {E} {E'} D⊆ E⊆ =
  lower (pair-mono ⟨ D , ⟨ E , ptt ⟩ ⟩ ⟨ D' , ⟨ E' , ptt ⟩ ⟩ ⟨ lift D⊆ , ⟨ lift E⊆ , _ ⟩ ⟩)

module _ (ds : List AST) (wf : DefsWF ds) where

  open Common ds

  {- the table, with ν added to every entry -}
  T⁺ : Table
  T⁺ k = table ds k ∪ ⌈ ν ⌉

  ⟦_⟧⁺ : AST → VEnv → 𝒫 Value
  ⟦ M ⟧⁺ ρ = ⟦ M ⟧[ T⁺ ] ρ

  {- Denotations of values, environments, continuations and states ------------}

  {- every entry of T⁺ holds ν and is consistent -}
  table-ν∈ : ∀ Ns k {x} → x ∈ table Ns k → ν ∈ table Ns k
  table-ν∈ (N ∷ Ns) k x∈ with k ≟ length Ns
  ... | yes _ = tt
  ... | no _ = table-ν∈ Ns k x∈

  T⁺-con : ∀ k → Con (T⁺ k)
  T⁺-con k a b (inj₁ a∈) (inj₁ b∈) = table-con ds k a b a∈ b∈
  T⁺-con k a b (inj₁ a∈) (inj₂ refl) = table-con ds k a ν a∈ (table-ν∈ ds k a∈)
  T⁺-con k a b (inj₂ refl) (inj₁ b∈) = table-con ds k ν b (table-ν∈ ds k b∈) b∈
  T⁺-con k a b (inj₂ refl) (inj₂ refl) = tt

  open Den T⁺ (λ k → inj₂ refl) T⁺-con

  𝓔 : Env → VEnv
  𝓔 [] x = init
  𝓔 (v ∷ γ) zero = 𝒱 v
  𝓔 (v ∷ γ) (suc x) = 𝓔 γ x

  rev𝒱 : List Val → List (𝒫 Value) → List (𝒫 Value)
  rev𝒱 [] Ds = Ds
  rev𝒱 (v ∷ vs) Ds = rev𝒱 vs (𝒱 v ∷ Ds)

  ⟦_⟧* : List AST → VEnv → List (𝒫 Value)
  ⟦ [] ⟧* ρ = []
  ⟦ M ∷ Ms ⟧* ρ = ⟦ M ⟧⁺ ρ ∷ ⟦ Ms ⟧* ρ

  𝒦 : Cont → 𝒫 Value → 𝒫 Value
  𝒦 halt D = D
  𝒦 (appF M N γ κ) D = 𝒦 κ (⋆ ⟨ ⋆ ⟨ D , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩ , ⟨ ⟦ N ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩)
  𝒦 (appE f N γ κ) D = 𝒦 κ (⋆ ⟨ ⋆ ⟨ 𝒱 f , ⟨ D , ptt ⟩ ⟩ , ⟨ ⟦ N ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩)
  𝒦 (appA f e κ) D = 𝒦 κ (⋆ ⟨ ⋆ ⟨ 𝒱 f , ⟨ 𝒱 e , ptt ⟩ ⟩ , ⟨ D , ptt ⟩ ⟩)
  𝒦 (pairL M γ κ) D = 𝒦 κ (dpair ⟨ D , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩)
  𝒦 (pairR v κ) D = 𝒦 κ (dpair ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)
  𝒦 (fstK κ) D = 𝒦 κ (car ⟨ D , ptt ⟩)
  𝒦 (sndK κ) D = 𝒦 κ (cdr ⟨ D , ptt ⟩)
  𝒦 (tupK vs Ms γ κ) D = 𝒦 κ (𝒯L (rev𝒱 vs (D ∷ ⟦ Ms ⟧* (𝓔 γ))))
  𝒦 (getK i κ) D = 𝒦 κ (dproj i ⟨ D , ptt ⟩)
  𝒦 (inlK κ) D = 𝒦 κ (inl ⟨ D , ptt ⟩)
  𝒦 (inrK κ) D = 𝒦 κ (inr ⟨ D , ptt ⟩)
  𝒦 (caseK M N γ κ) D =
    𝒦 κ (𝒞 ⟨ D , ⟨ (λ X → ⟦ M ⟧⁺ (X • 𝓔 γ)) , ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩ ⟩ ⟩)
  𝒦 (letK N γ κ) D = 𝒦 κ (⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩)
  𝒦 (primL p M γ κ) D = 𝒦 κ (primD p ⟨ D , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩)
  𝒦 (primR p v κ) D = 𝒦 κ (primD p ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩)

  𝒮 : State → 𝒫 Value
  𝒮 (eval M γ κ) = 𝒦 κ (⟦ M ⟧⁺ (𝓔 γ))
  𝒮 (ret v κ) = 𝒦 κ (𝒱 v)

  {- Basic properties ----------------------------------------------------------}

  rev𝒱-mono : ∀ vs Ds Es → Ds ⊆L Es → rev𝒱 vs Ds ⊆L rev𝒱 vs Es
  rev𝒱-mono [] Ds Es s = s
  rev𝒱-mono (v ∷ vs) Ds Es s = rev𝒱-mono vs (𝒱 v ∷ Ds) (𝒱 v ∷ Es) ⟨ (λ d z → z) , s ⟩

  𝒦-mono : ∀ κ {D E} → D ⊆ E → 𝒦 κ D ⊆ 𝒦 κ E
  𝒦-mono halt D⊆ = D⊆
  𝒦-mono (appF M N γ κ) {D} {E} D⊆ = 𝒦-mono κ G
    where
    G : ⋆ ⟨ ⋆ ⟨ D , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩ , ⟨ ⟦ N ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩
      ⊆ ⋆ ⟨ ⋆ ⟨ E , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩ , ⟨ ⟦ N ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩
    G w ⟨ V , ⟨ ⟨ U , ⟨ f∈ , restU ⟩ ⟩ , rest ⟩ ⟩ = ⟨ V , ⟨ ⟨ U , ⟨ D⊆ _ f∈ , restU ⟩ ⟩ , rest ⟩ ⟩
  𝒦-mono (appE f N γ κ) {D} {E} D⊆ = 𝒦-mono κ G
    where
    G : ⋆ ⟨ ⋆ ⟨ 𝒱 f , ⟨ D , ptt ⟩ ⟩ , ⟨ ⟦ N ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩
      ⊆ ⋆ ⟨ ⋆ ⟨ 𝒱 f , ⟨ E , ptt ⟩ ⟩ , ⟨ ⟦ N ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩
    G w ⟨ V , ⟨ ⟨ U , ⟨ f∈ , ⟨ U⊆ , neU ⟩ ⟩ ⟩ , rest ⟩ ⟩ =
      ⟨ V , ⟨ ⟨ U , ⟨ f∈ , ⟨ (λ d d∈ → D⊆ d (U⊆ d d∈)) , neU ⟩ ⟩ ⟩ , rest ⟩ ⟩
  𝒦-mono (appA f e κ) {D} {E} D⊆ = 𝒦-mono κ G
    where
    G : ⋆ ⟨ ⋆ ⟨ 𝒱 f , ⟨ 𝒱 e , ptt ⟩ ⟩ , ⟨ D , ptt ⟩ ⟩ ⊆ ⋆ ⟨ ⋆ ⟨ 𝒱 f , ⟨ 𝒱 e , ptt ⟩ ⟩ , ⟨ E , ptt ⟩ ⟩
    G w ⟨ V , ⟨ f∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ⟨ V , ⟨ f∈ , ⟨ (λ d d∈ → D⊆ d (V⊆ d d∈)) , ne ⟩ ⟩ ⟩
  𝒦-mono (pairL M γ κ) {D} {E} D⊆ = 𝒦-mono κ G
    where
    G : dpair ⟨ D , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩ ⊆ dpair ⟨ E , ⟨ ⟦ M ⟧⁺ (𝓔 γ) , ptt ⟩ ⟩
    G = pair-⊆ {D} {E} {⟦ M ⟧⁺ (𝓔 γ)} {⟦ M ⟧⁺ (𝓔 γ)} D⊆ (λ d z → z)
  𝒦-mono (pairR v κ) {D} {E} D⊆ = 𝒦-mono κ G
    where
    G : dpair ⟨ 𝒱 v , ⟨ D , ptt ⟩ ⟩ ⊆ dpair ⟨ 𝒱 v , ⟨ E , ptt ⟩ ⟩
    G = pair-⊆ {𝒱 v} {𝒱 v} {D} {E} (λ d z → z) D⊆
  𝒦-mono (fstK κ) D⊆ = 𝒦-mono κ (λ { d ⟨ e , de∈ ⟩ → ⟨ e , D⊆ _ de∈ ⟩ })
  𝒦-mono (sndK κ) D⊆ = 𝒦-mono κ (λ { e ⟨ d , de∈ ⟩ → ⟨ d , D⊆ _ de∈ ⟩ })
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
  𝒦-mono (letK N γ κ) {D} {E} D⊆ = 𝒦-mono κ G
    where
    G : ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩ , ⟨ D , ptt ⟩ ⟩
      ⊆ ⋆ ⟨ Λ ⟨ (λ X → ⟦ N ⟧⁺ (X • 𝓔 γ)) , ptt ⟩ , ⟨ E , ptt ⟩ ⟩
    G w ⟨ V , ⟨ f∈ , ⟨ V⊆ , ne ⟩ ⟩ ⟩ = ⟨ V , ⟨ f∈ , ⟨ (λ d d∈ → D⊆ d (V⊆ d d∈)) , ne ⟩ ⟩ ⟩
  𝒦-mono (primL p M γ κ) D⊆ =
    𝒦-mono κ λ { w ⟨ n , ⟨ m , ⟨ n∈ , rest ⟩ ⟩ ⟩ → ⟨ n , ⟨ m , ⟨ D⊆ _ n∈ , rest ⟩ ⟩ ⟩ }
  𝒦-mono (primR p v κ) D⊆ =
    𝒦-mono κ λ { w ⟨ n , ⟨ m , ⟨ n∈ , ⟨ m∈ , eq ⟩ ⟩ ⟩ ⟩ → ⟨ n , ⟨ m , ⟨ n∈ , ⟨ D⊆ _ m∈ , eq ⟩ ⟩ ⟩ ⟩ }

  𝓔-nonempty : ∀ γ → proof.Framework.GraphModel.Env.nonempty-env (𝓔 γ)
  𝓔-nonempty [] x = ⟨ ω , refl ⟩
  𝓔-nonempty (v ∷ γ) zero = 𝒱-nonempty v
  𝓔-nonempty (v ∷ γ) (suc x) = 𝓔-nonempty γ x

  𝓔-lookup : ∀ γ x {v} → γ ‼ x ≡ just v → 𝒱 v ⊆ 𝓔 γ x
  𝓔-lookup (v ∷ γ) zero refl d d∈ = d∈
  𝓔-lookup (v ∷ γ) (suc x) eq = 𝓔-lookup γ x eq

  {- β for one parameter (case, let) -}
  body-in : ∀ N γ v d → d ∈ ⟦ N ⟧⁺ (𝓔 (v ∷ γ))
    → Σ[ V ∈ List Value ] V ≢ [] × mem V ⊆ 𝒱 v × d ∈ ⟦ N ⟧⁺ (mem V • 𝓔 γ)
  body-in N γ v d d∈ with term-continuous T⁺ N (𝓔 (v ∷ γ)) (𝓔-nonempty (v ∷ γ)) d d∈
  ... | ⟨ Vs , ⟨ ok , d∈′ ⟩ ⟩ =
    ⟨ Vs 0 , ⟨ proj₁ (ok 0) , ⟨ proj₂ (ok 0) , ⟦⟧[]-monotone T⁺ N G d d∈′ ⟩ ⟩ ⟩
    where
    G : ∀ x → mem (Vs x) ⊆ (mem (Vs 0) • 𝓔 γ) x
    G zero d d∈ = d∈
    G (suc x) = proj₂ (ok (suc x))

  {- β for the two parameters of code: calling code k, found in the table
     as B, on the environment e and the argument w -}
  call-⊆ : ∀ k {B} w e → global ds k ≡ just B
    → ⟦ B ⟧⁺ (𝓔 (w ∷ e ∷ [])) ⊆ ⋆ ⟨ ⋆ ⟨ T⁺ k , ⟨ 𝒱 e , ptt ⟩ ⟩ , ⟨ 𝒱 w , ptt ⟩ ⟩
  call-⊆ k {B} w e g d d∈ with global-split k g
  ... | ⟨ Ns , ⟨ p , refl ⟩ ⟩
      with term-continuous (table Ns) B ρ (𝓔-nonempty (w ∷ e ∷ [])) d
             (proj₁ (stab (length Ns) T⁺ (table Ns) B ρ ρ ag (proj₁ (proj₁ (DefsWF-⊑ p wf)))
                       (λ x → ≃-refl)) d d∈)
    where
    ρ = 𝓔 (w ∷ e ∷ [])
    ag : Agree (length Ns) T⁺ (table Ns)
    ag j j< = ⟨ to , (λ x x∈ → inj₁ (≡→⊆ (sym (table-agree (∷-⊑ p) j j<)) x x∈)) ⟩
      where
      to : T⁺ j ⊆ table Ns j
      to x (inj₁ x∈) = ≡→⊆ (table-agree (∷-⊑ p) j j<) x x∈
      to x (inj₂ refl) = ν-table Ns j j<
  ... | ⟨ Vs , ⟨ ok , d∈′ ⟩ ⟩ =
    ⟨ Vs 0 , ⟨ ⟨ Vs 1 , ⟨ inj₁ (≡→⊆ (sym (table-at p)) _ in-code)
                       , ⟨ proj₂ (ok 1) , proj₁ (ok 1) ⟩ ⟩ ⟩
             , ⟨ proj₂ (ok 0) , proj₁ (ok 0) ⟩ ⟩ ⟩
    where
    G : ∀ x → mem (Vs x) ⊆ (mem (Vs 0) • mem (Vs 1) • (λ _ → init)) x
    G zero d d∈ = d∈
    G (suc zero) d d∈ = d∈
    G (suc (suc x)) = proj₂ (ok (suc (suc x)))
    in-code : (Vs 1 ↦ (Vs 0 ↦ d)) ∈ codeD (table Ns) B
    in-code = ⟨ ⟨ ⟦⟧[]-monotone (table Ns) B G d d∈′ , ⟨ proj₁ (ok 0) , Con⇒≈ (Vs 0) (𝒱-con w) (proj₂ (ok 0)) ⟩ ⟩
              , ⟨ proj₁ (ok 1) , Con⇒≈ (Vs 1) (𝒱-con e) (proj₂ (ok 1)) ⟩ ⟩

  {- Tuples --------------------------------------------------------------------}

  𝒱s-reverseAcc : ∀ acc vs → 𝒱s (reverseAcc acc vs) ≡ rev𝒱 vs (𝒱s acc)
  𝒱s-reverseAcc acc [] = refl
  𝒱s-reverseAcc acc (v ∷ vs) = 𝒱s-reverseAcc (v ∷ acc) vs

  tuple-next-𝒮 : ∀ vs Ms γ κ → 𝒮 (tuple-next vs Ms γ κ) ⊆ 𝒦 κ (𝒯L (rev𝒱 vs (⟦ Ms ⟧* (𝓔 γ))))
  tuple-next-𝒮 vs [] γ κ d d∈ = subst (λ Ds → 𝒦 κ (𝒯L Ds) d) (𝒱s-reverseAcc [] vs) d∈
  tuple-next-𝒮 vs (M ∷ Ms) γ κ d d∈ = d∈

  At-args : ∀ {n} (args : Args (replicate n ■)) ρ (i : Fin n) d
    → At i (⟦ args→list args ⟧* ρ) d → d ∈ nthD (⟦ args ⟧₊[ T⁺ ] ρ) i
  At-args {suc n} (M ,, args) ρ zero d ⟨ _ , d∈ ⟩ = d∈
  At-args {suc n} (M ,, args) ρ (suc i) d a = At-args args ρ i d a

  AllNE-args : ∀ {n} (args : Args (replicate n ■)) ρ
    → AllNE (⟦ args→list args ⟧* ρ) → ∀ i → nonempty (nthD (⟦ args ⟧₊[ T⁺ ] ρ) i)
  AllNE-args {suc n} (M ,, args) ρ ⟨ ne , _ ⟩ zero = ne
  AllNE-args {suc n} (M ,, args) ρ ⟨ _ , nes ⟩ (suc i) = AllNE-args args ρ nes i

  length-args : ∀ {n} (args : Args (replicate n ■)) ρ → length (⟦ args→list args ⟧* ρ) ≡ n
  length-args {zero} Nil ρ = refl
  length-args {suc n} (M ,, args) ρ = cong suc (length-args args ρ)

  𝒯L-args : ∀ {n} (args : Args (replicate n ■)) ρ → 𝒯L (⟦ args→list args ⟧* ρ) ⊆ 𝒯 n (⟦ args ⟧₊[ T⁺ ] ρ)
  𝒯L-args {zero} Nil ρ ⟨⟩ tt = tt
  𝒯L-args {zero} Nil ρ (tup[ zero ] d) ⟨ () , _ ⟩
  𝒯L-args {zero} Nil ρ (tup[ suc i ] d) ⟨ () , _ ⟩
  𝒯L-args {suc n} (M ,, args) ρ ⟨⟩ ()
  𝒯L-args {suc n} args ρ (tup[_]_ {m} i d) ⟨ a , ne ⟩
      with At-length i _ d a
  ... | len with subst (λ k → k ≡ m) (length-args args ρ) len
  ... | refl = ⟨ refl , ⟨ At-args args ρ i d a , AllNE-args args ρ ne ⟩ ⟩

  {- Steps shrink the denotation of the state --------------------------------}

  step-⊆ : ∀ s {s'} → step ds s ≡ next s' → 𝒮 s' ⊆ 𝒮 s
  step-⊆ (eval (` x) γ κ) eq with γ ‼ x in look
  step-⊆ (eval (` x) γ κ) refl | just v = 𝒦-mono κ (𝓔-lookup γ x look)
  step-⊆ (eval (` x) γ κ) () | nothing
  step-⊆ (eval (fun-ref k ⦅ Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (app ⦅ L ,, M ,, N ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (lit B k ⦅ Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (pair-op ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (fst-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (snd-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (tuple n ⦅ args ⦆) γ κ) refl d d∈ =
    𝒦-mono κ (𝒯L-args args (𝓔 γ)) d (tuple-next-𝒮 [] (args→list args) γ κ d d∈)
  step-⊆ (eval (get i ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (ret v halt) ()
  step-⊆ (ret f (appF M N γ κ)) refl d d∈ = d∈
  step-⊆ (ret e (appE f N γ κ)) refl d d∈ = d∈
  step-⊆ (ret w (appA (code k) e κ)) eq with global ds k in g
  step-⊆ (ret w (appA (code k) e κ)) refl | just B = 𝒦-mono κ (call-⊆ k w e g)
  step-⊆ (ret w (appA (code k) e κ)) () | nothing
  step-⊆ (ret w (appA (pair _ _) e κ)) ()
  step-⊆ (ret w (appA (const B k) e κ)) ()
  step-⊆ (ret w (appA (tup vs) e κ)) ()
  step-⊆ (ret w (appA (T.inl v) e κ)) ()
  step-⊆ (ret w (appA (T.inr v) e κ)) ()
  step-⊆ (ret v (pairL M γ κ)) refl d d∈ = d∈
  step-⊆ (ret w (pairR v κ)) refl d d∈ = d∈
  step-⊆ (ret (pair v w) (fstK κ)) refl = 𝒦-mono κ λ d d∈ → ⟨ proj₁ (𝒱-nonempty w) , ⟨ d∈ , proj₂ (𝒱-nonempty w) ⟩ ⟩
  step-⊆ (ret (code k) (fstK κ)) ()
  step-⊆ (ret (const B k) (fstK κ)) ()
  step-⊆ (ret (tup vs) (fstK κ)) ()
  step-⊆ (ret (T.inl v) (fstK κ)) ()
  step-⊆ (ret (T.inr v) (fstK κ)) ()
  step-⊆ (ret (pair v w) (sndK κ)) refl = 𝒦-mono κ λ d d∈ → ⟨ proj₁ (𝒱-nonempty v) , ⟨ proj₂ (𝒱-nonempty v) , d∈ ⟩ ⟩
  step-⊆ (ret (code k) (sndK κ)) ()
  step-⊆ (ret (const B k) (sndK κ)) ()
  step-⊆ (ret (tup vs) (sndK κ)) ()
  step-⊆ (ret (T.inl v) (sndK κ)) ()
  step-⊆ (ret (T.inr v) (sndK κ)) ()
  step-⊆ (ret v (tupK vs Ms γ κ)) refl = tuple-next-𝒮 (v ∷ vs) Ms γ κ
  step-⊆ (ret (tup vs) (getK i κ)) eq with proj i vs in p
  step-⊆ (ret (tup vs) (getK i κ)) refl | just v =
    𝒦-mono κ λ d d∈ → ⟨ proj-𝒱s i vs p d d∈ , 𝒱s-nonempty vs ⟩
  step-⊆ (ret (tup vs) (getK i κ)) () | nothing
  step-⊆ (ret (code k) (getK i κ)) ()
  step-⊆ (ret (pair v w) (getK i κ)) ()
  step-⊆ (ret (const B k) (getK i κ)) ()
  step-⊆ (ret (T.inl v) (getK i κ)) ()
  step-⊆ (ret (T.inr v) (getK i κ)) ()
  step-⊆ (ret v (inlK κ)) refl d d∈ = d∈
  step-⊆ (ret v (inrK κ)) refl d d∈ = d∈
  step-⊆ (ret (T.inl v) (caseK M N γ κ)) refl = 𝒦-mono κ β
    where
    β : ⟦ M ⟧⁺ (𝓔 (v ∷ γ)) ⊆ _
    β d d∈ with body-in M γ v d d∈
    ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
    ... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = inj₁ ⟨ u , ⟨ U , ⟨ V⊆ , ⟨ d∈′ , Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ ⟩ ⟩ ⟩ ⟩
  step-⊆ (ret (T.inr v) (caseK M N γ κ)) refl = 𝒦-mono κ β
    where
    β : ⟦ N ⟧⁺ (𝓔 (v ∷ γ)) ⊆ _
    β d d∈ with body-in N γ v d d∈
    ... | ⟨ [] , ⟨ ne , _ ⟩ ⟩ = ⊥-elim (ne refl)
    ... | ⟨ u ∷ U , ⟨ _ , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = inj₂ ⟨ u , ⟨ U , ⟨ V⊆ , ⟨ d∈′ , Con⇒≈ (u ∷ U) (𝒱-con v) V⊆ ⟩ ⟩ ⟩ ⟩
  step-⊆ (ret (code k) (caseK M N γ κ)) ()
  step-⊆ (ret (pair v w) (caseK M N γ κ)) ()
  step-⊆ (ret (const B k) (caseK M N γ κ)) ()
  step-⊆ (ret (tup vs) (caseK M N γ κ)) ()
  step-⊆ (ret v (letK N γ κ)) refl = 𝒦-mono κ β
    where
    β : ⟦ N ⟧⁺ (𝓔 (v ∷ γ)) ⊆ _
    β d d∈ with body-in N γ v d d∈
    ... | ⟨ V , ⟨ ne , ⟨ V⊆ , d∈′ ⟩ ⟩ ⟩ = ⟨ V , ⟨ ⟨ d∈′ , ⟨ ne , Con⇒≈ V (𝒱-con v) V⊆ ⟩ ⟩ , ⟨ V⊆ , ne ⟩ ⟩ ⟩
  step-⊆ (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) refl d d∈ = d∈
  step-⊆ (ret v (primL p M γ κ)) refl d d∈ = d∈
  step-⊆ (ret w (primR p v κ)) eq with δ? p (obs v) (obs w) in e
  step-⊆ (ret w (primR p v κ)) refl | just r = 𝒦-mono κ (prim-⊆ p v w r e)
  step-⊆ (ret w (primR p v κ)) () | nothing

  ↠-⊆ : ∀ {s t} → s ↠ t → 𝒮 t ⊆ 𝒮 s
  ↠-⊆ done d d∈ = d∈
  ↠-⊆ {s} (st ∷↠ σ) d d∈ = step-⊆ s st d (↠-⊆ σ d d∈)

  {- Final states ----------------------------------------------------------------}

  private
    error : ∀ {o} → stop {State} o-error ≡ stop o → Answer o → ⊥
    error refl ans = ans refl

  {- a state that stops with an answer returns a value to halt -}
  halts : ∀ s {o} → step ds s ≡ stop o → Answer o → Σ[ v ∈ Val ] s ≡ ret v halt × o ≡ obs v
  halts (eval (` x) γ κ) eq ans with γ ‼ x
  halts (eval (` x) γ κ) () ans | just v
  halts (eval (` x) γ κ) eq ans | nothing = ⊥-elim (error eq ans)
  halts (eval (fun-ref k ⦅ Nil ⦆) γ κ) () ans
  halts (eval (app ⦅ L ,, M ,, N ,, Nil ⦆) γ κ) () ans
  halts (eval (lit B k ⦅ Nil ⦆) γ κ) () ans
  halts (eval (pair-op ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
  halts (eval (fst-op ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (snd-op ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (tuple n ⦅ args ⦆) γ κ) () ans
  halts (eval (get i ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (inl-op ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (inr-op ⦅ M ,, Nil ⦆) γ κ) () ans
  halts (eval (case-op ⦅ L ,, ⟩ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
  halts (eval (let-op ⦅ M ,, ⟩ N ,, Nil ⦆) γ κ) () ans
  halts (ret v halt) refl ans = ⟨ v , ⟨ refl , refl ⟩ ⟩
  halts (ret f (appF M N γ κ)) () ans
  halts (ret e (appE f N γ κ)) () ans
  halts (ret w (appA (code k) e κ)) eq ans with global ds k
  halts (ret w (appA (code k) e κ)) () ans | just B
  halts (ret w (appA (code k) e κ)) eq ans | nothing = ⊥-elim (error eq ans)
  halts (ret w (appA (pair _ _) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret w (appA (const B k) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret w (appA (tup vs) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret w (appA (T.inl v) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret w (appA (T.inr v) e κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret v (pairL M γ κ)) () ans
  halts (ret w (pairR v κ)) () ans
  halts (ret (pair v w) (fstK κ)) () ans
  halts (ret (code k) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (const B k) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (tup vs) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (T.inl v) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (T.inr v) (fstK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (pair v w) (sndK κ)) () ans
  halts (ret (code k) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (const B k) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (tup vs) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (T.inl v) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (T.inr v) (sndK κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret v (tupK vs Ms γ κ)) () ans
  halts (ret (tup vs) (getK i κ)) eq ans with proj i vs
  halts (ret (tup vs) (getK i κ)) () ans | just v
  halts (ret (tup vs) (getK i κ)) eq ans | nothing = ⊥-elim (error eq ans)
  halts (ret (code k) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (pair v w) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (const B k) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (T.inl v) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (T.inr v) (getK i κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret v (inlK κ)) () ans
  halts (ret v (inrK κ)) () ans
  halts (ret (T.inl v) (caseK M N γ κ)) () ans
  halts (ret (T.inr v) (caseK M N γ κ)) () ans
  halts (ret (code k) (caseK M N γ κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (pair v w) (caseK M N γ κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (const B k) (caseK M N γ κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret (tup vs) (caseK M N γ κ)) eq ans = ⊥-elim (error eq ans)
  halts (ret v (letK N γ κ)) () ans
  halts (eval (prim p ⦅ L ,, M ,, Nil ⦆) γ κ) () ans
  halts (ret v (primL p M γ κ)) () ans
  halts (ret w (primR p v κ)) eq ans with δ? p (obs v) (obs w)
  halts (ret w (primR p v κ)) () ans | just r
  halts (ret w (primR p v κ)) eq ans | nothing = ⊥-elim (error eq ans)

  final-shape : ∀ s {o} → step ds s ≡ stop o → Answer o → Σ[ d ∈ Value ] d ∈ 𝒮 s × ShapeOf o d
  final-shape s fin ans with halts s fin ans
  ... | ⟨ v , ⟨ refl , refl ⟩ ⟩ = 𝒱-shape v

{- Soundness ------------------------------------------------------------------}

{- a well-formed program that terminates with an answer o has an element
   of the shape of o in its denotation -}
soundness : ∀ P → WF P → ∀ {o} → Terminates (sem P) o → Answer o
  → Σ[ d ∈ Value ] d ∈ ⟦ P ⟧ₚ × ShapeOf o d
soundness (program ds M) ⟨ wfd , ⟨ rb , _ ⟩ ⟩ (⟨ s , ⟨ σ , fin ⟩ ⟩) ans
    with final-shape ds wfd s fin ans
... | ⟨ d , ⟨ d∈ , sh ⟩ ⟩ =
  ⟨ d , ⟨ proj₁ (stab (length ds) (T⁺ ds wfd) (table ds) M ρ ρ ag rb (λ x → ≃-refl)) d
            (↠-⊆ ds wfd (Common.star→↠ ds σ) d d∈)
        , sh ⟩ ⟩
  where
  ρ : VEnv
  ρ = λ _ → init
  ag : Agree (length ds) (T⁺ ds wfd) (table ds)
  ag j j< = ⟨ to , (λ x x∈ → inj₁ x∈) ⟩
    where
    to : T⁺ ds wfd j ⊆ table ds j
    to x (inj₁ x∈) = x∈
    to x (inj₂ refl) = Common.ν-table ds ds j j<
