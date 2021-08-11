module ISWIMPlusPValue where

open import Primitives
open import Syntax using (Rename)
open import ISWIMPlus hiding (Ctx)
open ISWIMPlus.ASTMod using (WF-rel; len-mk-list)
open import AbstractBindingTree Op sig using (Ctx; CHole)
open import WellScoped Op sig using (WF-plug; not-WF-0-var) 
open import Fold2 Op sig
open import ScopedTuple hiding (𝒫)
open import Sig
open import Utilities using (extensionality)
open import SetsAsPredicates
open import PValueCBV renaming (cons to 〘_,_〙)
open import SemanticProperties Op sig

open import Data.Empty using (⊥-elim) renaming (⊥ to False)
open import Data.List using (List ; _∷_ ; []; length; replicate)
open import Data.List.Relation.Unary.Any using (here; there) 
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂)
    renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt) renaming (⊤ to True)
open import Level renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality
    using (_≡_; _≢_; refl; sym; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)


{- Denotational Semantics of the ISWIM Language via fold ----------------------}

interp-op  : (op : Op) → Tuple (sig op) (Result (𝒫 Value)) → 𝒫 Value
interp-op lam ⟨ F , _ ⟩ = Λ F
interp-op app ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = D₁ ▪ D₂
interp-op (lit P k) _ = ℘ P k
interp-op pair-op ⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩ = 〘 D₁ , D₂ 〙
interp-op fst-op ⟨ D , _ ⟩  = car D
interp-op snd-op ⟨ D , _ ⟩ = cdr D
interp-op (tuple n) args = 𝒯 n args
interp-op (get i) ⟨ D , _ ⟩ = proj D i

{- interp-op is monotonic -}
mono-op : {op : Op} {xs ys : Tuple (sig op) (Result (𝒫 Value))}
   → ⊆-results (sig op) xs ys → interp-op op xs ⊆ interp-op op ys
mono-op {lam} {⟨ f , _ ⟩ } {⟨ g , _ ⟩} ⟨ f⊆g , _ ⟩ =
    Λ-ext-⊆ (λ {X} → lower (f⊆g X))
mono-op {app} {⟨ a , ⟨ b , _ ⟩ ⟩} {⟨ c , ⟨ d , _ ⟩ ⟩} ⟨ a<c , ⟨ b<d , _ ⟩ ⟩ =
    ▪-cong-⊆ (lower a<c) (lower b<d)
mono-op {lit P k} {xs} {ys} xs⊆ys d d∈k = d∈k
mono-op {pair-op} {⟨ D₁ , ⟨ D₂ , _ ⟩ ⟩} {⟨ E₁ , ⟨ E₂ , _ ⟩ ⟩}
    ⟨ lift D₁⊆E₁ , ⟨ lift D₂⊆E₂ , _ ⟩ ⟩ = cons-cong-⊆ D₁⊆E₁ D₂⊆E₂
mono-op {fst-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = car-cong-⊆ D⊆E 
mono-op {snd-op} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = cdr-cong-⊆ D⊆E 
mono-op {tuple n} {args₁}{args₂} IHs =
    𝒯-cong-⊆ (rel-results⇒rel-∏ ⊆-result⇒⊆ IHs)
mono-op {get i} {⟨ D , _ ⟩} {⟨ E , _ ⟩} ⟨ lift D⊆E , _ ⟩ = proj-cong-⊆ D⊆E

instance
  ISWIM-Semantics : Semantics
  ISWIM-Semantics = record { interp-op = interp-op ;
                             mono-op = λ {op} → mono-op {op} }
open Semantics {{...}}

⟦⟧-app : ∀{L M : Term}{ρ : Env}
  → ⟦ L · M ⟧ ρ ≡ ⟦ L ⟧ ρ ▪ ⟦ M ⟧ ρ
⟦⟧-app = refl

⟦⟧-lam : ∀{N : Term}{ρ : Env}
  → ⟦ ƛ N ⟧ ρ ≡ Λ (λ D → ⟦ N ⟧ (D • ρ))
⟦⟧-lam = refl

⟦⟧-prim : ∀{P : Prim}{k : rep P}{ρ : Env}
  → ⟦ $ P k ⟧ ρ ≡ ℘ P k
⟦⟧-prim = refl

{- interp-op is continuous -}
continuous-op : ∀{op}{ρ}{NE-ρ}{v}{args}
   → v ∈ ⟦ op ⦅ args ⦆ ⟧ ρ
   → all-args (Cont-Env-Arg ρ NE-ρ) (sig op) args
   → Σ[ ρ′ ∈ Env ] finite-env ρ′ × ρ′ ⊆ₑ ρ × v ∈ (⟦ op ⦅ args ⦆ ⟧ ρ′)
continuous-op {lam} {ρ} {NE-ρ} {v} {cons (bind (ast N)) nil}
    v∈Λ ⟨ IH-N , _ ⟩ =
    Λ-continuous {NE-ρ = NE-ρ} v∈Λ IH-N (⟦⟧-monotone N)
continuous-op {app} {ρ} {NE-ρ} {w} {cons (ast L) (cons (ast M) nil)}
    w∈⟦L·M⟧ρ ⟨ IH-L , ⟨ IH-M , _ ⟩ ⟩ =
    ▪-continuous{NE-ρ = NE-ρ} w∈⟦L·M⟧ρ IH-L IH-M (⟦⟧-monotone L) (⟦⟧-monotone M)
continuous-op {lit p x} {ρ} {NE-ρ} {v} {nil} v∈⟦M⟧ρ _ =
    ⟨ initial-finite-env ρ NE-ρ , ⟨ initial-fin ρ NE-ρ ,
    ⟨ initial-fin-⊆ ρ NE-ρ ,
      v∈⟦M⟧ρ ⟩ ⟩ ⟩
continuous-op {pair-op}{ρ}{NE-ρ}{v}{cons (ast M) (cons (ast N) nil)} v∈⟦M⟧ρ
    ⟨ IH-M , ⟨ IH-N , _ ⟩ ⟩ =
    cons-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ IH-M IH-N
        (⟦⟧-monotone M) (⟦⟧-monotone N)
continuous-op {fst-op} {ρ} {NE-ρ} {v} {cons (ast M) nil} v∈⟦M⟧ρ
    ⟨ IH-M , _ ⟩ =
    car-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ IH-M (⟦⟧-monotone M)
continuous-op {snd-op} {ρ} {NE-ρ} {v} {cons (ast M) nil} v∈⟦M⟧ρ
    ⟨ IH-M , _ ⟩ =
    cdr-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ IH-M (⟦⟧-monotone M)
continuous-op {tuple n} {ρ} {NE-ρ} {v} {args} v∈⟦M⟧ρ cont-args =
   let Ds : Env → ∏ n (𝒫 Value)
       Ds = ⟦ args ⟧₊ in
   let xx : v ∈ 𝒯 n (Ds ρ)
       xx = v∈⟦M⟧ρ in
   {!!}
continuous-op {get i} {ρ} {NE-ρ} {v} {cons (ast M) nil} v∈⟦M⟧ρ ⟨ cM , _ ⟩ =
    proj-continuous{NE-ρ = NE-ρ} v∈⟦M⟧ρ cM (⟦⟧-monotone M)

instance
  ISWIM-Continuous : ContinuousSemantics
  ISWIM-Continuous = record { continuous-op =
      λ{op}{ρ}{NE-ρ} → continuous-op{op}{ρ}{NE-ρ} }
open ContinuousSemantics {{...}}

{- Syntactic values terminate (i.e., have nonempty denotations) ---------------}

value-nonempty : ∀{V : Term}{ρ}
  → nonempty-env ρ → TermValue V → nonempty (⟦ V ⟧ ρ)
value-nonempty NE-ρ (V-var {x}) = NE-ρ x
value-nonempty NE-ρ (V-ƛ) = ⟨ ν , tt ⟩
value-nonempty NE-ρ (V-lit {base B} {k}) = ⟨ const k , k∈℘k ⟩
value-nonempty NE-ρ (V-lit {B ⇒ P} {k}) = ⟨ ν , tt ⟩
value-nonempty NE-ρ (V-pair Mv Nv)
    with value-nonempty NE-ρ Mv | value-nonempty NE-ρ Nv
... | ⟨ u , u∈ ⟩ | ⟨ v , v∈ ⟩ =
    ⟨ ❲ u , v ❳ , ⟨ u∈ , v∈ ⟩ ⟩
value-nonempty NE-ρ (V-tuple vs) = {!!}

{- Substitution Lemma (via fold-subst-fusion) ---------------------------------}

⟦⟧-par-subst : ∀ {M : Term}{σ : Subst}{ρ : Var → 𝒫 Value}
  → ⟦ ⟪ σ ⟫ M ⟧ ρ ≡ ⟦ M ⟧ (λ x → ⟦ σ x ⟧ ρ)
⟦⟧-par-subst {M}{ρ} = fold-subst-fusion M

⟦⟧-subst : ∀ {M N : Term}{ρ : Var → 𝒫 Value}
  → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ ((⟦ N ⟧ ρ) • ρ)
⟦⟧-subst {M}{N}{ρ} =
  subst (λ X → ⟦ M [ N ] ⟧ ρ ≡ ⟦ M ⟧ X) (extensionality EQ)
        (⟦⟧-par-subst {M}{N • id})
  where 
  EQ : (x : Var) → ⟦ (N • id) x ⟧ ρ ≡ (⟦ N ⟧ ρ • ρ) x
  EQ zero = refl
  EQ (suc x) = refl

{- Soundness of Reduction with respect to Denotations -------------------------}

ArgsValue⇒NE-∏ : ∀{n}{args : Args (Data.List.replicate n ■)}
    {ρ}{NE-ρ : nonempty-env ρ}
   → ArgsValue args → NE-∏ (⟦ args ⟧₊ ρ)
ArgsValue⇒NE-∏ {zero} {nil} vs = {!!}
ArgsValue⇒NE-∏ {suc n} {cons (ast M) args}{ρ}{NE-ρ} (V-cons Mv vs) =
    ⟨ value-nonempty NE-ρ Mv , ArgsValue⇒NE-∏ {NE-ρ = NE-ρ} vs ⟩

⟦⟧—→ : ∀{M N : Term}{ρ : Var → 𝒫 Value} {NE-ρ : nonempty-env ρ}
   → M —→ N
   → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
⟦⟧—→ {.(_ · _)} {.(_ · _)} {ρ} {NE-ρ} (ξ-rule {L}{L′} (F-·₁ M) L—→L′) = 
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} L—→L′ in
    ⟦ L · M ⟧ ρ              ≃⟨⟩
    (⟦ L ⟧ ρ) ▪ (⟦ M ⟧ ρ)    ≃⟨ ▪-cong IH ≃-refl ⟩
    (⟦ L′ ⟧ ρ) ▪ (⟦ M ⟧ ρ)   ≃⟨⟩
    ⟦ L′ · M ⟧ ρ             ∎ where open ≃-Reasoning  
⟦⟧—→ {.(_ · _)} {.(_ · _)} {ρ} {NE-ρ} (ξ-rule {M}{M′} (F-·₂ V {v}) M—→M′) =
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ in
    ⟦ V · M ⟧ ρ              ≃⟨⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M ⟧ ρ)    ≃⟨ ▪-cong (≃-refl{D = ⟦ V ⟧ ρ}) IH ⟩
    (⟦ V ⟧ ρ) ▪ (⟦ M′ ⟧ ρ)   ≃⟨⟩
    ⟦ V · M′ ⟧ ρ             ∎ where open ≃-Reasoning
⟦⟧—→ {.(pair _ _)} {.(pair _ _)} {ρ} {NE-ρ} (ξ-rule {M}{M′} (F-×₁ N) M—→M′) =
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ in
    ⟦ pair M N ⟧ ρ              ≃⟨⟩
    〘 ⟦ M ⟧ ρ , ⟦ N ⟧ ρ 〙      ≃⟨ cons-cong IH ≃-refl ⟩
    〘 ⟦ M′ ⟧ ρ , ⟦ N ⟧ ρ 〙     ≃⟨⟩
    ⟦ pair M′ N ⟧ ρ             ∎ where open ≃-Reasoning  
⟦⟧—→ {.(pair V _)} {.(pair V _)} {ρ} {NE-ρ} (ξ-rule {M}{M′}(F-×₂ V {v}) M—→M′) =
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ in
    ⟦ pair V M ⟧ ρ              ≃⟨⟩
   〘 ⟦ V ⟧ ρ , ⟦ M ⟧ ρ 〙      ≃⟨ cons-cong (≃-refl{D = ⟦ V ⟧ ρ}) IH ⟩
   〘 ⟦ V ⟧ ρ , ⟦ M′ ⟧ ρ 〙     ≃⟨⟩
    ⟦ pair V M′ ⟧ ρ             ∎ where open ≃-Reasoning
⟦⟧—→ {.(fst _)} {.(fst _)} {ρ} {NE-ρ} (ξ-rule {M}{M′} F-fst M—→M′) =
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ in
    ⟦ fst M ⟧ ρ              ≃⟨⟩
    car (⟦ M ⟧ ρ)            ≃⟨ car-cong IH ⟩
    car (⟦ M′ ⟧ ρ)            ≃⟨⟩
    ⟦ fst M′ ⟧ ρ             ∎ where open ≃-Reasoning
⟦⟧—→ {.(snd _)} {.(snd _)} {ρ} {NE-ρ} (ξ-rule {M}{M′} F-snd M—→M′) =
    let IH = ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ in
    ⟦ snd M ⟧ ρ              ≃⟨⟩
    cdr (⟦ M ⟧ ρ)            ≃⟨ cdr-cong IH ⟩
    cdr (⟦ M′ ⟧ ρ)            ≃⟨⟩
    ⟦ snd M′ ⟧ ρ             ∎ where open ≃-Reasoning
⟦⟧—→ {_} {_} {ρ} {NE-ρ} (ξ-rule {M}{M′} (F-tuple vargs vs args) M—→M′) = {!!}
⟦⟧—→ {_} {_} {ρ} {NE-ρ} (ξ-rule {M}{M′} (F-get i) M—→M′) = {!!}
⟦⟧—→ {ƛ N · V} {_} {ρ} {NE-ρ} (β-rule v) =
    ⟦ ƛ N · V ⟧ ρ                           ≃⟨⟩
    (Λ (λ D → ⟦ N ⟧ (D • ρ))) ▪ (⟦ V ⟧ ρ)   ≃⟨ Λ⟦⟧-▪-id {N}{ρ}{NE-ρ}
                                                   (value-nonempty NE-ρ v) ⟩
    ⟦ N ⟧ (⟦ V ⟧ ρ • ρ)               ≃⟨ ≃-reflexive (sym (⟦⟧-subst{N}{V}{ρ})) ⟩
    ⟦ N [ V ] ⟧ ρ                     ∎ where open ≃-Reasoning
⟦⟧—→ {($ (B ⇒ P) f · $ (base B) k)} {_} {ρ} δ-rule =
    ⟦ $ (B ⇒ P) f · $ (base B) k ⟧ ρ        ≃⟨⟩
    (℘ (B ⇒ P) f) ▪ (℘ (base B) k)         ≃⟨ ℘-▪-≃ {B}{P} ⟩
    ⟦ $ P (f k) ⟧ ρ                         ∎ where open ≃-Reasoning
⟦⟧—→ {.(fst (pair _ _))} {_} {ρ} {NE-ρ} (fst-rule {N}{M} Mv Nv) =
    ⟦ fst (pair M N) ⟧ ρ          ≃⟨⟩ 
    car 〘 ⟦ M ⟧ ρ , ⟦ N ⟧ ρ 〙    ≃⟨ car-of-cons (value-nonempty NE-ρ Nv) ⟩ 
    ⟦ M ⟧ ρ                        ∎ where open ≃-Reasoning
⟦⟧—→ {.(snd (pair _ _))} {_} {ρ} {NE-ρ} (snd-rule {N}{M} Mv Nv) =
    ⟦ snd (pair M N) ⟧ ρ          ≃⟨⟩ 
    cdr 〘 ⟦ M ⟧ ρ , ⟦ N ⟧ ρ 〙    ≃⟨ cdr-of-cons (value-nonempty NE-ρ Mv) ⟩ 
    ⟦ N ⟧ ρ                        ∎ where open ≃-Reasoning
⟦⟧—→ {_} {_} {ρ} {NE-ρ} (get-rule {n}{i}{args} vs) =
    ⟦ get i ⦅ cons (ast (tuple n ⦅ args ⦆)) nil ⦆ ⟧ ρ   ≃⟨⟩
    proj (𝒯 n (⟦ args ⟧₊ ρ)) i            ≃⟨ G i n args vs ⟩
    ⟦ nth-arg args i ⟧ ρ               ∎
    where
    open ≃-Reasoning
    G : ∀ i n (args : Args (replicate n ■)) → ArgsValue args
       → proj (𝒯 n (⟦ args ⟧₊ ρ)) i ≃ ⟦ nth-arg args i ⟧ ρ
    G i zero nil vs = ⟨ H , J ⟩
      where
      H : proj (𝒯 zero (⟦ nil ⟧₊ ρ)) i ⊆ ⟦ $ (base Nat) 0 ⟧ ρ
      H v ⟨ vs , ⟨ _ , refl ⟩ ⟩ = {!!}
      J : ⟦ $ (base Nat) 0 ⟧ ρ ⊆ proj (𝒯 zero (⟦ nil ⟧₊ ρ)) i
      J (const {B} k) xx
          with base-eq? Nat B | xx
      ... | yes refl | refl = ⟨ [] , ⟨ {!!} , refl ⟩ ⟩
      ... | no neq | ()

    G 0 (suc n) (cons (ast M) args) (V-cons Mv vs) = 
      proj (𝒯 (suc n) (⟦ cons (ast M) args ⟧₊ ρ)) zero   ≃⟨⟩
      proj (𝒯 (suc n) ⟨ ⟦ M ⟧ ρ , ⟦ args ⟧₊ ρ ⟩) zero   ≃⟨ 𝒯-nth-0 (ArgsValue⇒NE-∏{NE-ρ = NE-ρ} vs) ⟩
      ⟦ M ⟧ ρ                                  ≃⟨⟩
      ⟦ nth-arg (cons (ast M) args) zero ⟧ ρ   ∎
    G (suc i) (suc n) (cons (ast M) args) (V-cons Mv vs) =
        let IH = G i n args vs in
        proj (𝒯 (suc n) (⟦ cons (ast M) args ⟧₊ ρ)) (suc i) ≃⟨⟩ 
        proj (𝒯 (suc n) ⟨ ⟦ M ⟧ ρ , ⟦ args ⟧₊ ρ ⟩) (suc i)
                                  ≃⟨ 𝒯-nth-suc (value-nonempty NE-ρ Mv)
                                            (ArgsValue⇒NE-∏{NE-ρ = NE-ρ} vs) ⟩ 
        proj (𝒯 n (⟦ args ⟧₊ ρ)) i             ≃⟨ IH ⟩ 
        ⟦ nth-arg args i ⟧ ρ ∎

    

soundness : ∀ {M N : Term} {ρ : Env}{NE-ρ : nonempty-env ρ}
  → M —↠ N
    -------------------
  → ⟦ M ⟧ ρ ≃ ⟦ N ⟧ ρ
soundness {M}{_}{ρ} (M □) =
    ⟦ M ⟧ ρ ≃⟨⟩ ⟦ M ⟧ ρ ∎ where open ≃-Reasoning
soundness {M}{N}{ρ}{NE-ρ} (_—→⟨_⟩_ M {M = M′} M—→M′ M′—↠N) =
    ⟦ M ⟧ ρ      ≃⟨ ⟦⟧—→{ρ = ρ}{NE-ρ} M—→M′ ⟩ 
    ⟦ M′ ⟧ ρ     ≃⟨ soundness{ρ = ρ}{NE-ρ} M′—↠N ⟩ 
    ⟦ N ⟧ ρ      ∎ where open ≃-Reasoning

