\begin{code}
module SN where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.List using ([] ; _∷_)
open import Data.Product using (∃-syntax; Σ-syntax; _,_)
open import Function using (id; _∘_; _$_) renaming (_∋_ to _of-type_)

open import Common
open import STLC hiding ()

\end{code}

TODO desc

\begin{code}

record _⇓ {Γ σ} (e : Γ ⊢ σ) : Set where
  constructor pack
  field
    v     :  Γ ⊢ σ
    V     :  Value v
    e—↠v  :  e —↠ v

V⇓ : ∀ {Γ σ} {v : Γ ⊢ σ}
   → Value v
     -------
   → v ⇓
V⇓ {v = v} V = pack v V (v ∎)

data Closed : ∀ {Γ σ} → (Γ ⊢ σ) → Set where
  closed : ∀ {σ} → (N : [] ⊢ σ) → Closed N

record SN-α {Γ} (e : Γ ⊢ `ℕ) : Set₁
record SN-σ→τ {Γ σ τ} (e : Γ ⊢ σ ⇒ τ) (e' : Γ ⊢ σ) : Set₁
SN : ∀ {Γ σ} → (e : Γ ⊢ σ) → Set₁

record SN-α {Γ} e where
  constructor pack
  field
    Closed-e  :  Closed e
    e⇓        :  e ⇓

record SN-σ→τ {Γ σ τ} e where  -- TODO factor the operand out and index by it
  constructor pack                -- but this causes problems with the set hierarchy
  field
    Closed-e  :  Closed e
    e⇓        :  e ⇓
    SN-app    :  ∀ {e'} : SN e' → SN (e · e')       -- TODO understand positivity checking 
open SN-σ→τ using (SN-app)

SN {σ = `ℕ} e     =  SN-α e
SN {σ = σ ⇒ τ} e  =  SN-σ→τ e



-- ∀ {Γ Δ σ} → (e: Γ ⊢ σ) → (Γ ─Env) 𝓥 Δ → SN e Γ σ




record PModel (𝓜 : Model) : Set₁ where
  constructor mkPModel
  field predicate : ∀ {Γ σ} → 𝓜 Γ σ → Set
open PModel

PKripke : {𝓥 : Model} (P𝓥 : PModel 𝓥)
          {𝓒 : Model} (P𝓒 : PModel 𝓒)
          {Δ : Context} {σ τ : Type}
        → Kripke 𝓥 𝓒 Δ σ τ
        → Set
PKripke {𝓥} P𝓥 P𝓒 {Δ} {σ} {τ} f =
    (ren : Thinning Δ (σ ∷ Δ)) {u : 𝓥 (σ ∷ Δ) σ}
  → predicate P𝓥 u
    -----------------------------------
  → predicate P𝓒 (f ren u)

PApplicative : {𝓒 : Model} → Applicative 𝓒 → PModel 𝓒 → Set
PApplicative {𝓒} _$_ P𝓒 =
  {Γ : Context} {σ τ : Type}
  {f : 𝓒 Γ (σ ⇒ τ)}
  {t : 𝓒 Γ σ}
  → predicate P𝓒 f
  → predicate P𝓒 t
  -----------------------
  → predicate P𝓒 (f $ t)

record ∀[_]
  {𝓥 : Model} {Γ Δ}
  (P𝓥 : PModel 𝓥)
  (ρ : (Γ ─Env) 𝓥 Δ)
  : Set where

  constructor packᴾ
  field
    lookupᴾ : ∀ {σ}
            → (x : Γ ∋ σ)
              --------------------------
            → predicate P𝓥 (lookup ρ x)
open ∀[_]

εᴾ : {𝓥 : Model} {P𝓥 : PModel 𝓥} {Γ : Context}
   → ∀[ P𝓥 ] ((([] ─Env) 𝓥 Γ) of-type ε)
lookupᴾ εᴾ ()

_∙ᴾ_ : {𝓥 : Model} {P𝓥 : PModel 𝓥} {Γ Δ : Context}
       {ρ : (Γ ─Env) 𝓥 Δ}
       (ρᴾ : ∀[ P𝓥 ] ρ)
       {σ : Type} {u : 𝓥 Δ σ}
     → predicate P𝓥 u
       -------------------
     → ∀[ P𝓥 ] (ρ ∙ u)
lookupᴾ (ρᴾ ∙ᴾ uᴾ) Z = uᴾ
lookupᴾ (ρᴾ ∙ᴾ uᴾ) (S x) = lookupᴾ ρᴾ x

record LogicalPredicate
  {𝓥 𝓒 : Model} (𝓢 : Sem 𝓥 𝓒)
  (P𝓥 : PModel 𝓥) (P𝓒 : PModel 𝓒)
  : Set where

  module 𝓢 = Sem 𝓢
  𝓟 = predicate P𝓒

  field
    P‿th^𝓥 : ∀ {Γ Δ Θ} {ρ : (Γ ─Env) 𝓥 Δ}
            → (ren : Thinning Δ Θ)
            → ∀[ P𝓥 ] ρ
              ----------------------------------------------------------
            → ∀[ P𝓥 ] (𝓢.th^𝓥 ren <$> ρ)
    
    P⟦V⟧ : ∀ {Γ Δ σ}
           {ρ : (Γ ─Env) 𝓥 Δ}
           (ρᴾ : ∀[ P𝓥 ] ρ)
           (x : Γ ∋ σ)
           ----------------------
         → 𝓟 (𝓢.⟦V⟧ (lookup ρ x))

    P⟦A⟧ : PApplicative 𝓢.⟦A⟧ P𝓒

    P⟦L⟧ : ∀ {Γ σ τ} {f : Kripke 𝓥 𝓒 Γ σ τ}
         → PKripke P𝓥 P𝓒 f
           -----------------
         → 𝓟 (𝓢.⟦L⟧ σ f)

  lemma : ∀ {Γ Δ σ}
        → {ρ : (Γ ─Env) 𝓥 Δ}
        → (ρᴾ : ∀[ P𝓥 ] ρ)
        → (N : Γ ⊢ σ)
          ------------------
        → 𝓟 (Sem.sem 𝓢 ρ N)
  lemma ρᴾ (` x)    =  P⟦V⟧ ρᴾ x
  lemma ρᴾ (ƛ N)    =  P⟦L⟧ (λ inc uᴾ → lemma (P‿th^𝓥 inc ρᴾ ∙ᴾ uᴾ) N)
  lemma ρᴾ (M · N)  =  P⟦A⟧ (lemma ρᴾ M) (lemma ρᴾ N)
open LogicalPredicate using (lemma)

StrongNormalisation : LogicalPredicate Substitution' (mkPModel SN) (mkPModel SN)
StrongNormalisation =
  record
    { P‿th^𝓥  =  {!!}  -- TODO prove that this is trivial for closed terms
    ; P⟦V⟧     =  λ ρᴾ x → lookupᴾ ρᴾ x
    ; P⟦A⟧     =  λ { fᴾ tᴾ → SN-app fᴾ tᴾ }
    ; P⟦L⟧     =  λ { {f = f} r → pack {!!} {!!} {!!} }
    }



-- ⊨_ : ∀ {Γ} → Substitution _⊢_ Γ [] → Set
-- ⊨_ {Γ} γ = ∀ {σ} → (e : Γ ∋ σ) → SN (γ e)

-- _∙_ : ∀ {Γ σ} {γ : Substitution _⊢_ Γ []} {e : [] ⊢ σ}
--   → ⊨ γ
--   → SN e
--   → Σ[ γ' ∈ Substitution _⊢_ (σ ∷ Γ) [] ] ⊨ γ'
-- _∙_ {Γ} {σ} {γ} {e} ⊨γ SN-e = γ' , ⊨γ'
--   where
--   γ' : Substitution _⊢_ (σ ∷ Γ) []
--   γ' Z = e
--   γ' (S x) = γ x
--   ⊨γ' : ⊨ γ'
--   ⊨γ' Z = SN-e
--   ⊨γ' (S x) = ⊨γ x

-- forward : ∀ {σ} {e e' : [] ⊢ σ}
--     → e —→ e'
--     → SN e
--       -------
--     → SN e'
-- forward {`ℕ} e—→e' (pack v V (.v ∎)) = ⊥-elim (V¬—→ V e—→e')
-- forward {`ℕ} e—→e' (pack v V (e —→⟨ e—→i ⟩ i—↠v)) with det e—→i e—→e'  -- TODO factor out proving e' ⇓
-- ... | i≡e' rewrite i≡e' = pack v V i—↠v
-- forward {σ ⇒ τ} e—→e' (pack (pack v V (.v ∎)) SN-app) = ⊥-elim (V¬—→ V e—→e')
-- forward {σ ⇒ τ} e—→e' (pack (pack v V (e —→⟨ e—→i ⟩ i—↠v)) SN-app) with det e—→i e—→e'
-- ... | i≡e' rewrite i≡e' = pack (pack v V i—↠v) (λ SN-e' → forward (ξ-·₁ e—→i) (SN-app SN-e'))

-- forward* : ∀ {σ} {e e' : [] ⊢ σ}
--     → e —↠ e'
--     → SN e
--       -------
--     → SN e'
-- forward* (e ∎) SN-e = SN-e
-- forward* (e —→⟨ e—→i ⟩ i—↠e') SN-e = forward* i—↠e' (forward e—→i SN-e)

-- backward : ∀ {σ} {e e' : [] ⊢ σ}
--     → e —→ e'
--     → SN e'
--       -------
--     → SN e
-- backward e—→e' SN-e = {!!}

-- backward* : ∀ {σ} {e e' : [] ⊢ σ}
--     → e —↠ e'
--     → SN e'
--       -------
--     → SN e
-- backward* = {!!}

-- ξ-·₂* : ∀ {Γ σ τ} {f : Γ ⊢ σ ⇒ τ} {e e' : Γ ⊢ σ}
--     → Value f
--     → e —↠ e'
--       --------
--     → f · e —↠ f · e'
-- ξ-·₂* {f = f} V-f (e ∎) = f · e ∎
-- ξ-·₂* {f = f} V-f (e —→⟨ e—→i ⟩ i—↠e') = f · e —→⟨ ξ-·₂ V-f e—→i ⟩ (ξ-·₂* V-f i—↠e')

-- sn : ∀ {Γ σ}
--    → {γ : Substitution _⊢_ Γ []}
--    → ⊨ γ
--    → (e : Γ ⊢ σ)
--    → SN (subst γ e)
-- sn ⊨γ (` x)               = ⊨γ x
-- sn ⊨γ (ƛ_ {A = `ℕ} e)     =  pack (V⇓ V-ƛ) (λ { (pack v V e—↠v) → {!!} })
-- sn ⊨γ (ƛ_ {A = σ ⇒ τ} e)  =  pack (V⇓ V-ƛ) λ SN-e' → {!!} 
-- sn ⊨γ (f · e) with sn ⊨γ f | sn ⊨γ e
-- ... | pack f⇓ SN-app | SN-e = SN-app SN-e

-- \end{code}

