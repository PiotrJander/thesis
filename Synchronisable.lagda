\begin{code}

module Synchronisable where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using ([] ; _∷_)
open import Data.Product using (∃-syntax; Σ-syntax; _,_)
open import Function using (_∘_; _$_) renaming (_∋_ to _of-type_)

open import Common
open import STLC hiding ()

record RModel (𝓒ᴬ 𝓒ᴮ : Model) : Set₁ where
  constructor mkRModel
  field related : ∀ {Γ σ} → 𝓒ᴬ Γ σ → 𝓒ᴮ Γ σ → Set
open RModel

RKripke : {𝓥ᴬ 𝓥ᴮ : Model} (𝓥ᴿ : RModel 𝓥ᴬ 𝓥ᴮ)
          {𝓒ᴬ 𝓒ᴮ : Model} (𝓒ᴿ : RModel 𝓒ᴬ 𝓒ᴮ)
          {Δ : Context} {σ τ : Type}
        → Kripke 𝓥ᴬ 𝓒ᴬ Δ σ τ
        → Kripke 𝓥ᴮ 𝓒ᴮ Δ σ τ
        → Set
RKripke {𝓥ᴬ} {𝓥ᴮ} 𝓥ᴿ 𝓒ᴿ {Δ} {σ} {τ} fᴬ fᴮ =
    (ren : Thinning Δ (σ ∷ Δ)) {uᴬ : 𝓥ᴬ (σ ∷ Δ) σ} {uᴮ : 𝓥ᴮ (σ ∷ Δ) σ}
  → related 𝓥ᴿ uᴬ uᴮ
    -----------------------------------
  → related 𝓒ᴿ (fᴬ ren uᴬ) (fᴮ ren uᴮ)

RApplicative : {𝓒ᴬ 𝓒ᴮ : Model} →
               Applicative 𝓒ᴬ → Applicative 𝓒ᴮ → RModel 𝓒ᴬ 𝓒ᴮ →
               Set
RApplicative {𝓒ᴬ} {𝓒ᴮ} _$$ᴬ_ _$$ᴮ_ 𝓒ᴿ =
  {Γ : Context} {σ τ : Type}
  {fᴬ : 𝓒ᴬ Γ (σ ⇒ τ)} {fᴮ : 𝓒ᴮ Γ (σ ⇒ τ)}
  {tᴬ : 𝓒ᴬ Γ σ} {tᴮ : 𝓒ᴮ Γ σ} →
  
    related 𝓒ᴿ fᴬ fᴮ → related 𝓒ᴿ tᴬ tᴮ →
  -----------------------------------------------
    related 𝓒ᴿ (fᴬ $$ᴬ tᴬ) (fᴮ $$ᴮ tᴮ)

record ∀[_]
  {𝓥ᴬ 𝓥ᴮ : Model} {Γ Δ}
  (𝓥ᴿ : RModel 𝓥ᴬ 𝓥ᴮ)
  (ρᴬ : (Γ ─Env) 𝓥ᴬ Δ) (ρᴮ : (Γ ─Env) 𝓥ᴮ Δ)
  : Set where

  constructor packᴿ
  field
    lookupᴿ : ∀ {σ}
            → (x : Γ ∋ σ)
              ---------------
            → related 𝓥ᴿ (lookup ρᴬ x) (lookup ρᴮ x)
open ∀[_]

εᴿ : {𝓥ᴬ 𝓥ᴮ : Model} {𝓥ᴿ : RModel 𝓥ᴬ 𝓥ᴮ} {Γ : Context}
   → ∀[ 𝓥ᴿ ] ((([] ─Env) 𝓥ᴬ Γ) of-type ε) ε
lookupᴿ εᴿ ()

_∙ᴿ_ : {𝓥ᴬ 𝓥ᴮ : Model} {𝓥ᴿ : RModel 𝓥ᴬ 𝓥ᴮ} {Γ Δ : Context}
       {ρᴬ : (Γ ─Env) 𝓥ᴬ Δ} {ρᴮ : (Γ ─Env) 𝓥ᴮ Δ}
       (ρᴿ : ∀[ 𝓥ᴿ ] ρᴬ ρᴮ)
       {σ : Type} {uᴬ : 𝓥ᴬ Δ σ} {uᴮ : 𝓥ᴮ Δ σ}
     → related 𝓥ᴿ uᴬ uᴮ
       -------------------
     → ∀[ 𝓥ᴿ ] (ρᴬ ∙ uᴬ) (ρᴮ ∙ uᴮ)
lookupᴿ (ρᴿ ∙ᴿ uᴿ) Z = uᴿ
lookupᴿ (ρᴿ ∙ᴿ uᴿ) (S x) = lookupᴿ ρᴿ x

record Synchronisable
  {𝓥ᴬ 𝓥ᴮ 𝓒ᴬ 𝓒ᴮ : Model}
  (𝓢ᴬ : Sem 𝓥ᴬ 𝓒ᴬ) (𝓢ᴮ : Sem 𝓥ᴮ 𝓒ᴮ)
  (𝓥ᴿ : RModel 𝓥ᴬ 𝓥ᴮ) (𝓒ᴿ : RModel 𝓒ᴬ 𝓒ᴮ)
  : Set where

  module 𝓢ᴬ = Sem 𝓢ᴬ
  module 𝓢ᴮ = Sem 𝓢ᴮ
  𝓡 = related 𝓒ᴿ

  field
    R‿th^𝓥 : ∀ {Γ Δ Θ} {ρᴬ : (Γ ─Env) 𝓥ᴬ Δ} {ρᴮ : (Γ ─Env) 𝓥ᴮ Δ}
            → (ren : Thinning Δ Θ)
            → ∀[ 𝓥ᴿ ] ρᴬ ρᴮ
              ----------------------------------------------------------
            → ∀[ 𝓥ᴿ ] (𝓢ᴬ.th^𝓥 ren <$> ρᴬ) (𝓢ᴮ.th^𝓥 ren <$> ρᴮ)
    
    R⟦V⟧ : ∀ {Γ Δ σ}
           {ρᴬ : (Γ ─Env) 𝓥ᴬ Δ} {ρᴮ : (Γ ─Env) 𝓥ᴮ Δ}
           (ρᴿ : ∀[ 𝓥ᴿ ] ρᴬ ρᴮ)
           (x : Γ ∋ σ)
           ----------------------
         → 𝓡 (𝓢ᴬ.⟦V⟧ (lookup ρᴬ x)) (𝓢ᴮ.⟦V⟧ (lookup ρᴮ x))

    R⟦A⟧ : RApplicative 𝓢ᴬ.⟦A⟧ 𝓢ᴮ.⟦A⟧ 𝓒ᴿ

    R⟦L⟧ : ∀ {Γ σ τ} {fᴬ : Kripke 𝓥ᴬ 𝓒ᴬ Γ σ τ} {fᴮ : Kripke 𝓥ᴮ 𝓒ᴮ Γ σ τ}
         → RKripke 𝓥ᴿ 𝓒ᴿ fᴬ fᴮ
           -----------------------------------------------------------------------
         → 𝓡 (𝓢ᴬ.⟦L⟧ σ fᴬ) (𝓢ᴮ.⟦L⟧ σ fᴮ)
 
  lemma : ∀ {Γ Δ σ}
        → {ρᴬ : (Γ ─Env) 𝓥ᴬ Δ} {ρᴮ : (Γ ─Env) 𝓥ᴮ Δ}
        → (ρᴿ : ∀[ 𝓥ᴿ ] ρᴬ ρᴮ)
        → (N : Γ ⊢ σ)
          ------------------
        → 𝓡 (Sem.sem 𝓢ᴬ ρᴬ N) (Sem.sem 𝓢ᴮ ρᴮ N)
  lemma ρᴿ (` x)    =  R⟦V⟧ ρᴿ x
  lemma ρᴿ (ƛ N)    =  R⟦L⟧ (λ inc uᴿ → lemma (R‿th^𝓥 inc ρᴿ ∙ᴿ uᴿ) N)
  lemma ρᴿ (M · N)  =  R⟦A⟧ (lemma ρᴿ M) (lemma ρᴿ N)
open Synchronisable using (lemma)

SynchronisableRenamingSubstitution :
  Synchronisable Renaming' Substitution' (mkRModel (λ v t → ` v ≡ t)) (mkRModel _≡_)
SynchronisableRenamingSubstitution =
  record
    { R‿th^𝓥  =  λ ren ρᴿ → packᴿ $ cong (Sem.sem Renaming' ren) ∘ lookupᴿ ρᴿ
    ; R⟦V⟧     =  λ ρᴿ x → lookupᴿ ρᴿ x
    ; R⟦A⟧     =  cong₂ _·_
    ; R⟦L⟧     =  λ r → cong ƛ_ (r _ refl)
    }

RenamingIsASubstitution :
  {Γ Δ : Context} {σ : Type} (t : Γ ⊢ σ) (ρ : Thinning Γ Δ) →
  Sem.sem Renaming' ρ t ≡ Sem.sem Substitution' (`_ <$> ρ) t
RenamingIsASubstitution t ρ = corollary (packᴿ (λ _ → refl)) t
  where corollary = lemma SynchronisableRenamingSubstitution
