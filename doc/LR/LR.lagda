\begin{code}
open import Data.List using (List; []; _∷_)

open import LR.Base
import LR.STLC as S
open S using (_[_])
import LR.Closure as T
open T using ()

module LR.LR where

data sim : {k : Kind} {τ : Type} → S.Exp₀ k τ → T.Exp₀ k τ → Set

infix 2 _~_
infix 2 _≈_

_~_ : ∀ {τ} → S.Trm₀ τ → T.Trm₀ τ → Set
N ~ N' = sim N N'

_≈_ : ∀ {τ} → S.Val₀ τ → T.Val₀ τ → Set
N ≈ N' = sim N N'

data sim where

  -- values

  ≈λ : ∀ {Δ σ τ} {M₁ : S.Trm τ (σ ∷ [])}
         {M₂ : T.Trm τ (σ ∷ Δ)} {E : T.Subst Δ []}
         {V₁ : S.Val₀ σ} {V₂ : T.Val₀ σ}
       → V₁ ≈ V₂
       → M₁ [ V₁ ] ~ T.subst (E ∙ V₂) M₂
         -------------------------------
       → S.`λ M₁ ≈ T.`λ M₂ E

  -- terms

  ~N : ∀ {σ} {N₁ : S.Trm₀ σ} {N₂ : T.Trm₀ σ}
             {V₁ : S.Val₀ σ} {V₂ : T.Val₀ σ}
     → N₁ S.⇓ V₁
     → N₂ T.⇓ V₂
     → V₁ ≈ V₂
       -------
     → N₁ ~ N₂

infix 2 _∙≈_
record _∙≈_ {Γ : List Type}
  (ρ^s : S.Subst Γ []) (ρ^t : T.Subst Γ []) : Set where
  constructor pack^R
  field lookup^R : {σ : Type} (v : Var σ Γ) → lookup ρ^s v ≈ lookup ρ^t v
open _∙≈_ public

ε^R : ε ∙≈ ε
lookup^R ε^R ()

_∙^R_ : ∀ {Γ τ}
        {ρ^s : S.Subst Γ []} {ρ^t : T.Subst Γ []}
        {N₁ : S.Val₀ τ} {N₂ : T.Val₀ τ}
      → ρ^s ∙≈ ρ^t
      → N₁ ≈ N₂
        -------------------------------------
      → ρ^s ∙ N₁ ∙≈ ρ^t ∙ N₂
lookup^R (ρ^R ∙^R ≈N) z      = ≈N
lookup^R (ρ^R ∙^R ≈N) (s x)  = lookup^R ρ^R x
