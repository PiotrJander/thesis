\begin{code}
open import Data.List using (List; []; _∷_)

open import LR.Base
import LR.STLC as S
open S using (_[_])
import LR.Closure as T
open T using ()

module LR.LR where

{-# NO_POSITIVITY_CHECK #-}
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
       → ({V₁ : S.Val₀ σ} {V₂ : T.Val₀ σ} → V₁ ≈ V₂ → M₁ [ V₁ ] ~ T.subst (E ∙ V₂) M₂)
         -------------------------------
       → S.`λ M₁ ≈ T.`λ M₂ E

  -- terms

  ~Trm : ∀ {σ} {N₁ : S.Trm₀ σ} {N₂ : T.Trm₀ σ}
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

infix  4 _~~_
data _~~_ : ∀ {Γ σ k} → S.Exp k σ Γ → T.Exp k σ Γ → Set where

  -- values

  ~var : ∀ {Γ σ} {x : Var σ Γ}
     ---------------
   → S.`var x ~~ T.`var x

  ~λ : ∀ {Γ Δ σ τ} {N₁ : S.Trm τ (σ ∷ Γ)} {N₂ : T.Trm τ (σ ∷ Δ)} {E : T.Subst Δ Γ}
    → N₁ ~~ T.subst (T.exts E) N₂
      -----------------
    → S.`λ N₁ ~~ T.`λ N₂ E

  -- terms

  _~$_ : ∀ {Γ σ τ} {L : S.Val (σ ⇒ τ) Γ} {L† : T.Val (σ ⇒ τ) Γ}
           {M : S.Val σ Γ} {M† : T.Val σ Γ}
    → L ~~ L†
    → M ~~ M†
      --------------------
    → L S.`$ M ~~ L† T.`$ M†

  ~let : ∀ {Γ σ τ} {M₁ : S.Trm σ Γ} {M₂ : T.Trm σ Γ}
           {N₁ : S.Trm τ (σ ∷ Γ)} {N₂ : T.Trm τ (σ ∷ Γ)}
    → M₁ ~~ M₂
    → N₁ ~~ N₂
      ----------------------------
    → S.`let M₁ N₁ ~~ T.`let M₂ N₂

  ~val : ∀ {Γ σ} {M₁ : S.Val σ Γ} {M₂ : T.Val σ Γ}
    → M₁ ~~ M₂
      ----------------------
    → S.`val M₁ ~~ T.`val M₂

lr : ∀ {Γ σ k} {M₁ : S.Exp k σ Γ} {M₂ : T.Exp k σ Γ}
       {ρ^s : S.Subst Γ []} {ρ^t : T.Subst Γ []}
   → ρ^s ∙≈ ρ^t
   → M₁ ~~ M₂
     -------------------------------
   → sim {k} (S.subst ρ^s M₁) (T.subst ρ^t M₂)
lr ∙≈ρ (~var {x = x}) = lookup^R ∙≈ρ x
lr ∙≈ρ (~λ ~N) = {!!}
lr ∙≈ρ (~M ~$ ~N) with lr ∙≈ρ ~M | lr ∙≈ρ ~M
... | p | q = {!!}
lr ∙≈ρ (~let ~M ~N) = {!!}
lr ∙≈ρ (~val ~M) = {!!}
