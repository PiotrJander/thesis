\begin{code}

module StateOfTheArt.Synchronisable where

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)

open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_ ; lookup)
open import Function

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; subst ; sym)

open import StateOfTheArt.ACMM

record related-env {Γ Δ : List Type}
  (ρ^ren : (Γ ─Env) Var Δ) (ρ^sub : (Γ ─Env) Lam Δ) : Set where
  constructor pack^R
  field lookup^R : {σ : Type} (v : Var σ Γ) → V (lookup ρ^ren v) ≡ lookup ρ^sub v
open related-env public

ε^R : ∀ {Δ} → related-env {Δ = Δ} ε ε
lookup^R ε^R ()

related-env' : {Γ Δ : List Type}
  (ρ^ren : (Γ ─Env) Var Δ) (ρ^sub : (Γ ─Env) Lam Δ) → Set
related-env' {Γ} ρ^ren ρ^sub
  = {σ : Type} (v : Var σ Γ) → V (lookup ρ^ren v) ≡ lookup ρ^sub v

ε^R' : ∀ {Δ} → related-env' {Δ = Δ} ε ε
ε^R' ()

extend^R : ∀ {Γ Δ τ}
        {ρ^ren : (Γ ─Env) Var Δ} {ρ^sub : (Γ ─Env) Lam Δ}
        {x : Var τ Δ}
      → related-env' ρ^ren ρ^sub
        -------------------------------------
      → related-env' (ρ^ren ∙ x) (ρ^sub ∙ V x)
extend^R ρ^R z = refl
extend^R ρ^R (s x) = ρ^R x

renaming-is-substitution : ∀ {Γ Δ σ}
    {ρ^ren : (Γ ─Env) Var Δ}
    {ρ^sub : (Γ ─Env) Lam Δ}
  → (ρ^R : related-env' ρ^ren ρ^sub)
  → (t : Lam σ Γ)
  → ren ρ^ren t ≡ sub ρ^sub t
renaming-is-substitution ρ^R (V x) = {!!}
renaming-is-substitution ρ^R (A M N) = {!!}
renaming-is-substitution ρ^R (L N) = {!!}

\end{code}
