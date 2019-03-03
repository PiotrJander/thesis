--------------------------------------------------------------------------------
-- This module demonstrates the similitudes between various semantics for STLC
-- before giving a generic notion of Scope-and-Type Safe Semantics à la
-- Type-and-scope Safe Programs and Their Proofs
-- (Allais, Chapman, McBride, and McKinna, CPP 17)
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-} 
module StateOfTheArt.Closure where

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)
open E.≡ᴱ-Reasoning
open import StateOfTheArt.Types

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_ ; lookup)
open import Function

--------------------------------------------------------------------------------
-- Well scoped-and-typed Simply-Typed Lambda Calculus

data Lam : Type ─Scoped 
Subst : Context → Context → Set

data Lam where
  V : {σ : Type} →    [ Var σ                ⟶ Lam σ        ]
  A : {σ τ : Type} →  [ Lam (σ ⇒ τ) ⟶ Lam σ  ⟶ Lam τ        ]
  L : {σ τ : Type} {Γ Δ : Context} → Lam τ (σ ∷ Δ) → Subst Δ Γ → Lam (σ ⇒ τ) Γ

Subst Γ Δ = (Γ ─Env) Lam Δ

Syntactic : Context → Context → Set
Syntactic Γ Δ = ∀ {σ} → Lam σ Γ → Lam σ Δ

{-# TERMINATING #-}
rename : ∀ {Γ Δ}
        → Thinning Γ Δ
          ---------------------------
        → Syntactic Γ Δ
rename ρ (V x) = V (lookup ρ x)
rename ρ (A M N) = A (rename ρ M) (rename ρ N)
rename ρ (L N E) = L N (rename ρ <$> E)

{-# TERMINATING #-}
subst : ∀ {Γ Δ}
     → Subst Γ Δ
       ----------------
     → Syntactic Γ Δ
subst ρ (V x) = lookup ρ x
subst ρ (A M N) = A (subst ρ M) (subst ρ N)
subst ρ (L N E) = L N (subst ρ <$> E)

----------------------------
-- Substitution combinators

s-step : ∀ {Γ Δ τ} → Subst Γ Δ → Subst Γ (τ ∷ Δ)
s-step ρ = rename E.extend <$> ρ

id-subst : ∀ {Γ} → Subst Γ Γ
lookup id-subst x = V x

-------
-- Values

data Value : ∀ {Γ σ} → Lam σ Γ → Set where

  V-L : ∀ {Γ Δ σ τ} {N : Lam τ (σ ∷ Δ)} {E : Subst Δ Γ}
      ---------------------------
    → Value (L N E)

-----------
-- Reductions

infix 2 _—→_
data _—→_ : ∀ {Γ σ} → (Lam σ Γ) → (Lam σ Γ) → Set where

  ξ-A₁ : ∀ {Γ σ τ} {M M′ : Lam (σ ⇒ τ) Γ} {N : Lam σ Γ}
    → M —→ M′
      ---------------
    → A M N —→ A M′ N

  ξ-A₂ : ∀ {Γ σ τ} {V : Lam (σ ⇒ τ) Γ} {N N′ : Lam σ Γ}
    → Value V
    → N —→ N′
      ---------------
    → A V N —→ A V N′

  β-L : ∀ {Γ Δ σ τ} {N : Lam τ (σ ∷ Δ)} {E : Subst Δ Γ} {V : Lam σ Γ}
    → Value V
      --------------------
    → A (L N E) V —→ subst (E ∙ V) N
