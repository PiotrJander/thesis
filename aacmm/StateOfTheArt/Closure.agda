--------------------------------------------------------------------------------
-- This module demonstrates the similitudes between various semantics for STLC
-- before giving a generic notion of Scope-and-Type Safe Semantics à la
-- Type-and-scope Safe Programs and Their Proofs
-- (Allais, Chapman, McBride, and McKinna, CPP 17)
--------------------------------------------------------------------------------

module StateOfTheArt.Closure where

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)
open import StateOfTheArt.Types

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong₂)
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

ext  : ∀ {Γ Δ} {σ : Type}
        → Thinning Γ Δ
          -----------------------------------
        → Thinning (σ ∷ Γ) (σ ∷ Δ)
ext ρ  =  step ρ ∙ z

exts : ∀ {Γ Δ σ}
     → Subst Γ Δ
       ----------------------------
     → Subst (σ ∷ Γ) (σ ∷ Δ)
exts ρ  =  rename E.extend <$> ρ ∙ V z

{-# TERMINATING #-}
subst : ∀ {Γ Δ}
     → Subst Γ Δ
       ----------------
     → Syntactic Γ Δ
subst ρ (V x) = lookup ρ x
subst ρ (A M N) = A (subst ρ M) (subst ρ N)
subst ρ (L N E) = L N (subst ρ <$> E)

-- a more general result would be that subst∘rename ≡ subst
-- where 

lemma-0 : ∀ {Γ Δ Θ τ} {ρρ : Thinning Γ Θ} {ρσ : Subst Δ Γ}
  → (N : Lam τ Δ)
    -------------
  → rename ρρ (subst ρσ N) ≡ subst (rename ρρ <$> ρσ) N
lemma-0 (V x)    =  refl
lemma-0 (A M N)  =  cong₂ A (lemma-0 M) (lemma-0 N)
lemma-0 (L N E)  =  {!cong₂ L refl ?!}

lemma-1 : ∀ {Γ Δ Θ σ τ} {ρρ : Thinning Γ Θ} {ρσ : Subst Δ Γ} {N : Lam τ (σ ∷ Δ)}
  → rename (ext ρρ) (subst (exts ρσ) N) ≡ subst (exts (rename ρρ <$> ρσ)) N
lemma-1 = {!!}
