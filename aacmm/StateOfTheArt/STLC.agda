--------------------------------------------------------------------------------
-- This module demonstrates the similitudes between various semantics for STLC
-- before giving a generic notion of Scope-and-Type Safe Semantics à la
-- Type-and-scope Safe Programs and Their Proofs
-- (Allais, Chapman, McBride, and McKinna, CPP 17)
--------------------------------------------------------------------------------

module StateOfTheArt.STLC where

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)
open import StateOfTheArt.Types

open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_ ; lookup)
open import Function

--------------------------------------------------------------------------------
-- Well scoped-and-typed Simply-Typed Lambda Calculus

data Lam : Type ─Scoped where
  V : {σ : Type} →    [ Var σ                ⟶ Lam σ        ]
  A : {σ τ : Type} →  [ Lam (σ ⇒ τ) ⟶ Lam σ  ⟶ Lam τ        ]
  L : {σ τ : Type} →  [ (σ ∷_) ⊢ Lam τ       ⟶ Lam (σ ⇒ τ)  ]

--------------------------------------------------------------------------------
-- A Generic Notion of Semantics and the corresponding generic traversal

record Sem (𝓥 𝓒 : Type ─Scoped) : Set where
  field  th^𝓥  : ∀ {σ} → Thinnable (𝓥 σ)
         ⟦V⟧   : {σ : Type} →               [ 𝓥 σ               ⟶ 𝓒 σ        ]
         ⟦A⟧   : {σ τ : Type} →             [ 𝓒 (σ ⇒ τ) ⟶ 𝓒 σ   ⟶ 𝓒 τ        ]
         ⟦L⟧   : (σ : Type) → {τ : Type} →  [ □ (𝓥 σ ⟶ 𝓒 τ)     ⟶ 𝓒 (σ ⇒ τ)  ]


  sem : {Γ Δ : List Type} {σ : Type} → (Γ ─Env) 𝓥 Δ → (Lam σ Γ → 𝓒 σ Δ)
  sem ρ (V k)    = ⟦V⟧ (lookup ρ k)
  sem ρ (A f t)  = ⟦A⟧ (sem ρ f) (sem ρ t)
  sem ρ (L b)    = ⟦L⟧ _ (λ σ v → sem (extend σ ρ v) b) where

   extend : {Γ Δ Θ : List Type} {σ : Type} →
            Thinning Δ Θ → (Γ ─Env) 𝓥 Δ → 𝓥 σ Θ → (σ ∷ Γ ─Env) 𝓥 Θ
   extend σ ρ v = (λ t → th^𝓥 t σ) <$> ρ ∙ v
open Sem

--------------------------------------------------------------------------------
-- Defining various traversals as instances of Sem

Renaming : Sem Var Lam
Renaming = record
  { th^𝓥  = th^Var
  ; ⟦V⟧    = V
  ; ⟦A⟧    = A
  ; ⟦L⟧    = λ σ b → L (b (pack s) z) }

rename : ∀ {Γ Δ σ} → (Γ ─Env) Var Δ → Lam σ Γ → Lam σ Δ
rename = Sem.sem Renaming

Substitution : Sem Lam Lam
Substitution = record
   { th^𝓥  = λ t ρ → Sem.sem Renaming ρ t
   ; ⟦V⟧    = id
   ; ⟦A⟧    = A
   ; ⟦L⟧    = λ σ b → L (b (pack s) (V z)) }

Subst : Context → Context → Set
Subst Γ Δ = (Γ ─Env) Lam Δ

subst : ∀ {Γ Δ σ} → (Γ ─Env) Lam Δ → Lam σ Γ → Lam σ Δ
subst = Sem.sem Substitution

--------------------------
-- Single substitution

_[_] : ∀ {σ τ} → [ (σ ∷_) ⊢ Lam τ ⟶ Lam σ ⟶ Lam τ ]
_[_] {σ} {_} {Γ} N M =  subst ρ N
  where
  ρ : Subst (σ ∷ Γ) Γ
  lookup ρ z      =  M
  lookup ρ (s x)  =  V x

