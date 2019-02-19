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

-- TODO write the informal proof in a comment here

{-# TERMINATING #-}
lemma-0 : ∀ {Γ Δ Θ τ} {ρρ : Thinning Γ Θ} {ρσ : Subst Δ Γ}
  → (N : Lam τ Δ)
    -------------
  → rename ρρ (subst ρσ N) ≡ subst (rename ρρ <$> ρσ) N
lemma-0 (V x)    =  refl
lemma-0 (A M N)  =  cong₂ A (lemma-0 M) (lemma-0 N)
lemma-0 {ρρ = ρρ} {ρσ} (L N E)  =  cong₂ L refl (env-extensionality h)
  where h : (_<$>_ {𝓦 = Lam} (rename ρρ) (_<$>_ {𝓦 = Lam} (subst ρσ) E))
            ≡ᴱ (subst (_<$>_ {𝓦 = Lam} (rename ρρ) ρσ) <$> E)
        h = beginᴱ
              _<$>_ {𝓦 = Lam} (rename ρρ) (_<$>_ {𝓦 = Lam} (subst ρσ) E)
            ≡ᴱ⟨ <$>-distr {𝓦 = Lam} (subst ρσ) (rename ρρ) E ⟩
              _<$>_ {𝓦 = Lam} (rename ρρ ∘ subst ρσ) E
            ≡ᴱ⟨ <$>-fun {𝓦 = Lam} (λ v → lemma-0 v) E ⟩
              subst (_<$>_ {𝓦 = Lam} (rename ρρ) ρσ) <$> E
            ∎ᴱ

lemma-3 : ∀ {Γ Δ τ} {ρ : Thinning Γ Δ}
  → lookup (ext {σ = τ} ρ) z ≡ z
lemma-3 = refl

lemma-4 : ∀ {Γ Δ τ} {ρ : Subst Γ Δ}
  → lookup (exts {σ = τ} ρ) z ≡ V z
lemma-4 = refl

lemma-5 : ∀ {Γ Δ σ τ} {ρ : Thinning Γ Δ} {x : Var τ Γ}
  → lookup (ext {σ = σ} ρ) (s x) ≡ s (lookup ρ x)
lemma-5 = refl

lemma-6 : ∀ {Γ Δ σ τ} {ρ : Subst Γ Δ} {x : Var τ Γ}
  → lookup (exts {σ = σ} ρ) (s x) ≡ rename E.extend (lookup ρ x)
lemma-6 = refl

lemma-2 : ∀ {Γ Δ Θ τ} {ρρ : Thinning Γ Θ} {ρσ : Subst Δ Γ}
  → rename (ext {σ = τ} ρρ) <$> (exts ρσ) ≡ᴱ exts (rename ρρ <$> ρσ)
eq (lemma-2 {τ = τ} {ρρ = ρρ} {ρσ}) z rewrite lemma-3 {τ = τ} {ρ = ρρ} = refl
eq (lemma-2 {τ = τ} {ρρ = ρρ} {ρσ}) (s x) = {!h!}
  where h : rename (ext {σ = τ} ρρ) (lookup (exts ρσ) (s x))
            ≡ lookup (exts (rename ρρ <$> ρσ)) (s x)
        h = begin
              rename (ext {σ = τ} ρρ) (lookup (exts ρσ) (s x))
            ≡⟨ cong (λ e → rename (ext {σ = τ} ρρ) e) (lemma-6 {σ = τ} {_} {ρσ} {x}) ⟩
              rename (ext {σ = τ} ρρ) (rename E.extend (lookup ρσ x))
            ≡⟨ {!!} ⟩
              lookup (exts (rename ρρ <$> ρσ)) (s x)
            ∎

lemma-1 : ∀ {Γ Δ Θ σ τ} {ρρ : Thinning Γ Θ} {ρσ : Subst Δ Γ} {N : Lam τ (σ ∷ Δ)}
  → rename (ext ρρ) (subst (exts ρσ) N) ≡ subst (exts (rename ρρ <$> ρσ)) N
lemma-1 {ρρ = ρρ} {ρσ} {N} =
  begin
    rename (ext ρρ) (subst (exts ρσ) N)
  ≡⟨ lemma-0 {ρρ = ext ρρ} {exts ρσ} N ⟩
    subst (rename (ext ρρ) <$> exts ρσ) N
  ≡⟨ cong (λ e → subst e N) (env-extensionality (lemma-2 {ρρ = ρρ} {ρσ})) ⟩
    subst (exts (rename ρρ <$> ρσ)) N
  ∎
