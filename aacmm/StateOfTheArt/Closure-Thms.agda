module StateOfTheArt.Closure-Thms where

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)
open E.≡ᴱ-Reasoning
open import StateOfTheArt.Types
open import StateOfTheArt.Closure

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_ ; lookup)
open import Function

-- TODO write the informal proof in a comment here
-- TODO make ρ and σ explicit

{-# TERMINATING #-}  -- rename∘subst
rename∘subst : ∀ {Γ Δ Θ τ} {ρρ : Thinning Γ Θ} {ρσ : Subst Δ Γ}
  → (N : Lam τ Δ)
    -------------
  → rename ρρ (subst ρσ N) ≡ subst (rename ρρ <$> ρσ) N
rename∘subst (V x)    =  refl
rename∘subst (A M N)  =  cong₂ A (rename∘subst M) (rename∘subst N)
rename∘subst {ρρ = ρρ} {ρσ} (L N E)  =  cong₂ L refl (env-extensionality h)
  where h : (_<$>_ {𝓦 = Lam} (rename ρρ) (_<$>_ {𝓦 = Lam} (subst ρσ) E))
            ≡ᴱ (subst (_<$>_ {𝓦 = Lam} (rename ρρ) ρσ) <$> E)
        h = beginᴱ
              _<$>_ {𝓦 = Lam} (rename ρρ) (_<$>_ {𝓦 = Lam} (subst ρσ) E)
            ≡ᴱ⟨ <$>-distr {𝓦 = Lam} (subst ρσ) (rename ρρ) E ⟩
              _<$>_ {𝓦 = Lam} (rename ρρ ∘ subst ρσ) E
            ≡ᴱ⟨ <$>-fun {𝓦 = Lam} (λ v → rename∘subst v) E ⟩
              subst (_<$>_ {𝓦 = Lam} (rename ρρ) ρσ) <$> E
            ∎ᴱ

{-# TERMINATING #-}
rename∘rename : ∀ {Γ Δ Θ τ} (ρ₁ : Thinning Γ Δ) (ρ₂ : Thinning Δ Θ)
  → (N : Lam τ Γ)
    -------------
  → rename ρ₂ (rename ρ₁ N) ≡ rename (select ρ₁ ρ₂) N
rename∘rename ρ₁ ρ₂ (V x)    =  refl
rename∘rename ρ₁ ρ₂ (A M N)  =  cong₂ A (rename∘rename ρ₁ ρ₂ M) (rename∘rename ρ₁ ρ₂ N)
rename∘rename ρ₁ ρ₂ (L N E)  =  cong₂ L refl (env-extensionality h)
  where h : (rename ρ₂ <$> (_<$>_ {𝓦 = Lam} (rename ρ₁) E)) ≡ᴱ (_<$>_ {𝓦 = Lam} (rename (select ρ₁ ρ₂)) E)
        h = beginᴱ
              rename ρ₂ <$> (_<$>_ {𝓦 = Lam} (rename ρ₁) E)
            ≡ᴱ⟨ <$>-distr {𝓦 = Lam} (rename ρ₁) (rename ρ₂) E ⟩
              _<$>_ {𝓦 = Lam} (rename ρ₂ ∘ rename ρ₁) E
            ≡ᴱ⟨ <$>-fun {𝓦 = Lam} (λ e → rename∘rename ρ₁ ρ₂ e) E ⟩
              _<$>_ {𝓦 = Lam} (rename (select ρ₁ ρ₂)) E
            ∎ᴱ

select-extend-ext-ρ≡step-ρ : ∀ {Γ Δ} {τ : Type} (ρ : Thinning Γ Δ)
  → select (E.extend {σ = τ}) (ext ρ) ≡ᴱ step ρ
eq (select-extend-ext-ρ≡step-ρ ρ) x = refl

select-ρ-extend≡step-ρ : ∀ {Γ Δ} {τ : Type} (ρ : Thinning Γ Δ)
  → select ρ (E.extend {σ = τ}) ≡ᴱ step ρ
eq (select-ρ-extend≡step-ρ ρ) x = refl

lemma-3 : ∀ {Γ Δ τ} {ρ : Thinning Γ Δ}
  → lookup (ext {σ = τ} ρ) z ≡ z
lemma-3 = refl

lemma-4 : ∀ {Γ Δ τ} {ρ : Subst Γ Δ}
  → lookup (exts {σ = τ} ρ) z ≡ V z
lemma-4 = refl

lemma-5 : ∀ {Γ Δ σ τ} {ρ : Thinning Γ Δ} {x : Var τ Γ}
  → lookup (ext {σ = σ} ρ) (s x) ≡ s (lookup ρ x)
lemma-5 = refl

lookup-exts-ρ-sx≡rename-extend-lookup-ρ-x : ∀ {Γ Δ σ τ} (ρ : Subst Γ Δ) (x : Var τ Γ)
  → lookup (exts {σ = σ} ρ) (s x) ≡ rename E.extend (lookup ρ x)
lookup-exts-ρ-sx≡rename-extend-lookup-ρ-x ρ x = refl

lemma-~ren-L-helper : ∀ {Γ Δ Θ τ} (ρρ : Thinning Γ Θ) (ρσ : Subst Δ Γ)
  → rename (ext {σ = τ} ρρ) <$> (exts ρσ) ≡ᴱ exts (rename ρρ <$> ρσ)
eq (lemma-~ren-L-helper {τ = τ} ρρ ρσ) z rewrite lemma-3 {τ = τ} {ρ = ρρ} = refl
eq (lemma-~ren-L-helper {τ = τ} ρρ ρσ) (s x) = h
  where 
        g : rename (ext {σ = τ} ρρ) (lookup (exts ρσ) (s x))
            ≡ rename (step ρρ) (lookup ρσ x)
        g = begin
              rename (ext {σ = τ} ρρ) (lookup (exts ρσ) (s x))
            ≡⟨ cong (λ e → rename (ext {σ = τ} ρρ) e) (lookup-exts-ρ-sx≡rename-extend-lookup-ρ-x {σ = τ} ρσ x) ⟩
              rename (ext {σ = τ} ρρ) (rename E.extend (lookup ρσ x))
            ≡⟨ rename∘rename E.extend (ext {σ = τ} ρρ) (lookup ρσ x) ⟩
              rename (select E.extend (ext {σ = τ} ρρ)) (lookup ρσ x)
            ≡⟨ cong (λ e → rename e (lookup ρσ x)) (env-extensionality (select-extend-ext-ρ≡step-ρ ρρ)) ⟩
              rename (step ρρ) (lookup ρσ x)
            ∎
        f : lookup (exts (rename ρρ <$> ρσ)) (s x)
            ≡ rename (step ρρ) (lookup ρσ x)
        f = begin
              lookup (exts (rename ρρ <$> ρσ)) (s x)
            ≡⟨ lookup-exts-ρ-sx≡rename-extend-lookup-ρ-x (rename ρρ <$> ρσ) x ⟩
              rename E.extend (lookup (_<$>_ {𝓦 = Lam} (rename ρρ) ρσ) x)
            ≡⟨⟩
              rename E.extend (rename ρρ (lookup ρσ x))
            ≡⟨ rename∘rename ρρ E.extend (lookup ρσ x) ⟩
              rename (select ρρ E.extend) (lookup ρσ x)
            ≡⟨ cong (λ e → rename e (lookup ρσ x)) (env-extensionality (select-ρ-extend≡step-ρ ρρ)) ⟩
              rename (step ρρ) (lookup ρσ x)
            ∎
        h : rename (ext {σ = τ} ρρ) (lookup (exts ρσ) (s x))
            ≡ lookup (exts (rename ρρ <$> ρσ)) (s x)
        h = trans g (sym f)

lemma-~ren-L : ∀ {Γ Δ Θ σ τ} (ρρ : Thinning Γ Θ) (ρσ : Subst Δ Γ) (N : Lam τ (σ ∷ Δ))
  → rename (ext ρρ) (subst (exts ρσ) N) ≡ subst (exts (rename ρρ <$> ρσ)) N
lemma-~ren-L ρρ ρσ N =
  begin
    rename (ext ρρ) (subst (exts ρσ) N)
  ≡⟨ rename∘subst {ρρ = ext ρρ} {exts ρσ} N ⟩
    subst (rename (ext ρρ) <$> exts ρσ) N
  ≡⟨ cong (λ e → subst e N) (env-extensionality (lemma-~ren-L-helper ρρ ρσ)) ⟩
    subst (exts (rename ρρ <$> ρσ)) N
  ∎
