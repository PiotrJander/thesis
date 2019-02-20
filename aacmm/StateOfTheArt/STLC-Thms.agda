module StateOfTheArt.STLC-Thms where

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)
open E.≡ᴱ-Reasoning
open import StateOfTheArt.Types
open import StateOfTheArt.STLC

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_ ; lookup)
open import Function


lookup-exts-sx : ∀ {Γ Δ σ τ} (ρ : Subst Γ Δ) (x : Var τ Γ)
  → lookup (exts {σ = σ} ρ) (s x) ≡ rename E.extend (lookup ρ x)
lookup-exts-sx ρ x = refl
