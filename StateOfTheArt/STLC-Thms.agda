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

-- id-subst∙V : ∀ {Γ σ τ} (N : Lam τ (σ ∷ Γ)) (VV : Lam σ Γ)
--   → subst (id-subst ∙ VV) N ≡ N / VV
-- id-subst∙V (V z) VV = refl
-- id-subst∙V (V (s x)) VV = refl
-- id-subst∙V (A M N) VV = cong₂ A (id-subst∙V M VV) (id-subst∙V N VV)
-- id-subst∙V (L N) VV = {!!}
