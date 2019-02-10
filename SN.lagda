\begin{code}
module SN where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using ([] ; _∷_; _++_)
open import Data.Product using (∃; ∃-syntax; Σ-syntax; _,_)

open import Common
open import STLC

\end{code}

TODO desc

\begin{code}

record _⇓ {σ} (e : [] ⊢ σ) : Set where
  constructor pack
  field
    v     :  [] ⊢ σ
    V     :  Value v
    e—↠v  :  e —↠ v

V⇓ : ∀ {σ} {v : [] ⊢ σ}
   → Value v
     -------
   → v ⇓
V⇓ {v = v} V = pack v V (v ∎)

record SN-α (e : [] ⊢ `ℕ) : Set
record SN-σ→τ {σ τ} (e : [] ⊢ σ ⇒ τ) : Set
SN : ∀ {σ} → (e : [] ⊢ σ) → Set

record SN-α e where
  constructor pack
  field
    e⇓ : e ⇓

{-# NO_POSITIVITY_CHECK #-}
record SN-σ→τ {σ τ} e where
  inductive
  constructor pack
  field
    e⇓ : e ⇓
    SN-app : {e' : [] ⊢ σ} → SN e' → SN (e · e')

SN {`ℕ} e = SN-α e
SN {σ ⇒ τ} e = SN-σ→τ e

⊨_ : ∀ {Γ} → Substitution _⊢_ Γ [] → Set
⊨_ {Γ} γ = ∀ {σ} → (e : Γ ∋ σ) → SN (γ e)

_∙_ : ∀ {Γ σ} {γ : Substitution _⊢_ Γ []} {e : [] ⊢ σ}
  → ⊨ γ
  → SN e
  → Σ[ γ' ∈ Substitution _⊢_ (σ ∷ Γ) [] ] ⊨ γ'
_∙_ {Γ} {σ} {γ} {e} ⊨γ SN-e = γ' , ⊨γ'
  where
  γ' : Substitution _⊢_ (σ ∷ Γ) []
  γ' Z = e
  γ' (S x) = γ x
  ⊨γ' : ⊨ γ'
  ⊨γ' Z = SN-e
  ⊨γ' (S x) = ⊨γ x

forward : ∀ {σ} {e e' : [] ⊢ σ}
    → e —→ e'
    → SN e
      -----------
    → SN e'
forward {`ℕ} e—→e' (pack (pack v V (.v ∎))) = ⊥-elim (V¬—→ V e—→e')
forward {`ℕ} e—→e' (pack (pack v V (e —→⟨ e—→i ⟩ i—↠v))) with det e—→i e—→e'
... | i≡e' rewrite i≡e' = pack (pack v V i—↠v)
forward {σ ⇒ τ} e—→e' (pack (pack v V (.v ∎)) SN-app) = ⊥-elim (V¬—→ V e—→e')
forward {σ ⇒ τ} e—→e' (pack (pack v V (e —→⟨ e—→i ⟩ i—↠v)) SN-app) with det e—→i e—→e'
... | i≡e' rewrite i≡e' = pack (pack v V i—↠v) (λ SN-e' → forward (ξ-·₁ e—→i) (SN-app SN-e'))

backward : ∀ {σ} {e e' : [] ⊢ σ}
    → e —→ e'
    → SN e'
      -----------
    → SN e
backward e—→e' SN-e = {!!}

sn : ∀ {Γ σ}
   → {γ : Substitution _⊢_ Γ []}
   → ⊨ γ
   → (e : Γ ⊢ σ)
   → SN (subst γ e)
sn ⊨γ (` x)               = ⊨γ x
sn ⊨γ (ƛ_ {A = `ℕ} e)     =  pack (V⇓ V-ƛ) (λ { (pack e⇓) → {!e⇓!} })
sn ⊨γ (ƛ_ {A = σ ⇒ τ} e)  =  pack (V⇓ V-ƛ) λ SN-e' → {!!}
sn ⊨γ (f · e) with sn ⊨γ f | sn ⊨γ e
... | pack f⇓ SN-app | SN-e = SN-app SN-e

\end{code}
