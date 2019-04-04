\begin{code}

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_)

open import LR.Base

module LR.Closure where

data Exp : Kind → Type → Context → Set

Trm : Type → Context → Set
Trm = Exp `trm

Val : Type → Context → Set
Val = Exp `val

Subst : Context → Context → Set
Subst Γ Δ = (Γ ─Env) Val Δ

infixl 5 _`$_

data Exp where
  -- values
  `var : ∀ {Γ σ} → Var σ Γ → Val σ Γ
  `λ : ∀ {Γ Δ σ τ} → Trm τ (σ ∷ Δ) → Subst Δ Γ → Val (σ ⇒ τ) Γ 
  `tt `ff : ∀ {Γ} → Val `𝔹 Γ

  -- terms
  _`$_ : ∀ {Γ σ τ} → Val (σ ⇒ τ) Γ → Val σ Γ → Trm τ Γ
  `let : ∀ {Γ σ τ} → Trm σ Γ → Trm τ (σ ∷ Γ) → Trm τ Γ
  `val : ∀ {Γ σ} → Val σ Γ → Trm σ Γ

{-# TERMINATING #-}
rename : ∀ {Γ Δ σ k} → Thinning Γ Δ → Exp k σ Γ → Exp k σ Δ
rename ρ (`var x)    = `var (lookup ρ x)
rename ρ (M `$ N)    = rename ρ M `$ rename ρ N
rename ρ (`λ N E)    = `λ N (rename ρ <$> E)
rename ρ (`let M N)  = `let (rename ρ M) (rename (s <$> ρ ∙ z) N)
rename ρ (`val N)    = `val (rename ρ N)
rename ρ `tt         = `tt
rename ρ `ff         = `ff

{-# TERMINATING #-}
subst : ∀ {Γ Δ σ k} → (Γ ─Env) Val Δ → Exp k σ Γ → Exp k σ Δ
subst ρ (`var x)    = lookup ρ x
subst ρ (M `$ N)    = subst ρ M `$ subst ρ N
subst ρ (`λ N E)    = `λ N (subst ρ <$> E)
subst ρ (`let M N)  = `let (subst ρ M) (subst (rename (pack s) <$> ρ ∙ `var z) N)
subst ρ (`val N)    = `val (subst ρ N)
subst ρ `tt         = `tt
subst ρ `ff         = `ff

Exp₀ : Kind → Type → Set
Exp₀ k τ = Exp k τ []

Trm₀ : Type → Set
Trm₀ = Exp₀ `trm

Val₀ : Type → Set
Val₀ = Exp₀ `val

id-subst : ∀ {Γ} → (Γ ─Env) Val Γ
lookup id-subst x = `var x

exts : ∀ {Γ Δ σ} → Subst Γ Δ → Subst (σ ∷ Γ) (σ ∷ Δ)
exts ρ = rename (pack s) <$> ρ ∙ `var z

infix 3 _[_]
_[_] : ∀ {Γ σ τ} → Trm τ (σ ∷ Γ) → Val σ Γ → Trm τ Γ
M [ V ] = subst (id-subst ∙ V) M

infix 2 _→₁_
infix 2 _⇓_

data _→₁_ : ∀ {σ} → Trm₀ σ → Trm₀ σ → Set where
  →₁app : ∀ {Δ σ τ} {M : Trm τ (σ ∷ Δ)} {E : Subst Δ []} {V : Val₀ σ} → `λ M E `$ V →₁ subst (E ∙ V) M
  -- →₁let : ∀ {σ τ} {M : Trm₀ σ} {N : Trm τ (σ ∷ [])} {V : Val₀ σ} → M ⇓ V → `let M N →₁ N [ V ]

data _⇓_ : ∀ {σ} → Trm₀ σ → Val₀ σ → Set where
  ⇓val   : ∀ {σ} {V : Val₀ σ} → `val V ⇓ V
  ⇓app   : ∀ {Δ σ τ} {M : Trm τ (σ ∷ Δ)} {E : Subst Δ []} {V : Val₀ σ} {U : Val₀ τ} → subst (E ∙ V) M ⇓ U → `λ M E `$ V ⇓ U
  ⇓let   : ∀ {σ τ} {M : Trm₀ σ} {N : Trm τ (σ ∷ [])} {U : Val₀ σ} {V : Val₀ τ} → M ⇓ U → N [ U ] ⇓ V → `let M N ⇓ V
  ⇓step  : ∀ {σ} {M M' : Trm₀ σ} {V : Val₀ σ} → M →₁ M' → M' ⇓ V → M ⇓ V

