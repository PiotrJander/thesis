\begin{code}

open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_)

module StateOfTheArt.lr where

data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type

Context : Set
Context = List Type

data Var : Type → Context → Set where
  z  : ∀ {Γ σ} → Var σ (σ ∷ Γ)
  s  : ∀ {Γ σ τ} → Var σ Γ → Var σ (τ ∷ Γ)

data Kind : Set where
  `val `trm : Kind

data Exp : Kind → Type → Context → Set

Trm : Type → Context → Set
Trm = Exp `trm

Val : Type → Context → Set
Val = Exp `val

infixl 5 _`$_

data Exp where
  `var : ∀ {Γ σ} → Var σ Γ → Val σ Γ
  _`$_ : ∀ {Γ σ τ} → Val (σ ⇒ τ) Γ → Val σ Γ → Trm τ Γ
  `λ : ∀ {Γ σ τ} → Trm τ (σ ∷ Γ) → Val (σ ⇒ τ) Γ 
  `let : ∀ {Γ σ τ} → Trm σ Γ → Trm τ (σ ∷ Γ) → Trm τ Γ
  `val : ∀ {Γ σ} → Val σ Γ → Trm σ Γ

infix 3 _─Env

record _─Env (Γ : Context) (𝓥 : Type → Context → Set) (Δ : Context) : Set where
  constructor pack
  field lookup : ∀ {σ} → Var σ Γ → 𝓥 σ Δ

open _─Env public

infixl 4 _∙_
infixr 5 _<$>_

ε : ∀ {𝓥 Δ} → ([] ─Env) 𝓥 Δ 
lookup ε ()

_∙_ : ∀ {Γ Δ σ 𝓥} → (Γ ─Env) 𝓥 Δ → 𝓥 σ Δ → (σ ∷ Γ ─Env) 𝓥 Δ
lookup (ρ ∙ v) z = v
lookup (ρ ∙ v) (s x) = lookup ρ x

_<$>_ : ∀ {Γ Δ Θ 𝓥₁ 𝓥₂}
      → (∀ {σ} → 𝓥₁ σ Δ → 𝓥₂ σ Θ) → (Γ ─Env) 𝓥₁ Δ → (Γ ─Env) 𝓥₂ Θ
lookup (f <$> ρ) x = f (lookup ρ x)

Thinning : Context → Context → Set
Thinning Γ Δ = (Γ ─Env) Var Δ

rename : ∀ {Γ Δ σ k} → Thinning Γ Δ → Exp k σ Γ → Exp k σ Δ
rename ρ (`var x)    = `var (lookup ρ x)
rename ρ (M `$ N)    = rename ρ M `$ rename ρ N
rename ρ (`λ N)      = `λ (rename (s <$> ρ ∙ z) N)
rename ρ (`let M N)  = `let (rename ρ M) (rename (s <$> ρ ∙ z) N)
rename ρ (`val N)    = `val (rename ρ N)

subst : ∀ {Γ Δ σ k} → (Γ ─Env) Val Δ → Exp k σ Γ → Exp k σ Δ
subst ρ (`var x)    = lookup ρ x
subst ρ (M `$ N)    = subst ρ M `$ subst ρ N
subst ρ (`λ N)      = `λ (subst (rename (pack s) <$> ρ ∙ `var z) N)
subst ρ (`let M N)  = `let (subst ρ M) (subst (rename (pack s) <$> ρ ∙ `var z) N)
subst ρ (`val N)    = `val (subst ρ N)

Exp₀ : Kind → Type → Set
Exp₀ k τ = Exp k τ []

Trm₀ : Type → Set
Trm₀ = Exp₀ `trm

Val₀ : Type → Set
Val₀ = Exp₀ `val

id-subst : ∀ {Γ} → (Γ ─Env) Val Γ
lookup id-subst x = `var x 

infix 3 _[_]
_[_] : ∀ {Γ σ τ} → Trm τ (σ ∷ Γ) → Val σ Γ → Trm τ Γ
M [ V ] = subst (id-subst ∙ V) M

infix 2 _→₁_
data _→₁_ : ∀ {σ} → Trm₀ σ → Trm₀ σ → Set where
  →₁app : ∀ {σ τ} {M : Trm τ (σ ∷ [])} {V : Val₀ σ} → `λ M `$ V →₁ M [ V ]

infix 2 _⇓_
data _⇓_ : ∀ {σ} → Trm₀ σ → Val₀ σ → Set where
  ⇓val   : ∀ {σ} {V : Val₀ σ} → `val V ⇓ V
  ⇓app   : ∀ {σ τ} {M : Trm τ (σ ∷ [])} {V : Val₀ σ} {U : Val₀ τ} → M [ V ] ⇓ U → `λ M `$ V ⇓ U
  ⇓let   : ∀ {σ τ} {M : Trm₀ σ} {N : Trm τ (σ ∷ [])} {U : Val₀ σ} {V : Val₀ τ} → M ⇓ U → N [ U ] ⇓ V → `let M N ⇓ V
  ⇓step  : ∀ {σ} {M M' : Trm₀ σ} {V : Val₀ σ} → M →₁ M' → M' ⇓ V → M ⇓ V

{-# TERMINATING #-}
sn : ∀ {σ} (N : Trm₀ σ) → Σ[ V ∈ Val₀ σ ] (N ⇓ V)
sn (`var () `$ _)
sn (`λ M `$ V) with sn (M [ V ])
sn (`λ M `$ V) | U , M[V]⇓U = U , ⇓step →₁app M[V]⇓U
sn (`let M N) = {!!}
sn (`val N) = {!!}
