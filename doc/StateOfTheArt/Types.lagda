\begin{code}
open import Data.List using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality as PEq hiding ([_])
open PEq using (_≡_; refl)
open import Function

module StateOfTheArt.Types where

infixr 3 _⇒_
\end{code}

%<*type>
\begin{code}
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type
\end{code}
%</type>

%<*context>
\begin{code}
Context : Set
Context = List Type
\end{code}
%</context>

%<*var>
\begin{code}
data Var : Type → Context → Set where
  z  : ∀ {σ Γ}    → Var σ (σ ∷ Γ)
  s  : ∀ {σ τ Γ}  → Var σ Γ  → Var σ (τ ∷ Γ) 
\end{code}
%</var>

\begin{code}
infix 1 _─Env
\end{code}

%<*env>
\begin{code}
record _─Env (Γ : Context) (𝓥 : Type → Context → Set) (Δ : Context) : Set where
  constructor pack
  field lookup : ∀ {σ} → Var σ Γ → 𝓥 σ Δ
\end{code}
%</env>

\begin{code}
open _─Env public

infixl 4 _∙_
-- infixr 5 _<$>_
\end{code}

%<*thinning>
\begin{code}
Thinning : Context → Context → Set
Thinning Γ Δ = (Γ ─Env) Var Δ
\end{code}
%</thinning>

%<*envops>
\begin{code}
ε : ∀ {𝓥 Δ} → ([] ─Env) 𝓥 Δ 
lookup ε ()

_∙_ : ∀ {Γ Δ σ 𝓥} → (Γ ─Env) 𝓥 Δ → 𝓥 σ Δ → ((σ ∷ Γ) ─Env) 𝓥 Δ
lookup (ρ ∙ v) z = v
lookup (ρ ∙ v) (s x) = lookup ρ x

_<$>_ : ∀ {Γ Δ Θ 𝓥 𝓦}
      → (∀ {σ} → 𝓥 σ Δ → 𝓦 σ Θ) → (Γ ─Env) 𝓥 Δ → (Γ ─Env) 𝓦 Θ
lookup (f <$> ρ) x = f (lookup ρ x)

select : ∀ {Γ Δ Θ 𝓥} → Thinning Γ Δ → (Δ ─Env) 𝓥 Θ → (Γ ─Env) 𝓥 Θ
lookup (select ren ρ) k = lookup ρ (lookup ren k)
\end{code}
%</envops>

\begin{code}
infix 4 _≡ᴱ_
record _≡ᴱ_ {𝓥 : Type → Context → Set} {Γ Δ : Context} (ρ₁ ρ₂ : (Γ ─Env) 𝓥 Δ) : Set where
  field eq : {i : Type} (x : Var i Γ) → lookup ρ₁ x ≡ lookup ρ₂ x
open _≡ᴱ_ public

postulate
  env-extensionality : {𝓥 : Type → Context → Set} {Γ Δ : Context} {ρ₁ ρ₂ : (Γ ─Env) 𝓥 Δ}
    → ρ₁ ≡ᴱ ρ₂
      -----------------------
    → ρ₁ ≡ ρ₂

≡ᴱ-refl : {𝓥 : Type → Context → Set} {Γ Δ : Context} {ρ : (Γ ─Env) 𝓥 Δ}
  → ρ ≡ᴱ ρ
eq ≡ᴱ-refl x = refl

≡ᴱ-trans : {𝓥 : Type → Context → Set} {Γ Δ : Context} {ρ₁ ρ₂ ρ₃ : (Γ ─Env) 𝓥 Δ}
    → ρ₁ ≡ᴱ ρ₂
    → ρ₂ ≡ᴱ ρ₃
      -----
    → ρ₁ ≡ᴱ ρ₃
eq (≡ᴱ-trans  ρ₁≡ᴱρ₂ ρ₂≡ᴱρ₃) x rewrite eq ρ₁≡ᴱρ₂ x | eq ρ₂≡ᴱρ₃ x = refl

module ≡ᴱ-Reasoning {𝓥 : Type → Context → Set} {Γ Δ : Context} where

  infix  1 beginᴱ_
  infixr 2 _≡ᴱ⟨_⟩_
  infix  3 _∎ᴱ

  beginᴱ_ : {ρ₁ ρ₂ : (Γ ─Env) 𝓥 Δ}
    → ρ₁ ≡ᴱ ρ₂
      -----
    → ρ₁ ≡ᴱ ρ₂
  beginᴱ_ ρ₁≡ᴱρ₂ = ρ₁≡ᴱρ₂

  _≡ᴱ⟨_⟩_ : (ρ₁ : (Γ ─Env) 𝓥 Δ) {ρ₂ ρ₃ : (Γ ─Env) 𝓥 Δ}
    → ρ₁ ≡ᴱ ρ₂
    → ρ₂ ≡ᴱ ρ₃
      -----
    → ρ₁ ≡ᴱ ρ₃
  ρ₁ ≡ᴱ⟨ ρ₁≡ᴱρ₂ ⟩ ρ₂≡ᴱρ₃ = ≡ᴱ-trans ρ₁≡ᴱρ₂ ρ₂≡ᴱρ₃

  _∎ᴱ : (ρ : (Γ ─Env) 𝓥 Δ)
      -----
    → ρ ≡ᴱ ρ
  ρ ∎ᴱ = ≡ᴱ-refl

<$>-distr : {𝓥 𝓦 𝓧 : Type → Context → Set} {Γ Δ Θ₁ Θ₂ : Context}
  (f : {i : Type} → 𝓥 i Δ → 𝓦 i Θ₁)
  (g : {i : Type} → 𝓦 i Θ₁ → 𝓧 i Θ₂)
  (ρ : (Γ ─Env) 𝓥 Δ)
    ---------------------------
  → _<$>_ {𝓦 = 𝓧} g (_<$>_ {𝓦 = 𝓦} f ρ) ≡ᴱ _<$>_ {𝓦 = 𝓧} (g ∘ f) ρ
eq (<$>-distr f g ρ) x = refl

<$>-fun : {𝓥 𝓦 : Type → Context → Set} {Γ Δ Θ : Context}
  → {f : {i : Type} → 𝓥 i Δ → 𝓦 i Θ}
  → {g : {i : Type} → 𝓥 i Δ → 𝓦 i Θ}
  → (f≡g : {i : Type} → (v : 𝓥 i Δ) → f v ≡ g v)
  → (ρ : (Γ ─Env) 𝓥 Δ)
    -------------
  → _<$>_ {𝓦 = 𝓦} f ρ ≡ᴱ _<$>_ {𝓦 = 𝓦} g ρ
eq (<$>-fun f≡g ρ) x rewrite f≡g (lookup ρ x) = refl
\end{code}


