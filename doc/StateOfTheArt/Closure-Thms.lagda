\begin{code}
module StateOfTheArt.Closure-Thms where

open import StateOfTheArt.Types
open ≡ᴱ-Reasoning
open import StateOfTheArt.Closure

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat.Base
open import Data.List.Base hiding ([_] ; _++_ ; lookup)
open import Function
\end{code}

\begin{code}
{-# TERMINATING #-}
\end{code}

%<*rename-subst>
\begin{code}
rename∘subst : ∀ {Γ Δ Θ τ} (ρρ : Thinning Γ Θ) (ρσ : Subst Δ Γ) (N : Lam τ Δ)
  → rename ρρ (subst ρσ N) ≡ subst (rename ρρ <$> ρσ) N
\end{code}
%</rename-subst>

\begin{code}
rename∘subst ρρ ρσ (V x)    =  refl
rename∘subst ρρ ρσ (A M N)  =  cong₂ A (rename∘subst ρρ ρσ M) (rename∘subst ρρ ρσ N)
rename∘subst ρρ ρσ (L N E)  =  cong₂ L refl (env-extensionality h)
  where h : (_<$>_ {𝓦 = Lam} (rename ρρ) (_<$>_ {𝓦 = Lam} (subst ρσ) E))
            ≡ᴱ (subst (_<$>_ {𝓦 = Lam} (rename ρρ) ρσ) <$> E)
        h = beginᴱ
              _<$>_ {𝓦 = Lam} (rename ρρ) (_<$>_ {𝓦 = Lam} (subst ρσ) E)
            ≡ᴱ⟨ <$>-distr {𝓦 = Lam} (subst ρσ) (rename ρρ) E ⟩
              _<$>_ {𝓦 = Lam} (rename ρρ ∘ subst ρσ) E
            ≡ᴱ⟨ <$>-fun {𝓦 = Lam} (λ v → rename∘subst ρρ ρσ v) E ⟩
              subst (_<$>_ {𝓦 = Lam} (rename ρρ) ρσ) <$> E
            ∎ᴱ
\end{code}

\begin{code}
{-# TERMINATING #-}
\end{code}

%<*subst-subst>
\begin{code}
subst∘subst : ∀ {Γ Δ Θ τ} (ρ₁ : Subst Γ Θ) (ρ₂ : Subst Δ Γ) (N : Lam τ Δ)
  → subst ρ₁ (subst ρ₂ N) ≡ subst (subst ρ₁ <$> ρ₂) N
\end{code}
%</subst-subst>

\begin{code}
subst∘subst ρ₁ ρ₂ (V x)    =  refl
subst∘subst ρ₁ ρ₂ (A M N)  =  cong₂ A (subst∘subst ρ₁ ρ₂ M) (subst∘subst ρ₁ ρ₂ N)
subst∘subst ρ₁ ρ₂ (L N E)  =  cong₂ L refl (env-extensionality h)
  where h : (_<$>_ {𝓦 = Lam} (subst ρ₁) (_<$>_ {𝓦 = Lam} (subst ρ₂) E)) ≡ᴱ (subst (_<$>_ {𝓦 = Lam} (subst ρ₁) ρ₂) <$> E)
        h = beginᴱ
              (_<$>_ {𝓦 = Lam} (subst ρ₁) (_<$>_ {𝓦 = Lam} (subst ρ₂) E))
            ≡ᴱ⟨ <$>-distr {𝓦 = Lam} (subst ρ₂) (subst ρ₁) E ⟩
              _<$>_ {𝓦 = Lam} (subst ρ₁ ∘ subst ρ₂) E
            ≡ᴱ⟨ <$>-fun {𝓦 = Lam} (λ e → subst∘subst ρ₁ ρ₂ e) E ⟩
              (subst (_<$>_ {𝓦 = Lam} (subst ρ₁) ρ₂) <$> E)
            ∎ᴱ
\end{code}

\begin{code}
{-# TERMINATING #-}
\end{code}

%<*subst-rename>
\begin{code}
subst∘rename : ∀ {Γ Δ Θ τ} (ρσ : Subst Γ Θ) (ρρ : Thinning Δ Γ) (N : Lam τ Δ)
  → subst ρσ (rename ρρ N) ≡ subst (select ρρ ρσ) N
\end{code}
%</subst-rename>

%<*subst-rename-proof>
\begin{code}
subst∘rename ρσ ρρ (V x)    =  refl
subst∘rename ρσ ρρ (A M N)  =  cong₂ A (subst∘rename ρσ ρρ M)
                                       (subst∘rename ρσ ρρ N)
subst∘rename ρσ ρρ (L N E)  =  cong₂ L refl (env-extensionality h)
  where h : (_<$>_ {𝓦 = Lam} (subst ρσ) (_<$>_ {𝓦 = Lam} (rename ρρ) E))
            ≡ᴱ (subst (select ρρ ρσ) <$> E)
        h = beginᴱ
              _<$>_ {𝓦 = Lam} (subst ρσ) (_<$>_ {𝓦 = Lam} (rename ρρ) E)
            ≡ᴱ⟨ <$>-distr {𝓦 = Lam} (rename ρρ) (subst ρσ) E ⟩
              _<$>_ {𝓦 = Lam} (subst ρσ ∘ rename ρρ) E
            ≡ᴱ⟨ <$>-fun {𝓦 = Lam} (λ e → subst∘rename ρσ ρρ e) E ⟩
              subst (select ρρ ρσ) <$> E
            ∎ᴱ
\end{code}
%</subst-rename-proof>

\begin{code}
{-# TERMINATING #-}
\end{code}

%<*rename-rename>
\begin{code}
rename∘rename : ∀ {Γ Δ Θ τ} (ρ₁ : Thinning Γ Δ) (ρ₂ : Thinning Δ Θ) (N : Lam τ Γ)
  → rename ρ₂ (rename ρ₁ N) ≡ rename (select ρ₁ ρ₂) N
\end{code}
%</rename-rename>

\begin{code}
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
\end{code}

\begin{code}
lemma-~subst-L-helper : ∀ {Γ Δ Θ τ} (ρ₁ : Subst Γ Θ) (ρ₂ : Subst Δ Γ)
  → subst (exts {σ = τ} ρ₁) <$> (exts ρ₂) ≡ᴱ exts (subst ρ₁ <$> ρ₂)
eq (lemma-~subst-L-helper ρ₁ ρ₂) z = refl
eq (lemma-~subst-L-helper {τ = τ} ρ₁ ρ₂) (s x) = h
  where f : subst (exts {σ = τ} ρ₁) (lookup (exts ρ₂) (s x))
            ≡ subst (s-step ρ₁) (lookup ρ₂ x)
        f = begin
              subst (exts {σ = τ} ρ₁) (lookup (exts ρ₂) (s x))
            ≡⟨⟩
              subst (exts {σ = τ} ρ₁) (rename (pack s) (lookup ρ₂ x))
            ≡⟨ subst∘rename (exts ρ₁) (pack s) (lookup ρ₂ x) ⟩
              subst (select (pack s) (exts ρ₁)) (lookup ρ₂ x)
            ≡⟨⟩
              subst (s-step ρ₁) (lookup ρ₂ x)
            ∎
        g : lookup (exts {σ = τ} (subst ρ₁ <$> ρ₂)) (s x)
            ≡ subst (s-step ρ₁) (lookup ρ₂ x)
        g = begin
              lookup (exts {σ = τ} (subst ρ₁ <$> ρ₂)) (s x)
            ≡⟨⟩
              rename (pack s) (lookup (_<$>_ {𝓦 = Lam} (subst ρ₁) ρ₂) x)
            ≡⟨⟩
              rename (pack s) (subst ρ₁ (lookup ρ₂ x))
            ≡⟨ rename∘subst (pack s) ρ₁ (lookup ρ₂ x) ⟩
              subst (rename (pack s) <$> ρ₁) (lookup ρ₂ x)
            ≡⟨⟩
              subst (s-step ρ₁) (lookup ρ₂ x)
            ∎
        h : subst (exts {σ = τ} ρ₁) (lookup (exts ρ₂) (s x))
            ≡ lookup (exts (subst ρ₁ <$> ρ₂)) (s x)
        h = trans f (sym g)

lemma-~ren-L-helper : ∀ {Γ Δ Θ τ} (ρρ : Thinning Γ Θ) (ρσ : Subst Δ Γ)
  → rename (ext {σ = τ} ρρ) <$> (exts ρσ) ≡ᴱ exts (rename ρρ <$> ρσ)
eq (lemma-~ren-L-helper {τ = τ} ρρ ρσ) z = refl
eq (lemma-~ren-L-helper {τ = τ} ρρ ρσ) (s x) = h
  where 
        g : rename (ext {σ = τ} ρρ) (lookup (exts ρσ) (s x))
            ≡ rename (s <$> ρρ) (lookup ρσ x)
        g = begin
              rename (ext {σ = τ} ρρ) (lookup (exts ρσ) (s x))
            ≡⟨⟩
              rename (ext {σ = τ} ρρ) (rename (pack s) (lookup ρσ x))
            ≡⟨ rename∘rename (pack s) (ext {σ = τ} ρρ) (lookup ρσ x) ⟩
              rename (select (pack s) (ext {σ = τ} ρρ)) (lookup ρσ x)
            ≡⟨⟩
              rename (s <$> ρρ) (lookup ρσ x)
            ∎
        f : lookup (exts (rename ρρ <$> ρσ)) (s x)
            ≡ rename (s <$> ρρ) (lookup ρσ x)
        f = begin
              lookup (exts (rename ρρ <$> ρσ)) (s x)
            ≡⟨⟩
              rename (pack s) (lookup (_<$>_ {𝓦 = Lam} (rename ρρ) ρσ) x)
            ≡⟨⟩
              rename (pack s) (rename ρρ (lookup ρσ x))
            ≡⟨ rename∘rename ρρ (pack s) (lookup ρσ x) ⟩
              rename (select ρρ (pack s)) (lookup ρσ x)
            ≡⟨⟩
              rename (s <$> ρρ) (lookup ρσ x)
            ∎
        h : rename (ext {σ = τ} ρρ) (lookup (exts ρσ) (s x))
            ≡ lookup (exts (rename ρρ <$> ρσ)) (s x)
        h = trans g (sym f)
\end{code}

%<*lemma-subst-comm>
\begin{code}
lemma-~subst-L : ∀ {Γ Δ Θ σ τ} (ρ₁ : Subst Γ Θ) (ρ₂ : Subst Δ Γ) (N : Lam τ (σ ∷ Δ))
  → subst (exts ρ₁) (subst (exts ρ₂) N) ≡ subst (exts (subst ρ₁ <$> ρ₂)) N
\end{code}
%</lemma-subst-comm>

\begin{code}
lemma-~subst-L ρ₁ ρ₂ N =
  begin
    subst (exts ρ₁) (subst (exts ρ₂) N)
  ≡⟨ subst∘subst (exts ρ₁) (exts ρ₂) N ⟩
    subst (subst (exts ρ₁) <$> exts ρ₂) N
  ≡⟨ cong (λ e → subst e N) (env-extensionality (lemma-~subst-L-helper ρ₁ ρ₂)) ⟩
    subst (exts (subst ρ₁ <$> ρ₂)) N
  ∎
\end{code}

%<*lemma-ren-comm>
\begin{code}
lemma-~ren-L : ∀ {Γ Δ Θ σ τ} (ρρ : Thinning Γ Θ) (ρσ : Subst Δ Γ) (N : Lam τ (σ ∷ Δ))
  → rename (ext ρρ) (subst (exts ρσ) N) ≡ subst (exts (rename ρρ <$> ρσ)) N
\end{code}
%</lemma-ren-comm>
\begin{code}
lemma-~ren-L ρρ ρσ N =
  begin
    rename (ext ρρ) (subst (exts ρσ) N)
  ≡⟨ rename∘subst (ext ρρ) (exts ρσ) N ⟩
    subst (rename (ext ρρ) <$> exts ρσ) N
  ≡⟨ cong (λ e → subst e N) (env-extensionality (lemma-~ren-L-helper ρρ ρσ)) ⟩
    subst (exts (rename ρρ <$> ρσ)) N
  ∎
\end{code}

\begin{code}
-- neat mutual recursion here

h : ∀ {Γ σ τ} (VV : Lam σ Γ) (N : Lam τ Γ)
  → subst (select (pack s) (id-subst ∙ VV)) N ≡ N
h1 : ∀ {Γ Δ σ} (E : Subst Δ Γ) (VV : Lam σ Γ)
  → (subst (select (pack s) (id-subst ∙ VV)) <$> E) ≡ᴱ E
h VV (V x) = refl
h VV (A M N) = cong₂ A (h VV M) (h VV N)
h VV (L N E) = cong₂ L refl (env-extensionality (h1 E VV))
eq (h1 E VV) x = h VV (lookup E x)

subst-E∙V : ∀ {Γ Δ σ τ} (N : Lam τ (σ ∷ Δ)) (E : Subst Δ Γ) (VV : Lam σ Γ)
  → subst (id-subst ∙ VV) (subst (exts E) N) ≡ subst (E ∙ VV) N
subst-E∙V {Γ} N E VV =
  begin
    subst (id-subst ∙ VV) (subst (exts E) N)
  ≡⟨ subst∘subst (id-subst ∙ VV) (exts E) N ⟩
    subst (subst (id-subst ∙ VV) <$> exts E) N
  ≡⟨ cong (λ e → subst e N) (env-extensionality E∙VV) ⟩
    subst (E ∙ VV) N
  ∎
  where
  E∙VV : subst (id-subst ∙ VV) <$> exts E ≡ᴱ (E ∙ VV)
  eq E∙VV z = refl
  eq E∙VV (s x) =
    begin
      lookup (_<$>_ {𝓦 = Lam} (subst (id-subst ∙ VV)) (exts E)) (s x)
    ≡⟨⟩
      subst (id-subst ∙ VV) (rename (pack s) (lookup E x))
    ≡⟨ subst∘rename (id-subst ∙ VV) (pack s) (lookup E x) ⟩
      subst (select (pack s) (id-subst ∙ VV)) (lookup E x)
    ≡⟨ h VV (lookup E x) ⟩
      lookup E x
    ≡⟨⟩
      lookup (E ∙ VV) (s x)
    ∎

exts-id-subst : ∀ {Γ σ}
  → id-subst {Γ = σ ∷ Γ} ≡ᴱ exts {σ = σ} (id-subst {Γ = Γ})
eq exts-id-subst z      =  refl
eq exts-id-subst (s x)  =  refl

subst-id-id : ∀ {Γ σ} (N : Lam σ Γ)
  → subst id-subst N ≡ N
subst-id-id (V x) = refl
subst-id-id (A f e) = cong₂ A (subst-id-id f) (subst-id-id e)
subst-id-id (L b ρ) = cong₂ L refl (env-extensionality g)
  where
  g : (subst id-subst <$> ρ) ≡ᴱ ρ
  eq g x rewrite subst-id-id (lookup ρ x) = refl
\end{code}
