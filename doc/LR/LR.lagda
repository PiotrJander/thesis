\begin{code}
open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)

open import LR.Base
import LR.STLC as S
open S using (_[_])
import LR.Closure as T
open T using ()

module LR.LR where

infix 2 _~_
infix 2 _≈_
\end{code}

%<*related>
\begin{code}
{-# NO_POSITIVITY_CHECK #-}
data _⇔_ : {k : Kind} {τ : Type} → S.Exp₀ k τ → T.Exp₀ k τ → Set

_~_ : ∀ {τ} → S.Trm₀ τ → T.Trm₀ τ → Set
_~_ = _⇔_

_≈_ : ∀ {τ} → S.Val₀ τ → T.Val₀ τ → Set
_≈_ = _⇔_

data _⇔_ where

  -- values

  ≈λ : ∀ {Δ σ τ} {M₁ : S.Trm τ (σ ∷ [])}
         {M₂ : T.Trm τ (σ ∷ Δ)} {E : T.Subst Δ []}
       → ({V₁ : S.Val₀ σ} {V₂ : T.Val₀ σ}
              → V₁ ≈ V₂ → M₁ [ V₁ ] ~ T.subst (E ∙ V₂) M₂)
         -------------------------------------------------
       → S.`λ M₁ ≈ T.`λ M₂ E

  -- terms

  ~Trm : ∀ {σ} {N₁ : S.Trm₀ σ} {N₂ : T.Trm₀ σ}
             {V₁ : S.Val₀ σ} {V₂ : T.Val₀ σ}
     → N₁ S.⇓ V₁
     → N₂ T.⇓ V₂
     → V₁ ≈ V₂
       -------
     → N₁ ~ N₂
\end{code}
%</related>

\begin{code}
infix 2 _∙≈_
\end{code}

%<*pointwise-related>
\begin{code}
record _∙≈_ {Γ : List Type}
  (ρ^s : S.Subst Γ []) (ρ^t : T.Subst Γ []) : Set where
  constructor pack^R
  field lookup^R : {σ : Type} (v : Var σ Γ)
                 → lookup ρ^s v ≈ lookup ρ^t v
\end{code}
%</pointwise-related>

\begin{code}
open _∙≈_ public

ε^R : ε ∙≈ ε
lookup^R ε^R ()
\end{code}

%<*pointwise-ext>
\begin{code}
_∙^R_ : ∀ {Γ τ}
        {ρ^s : S.Subst Γ []} {ρ^t : T.Subst Γ []}
        {N₁ : S.Val₀ τ} {N₂ : T.Val₀ τ}
      → ρ^s ∙≈ ρ^t
      → N₁ ≈ N₂
        -------------------------------------
      → ρ^s ∙ N₁ ∙≈ ρ^t ∙ N₂
lookup^R (ρ^R ∙^R ≈N) z      = ≈N
lookup^R (ρ^R ∙^R ≈N) (s x)  = lookup^R ρ^R x
\end{code}
%</pointwise-ext>

%<*compat>
\begin{code}
infix  4 _≅_
data _≅_ : ∀ {Γ σ k} → S.Exp k σ Γ → T.Exp k σ Γ → Set where

  -- values

  ~var : ∀ {Γ σ} {x : Var σ Γ}
     ---------------
   → S.`var x ≅ T.`var x

  ~λ : ∀ {Γ Δ σ τ} {N₁ : S.Trm τ (σ ∷ Γ)} {N₂ : T.Trm τ (σ ∷ Δ)} {E : T.Subst Δ Γ}
    → N₁ ≅ T.subst (T.exts E) N₂
      -----------------
    → S.`λ N₁ ≅ T.`λ N₂ E

  -- terms

  _~$_ : ∀ {Γ σ τ} {L : S.Val (σ ⇒ τ) Γ} {L† : T.Val (σ ⇒ τ) Γ}
           {M : S.Val σ Γ} {M† : T.Val σ Γ}
    → L ≅ L†
    → M ≅ M†
      --------------------
    → L S.`$ M ≅ L† T.`$ M†

  ~let : ∀ {Γ σ τ} {M₁ : S.Trm σ Γ} {M₂ : T.Trm σ Γ}
           {N₁ : S.Trm τ (σ ∷ Γ)} {N₂ : T.Trm τ (σ ∷ Γ)}
    → M₁ ≅ M₂
    → N₁ ≅ N₂
      ----------------------------
    → S.`let M₁ N₁ ≅ T.`let M₂ N₂

  ~val : ∀ {Γ σ} {M₁ : S.Val σ Γ} {M₂ : T.Val σ Γ}
    → M₁ ≅ M₂
      ----------------------
    → S.`val M₁ ≅ T.`val M₂
\end{code}
%</compat>

\begin{code}
postulate
  helper-1 : ∀ {Γ σ τ} (ρ^s : S.Subst Γ []) (N₁ : S.Trm τ (σ ∷ Γ)) (V₁ : S.Val₀ σ)
    → S.subst (S.id-subst ∙ V₁) (S.subst (S.rename (pack s) <$> ρ^s ∙ S.`var z) N₁) ≡ S.subst (ρ^s ∙ V₁) N₁

postulate
  helper-2 : ∀ {Γ Δ σ τ} (ρ^t : T.Subst Γ []) (E : T.Subst Δ Γ) (N₂ : T.Trm τ (σ ∷ Δ)) (V₂ : T.Val₀ σ)
    → T.subst (ρ^t ∙ V₂) (T.subst (T.rename (pack s) <$> E ∙ T.`var z) N₂) ≡ T.subst (T.subst ρ^t <$> E ∙ V₂) N₂
\end{code}

%<*fund-t>
\begin{code}
fund : ∀ {Γ σ k} {M₁ : S.Exp k σ Γ} {M₂ : T.Exp k σ Γ}
       {ρ^s : S.Subst Γ []} {ρ^t : T.Subst Γ []}
   → ρ^s ∙≈ ρ^t
   → M₁ ≅ M₂
     -------------------------------
   → S.subst ρ^s M₁ ⇔ T.subst ρ^t M₂
\end{code}
%</fund-t>

\begin{code}
fund-lam : ∀ {Γ Δ σ τ} {N₁ : S.Trm τ (σ ∷ Γ)} {N₂ : T.Trm τ (σ ∷ Δ)} {E : T.Subst Δ Γ} {V₁ : S.Val₀ σ} {V₂ : T.Val₀ σ}
       {ρ^s : S.Subst Γ []} {ρ^t : T.Subst Γ []}
   → ρ^s ∙≈ ρ^t
   → N₁ ≅ T.subst (T.exts E) N₂
   → V₁ ≈ V₂
     -----------------
   → S.subst (S.rename (pack s) <$> ρ^s ∙ S.`var z) N₁ [ V₁ ] ~ T.subst (T.subst ρ^t <$> E ∙ V₂) N₂  

fund ∙≈ρ (~var {x = x}) = lookup^R ∙≈ρ x
fund ∙≈ρ (~λ ~N) = ≈λ (λ V₁≈V₂ → ⊥-elim impossible) where postulate impossible : ⊥ -- fund-lam ∙≈ρ ~N V₁≈V₂
fund {ρ^s = ρ^s} {ρ^t} ∙≈ρ (_~$_ {L = L} {L†} ~M ~N) with S.subst ρ^s L | T.subst ρ^t L† | fund ∙≈ρ ~M | fund ∙≈ρ ~N
... | S.`var () | _ | _ | _
... | S.`λ _ | T.`var () | _ | _
fund {ρ^s = ρ^s} {ρ^t} ∙≈ρ (_~$_ {L = L} {L†} ~M ~N) | S.`λ N | T.`λ N† E | ≈λ p | ~V with p ~V
... | ~Trm N₁⇓U₁ N₂⇓U₂ U₁≈U₂ = ~Trm (S.⇓step S.→₁app N₁⇓U₁) (T.⇓step T.→₁app N₂⇓U₂) U₁≈U₂
fund ∙≈ρ (~let ~M ~N) = ⊥-elim impossible where postulate impossible : ⊥
fund ∙≈ρ (~val ~M) with fund ∙≈ρ ~M
... | ~V = ~Trm S.⇓val T.⇓val ~V
fund-lam {N₁ = N₁} {N₂} {E} {V₁} {V₂} {ρ^s} {ρ^t} ∙≈ρ ~N V₁≈V₂ with fund (∙≈ρ ∙^R V₁≈V₂) ~N
... | p rewrite helper-1 ρ^s N₁ V₁ | sym (helper-2 ρ^t E N₂ V₂) = p






postulate
  subst∘subst : ∀ {Γ Δ Θ τ} (ρ₁ : S.Subst Γ Θ) (ρ₂ : S.Subst Δ Γ) (N : S.Trm τ Δ)
    → S.subst ρ₁ (S.subst ρ₂ N) ≡ S.subst (S.subst ρ₁ <$> ρ₂) N
    
-- helper-1 ρ^s N₁ V₁ =
--   begin
--     S.subst (S.id-subst ∙ V₁) (S.subst (S.rename (pack s) <$> ρ^s ∙ S.`var z) N₁)
--   ≡⟨ subst∘subst (S.id-subst ∙ V₁) (S.rename (pack s) <$> ρ^s ∙ S.`var z) N₁ ⟩  -- 
--     S.subst (S.subst (S.id-subst ∙ V₁) <$> (S.rename (pack s) <$> ρ^s ∙ S.`var z)) N₁
--   ≡⟨⟩
--     S.subst (S.subst (S.id-subst ∙ V₁) <$> S.rename (pack s) <$> ρ^s ∙ V₁) N₁
--   ≡⟨ {!!} ⟩
--     S.subst (S.subst (S.id-subst ∙ V₁) <$> S.rename (pack s) <$> ρ^s ∙ V₁) N₁
--   ≡⟨ ⟩
--     S.subst (ρ^s ∙ V₁) N₁
--   ∎
  
-- S.subst (S.id-subst ∙ V₁) (S.subst (S.rename (pack s) <$> ρ^s ∙ S.`var z) N₁)
-- S.subst (S.subst (S.id-subst ∙ V₁) <$> (S.rename (pack s) <$> ρ^s ∙ S.`var z)) N₁
-- S.subst (S.subst (S.id-subst ∙ V₁) ∘ S.rename (pack s) <$> ρ^s ∙ V₁) N₁
-- S.subst (ρ^s ∙ V₁) N₁

-- T.subst (ρ^t ∙ V₂) (T.subst (T.rename (pack s) <$> E ∙ T.`var z) N₂)
-- T.subst (T.subst (ρ^t ∙ V₂) <$> (T.rename (pack s) <$> E ∙ T.`var z)) N₂
-- T.subst (T.subst (ρ^t ∙ V₂) <$> T.rename (pack s) <$> E ∙ V₂) N₂
-- T.subst (T.subst ρ^t <$> E ∙ V₂) N₂
