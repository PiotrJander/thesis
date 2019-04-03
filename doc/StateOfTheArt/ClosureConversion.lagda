\chapter{Conversion}

\section{Imports}

\begin{code}
module StateOfTheArt.ClosureConversion where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; inspect; [_])
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat -- using (ℕ; zero; suc; _+_)
open import Relation.Nullary using (¬_)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Sublist.Propositional using (_⊆_ ; []⊆_ ; base ; keep ; skip)
open import Data.List.Relation.Sublist.Propositional.Properties using (⊆-refl ; ⊆-trans)
open import Function using (_∘_)
open import Induction.WellFounded
open import Induction.Nat
open import Data.Product using (_×_; _,_; ∃-syntax; Σ-syntax; proj₁; proj₂)
open import Relation.Binary hiding (_⇒_)
open import Level renaming (zero to lzero)

open import StateOfTheArt.Types
import StateOfTheArt.STLC as S
open S using (_/_)
import StateOfTheArt.Closure as T
open import StateOfTheArt.Closure-Thms hiding (h; h1)
open import StateOfTheArt.SubContext
open import StateOfTheArt.Bisimulation
\end{code}

\section{Existential types for environments}

It is a well-known property of typed closure conversion that environments have existential types.
This implementation has the prperty that as it transforms the source term bottom-up, it maintains a minimal context,
which is the Δ field on the dependent record.

%<*ex-subctx-trm>
\begin{code}
record _⊩_ (Γ : Context) (A : Type) : Set where
  constructor ∃[_]_∧_
  field
    Δ : Context
    Δ⊆Γ : Δ ⊆ Γ
    N : T.Lam A Δ
\end{code}
%</ex-subctx-trm>

\section{Helper functions for closure conversion}

\begin{code}
Var→⊆ : ∀ {Γ} {A : Type} → Var A Γ → A ∷ [] ⊆ Γ
Var→⊆ {_ ∷ Γ} z = keep ([]⊆ Γ)
Var→⊆ (s x) = skip (Var→⊆ x)
\end{code}

%<*adjust-context-t>
\begin{code}
record AdjustContext {A Γ Δ} (Δ⊆A∷Γ : Δ ⊆ A ∷ Γ) : Set where
  constructor adjust
  field
    Δ₁     : Context
    Δ₁⊆Γ   : Δ₁ ⊆ Γ
    Δ⊆AΔ₁  : Δ ⊆ A ∷ Δ₁
    well   : Δ⊆A∷Γ ≡ ⊆-trans Δ⊆AΔ₁ (keep Δ₁⊆Γ)
\end{code}
%</adjust-context-t>

\begin{code}
helper-1 : {Γ Δ : Context} (Δ⊆Γ : Δ ⊆ Γ) → ⊆-trans ⊆-refl Δ⊆Γ ≡ Δ⊆Γ
helper-1 base = refl
helper-1 (skip Δ⊆Γ) = cong skip (helper-1 Δ⊆Γ)
helper-1 (keep Δ⊆Γ) = cong keep (helper-1 Δ⊆Γ)
\end{code}

%<*adjust-context-f>
\begin{code}
adjust-context : ∀ {Γ Δ A} → (Δ⊆A∷Γ : Δ ⊆ A ∷ Γ) → AdjustContext Δ⊆A∷Γ
\end{code}
%</adjust-context-f>

\begin{code}
adjust-context (skip {xs = Δ₁} Δ⊆Γ) = adjust Δ₁ Δ⊆Γ (skip ⊆-refl) (cong skip (sym (helper-1 Δ⊆Γ)))
adjust-context (keep {xs = Δ₁} Δ⊆Γ) = adjust Δ₁ Δ⊆Γ (keep ⊆-refl) (cong keep (sym (helper-1 Δ⊆Γ)))
\end{code}

\section{Closure conversion}

This formulation of closure conversion is in its essence a simple mapping between syntactic counterparts in the source and target language.
The main source of compilcation is the need to merge minimal contexts.

The case of the lambda abstraction is most interesting. A recursive call on the body produces a minimal context which describes the minimal environment.

%<*subctx-to-ren>
\begin{code}
⊆→ρ : {Γ Δ : Context} → Γ ⊆ Δ → Thinning Γ Δ
lookup (⊆→ρ base) ()
lookup (⊆→ρ (skip Γ⊆Δ)) x = s (lookup (⊆→ρ Γ⊆Δ) x)
lookup (⊆→ρ (keep Γ⊆Δ)) z = z
lookup (⊆→ρ (keep Γ⊆Δ)) (s x) = s (lookup (⊆→ρ Γ⊆Δ) x)
\end{code}
%</subctx-to-ren>

%<*min-cc>
\begin{code}
cc : ∀ {Γ A} → S.Lam A Γ → Γ ⊩ A
\end{code}
%</min-cc>

%<*min-cc-v>
\begin{code}
cc {A = A} (S.V x) = ∃[ A ∷ [] ] Var→⊆ x ∧ T.V z
\end{code}
%</min-cc-v>

%<*min-cc-a>
\begin{code}
cc (S.A M N) with cc M | cc N
cc (S.A M N) | ∃[ Δ ] Δ⊆Γ ∧ M† | ∃[ Δ₁ ] Δ₁⊆Γ ∧ N† with merge Δ⊆Γ Δ₁⊆Γ
cc (S.A M N) | ∃[ Δ ] Δ⊆Γ ∧ M† | ∃[ Δ₁ ] Δ₁⊆Γ ∧ N† | subListSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ _ _
  = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.A (T.rename (⊆→ρ Δ⊆Γ₁) M†) (T.rename (⊆→ρ Δ₁⊆Γ₁) N†))
\end{code}
%</min-cc-a>

%<*min-cc-l>
\begin{code}
cc (S.L N) with cc N
cc (S.L N) | ∃[ Δ ] Δ⊆Γ ∧ N† with adjust-context Δ⊆Γ
cc (S.L N) | ∃[ Δ ] Δ⊆Γ ∧ N† | adjust Δ₁ Δ₁⊆Γ Δ⊆AΔ₁ _
  = ∃[ Δ₁ ] Δ₁⊆Γ ∧ (T.L (T.rename (⊆→ρ Δ⊆AΔ₁) N†) T.id-subst)
\end{code}
%</min-cc-l>

%<*min-cc-sim>
%<*dag>
\begin{code}
_† : ∀ {Γ A} → S.Lam A Γ → T.Lam A Γ
M † with cc M
M † | ∃[ Δ ] Δ⊆Γ ∧ N = T.rename (⊆→ρ Δ⊆Γ) N
\end{code}
%</dag>

%<*undo-compat>
\begin{code}
{-# TERMINATING #-}
undo : ∀ {Γ A} → T.Lam A Γ → S.Lam A Γ
undo (T.V x)    = S.V x
undo (T.A M N)  = S.A (undo M) (undo N)
undo (T.L M E)  = S.L (undo (T.subst (T.exts E) M))

{-# TERMINATING #-}
undo-compat : ∀ {Γ σ} (N : T.Lam σ Γ) → undo N ~ N
undo-compat (T.V x)    = ~V
undo-compat (T.A M N)  = ~A (undo-compat M) (undo-compat N)
undo-compat (T.L N E)  = ~L (undo-compat _)
\end{code}
%</undo-compat>

\begin{code}
helper-2 : ∀ {Γ A} (x : Var A Γ)
  → lookup (⊆→ρ (Var→⊆ x)) z ≡ x
helper-2 z = refl
helper-2 (s x) = cong s (helper-2 x)

helper-3 : ∀ {Δ₁ Γ₁ Γ} (Δ₁⊆Γ₁ : Δ₁ ⊆ Γ₁) (Γ₁⊆Γ : Γ₁ ⊆ Γ)
  → select (⊆→ρ Δ₁⊆Γ₁) (⊆→ρ Γ₁⊆Γ) ≡ᴱ ⊆→ρ (⊆-trans Δ₁⊆Γ₁ Γ₁⊆Γ)
eq (helper-3 base base) ()
eq (helper-3 Δ₁⊆Γ₁ (skip Γ₁⊆Γ)) x
  = cong s (eq (helper-3 Δ₁⊆Γ₁ Γ₁⊆Γ) x)
eq (helper-3 (skip Δ₁⊆Γ₁) (keep Γ₁⊆Γ)) x
  = cong s (eq (helper-3 Δ₁⊆Γ₁ Γ₁⊆Γ) x)
eq (helper-3 (keep Δ₁⊆Γ₁) (keep Γ₁⊆Γ)) z
  = refl
eq (helper-3 (keep Δ₁⊆Γ₁) (keep Γ₁⊆Γ)) (s x)
  = cong s (eq (helper-3 Δ₁⊆Γ₁ Γ₁⊆Γ) x)

helper-4 : ∀ {Δ₁ Γ₁ Γ τ}
  (Δ₁⊆Γ₁ : Δ₁ ⊆ Γ₁) (Γ₁⊆Γ : Γ₁ ⊆ Γ)
  (Δ₁⊆Γ : Δ₁ ⊆ Γ) (M† : T.Lam τ Δ₁)
  → ⊆-trans Δ₁⊆Γ₁ Γ₁⊆Γ ≡ Δ₁⊆Γ
  → T.rename (⊆→ρ Γ₁⊆Γ) (T.rename (⊆→ρ Δ₁⊆Γ₁) M†)
    ≡ T.rename (⊆→ρ Δ₁⊆Γ) M†
helper-4 Δ₁⊆Γ₁ Γ₁⊆Γ Δ₁⊆Γ M† well =
  begin
    T.rename (⊆→ρ Γ₁⊆Γ) (T.rename (⊆→ρ Δ₁⊆Γ₁) M†)
  ≡⟨ rename∘rename (⊆→ρ Δ₁⊆Γ₁) (⊆→ρ Γ₁⊆Γ) M† ⟩
    T.rename (select (⊆→ρ Δ₁⊆Γ₁) (⊆→ρ Γ₁⊆Γ)) M†
  ≡⟨ cong (λ e → T.rename e M†)
          (env-extensionality (helper-3 Δ₁⊆Γ₁ Γ₁⊆Γ)) ⟩
    T.rename (⊆→ρ (⊆-trans Δ₁⊆Γ₁ Γ₁⊆Γ)) M†
  ≡⟨ cong (λ e → T.rename (⊆→ρ e) M†) well ⟩
    T.rename (⊆→ρ Δ₁⊆Γ) M†
  ∎

{-# TERMINATING #-}
helper-5 : ∀ {Γ Δ σ τ} (Δ⊆Γ : Δ ⊆ Γ) (N : T.Lam σ (τ ∷ Δ))
  → T.subst (T.exts (T.rename (⊆→ρ Δ⊆Γ) <$> T.id-subst)) N
    ≡ T.rename (⊆→ρ (keep Δ⊆Γ)) N
helper-5 Δ⊆Γ (T.V x) with x
helper-5 Δ⊆Γ (T.V x) | z = refl
helper-5 Δ⊆Γ (T.V x) | s x' = refl
helper-5 Δ⊆Γ (T.A M N)
  = cong₂ T.A (helper-5 Δ⊆Γ M) (helper-5 Δ⊆Γ N)
helper-5 Δ⊆Γ (T.L N E) = cong (T.L N) h
  where
  h : T.subst (T.exts (T.rename (⊆→ρ Δ⊆Γ) <$> T.id-subst)) <$> E
      ≡ _<$>_ {𝓦 = T.Lam} (T.rename (⊆→ρ (keep Δ⊆Γ))) E
  h =
    begin
      T.subst (T.exts (T.rename (⊆→ρ Δ⊆Γ) <$> T.id-subst)) <$> E
    ≡⟨ env-extensionality (<$>-fun (helper-5 Δ⊆Γ) E) ⟩
      _<$>_ {𝓦 = T.Lam} (T.rename (⊆→ρ (keep Δ⊆Γ))) E
    ∎
\end{code}

%<*min-cc-sim-t>
\begin{code}
N~N† : ∀ {Γ A} (N : S.Lam A Γ)
  → N ~ N †
\end{code}
%</min-cc-sim-t>

\begin{code}
N~N† (S.V x) with cc (S.V x)
N~N† (S.V x) | ∃[ Δ ] Δ⊆Γ ∧ N rewrite helper-2 x = ~V
N~N† (S.A M N) with cc M | cc N | inspect _† M | inspect _† N
N~N† (S.A M N) | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M† | ∃[ Δ₂ ] Δ₂⊆Γ ∧ N†
  | [ p ] | [ q ] with merge Δ₁⊆Γ Δ₂⊆Γ
N~N† (S.A M N) | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M† | ∃[ Δ₂ ] Δ₂⊆Γ ∧ N†
  | [ p ] | [ q ] | subListSum Γ₁ Γ₁⊆Γ Δ₁⊆Γ₁ Δ₂⊆Γ₁ well well₁
  rewrite helper-4 Δ₁⊆Γ₁ Γ₁⊆Γ Δ₁⊆Γ M† well
  | helper-4 Δ₂⊆Γ₁ Γ₁⊆Γ Δ₂⊆Γ N† well₁ | sym p | sym q
  = ~A (N~N† M) (N~N† N)
N~N† (S.L N) with cc N | inspect _† N
N~N† (S.L N) | ∃[ Δ ] Δ⊆Γ ∧ N' | [ p ]
  with adjust-context Δ⊆Γ
N~N† (S.L N) | ∃[ Δ ] Δ⊆Γ ∧ N' | [ p ]
  | adjust Δ₁ Δ₁⊆Γ Δ⊆AΔ₁ well = ~L g
  where
  h : T.subst (T.exts (T.rename (⊆→ρ Δ₁⊆Γ) <$> T.id-subst))
      (T.rename (⊆→ρ Δ⊆AΔ₁) N') ≡ T.rename (⊆→ρ Δ⊆Γ) N'
  h =
    begin
      T.subst (T.exts (T.rename (⊆→ρ Δ₁⊆Γ) <$> T.id-subst))
        (T.rename (⊆→ρ Δ⊆AΔ₁) N')
    ≡⟨ helper-5 Δ₁⊆Γ (T.rename (⊆→ρ Δ⊆AΔ₁) N') ⟩
      T.rename (⊆→ρ (keep Δ₁⊆Γ)) (T.rename (⊆→ρ Δ⊆AΔ₁) N')
    ≡⟨ rename∘rename (⊆→ρ Δ⊆AΔ₁) (⊆→ρ (keep Δ₁⊆Γ)) N' ⟩
      T.rename (select (⊆→ρ Δ⊆AΔ₁) (⊆→ρ (keep Δ₁⊆Γ))) N'
    ≡⟨ cong (λ e → T.rename e N')
       (env-extensionality (helper-3 Δ⊆AΔ₁ (keep Δ₁⊆Γ))) ⟩
      T.rename (⊆→ρ (⊆-trans Δ⊆AΔ₁ (keep Δ₁⊆Γ))) N'
    ≡⟨ cong (λ e → T.rename (⊆→ρ e) N') (sym well) ⟩
      T.rename (⊆→ρ Δ⊆Γ) N'
    ∎
  g : N ~ T.subst (T.exts (T.rename (⊆→ρ Δ₁⊆Γ) <$> T.id-subst))
                  (T.rename (⊆→ρ Δ⊆AΔ₁) N')
  g rewrite h | sym p = N~N† N
\end{code}
%</min-cc-sim>
