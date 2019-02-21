{-# OPTIONS --allow-unsolved-metas #-} 
module StateOfTheArt.Bisimulation where

open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)

open import StateOfTheArt.Types
import StateOfTheArt.STLC as S
open S using (_/_)
import StateOfTheArt.Closure as T
import StateOfTheArt.STLC-Thms as ST
import StateOfTheArt.Closure-Thms as TT 

infix  4 _~_

data _~_ : ∀ {Γ σ} → S.Lam σ Γ → T.Lam σ Γ → Set where

  ~V : ∀ {Γ σ} {x : Var σ Γ}
     ---------------
   → S.V x ~ T.V x

  ~L : ∀ {Γ Δ σ τ} {N : S.Lam τ (σ ∷ Γ)} {N† : T.Lam τ (σ ∷ Δ)} {E : T.Subst Δ Γ}
    → N ~ T.subst (T.exts E) N†
      -----------------
    → S.L N ~ T.L N† E

  ~A : ∀ {Γ σ τ} {L : S.Lam (σ ⇒ τ) Γ} {L† : T.Lam (σ ⇒ τ) Γ}
           {M : S.Lam σ Γ} {M† : T.Lam σ Γ}
    → L ~ L†
    → M ~ M†
      --------------------
    → S.A L M ~ T.A L† M†

~val : ∀ {Γ σ} {M : S.Lam σ Γ} {M† : T.Lam σ Γ}
  → M ~ M†
  → S.Value M
    ---------
  → T.Value M†
~val ~V         ()
~val (~L ~N)    S.V-L  =  T.V-L
~val (~A ~M ~N) ()

~rename : ∀ {Γ Δ}
  → (ρ : Thinning Γ Δ)
    ----------------------------------------------------------
  → ∀ {σ} {M : S.Lam σ Γ} {M† : T.Lam σ Γ} → M ~ M† → S.rename ρ M ~ T.rename ρ M†
~rename ρ ~V = ~V
~rename ρ (~A ~M ~N) = ~A (~rename ρ ~M) (~rename ρ ~N)
~rename ρ (~L {N = N} {N†} {E} ~N) with ~rename (T.ext ρ) ~N
... | ~ρN rewrite TT.lemma-~ren-L ρ E N† = ~L ~ρN

record _~σ_ {Γ Δ : Context} (ρ : S.Subst Γ Δ) (ρ† : T.Subst Γ Δ) : Set where
  field ρ~ρ† : ∀ {σ} → (x : Var σ Γ) → lookup ρ x ~ lookup ρ† x
open _~σ_ public

~exts : ∀ {Γ Δ σ}
  → {ρ  : S.Subst Γ Δ}
  → {ρ† : T.Subst Γ Δ}
  → ρ ~σ ρ†
    --------------------------------------------------
  → S.exts {σ = σ} ρ ~σ T.exts ρ†
ρ~ρ† (~exts ~ρ) z = ~V
ρ~ρ† (~exts {σ = σ} {ρ = ρ} {ρ†} ~ρ) (s x) = ~rename E.extend (ρ~ρ† ~ρ x)

~subst : ∀ {Γ Δ}
  → {ρ  : S.Subst Γ Δ}
  → {ρ† : T.Subst Γ Δ}
  → ρ ~σ ρ†
    ---------------------------------------------------------
  → (∀ {τ} {M : S.Lam τ Γ} {M† : T.Lam τ Γ} → M ~ M† → S.subst ρ M ~ T.subst ρ† M†)
~subst ~ρ (~V {x = x}) = ρ~ρ† ~ρ x
~subst {ρ† = ρ†} ~ρ (~L {N = N} {N†} {E} ~N) with ~subst (~exts ~ρ) ~N
... | ~ρN rewrite TT.lemma-~subst-L ρ† E N† = ~L ~ρN 
~subst ~ρ (~A ~M ~N) = ~A (~subst ~ρ ~M) (~subst ~ρ ~N) 

data Leg {Γ σ} (M† : T.Lam σ Γ) (N : S.Lam σ Γ) : Set where

  leg : ∀ {N† : T.Lam σ Γ}
    → N ~ N†
    → M† T.—→ N†
      --------
    → Leg M† N

foo : ∀ {Γ Δ σ τ}
    {N : S.Lam τ (σ ∷ Γ)} {N† : T.Lam τ (σ ∷ Δ)} {E : T.Subst Δ Γ}
    {V : S.Lam σ Γ} {V† : T.Lam σ Γ}
  → N ~ T.subst (T.exts E) N†
  → V ~ V†
    --------------------------
  → N / V ~ T.subst (E ∙ V†) N†
foo ~N ~VV = {!!}

sim : ∀ {Γ σ} {M N : S.Lam σ Γ} {M† : T.Lam σ Γ}
  → M ~ M†
  → M S.—→ N
    ---------
  → Leg M† N
sim ~V ()
sim (~L ~N) ()
sim (~A ~M ~N) (S.ξ-A₁ M—→)
  with sim ~M M—→
... | leg ~M' M†—→ = leg (~A ~M' ~N) (T.ξ-A₁ M†—→)
sim (~A ~M ~N) (S.ξ-A₂ VV N—→)
  with sim ~N N—→
... | leg ~N′ N†—→ = leg (~A ~M ~N′) (T.ξ-A₂ (~val ~M VV) N†—→)
sim (~A (~L ~N) ~VV) (S.β-L VV) = leg {!!} {!!}
