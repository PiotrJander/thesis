\begin{code}
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
import StateOfTheArt.Closure-Thms as TT
\end{code}}

%<*tilde>
\begin{code}
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
\end{code}
%</tilde>

%<*convert>
\begin{code}
convert : ∀ {Γ σ}
  → S.Lam σ Γ
  → T.Lam σ Γ
convert (S.V x) = T.V x
convert (S.A M N) = T.A (convert M) (convert N)
convert (S.L N) = T.L (convert N) T.id-subst
\end{code}
%</convert>

%<*graph>
\begin{code}
graph→relation : ∀ {Γ σ} (N : S.Lam σ Γ)
  → N ~ convert N
graph→relation (S.V x) = ~V
graph→relation (S.A f e) = ~A (graph→relation f) (graph→relation e)
graph→relation (S.L b) = ~L g
  where
  h : T.subst (T.exts T.id-subst) (convert b) ≡ convert b
  h =
    begin
      T.subst (T.exts T.id-subst) (convert b)
    ≡⟨ cong (λ e → T.subst e (convert b)) (sym (env-extensionality TT.exts-id-subst)) ⟩
      T.subst T.id-subst (convert b)
    ≡⟨ TT.subst-id-id (convert b) ⟩
      convert b
    ∎
  g : b ~ T.subst (T.exts T.id-subst) (convert b)
  g rewrite h = graph→relation b
\end{code}
%</graph>

%<*val-comm>
\begin{code}
~val : ∀ {Γ σ} {M : S.Lam σ Γ} {M† : T.Lam σ Γ}
  → M ~ M†
  → S.Value M
    ---------
  → T.Value M†
~val ~V         ()
~val (~L ~N)    S.V-L  =  T.V-L
~val (~A ~M ~N) ()
\end{code}
%</val-comm>

\begin{code}

~rename : ∀ {Γ Δ σ} {M : S.Lam σ Γ} {M† : T.Lam σ Γ}
  → (ρ : Thinning Γ Δ)
  → M ~ M†
    ----------------------------------------------------------
  → S.rename ρ M ~ T.rename ρ M†
~rename ρ ~V = ~V
~rename ρ (~A ~M ~N) = ~A (~rename ρ ~M) (~rename ρ ~N)
~rename ρ (~L {N = N} {N†} {E} ~N) = {!!} -- with ~rename (T.ext ρ) ~N
-- ... | ~ρN rewrite TT.lemma-~ren-L ρ E N† = ~L ~ρN

infix 3 _~σ_
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

~id-subst : ∀ {Γ} → S.id-subst {Γ} ~σ T.id-subst {Γ}
ρ~ρ† ~id-subst x = ~V

_~∙_ : ∀ {Γ Δ σ}
    {ρ  : S.Subst Γ Δ} {ρ† : T.Subst Γ Δ}
    {M : S.Lam σ Δ} {M† : T.Lam σ Δ}
  → ρ ~σ ρ†
  → M ~ M†
    --------------------------------------------------
  → ρ ∙ M ~σ ρ† ∙ M†
ρ~ρ† (ρ~σρ† ~∙ M~M†) z = M~M†
ρ~ρ† (ρ~σρ† ~∙ M~M†) (s x) = ρ~ρ† ρ~σρ† x

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

/V≡E∙V† : ∀ {Γ Δ σ τ}
    {N : S.Lam τ (σ ∷ Γ)} {N† : T.Lam τ (σ ∷ Δ)} {E : T.Subst Δ Γ}
    {V : S.Lam σ Γ} {V† : T.Lam σ Γ}
  → N ~ T.subst (T.exts E) N†
  → V ~ V†
    --------------------------
  → N / V ~ T.subst (E ∙ V†) N†
/V≡E∙V† {N = N} {N†} {E} {VV} {V†} ~N ~VV
  rewrite cong (λ e → (N / VV) ~ e) (sym (TT.subst-E∙V N† E V†))
  = ~subst (~id-subst ~∙ ~VV) ~N

data Leg {Γ σ} (M† : T.Lam σ Γ) (N : S.Lam σ Γ) : Set where

  leg : ∀ {N† : T.Lam σ Γ}
    → N ~ N†
    → M† T.—→ N†
      --------
    → Leg M† N

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
sim (~A (~L {N = N} {N†} ~N) ~VV) (S.β-L VV)
  = leg (/V≡E∙V† {N = N} {N†} ~N ~VV) (T.β-L (~val ~VV VV))
\end{code}
