\begin{code}
module StateOfTheArt.Bisimulation where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; ∃-syntax)
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

  ~A : ∀ {Γ σ τ} {L : S.Lam (σ ⇒ τ) Γ} {L† : T.Lam (σ ⇒ τ) Γ}
           {M : S.Lam σ Γ} {M† : T.Lam σ Γ}
    → L ~ L†
    → M ~ M†
      --------------------
    → S.A L M ~ T.A L† M†

  ~L : ∀ {Γ Δ σ τ} {N : S.Lam τ (σ ∷ Γ)}
         {N† : T.Lam τ (σ ∷ Δ)} {E : T.Subst Δ Γ}
    → N ~ T.subst (T.exts E) N†
      ------------------------------------------------
    → S.L N ~ T.L N† E
\end{code}
%</tilde>

%<*convert>
\begin{code}
simple-cc : ∀ {Γ σ} → S.Lam σ Γ → T.Lam σ Γ
simple-cc (S.V x) = T.V x
simple-cc (S.A M N) = T.A (simple-cc M) (simple-cc N)
simple-cc (S.L N) = T.L (simple-cc N) T.id-subst
\end{code}
%</convert>

%<*graph>
\begin{code}
simple-cc→sim : ∀ {Γ σ} (N : S.Lam σ Γ)
  → N ~ simple-cc N
simple-cc→sim (S.V x) = ~V
simple-cc→sim (S.A f e) = ~A (simple-cc→sim f) (simple-cc→sim e)
simple-cc→sim (S.L b) = ~L g
  where
  h : ∀ {Γ σ τ} (M : T.Lam σ (τ ∷ Γ)) → T.subst (T.exts T.id-subst) M ≡ M
  h M =
    begin
      T.subst (T.exts T.id-subst) M
    ≡⟨ cong (λ e → T.subst e M) (sym (env-extensionality TT.exts-id-subst)) ⟩
      T.subst T.id-subst M
    ≡⟨ TT.subst-id-id M ⟩
      M
    ∎
  g : b ~ T.subst (T.exts T.id-subst) (simple-cc b)
  g rewrite h (simple-cc b) = simple-cc→sim b
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
~ts-val : ∀ {Γ σ} {M : S.Lam σ Γ} {M† : T.Lam σ Γ}
  → M ~ M†
  → T.Value M†
    ---------
  → S.Value M
~ts-val ~V          ()
~ts-val (~L ~N)     T.V-L  = S.V-L
~ts-val (~A ~M ~N)  ()
\end{code}

%<*rename-comm>
\begin{code}
~rename : ∀ {Γ Δ σ} {M : S.Lam σ Γ} {M† : T.Lam σ Γ}
  → (ρ : Thinning Γ Δ)
  → M ~ M†
    ----------------------------
  → S.rename ρ M ~ T.rename ρ M†
~rename ρ ~V                              = ~V
~rename ρ (~A ~M ~N)                      = ~A (~rename ρ ~M) (~rename ρ ~N)
~rename ρ (~L {N = N} {N†} {E} ~N) with ~rename (T.ext ρ) ~N
... | ~ρN rewrite TT.lemma-~ren-L ρ E N†  =  ~L ~ρN
\end{code}
%</rename-comm>

\begin{code}
infix 3 _~σ_
\end{code}

%<*pointwise-sim>
\begin{code}
record _~σ_ {Γ Δ : Context} (ρ : S.Subst Γ Δ) (ρ† : T.Subst Γ Δ) : Set where
  field ρ~ρ† : ∀ {σ} → (x : Var σ Γ) → lookup ρ x ~ lookup ρ† x

\end{code}
%</pointwise-sim>

\begin{code}
open _~σ_ public
\end{code}

%<*pointwise-sim-extend>
\begin{code}
_~∙_ : ∀ {Γ Δ σ} {ρ  : S.Subst Γ Δ} {ρ† : T.Subst Γ Δ}
         {M : S.Lam σ Δ} {M† : T.Lam σ Δ}
  → ρ ~σ ρ† → M ~ M†
  → ρ ∙ M ~σ ρ† ∙ M†
ρ~ρ† (ρ~σρ† ~∙ M~M†) z = M~M†
ρ~ρ† (ρ~σρ† ~∙ M~M†) (s x) = ρ~ρ† ρ~σρ† x
\end{code}
%</pointwise-sim-extend>

%<*pointwise-sim-exts>
\begin{code}
~exts : ∀ {Γ Δ} {σ : Type} {ρ  : S.Subst Γ Δ} {ρ† : T.Subst Γ Δ}
  → ρ ~σ ρ†
  → S.exts {τ = σ} ρ ~σ T.exts ρ†
ρ~ρ† (~exts ~ρ) z  = ~V
ρ~ρ† (~exts {σ = σ} {ρ = ρ} {ρ†} ~ρ) (s x)
  = ~rename E.extend (ρ~ρ† ~ρ x)
\end{code}
%</pointwise-sim-exts>

\begin{code}
~id-subst : ∀ {Γ} → S.id-subst {Γ} ~σ T.id-subst {Γ}
ρ~ρ† ~id-subst x = ~V
\end{code}

%<*subst-comm>
\begin{code}
~subst : ∀ {Γ Δ τ} {ρ  : S.Subst Γ Δ} {ρ† : T.Subst Γ Δ}
           {M : S.Lam τ Γ} {M† : T.Lam τ Γ}
  → ρ ~σ ρ† → M ~ M†
  → S.subst ρ M ~ T.subst ρ† M†
~subst ~ρ (~V {x = x}) = ρ~ρ† ~ρ x
~subst ~ρ (~A ~M ~N) = ~A (~subst ~ρ ~M) (~subst ~ρ ~N) 
~subst {ρ† = ρ†} ~ρ (~L {N = N} {N†} {E} ~N) with ~subst (~exts ~ρ) ~N
... | ~ρN rewrite TT.lemma-~subst-L ρ† E N† = ~L ~ρN 
\end{code}
%</subst-comm>

\begin{code}
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

Rel : Set₁
\end{code}

%<*simulation>
\begin{code}
Rel = ∀ {Γ σ} → S.Lam σ Γ → T.Lam σ Γ → Set

ST-Simulation : Rel → Set
ST-Simulation _≈_ = ∀ {Γ σ} {M N : S.Lam σ Γ} {M† : T.Lam σ Γ}
  → M ≈ M† → M S.—→ N
    ---------
  → ∃[ N† ] ((N ≈ N†) × (M† T.—→ N†))

TS-Simulation : Rel → Set
TS-Simulation _≈_ = ∀ {Γ σ} {M : S.Lam σ Γ} {M† N† : T.Lam σ Γ}
  → M ≈ M† → M† T.—→ N†
    ------------------------------
  → ∃[ N ] ((N ≈ N†) × (M S.—→ N))
\end{code}
%</simulation>

%<*bisimulation>
\begin{code}
Bisimulation : (∀ {Γ σ} → S.Lam σ Γ → T.Lam σ Γ → Set) → Set
Bisimulation _≈_ = ST-Simulation _≈_ × TS-Simulation _≈_
\end{code}
%</bisimulation>

\begin{code}
st-sim : ST-Simulation _~_
st-sim ~V ()
st-sim (~L ~N) ()
st-sim (~A ~M ~N) (S.ξ-A₁ M—→)
  with st-sim ~M M—→
... | _ , ~M' , M†—→ = _ , ~A ~M' ~N , T.ξ-A₁ M†—→
st-sim (~A ~M ~N) (S.ξ-A₂ VV N—→)
  with st-sim ~N N—→
... | _ , ~N′ , N†—→ = _ , ~A ~M ~N′ , T.ξ-A₂ (~val ~M VV) N†—→
st-sim (~A (~L {N = N} {N†} ~N) ~VV) (S.β-L VV)
  = _ , /V≡E∙V† {N = N} {N†} ~N ~VV , T.β-L (~val ~VV VV)
  
ts-sim : TS-Simulation _~_
ts-sim ~V ()
ts-sim (~L ~N) ()
ts-sim (~A ~M ~N) (T.ξ-A₁ M†—→) with ts-sim ~M M†—→
... | _ , ~M' , M—→ = _ , ~A ~M' ~N , S.ξ-A₁ M—→
ts-sim (~A ~M ~N) (T.ξ-A₂ VV† N†—→) with ts-sim ~N N†—→
... | _ , ~N' , N—→ = _ , ~A ~M ~N' , S.ξ-A₂ (~ts-val ~M VV†) N—→
ts-sim (~A (~L {N = N} {N†} ~N) ~VV) (T.β-L VV†)
  = _ , /V≡E∙V† {N = N} {N†} ~N ~VV , S.β-L (~ts-val ~VV VV†)

bisim : Bisimulation _~_
bisim = st-sim , ts-sim

\end{code}
