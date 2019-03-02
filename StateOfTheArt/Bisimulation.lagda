\newcommand{\APT}{\AgdaPrimitiveType}
\newcommand{\AK}{\AgdaKeyword}
\newcommand{\AM}{\AgdaModule}
\newcommand{\AS}{\AgdaSymbol}
\newcommand{\AStr}{\AgdaString}
\newcommand{\AN}{\AgdaNumber}
\newcommand{\AD}{\AgdaDatatype}
\newcommand{\AF}{\AgdaFunction}
\newcommand{\AR}{\AgdaRecord}
\newcommand{\ARF}{\AgdaField}
\newcommand{\AB}{\AgdaBound}
\newcommand{\AIC}{\AgdaInductiveConstructor}
\newcommand{\ti}{\textasciitilde}

\chapter{Bisimulation}

In the previous chapters, we defined the source and target languages
of the closure conversion, together with reduction rules for each, and
a translation function from source to target.

TODO we or passive voice?

Our implementation of closure conversion is type and scope-preserving
by construction. The property of type preservation would be considered
a strong indication of correctness in a real-world compiler, but in
this theoretical development which deals with a small, toy language,
we prove stronger correctness properties which speak about operation
correctness.

One such property of operational correctness of a pair of languages is
bisimulation. Intuition about bisimulation is captured by a slogan: pairwise similar terms
reduce to pairwise similar terms. 

\section{Similarity relation}

\AgdaHide{
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
import StateOfTheArt.STLC-Thms as ST
import StateOfTheArt.Closure-Thms as TT
\end{code}}

Before we can precisely define
bisimulation, we need a definition of similarity between source
and target terms of closure conversion.

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

\begin{definition}
  Given a source language term \AS{M} and a target language term \AS{M†},
  the similarity relation \AS{M \ti M†} is defined inductively as
  follows:

  \begin{itemize}
  \item
    (Variable) For any given variable (proof of context membership) \AS{x}, we have
    \AS{S.` x \ti T.` x}.

  \item
    (Application) If \AS{M \ti M†} and \AS{N \ti N†},
    then \AS{M S.· N \ti M† T.· N†}.

  \item
    (Abstraction) If \AS{N \ti T.subst (T.exts E) N†},
    then \AS{λ N \ti ⟪ N† , E ⟫}.
  \end{itemize}
\end{definition}

We unpack the definition here. Recall that in our definition of
closure conversion, source and target languages share the same (meta)
type of (object) types, contexts, and variables (proofs of context
membership). In fact, similarity is only defined for source and target
terms of the same type in the same context (this is explicit in the Agda
definition). 

Therefore, similarity of (syntactic) variables can be defined in terms
of identity of proofs of membership.

Similarity of applications is defined by congruence.

Finally, the non-trivial case of abstractions. What are the necessary
conditions for \AS{λ N \ti ⟪ N† , E ⟫}, where \AS{λ N} and 
\AS{⟪ N† , E ⟫} are defined in context \AS{Γ}? Clearly, we cannot require
that \AS{N \ti N†}, as the context \AS{Δ} in which the closure body is
defined is existentially quantified. However, recall that the closure environment
\AS{E} is defined as a substitution from \AS{Δ} to \AS{Γ}. Applying
this substitution to the closure body (\AS{T.subst (T.exts E) N†})
results in a term in \AS{Γ} which can be in a similarity relation with
\AS{N}, and this is precisely what we require in the definition.

(Note: the \AS{exts} accounts for the fact that the closure body is
defined in the context \AS{Δ} extended by the variable bound by the
abstraction, similarly to the lambda body.)

It is natural to ask what the relationship between a closure
conversion function and the similarity relation. Is the similarity
relation as graph relation of a closure conversion function? It is
not. Recall that closure conversion can be implemented by any function
which takes source terms to target terms and preserves the type and
context. But an implementation has freedom in how it deals with
closure environments; the meta language type of closures only requires
that the environment is \textit{some} substitution from the closure
body context \AS{Δ} to the outer context \AS{Γ}.

For example, the closure conversion transformation we described in
Chapter ??? had the property that closure environments were minimal:
they only contained parts of context actually used by the closure
body. In contrast, the simplest possible closure conversion could use
identity environments:

\begin{code}
convert : ∀ {Γ σ}
  → S.Lam σ Γ
  → T.Lam σ Γ
convert (S.V x) = T.V x
convert (S.A M N) = T.A (convert M) (convert N)
convert (S.L N) = T.L (convert N) T.id-subst
\end{code}

We require that for every well-behaved closure conversion function \AS{c}, any
source term \AS{N} is similar to the result of its translation with
\AS{c}: \AS{N \ti c N}. This is indeed the case for the \AS{convert}
function. The proof is by straightforward induction; in the
abstraction case, we need to argue that applying an identity substitution
leaves the term unchanged.

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

A similar result could be obtained for the closure conversion
algorithm which minimises environments from Chapter ???, but the proof
would be longer.

However, given \AS{M \ti M†}, it is not
necessarily the case that \AS{M† ≡ c M} for any \textit{fixed}
function \AS{c}; instead, \AS{M† ≡ c M} holds for \textit{some}
function \AS{c}. Therefore, the similarity relation is not the graph
relation of any \textit{specific} conversion \AS{c}.

Having defined the notion of similarity, we are in a position to
define bisimulation.

\section{Bisimulation}

Bisimulation is a two-way property which is defined in terms of a
simpler one-way property of simulation.

\begin{definition}{}
Given two languages \AS{S} and \AS{T} and a similarity relation
\AS{\_\textasciitilde\_}
between them, \AS{S} and \AS{T} are in \textbf{simulation} if and only
if the following holds:
Given source language terms \AS{M} and \AS{N}, and a target language
term \AS{M†} such that \AS{M} reduces to \AS{N} in a single step (\AS{M —→ N}) and
\AS{M} is similar to \AS{M†} (\AS{M \~ M†}), there exists a target
language term \AS{N†} such that \AS{M†} reduces to \AS{N†} in some
number of steps (\AS{M† —→* N†}) and \AS{N} is similar to \AS{N†} (\AS{N \~ N†}).
\end{definition}

\begin{definition}
Given two languages \AS{S} and \AS{T},  \AS{S} and \AS{T} are in a
\textbf{bisimulation} if and only if \AS{S} is in a simulation with \AS{T} and
\AS{T} is in a simulation with \AS{S}.
\end{definition}

The essence of simulation can be captured in a diagram.

TODO diagram here

TODO give names to the source and target langs

In fact, our source and target languages of closure conversion have a
stronger property: \textit{lock-step} bisimulation, which is defined
in terms of \textit{lock-step} simulations. A lock-step simulation is
one where for each reduction step of the source term, there is exactly
one corresponding reduction step in the target language. We illustrate
this at another diagram:

TODO another diagram

Before we can prove that λ and λT are in simulation, we need three
lemmas:

\begin{enumerate}
\item
  Values commute with similarity. If \AS{M \ti M†} and \AS{M} is a
  value, then \AS{M†} is also a value.

\item
  Renaming commutes with similarity. If \AS{ρ} is a renaming from
  \AS{Γ} to \AS{Δ}, and \AS{M \ti M†} are similar terms in the context
  \AS{Γ}, then the results of renaming \AS{M} and \AS{M†} with \AS{ρ}
  are also similar: \AS{S.rename ρ M \ti T.rename ρ M†}.

\item
  Substitution commutes with similarity. Suppose \AS{ρ} and \AS{ρ†} are two
  substitutions which take variables \AS{x} in \AS{Γ} to terms in \AS{Δ},
  such that for all \AS{x} we have that \AS{lookup ρ x \ti lookup ρ†
    x}. Then given similar terms \AS{M \ti M†} in \AS{Γ}, the results
  of applying \AS{ρ} to \AS{M} and \AS{ρ†} to \AS{M†} are also
  similar: \AS{S.subst ρ M \ti T.subst ρ† M†}.
\end{enumerate}

The proof that values commute with similarity is straightforward.

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

Before we will be able to prove the lemmas about renaming and substitution, we need an interlude
where we discuss so-called fusion lemmas for the closure language λT.

TODO acknowledge PLFA here


\section{Fusion lemmas for the closure language λT}

\ExecuteMetaData[StateOfTheArt/Closure-Thms.tex]{rename-subst}

foo


\section{Back to \ti rename and \ti subst}

\begin{code}

~rename : ∀ {Γ Δ}
  → (ρ : Thinning Γ Δ)
    ----------------------------------------------------------
  → ∀ {σ} {M : S.Lam σ Γ} {M† : T.Lam σ Γ} → M ~ M† → S.rename ρ M ~ T.rename ρ M†
~rename ρ ~V = ~V
~rename ρ (~A ~M ~N) = ~A (~rename ρ ~M) (~rename ρ ~N)
~rename ρ (~L {N = N} {N†} {E} ~N) with ~rename (T.ext ρ) ~N
... | ~ρN rewrite TT.lemma-~ren-L ρ E N† = ~L ~ρN

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
