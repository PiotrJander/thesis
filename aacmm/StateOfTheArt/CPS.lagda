\begin{code}

module StateOfTheArt.CPS where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; subst ; sym)
open import Data.List using (List; []; _∷_; map)
open import Function using (_∘_)
open import var using (Var; _<$>_; _─Scoped; z; s; Injective; _<$>⁻¹_)
import environment as E
open import Data.Product hiding (map)
open E using (_─Env ; lookup; extend; step; _∙_; ε; Thinning)

import StateOfTheArt.ACMM as S
open S hiding (Type)

infixr 20 _⇒#_ #_
data Type : Set where
  α     : Type
  _⇒#_  : Type → Type → Type
  #_    : Type → Type

Context : Set
Context = List Type

infix 4 _⊢_
data _⊢_ (Γ : Context) : Type → Set where

  `_     : ∀ {σ} →
  
                Var σ Γ →
              --------------
                Γ ⊢ σ

  _·_     : ∀ {σ τ} →

                Γ ⊢ (σ ⇒# τ) →
                Γ ⊢ σ →
              --------------------------
                Γ ⊢ # τ

  ƛ       : ∀ {σ τ} →

                σ ∷ Γ ⊢ # τ →
              ----------------
                Γ ⊢ σ ⇒# τ

  _`>>=_ : ∀ {σ τ} →

                Γ ⊢ # σ →
                Γ ⊢ (σ ⇒# τ) →
              ------------------------------
                Γ ⊢ # τ

  `return : ∀ {σ} →

                Γ ⊢ σ →
              -------------
                Γ ⊢ # σ

Cont : S.Type → S.Type → S.Type
Cont r σ = (σ ⇒ r) ⇒ r

return : ∀ {Γ σ r} → Lam σ Γ → Lam (Cont r σ) Γ
return t = L (A (V z) (ren extend t))

bind : ∀ {Γ σ τ r}
     → Lam (Cont r σ) Γ
     → Lam (σ ⇒ Cont r τ) Γ
       ------------------
     → Lam (Cont r τ) Γ
bind m f = L (A (ren extend m) (L (A (A (ren (step extend) f) (V z)) (V (s z)))))

CPS[_]  : (r : S.Type) (σ : Type) → S.Type
#CPS[_] : (r : S.Type) (σ : Type) → S.Type

CPS[ r ] α         =  α
CPS[ r ] (σ ⇒# τ)  =  CPS[ r ] σ ⇒ #CPS[ r ] τ
CPS[ r ] (# σ)     =  #CPS[ r ] σ
#CPS[ r ] σ        =  Cont r (CPS[ r ] σ)

cps : ∀ {Γ σ r}
  → Γ ⊢ σ
    -----------------
  → Lam (CPS[ r ] σ) (map CPS[ r ] Γ)
cps {r = r} (` x) = V (CPS[ r ] <$> x)
cps (M · N) = A (cps M) (cps N)
cps (ƛ N) = L (cps N)
cps (M `>>= F) = bind (cps M) (cps F)
cps (`return M) = return (cps M)

⟦_⟧ : S.Type → Type
⟦ α ⟧      =    α
⟦ σ ⇒ τ ⟧  =  ⟦ σ ⟧ ⇒# ⟦ τ ⟧

#⟦_⟧ : S.Type → Type
#⟦ σ ⟧      =  # ⟦ σ ⟧ 

Value : S.Type ─Scoped
Value σ Γ = map ⟦_⟧ Γ ⊢ ⟦ σ ⟧

Computation : S.Type ─Scoped
Computation σ Γ = map ⟦_⟧ Γ ⊢ #⟦ σ ⟧

ext' : ∀ {Γ Δ} {τ : Type}
  → (∀ {σ} → Var σ Γ       → Var σ Δ)
  →  ∀ {σ} → Var σ (τ ∷ Γ) → Var σ (τ ∷ Δ)
ext' ρ z = z
ext' ρ (s x) = s (ρ x)

rename' : ∀ {Γ Δ}
  → (∀ {σ} → Var σ Γ → Var σ Δ)
  →  ∀ {σ} → Γ ⊢ σ   → Δ ⊢ σ
rename' ρ (` x) = ` ρ x
rename' ρ (M · N) = rename' ρ M · rename' ρ N
rename' ρ (ƛ N) = ƛ (rename' (ext' ρ) N)
rename' ρ (M `>>= F) = rename' ρ M `>>= rename' ρ F
rename' ρ (`return N) = `return (rename' ρ N)

ext : ∀ {Γ Δ} {σ : Type}
  → Thinning Γ Δ
    ------------------------
  → Thinning (σ ∷ Γ) (σ ∷ Δ)
ext ρ = s E.<$> ρ ∙ z

ext'' : ∀ {Γ Δ} {σ : S.Type}
  → Thinning Γ Δ
    ------------------------
  → Thinning (σ ∷ Γ) (σ ∷ Δ)
ext'' ρ = s E.<$> ρ ∙ z

rename : ∀ {Γ Δ}
  → Thinning Γ Δ
  → ∀ {σ} → Γ ⊢ σ → Δ ⊢ σ
rename ρ (` x) = ` lookup ρ x
rename ρ (M · N) = rename ρ M · rename ρ N
rename ρ (ƛ N) = ƛ (rename (ext ρ) N)
rename ρ (M `>>= F) = rename ρ M `>>= rename ρ F
rename ρ (`return N) = `return (rename ρ N)

extend‿cbv : ∀ {Γ Δ σ}
  → (Γ ─Env) Value Δ
  → Value σ (σ ∷ Δ)
    --------------------------
  → (σ ∷ Γ ─Env) Value (σ ∷ Δ)
lookup (extend‿cbv ρ N) z = N
lookup (extend‿cbv ρ N) (s x) = rename' s (lookup ρ x)

cbv : ∀ {Γ σ} → (Γ ─Env) Value Γ → Lam σ Γ → Computation σ Γ
cbv ρ (V x) = `return (lookup ρ x)
cbv ρ (A M N) = cbv ρ M `>>= ƛ (rename' s (cbv ρ N) `>>= ƛ ((` (s z)) · (` z)))
cbv ρ (L N) = `return (ƛ (cbv (extend‿cbv ρ (` z)) N)) 

map-inv : {A B : Set} {Γ : List A} {τ : B} (f : A → B) → Var τ (map f Γ) → ∃ λ σ → τ ≡ f σ
map-inv f = go _ refl where
  go : ∀ Γ {Δ τ} → map f Γ ≡ Δ → Var τ Δ → ∃ λ σ → τ ≡ f σ
  go [] refl ()
  go (_ ∷ Γ) refl z = -, refl
  go (_ ∷ Γ) refl (s x) = go Γ refl x

Th^map : {A B : Set} {Γ Δ : List A}
    → (f : A → B)
    → Injective f
    → Thinning Γ Δ
      --------------------
    → Thinning (map f Γ) (map f Δ)
lookup (Th^map f inj ρ) x =
  let (σ , eq) = map-inv f x
      v₁       = inj <$>⁻¹ (subst (λ x → Var x _) eq x)
      v₂       = lookup ρ v₁
      v₃       = f <$> v₂
  in  subst (λ x → Var x _) (sym eq) v₃ 

⟦⟧-inj : ∀ {σ τ} → ⟦ σ ⟧ ≡ ⟦ τ ⟧ → σ ≡ τ
⟦⟧-inj {α} {α} eq = refl
⟦⟧-inj {α} {τ ⇒ τ₁} ()
⟦⟧-inj {σ ⇒ σ₁} {α} ()
⟦⟧-inj {σ ⇒ σ₁} {τ ⇒ τ₁} eq = {!!}

CBV : Sem Value Computation
CBV = record
   { th^𝓥  = λ t ρ → rename (Th^map ⟦_⟧ (Injective.mkInjective ⟦⟧-inj) ρ) t
   ; ⟦V⟧    = `return
   ; ⟦A⟧    = λ m n → m `>>= ƛ (rename' s (n) `>>= ƛ ((` (s z)) · (` z)))
   ; ⟦L⟧    = λ σ b → `return (ƛ (b extend (` z)))
   }

cps-convert : ∀ {σ r} → Lam σ [] → Lam (CPS[ r ] #⟦ σ ⟧) []
cps-convert N = cps (cbv ε N)

cps-convert' : ∀ {σ r} → Lam σ [] → Lam (CPS[ r ] #⟦ σ ⟧) []
cps-convert' N = cps (Sem.sem CBV {Δ = []} ε N)

id : ∀ {σ} → Lam (σ ⇒ σ) []
id = L (V z)


\end{code}
