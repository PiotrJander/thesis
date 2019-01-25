\begin{code}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Nullary using (¬_)
open import Data.List using (List ; _∷_ ; [])
open import Data.List.Relation.Sublist.Propositional using (_⊆_ ; []⊆_ ; base ; keep ; skip)
open import Data.List.Relation.Sublist.Propositional.Properties using (⊆-refl ; ⊆-trans)
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

import PCF as S
import Closure as T
open S using (_,_ ; ∅ ; Z ; S_)
open T using (z ; s_ ; ⟪_,_⟫)
open import SubContext

convert-type : S.Type → T.Type
convert-type S.`ℕ = T.`ℕ
convert-type (A S.⇒ B) = convert-type A T.⇒ convert-type B

convert-context : S.Context → T.Context
convert-context ∅ = []
convert-context (Γ , A) = convert-type A ∷ convert-context Γ

record _⊩_ (Γ : T.Context) (A : T.Type) : Set where
  constructor ∃[_]_∧_
  field
    Δ : T.Context
    Δ⊆Γ : Δ ⊆ Γ
    N : Δ T.⊢ A

Closure : S.Type → S.Context → Set
Closure A Γ = convert-context Γ ⊩ convert-type A

Var→⊆ : ∀ {Γ A} → Γ S.∋ A → convert-type A ∷ [] ⊆ convert-context Γ
Var→⊆ {Γ , _} Z = keep ([]⊆ convert-context Γ)
Var→⊆ (S x) = skip (Var→⊆ x)

record AdjustContext {A B Γ Δ} (Δ⊆ABΓ : Δ ⊆ A ∷ B ∷ Γ) : Set where
  constructor adjust
  field
    Δ₁ : T.Context
    Δ₁⊆Γ : Δ₁ ⊆ Γ
    Δ⊆ABΔ₁ : Δ ⊆ A ∷ B ∷ Δ₁

adjust-context : ∀ {Γ Δ A B} → (Δ⊆ABΓ : Δ ⊆ A ∷ B ∷ Γ) → AdjustContext Δ⊆ABΓ
adjust-context (skip (skip {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (skip (skip ⊆-refl))
adjust-context (skip (keep {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (skip (keep ⊆-refl))
adjust-context (keep (skip {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (keep (skip ⊆-refl))
adjust-context (keep (keep {xs = Δ₁} Δ⊆Γ)) = adjust Δ₁ Δ⊆Γ (keep (keep ⊆-refl))

make-env : (Δ : T.Context) → T.Env Δ Δ
make-env [] = T.[]
make-env (A ∷ Δ) =  (T.` z) T.∷ T.rename-env T.weaken (make-env Δ)

cc : ∀ {Γ A} → Γ S.⊢ A → Closure A Γ
cc {A = A} (S.` x) = ∃[ convert-type A ∷ [] ] Var→⊆ x ∧ (T.` z)
cc (S.ƛ N) with cc N
cc (S.ƛ N) | ∃[ Δ ] Δ⊆Γ ∧ N₁ with adjust-context Δ⊆Γ
cc (S.ƛ N) | ∃[ Δ ] Δ⊆Γ ∧ N₁ | adjust Δ₁ Δ₁⊆Γ Δ⊆ABΔ₁ = ∃[ Δ₁ ] Δ₁⊆Γ ∧ ⟪ T.rename (⊆→ρ Δ⊆ABΔ₁) N₁ , make-env Δ₁ ⟫
cc (L S.· M) with cc L | cc M
cc (L S.· M) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ with merge Δ⊆Γ Δ₁⊆Γ
cc (L S.· M) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.rename (⊆→ρ Δ⊆Γ₁) L′ T.· T.rename (⊆→ρ Δ₁⊆Γ₁) M′)
cc {Γ} S.`zero = ∃[ [] ] []⊆ convert-context Γ ∧ T.`zero
cc (S.`suc N) with cc N
cc (S.`suc N) | ∃[ Δ ] Δ⊆Γ ∧ N₁ = ∃[ Δ ] Δ⊆Γ ∧ (T.`suc N₁)
cc (S.case L M N) with cc L | cc M | cc N
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ Δ₂ ] skip Δ₂⊆Γ ∧ N′ with merge₃ Δ⊆Γ Δ₁⊆Γ Δ₂⊆Γ
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ Δ₂ ] skip Δ₂⊆Γ ∧ N′ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ Δ₂⊆Γ₁
  = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.case (T.rename (⊆→ρ Δ⊆Γ₁) L′) (T.rename (⊆→ρ Δ₁⊆Γ₁) M′) (T.rename (⊆→ρ (skip Δ₂⊆Γ₁)) N′))
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ .(T.`ℕ ∷ _) ] keep Δ₂⊆Γ ∧ N′ with merge₃ Δ⊆Γ Δ₁⊆Γ Δ₂⊆Γ
cc (S.case L M N) | ∃[ Δ ] Δ⊆Γ ∧ L′ | ∃[ Δ₁ ] Δ₁⊆Γ ∧ M′ | ∃[ .(T.`ℕ ∷ _) ] keep Δ₂⊆Γ ∧ N′ | subContextSum Γ₁ Γ₁⊆Γ Δ⊆Γ₁ Δ₁⊆Γ₁ Δ₂⊆Γ₁
  = ∃[ Γ₁ ] Γ₁⊆Γ ∧ (T.case (T.rename (⊆→ρ Δ⊆Γ₁) L′) (T.rename (⊆→ρ Δ₁⊆Γ₁) M′) (T.rename (⊆→ρ (keep Δ₂⊆Γ₁)) N′))

\end{code}
