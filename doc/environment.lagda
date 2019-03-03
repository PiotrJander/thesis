\begin{code}
module environment {I : Set} where

open import Data.Nat.Base as ℕ
import Data.List.Base as L
open L hiding (lookup ; [_] ; map)
open import Data.Sum as S hiding (map)
open import Function
open import Relation.Binary.PropositionalEquality as PEq hiding ([_])
open PEq using (_≡_; refl)

open import indexed
open import var hiding (_<$>_)

infix 3 _─Env

record _─Env (Γ : List I) (𝓥 : I ─Scoped) (Δ : List I) : Set where
  constructor pack
  field lookup : ∀ {i} → Var i Γ → 𝓥 i Δ

open _─Env public


Thinning : List I → List I → Set
Thinning Γ Δ = (Γ ─Env) Var Δ


ε : ∀ {𝓥 n} → ([] ─Env) 𝓥 n
lookup ε ()

_<$>_ : {𝓥 𝓦 : I ─Scoped} {Γ Δ Θ : List I} → ({i : I} → 𝓥 i Δ → 𝓦 i Θ) → (Γ ─Env) 𝓥 Δ → (Γ ─Env) 𝓦 Θ
lookup (f <$> ρ) k = f (lookup ρ k)

infix 4 _≡ᴱ_
record _≡ᴱ_ {𝓥 : I ─Scoped} {Γ Δ : List I} (ρ₁ ρ₂ : (Γ ─Env) 𝓥 Δ) : Set where
  field eq : {i : I} (x : Var i Γ) → lookup ρ₁ x ≡ lookup ρ₂ x
open _≡ᴱ_ public

postulate
  env-extensionality : {𝓥 : I ─Scoped} {Γ Δ : List I} {ρ₁ ρ₂ : (Γ ─Env) 𝓥 Δ}
    → ρ₁ ≡ᴱ ρ₂
      -----------------------
    → ρ₁ ≡ ρ₂

≡ᴱ-refl : {𝓥 : I ─Scoped} {Γ Δ : List I} {ρ : (Γ ─Env) 𝓥 Δ}
  → ρ ≡ᴱ ρ
eq ≡ᴱ-refl x = refl

≡ᴱ-trans : {𝓥 : I ─Scoped} {Γ Δ : List I} {ρ₁ ρ₂ ρ₃ : (Γ ─Env) 𝓥 Δ}
    → ρ₁ ≡ᴱ ρ₂
    → ρ₂ ≡ᴱ ρ₃
      -----
    → ρ₁ ≡ᴱ ρ₃
eq (≡ᴱ-trans  ρ₁≡ᴱρ₂ ρ₂≡ᴱρ₃) x rewrite eq ρ₁≡ᴱρ₂ x | eq ρ₂≡ᴱρ₃ x = refl

module ≡ᴱ-Reasoning {𝓥 : I ─Scoped} {Γ Δ : List I} where

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

<$>-distr : {𝓥 𝓦 𝓧 : I ─Scoped} {Γ Δ Θ₁ Θ₂ : List I}
  (f : {i : I} → 𝓥 i Δ → 𝓦 i Θ₁)
  (g : {i : I} → 𝓦 i Θ₁ → 𝓧 i Θ₂)
  (ρ : (Γ ─Env) 𝓥 Δ)
    ---------------------------
  → _<$>_ {𝓦 = 𝓧} g (_<$>_ {𝓦 = 𝓦} f ρ) ≡ᴱ _<$>_ {𝓦 = 𝓧} (g ∘ f) ρ
eq (<$>-distr f g ρ) x = refl

<$>-fun : {𝓥 𝓦 : I ─Scoped} {Γ Δ Θ : List I}
  → {f : {i : I} → 𝓥 i Δ → 𝓦 i Θ}
  → {g : {i : I} → 𝓥 i Δ → 𝓦 i Θ}
  → (f≡g : {i : I} → (v : 𝓥 i Δ) → f v ≡ g v)
  → (ρ : (Γ ─Env) 𝓥 Δ)
    -------------
  → _<$>_ {𝓦 = 𝓦} f ρ ≡ᴱ _<$>_ {𝓦 = 𝓦} g ρ
eq (<$>-fun f≡g ρ) x rewrite f≡g (lookup ρ x) = refl

data Split (i : I) Γ Δ : Var i (Γ ++ Δ) → Set where
  inj₁ : (k : Var i Γ) → Split i Γ Δ (injectˡ Δ k)
  inj₂ : (k : Var i Δ) → Split i Γ Δ (injectʳ Γ k)

split : ∀ {Δ} {i : I} Γ (k : Var i (Γ ++ Δ)) → Split i Γ Δ k
split []      k     = inj₂ k
split (σ ∷ Γ) z     = inj₁ z
split (σ ∷ Γ) (s k) with split Γ k
... | inj₁ k₁ = inj₁ (s k₁)
... | inj₂ k₂ = inj₂ k₂

split-injectˡ :  (Γ : List I) {Δ : List I} {σ : I} (v : Var σ Δ) → split Δ (injectˡ Γ v) ≡ inj₁ v
split-injectˡ Γ z                               = refl
split-injectˡ Γ (s v) rewrite split-injectˡ Γ v = refl

split-injectʳ : {Γ : List I} (Δ : List I) {σ : I} (v : Var σ Γ) → split Δ (injectʳ Δ v) ≡ inj₂ v
split-injectʳ []      v                           = refl
split-injectʳ (_ ∷ Δ) v rewrite split-injectʳ Δ v = refl

_>>_ : ∀ {𝓥 Γ Δ Θ} → (Γ ─Env) 𝓥 Θ → (Δ ─Env) 𝓥 Θ → (Γ ++ Δ ─Env) 𝓥 Θ
lookup (_>>_ {Γ = Γ} ρ₁ ρ₂) k with split Γ k
... | inj₁ k₁ = lookup ρ₁ k₁
... | inj₂ k₂ = lookup ρ₂ k₂

injectˡ->> : ∀ {𝓥 Γ Δ Θ i} (ρ₁ : (Γ ─Env) 𝓥 Θ) (ρ₂ : (Δ ─Env) 𝓥 Θ) (v : Var i Γ) →
             lookup (ρ₁ >> ρ₂) (injectˡ Δ v) ≡ lookup ρ₁ v
injectˡ->> {Δ = Δ} ρ₁ ρ₂ v rewrite split-injectˡ Δ v = refl

injectʳ->> : ∀ {𝓥 Γ Δ Θ i} (ρ₁ : (Γ ─Env) 𝓥 Θ) (ρ₂ : (Δ ─Env) 𝓥 Θ) (v : Var i Δ) →
             lookup (ρ₁ >> ρ₂) (injectʳ Γ v) ≡ lookup ρ₂ v
injectʳ->> {Γ = Γ} ρ₁ ρ₂ v rewrite split-injectʳ Γ v = refl

infixl 10 _∙_
_∙_ : ∀ {𝓥 Γ Δ σ} → (Γ ─Env) 𝓥 Δ → 𝓥 σ Δ → (σ ∷ Γ ─Env) 𝓥 Δ
lookup (ρ ∙ v) z    = v
lookup (ρ ∙ v) (s k) = lookup ρ k

select : ∀ {Γ Δ Θ 𝓥} → Thinning Γ Δ → (Δ ─Env) 𝓥 Θ → (Γ ─Env) 𝓥 Θ
lookup (select ren ρ) k = lookup ρ (lookup ren k)

extend : ∀ {Γ σ} → Thinning Γ (σ ∷ Γ)
lookup extend v = s v

step : ∀ {Γ Δ σ} → Thinning Γ Δ → Thinning Γ (σ ∷ Δ)
step ρ = s <$> ρ

-- Like the flipped version of _>>_ but it computes. Which is convenient when
-- dealing with concrete Γs (cf. βred)
_<+>_ : ∀ {Γ 𝓥 Δ Θ} → (Δ ─Env) 𝓥 Θ → (Γ ─Env) 𝓥 Θ → (Γ ++ Δ ─Env) 𝓥 Θ
_<+>_ {[]}    ρ₁ ρ₂ = ρ₁
_<+>_ {_ ∷ Γ} ρ₁ ρ₂ = (ρ₁ <+> select extend ρ₂) ∙ lookup ρ₂ z

injectˡ-<+> : ∀ Δ {𝓥 Γ Θ i} (ρ₁ : (Δ ─Env) 𝓥 Θ) (ρ₂ : (Γ ─Env) 𝓥 Θ) (v : Var i Γ) →
              lookup (ρ₁ <+> ρ₂) (injectˡ Δ v) ≡ lookup ρ₂ v
injectˡ-<+> Δ ρ₁ ρ₂ z     = refl
injectˡ-<+> Δ ρ₁ ρ₂ (s v) = injectˡ-<+> Δ ρ₁ (select extend ρ₂) v

injectʳ-<+> : ∀ Γ {𝓥 Δ Θ i} (ρ₁ : (Δ ─Env) 𝓥 Θ) (ρ₂ : (Γ ─Env) 𝓥 Θ) (v : Var i Δ) →
              lookup (ρ₁ <+> ρ₂) (injectʳ Γ v) ≡ lookup ρ₁ v
injectʳ-<+> []      ρ₁ ρ₂ v = refl
injectʳ-<+> (x ∷ Γ) ρ₁ ρ₂ v = injectʳ-<+> Γ ρ₁ (select extend ρ₂) v


□ : (List I → Set) → (List I → Set)
(□ T) Γ = [ Thinning Γ ⟶ T ]

extract    : {T : List I → Set} → [ □ T ⟶ T        ]
duplicate  : {T : List I → Set} → [ □ T ⟶ □ (□ T)  ]

extract t = t (pack id)
duplicate t ρ σ = t (select ρ σ)

join : {T : List I → Set} → [ □ (□ T) ⟶ □ T ]
join = extract

Thinnable : (List I → Set) → Set
Thinnable T = [ T ⟶ □ T ]


th^Var : {i : I} → Thinnable (Var i)
th^Var v ρ = lookup ρ v

th^Env : ∀ {Γ 𝓥} → ({i : I} → Thinnable (𝓥 i)) → Thinnable ((Γ ─Env) 𝓥)
lookup (th^Env th^𝓥 ρ ren) k = th^𝓥 (lookup ρ k) ren

th^□ : {T : List I → Set} → Thinnable (□ T)
th^□ = duplicate

Kripke :  (𝓥 𝓒 : I ─Scoped) → (List I → I ─Scoped)
Kripke 𝓥 𝓒 []  i = 𝓒 i
Kripke 𝓥 𝓒 Γ   i = □ ((Γ ─Env) 𝓥 ⟶ 𝓒 i)

module _ {𝓥 𝓒 : I ─Scoped} where

  _$$_ : ∀ {Γ i} → [ Kripke 𝓥 𝓒 Γ i ⟶ (Γ ─Env) 𝓥 ⟶ 𝓒 i ]
  _$$_ {[]}    f ts = f
  _$$_ {_ ∷ _} f ts = extract f ts

  th^Kr : (Γ : List I) → ({i : I} → Thinnable (𝓒 i)) →
          {i : I} → Thinnable (Kripke 𝓥 𝓒 Γ i)
  th^Kr []       th^𝓒 = th^𝓒
  th^Kr (_ ∷ _)  th^𝓒 = th^□

open import Category.Applicative

module _ {𝓥 : I ─Scoped} {A : Set → Set} (app : RawApplicative A) where

 private module A = RawApplicative app
 open A

 traverse : {Γ Δ : List I} → (Γ ─Env) (λ i Γ → A (𝓥 i Γ)) Δ → A ((Γ ─Env) 𝓥 Δ)
 traverse = go _ where

   go : ∀ Γ {Δ} → (Γ ─Env) (λ i Γ → A (𝓥 i Γ)) Δ → A ((Γ ─Env) 𝓥 Δ)
   go []       ρ = pure ε
   go (σ ∷ Γ)  ρ = flip _∙_ A.<$> lookup ρ z ⊛ go Γ (select extend ρ)
\end{coe}
