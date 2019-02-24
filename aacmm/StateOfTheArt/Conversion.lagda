\begin{code}

module StateOfTheArt.Conversion where

open import Data.List using (List; []; _∷_)
import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl; trans; cong; sym; cong₂)
-- open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import indexed
open import var hiding (_<$>_ ; get)
open import environment as E hiding (_>>_ ; extend)

open import StateOfTheArt.Types
import StateOfTheArt.STLC as S
open S using (_/_)
import StateOfTheArt.Closure as T

convert : ∀ {Γ σ}
  → S.Lam σ Γ
  → T.Lam σ Γ
convert (S.V x) = T.V x
convert (S.A M N) = T.A (convert M) (convert N)
convert (S.L N) = T.L (convert N) T.id-subst
