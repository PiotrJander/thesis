open import Data.List using (List)

module StateOfTheArt.Types where

infixr 3 _⇒_
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type
  
Context : Set
Context = List Type
