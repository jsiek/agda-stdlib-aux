module Data.MoreList where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.List.Properties
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app; subst)

private
 variable
  ℓ : Level
  A : Set ℓ

_!_ : (xs : List A) → (i : ℕ) → Maybe A
[] ! i = nothing
(x ∷ xs) ! zero = just x
(x ∷ xs) ! (suc i) = xs ! i
