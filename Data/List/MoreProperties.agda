module Data.List.MoreProperties where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Maybe using (Maybe; nothing; just) renaming (map to mmap)
open import Data.Nat
open import Data.Nat.Properties
open import Data.List
open import Data.List.Properties
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; cong-app; subst)
open import Data.MoreList

private
 variable
  ℓ : Level
  A B C : Set ℓ

nth-++ˡ : ∀ (xs ys : List A) (i : ℕ)
   → i < length xs
   → (xs ++ ys) ! i ≡ xs ! i
nth-++ˡ (x ∷ xs) ys zero i<xs = refl
nth-++ˡ (x ∷ xs) ys (suc i) i<xs = nth-++ˡ xs ys i (≤-pred i<xs)

nth-++ʳ : ∀ (xs ys : List A) (i : ℕ)
   → length xs < i
   → (xs ++ ys) ! i ≡ ys ! (i ∸ length xs)
nth-++ʳ [] ys (suc i) xs<i = refl
nth-++ʳ (x ∷ xs) ys (suc i) xs<i = nth-++ʳ xs ys i (≤-pred xs<i)

nth-length-++ : ∀ (xs ys : List A) (y : A)
   → (xs ++ (y ∷ ys)) ! (length xs) ≡ just y
nth-length-++ [] ys y = refl
nth-length-++ (x ∷ xs) ys y = nth-length-++ xs ys y

nth-length-+-++ : ∀ (xs ys : List A) (n : ℕ)
   → (xs ++ ys) ! (length xs + n) ≡ ys ! n
nth-length-+-++ [] ys n = refl
nth-length-+-++ (x ∷ xs) ys n = nth-length-+-++ xs ys n

nth-map : (f : A → B) (xs : List A) (i : ℕ)
  → i < length xs
  → (map f xs) ! i ≡ mmap f (xs ! i)
nth-map f (x ∷ xs) zero i<xs = refl
nth-map f (x ∷ xs) (suc i) i<xs = nth-map f xs i (≤-pred i<xs)
