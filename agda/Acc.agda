{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude

module Acc
  (Level : Set)
  (_<_ : Level → Level → Set) where

record Acc (k : Level) : Set where
  pattern
  inductive
  constructor acc<
  field acc : ∀ {j} → j < k → Acc j
open Acc

accProp : ∀ {k} (p q : Acc k) → p ≡ q
accProp {k} (acc< f) (acc< g) = congS acc< (λ i j<k → accProp (f j<k) (g j<k) i)