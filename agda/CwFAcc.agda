{-# OPTIONS --cubical #-}

import Acc
open import Data.Empty
open import Data.Unit
open import Data.Product.Base using (∃-syntax)
open import Cubical.Foundations.Prelude hiding (lift)

module CwFAcc
  (Level : Set)
  (_<_ : Level → Level → Set)
  (trans< : ∀ {i j k} → i < j → j < k → i < k)
  (open Acc Level _<_)
  (wf : ∀ k → Acc k) where

data U' k (U< : ∀ {j} → j < k → Set) : Set
el' : ∀ k (U< : ∀ {j} → j < k → Set) → U' k U< → Set

data U' k U< where
  Û : ∀ j → j < k → U' k U<
  ⊥̂ : U' k U<
  Π̂ : ∀ (A : U' k U<) → (el' k U< A → U' k U<) → U' k U<
  L̂ : Level → U' k U<

el' _ U< (Û j j<k) = U< j<k
el' _ U< ⊥̂  = ⊥
el' _ U< (Π̂ A B) = ∀ (a : el' _ U< A) → el' _ U< (B a)
el' _ U< (L̂ ℓ) = ∃[ k ] k < ℓ

U<  : ∀ {k} → Acc k → ∀ {j} → j < k → Set
el< : ∀ {k} (p : Acc k) {j} (j<k : j < k) → U< p j<k → Set

U<  (acc< f) {j} j<k = U'  j (U< (f j<k))
el< (acc< f) {j} j<k = el' j (U< (f j<k))

U : ∀ k → Acc k → Set
U k acck = U' k (U< acck)

el : ∀ k (acck : Acc k) → U k acck → Set
el k acck = el' k (U< acck)

lift : ∀ {j k} (accj : Acc j) (acck : Acc k) → j < k → U j accj → U k acck
el≡  : ∀ {j k} (accj : Acc j) (acck : Acc k) (j<k : j < k) (u : U j accj) → el j accj u ≡ el k acck (lift accj acck j<k u)

lift _ _ j<k (Û i i<j) = Û i (trans< i<j j<k)
lift _ _ _ ⊥̂ = ⊥̂ 
lift accj acck j<k (Π̂ A B) = Π̂ (lift accj acck j<k A) (λ a → lift accj acck j<k (B (transport (sym (el≡ accj acck j<k A)) a)))
lift _ _ _ (L̂ ℓ) = L̂ ℓ

{-
Type
———— Boundary (wanted) —————————————————————————————————————
ii = i0 ⊢ U< accj i<j
ii = i1 ⊢ U< acck (trans< i<j j<k)
-}
el≡ accj acck j<k (Û i i<j) ii = {!   !}
el≡ _ _ _ ⊥̂ = refl
el≡ accj acck j<k (Π̂ A B) i = (a : el≡ accj acck j<k A i) → el≡ accj acck j<k (B (transp (λ j → el≡ accj acck j<k A (i ∧ ~ j)) (~ i) a)) i
el≡ _ _ _ (L̂ _) = refl