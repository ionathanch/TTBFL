{-# OPTIONS --cubical #-}

import Acc
open import Data.Empty
open import Data.Unit
open import Data.Product.Base using (∃-syntax)
open import Cubical.Foundations.Prelude hiding (lift)

module CwF
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

U : Level → Set
U k = U' k (U< (wf k))

el : ∀ k → U k → Set
el k = el' k (U< (wf k))

{------------------------------------------------
  Some important properties:
  * Universes irrelevant in Acc
  * Universes can be lifted to higher levels
  * Interpretations of lifted universes unchanged
------------------------------------------------}

U≡ : ∀ {j k} (acck : Acc k) (j<k : j < k) → U j ≡ U< acck j<k
U≡ {j} {k} acck j<k i
  with acc< f ← wf k
  with acc< g ← acck
  = U' j (U< (accProp (wf j) (g j<k) i))

lift : ∀ {j k} → j < k → U j → U k
el≡  : ∀ {j k} (j<k : j < k) (u : U j) → el j u ≡ el k (lift j<k u)

lift j<k (Û i i<j) = Û i (trans< i<j j<k)
lift _ ⊥̂ = ⊥̂ 
lift j<k (Π̂ A B) = Π̂ (lift j<k A) (λ a → lift j<k (B (transport (sym (el≡ j<k A)) a)))
lift _ (L̂ ℓ) = L̂ ℓ

el≡ j<k (Û i i<j) = refl
el≡ _ ⊥̂ = refl
el≡ j<k (Π̂ A B) i = (a : el≡ j<k A i) → el≡ j<k (B (transp (λ j → el≡ j<k A (i ∧ ~ j)) (~ i) a)) i
el≡ _ (L̂ _) = refl

{---------------------------------
  CwF essentials:
  contexts, levels, types, terms
---------------------------------}

data Ctxt : Set
em : Ctxt → Set

Lvl : Ctxt → Set
Lvl Γ = em Γ → Level

Lt : ∀ {Γ} → Lvl Γ → Lvl Γ → Set
Lt {Γ} j k = (γ : em Γ) → j γ < k γ

Ty : ∀ Γ → Lvl Γ → Set
Ty Γ ℓ = (γ : em Γ) → U (ℓ γ)

Tm : ∀ Γ ℓ → Ty Γ ℓ → Set
Tm Γ ℓ A = (γ : em Γ) → el (ℓ γ) (A γ)

data Ctxt where
  nil : Ctxt
  cons : ∀ (Γ : Ctxt) (ℓ : Lvl Γ) → Ty Γ ℓ → Ctxt

em nil = ⊤
em (cons Γ ℓ A) = Σ[ γ ∈ em Γ ] el (ℓ γ) (A γ)

liftTy : ∀ {Γ} {j k : Lvl Γ} → Lt j k → Ty Γ j → Ty Γ k
liftTy j<k A γ = lift (j<k γ) (A γ)

liftTm : ∀ {Γ} {j k : Lvl Γ} (j<k : Lt j k) (A : Ty Γ j) → Tm Γ j A ≡ Tm Γ k (liftTy j<k A)
liftTm {Γ} j<k A i = (γ : em Γ) → el≡ (j<k γ) (A γ) i

{-----------------------------------------
  Substitutions, with special syntax
  for weakening and single substitutions
-----------------------------------------}

_⇒_ : Ctxt → Ctxt → Set
Γ ⇒ Δ = em Γ → em Δ

_[_]ᴸ : ∀ {Γ Δ} → Lvl Δ → Γ ⇒ Δ → Lvl Γ
(ℓ [ σ ]ᴸ) γ = ℓ (σ γ)

_[_]ᵀ : ∀ {Γ Δ} {ℓ : Lvl Δ} → Ty Δ ℓ → (σ : Γ ⇒ Δ) → Ty Γ (ℓ [ σ ]ᴸ)
(A [ σ ]ᵀ) γ = A (σ γ)

_[_]ᵗ : ∀ {Γ Δ} {ℓ : Lvl Δ} {A : Ty Δ ℓ} → Tm Δ ℓ A → (σ : Γ ⇒ Δ) → Tm Γ (ℓ [ σ ]ᴸ) (A [ σ ]ᵀ)
(a [ σ ]ᵗ) γ = a (σ γ)

wkᴸ : ∀ {Γ k} (A : Ty Γ k) → Lvl Γ → Lvl (cons Γ k A)
wkᴸ A ℓ (γ , _) = ℓ γ

wkᵀ : ∀ {Γ k} (A : Ty Γ k) {ℓ : Lvl Γ} → Ty Γ ℓ → Ty (cons Γ k A) (wkᴸ A ℓ)
wkᵀ A B (γ , _) = B γ

wkᵗ : ∀ {Γ k} (A : Ty Γ k) {ℓ : Lvl Γ} {B : Ty Γ ℓ} → Tm Γ ℓ B → Tm (cons Γ k A) (wkᴸ A ℓ) (wkᵀ A B)
wkᵗ A a (γ , _) = a γ

var : ∀ {Γ k} (A : Ty Γ k) → Tm (cons Γ k A) (wkᴸ A k) (wkᵀ A A)
var A (_ , a) = a

substᴸ : ∀ {Γ k} (A : Ty Γ k) → Lvl (cons Γ k A) → (a : Tm Γ k A) → Lvl Γ
substᴸ A ℓ a γ = ℓ (γ , a γ)
syntax substᴸ A ℓ a = ℓ ⟨ a ∈ A ⟩ᴸ

substᵀ : ∀ {Γ k} (A : Ty Γ k) {ℓ : Lvl (cons Γ k A)} → Ty (cons Γ k A) ℓ → (a : Tm Γ k A) → Ty Γ (ℓ ⟨ a ∈ A ⟩ᴸ)
substᵀ A B a γ = B (γ , a γ)
syntax substᵀ A B a = B ⟨ a ∈ A ⟩ᵀ

substᵗ : ∀ {Γ k} (A : Ty Γ k) {ℓ : Lvl (cons Γ k A)} (B : Ty (cons Γ k A) ℓ) → Tm (cons Γ k A) ℓ B → (a : Tm Γ k A) → Tm Γ (ℓ ⟨ a ∈ A ⟩ᴸ) (B ⟨ a ∈ A ⟩ᵀ)
substᵗ A B b a γ = b (γ , a γ)
syntax substᵗ A B b a = b ∈ B ⟨ a ∈ A ⟩ᵗ

{--------------
  Level rules
--------------}

Level< : ∀ {Γ ℓ} → (k : Lvl Γ) → Ty Γ ℓ
Level< k γ = L̂ (k γ)

unlvl : ∀ {Γ k ℓ} → Tm Γ ℓ (Level< k) → Σ[ j ∈ Lvl Γ ] Lt j k
unlvl {Γ} {k} {ℓ} j = (λ γ → let (j' , _) = j γ in j') , (λ γ → let (_ , j<k) = j γ in j<k)

unlvl₁ : ∀ {Γ k ℓ} → Tm Γ ℓ (Level< k) → Lvl Γ
unlvl₁ {ℓ = ℓ} j = unlvl {ℓ = ℓ} j .fst

unlvl₂ : ∀ {Γ k ℓ} (j : Tm Γ ℓ (Level< k)) → Lt (unlvl₁ {ℓ = ℓ} j) k
unlvl₂ {ℓ = ℓ} j = unlvl {ℓ = ℓ} j .snd

-- rule Level< (type former)
Level<' : ∀ {Γ k ℓ} → (j : Tm Γ ℓ (Level< k)) → Ty Γ ℓ
Level<' {k = k} {ℓ = ℓ} j = Level< (unlvl₁ {ℓ = k} j)

lvl : ∀ {Γ k ℓ} (j : Lvl Γ) → Lt j k → Tm Γ ℓ (Level< k)
lvl j j<k γ = j γ , j<k γ

-- rule Lvl (constructor)
lvl' : ∀ {Γ j k ℓ} → j < k → Tm Γ ℓ (Level< (λ _ → k))
lvl' {j = j} {ℓ = ℓ} j<k = lvl {ℓ = ℓ} (λ _ → j) (λ _ → j<k)

-- rule Trans
trans : ∀ {Γ ℓ k' j'} (k : Tm Γ k' (Level< ℓ)) (j : Tm Γ j' (Level< (unlvl₁ {ℓ = k'} k))) → Tm Γ k' (Level< ℓ)
trans {Γ} {ℓ} k j γ = unlvl₁ {ℓ = ℓ} j γ , trans< (unlvl₂ {ℓ = ℓ} j γ) (unlvl₂ {ℓ = ℓ} k γ)

trans≡ : ∀ {Γ ℓ k' j'} (k : Tm Γ k' (Level< ℓ)) (j : Tm Γ j' (Level< (unlvl₁ {ℓ = k'} k))) →
  unlvl₁ {ℓ = j'} j ≡ unlvl₁ {ℓ = k'} (trans {k' = k'} {j' = j'} k j)
trans≡ k j = refl

{-----------------
  Universe rules
-----------------}

-- rule Univ
Univ : ∀ {Γ k ℓ} → Tm Γ ℓ (Level< k) → Ty Γ k
Univ {ℓ = ℓ} j γ with (j' , j<k) ← j γ = Û j' j<k

russell : ∀ {Γ k ℓ} (j : Tm Γ ℓ (Level< k)) → Tm Γ k (Univ {ℓ = ℓ} j) ≡ Ty Γ (unlvl₁ {ℓ = ℓ} j)
russell {Γ} {k} {ℓ} j i = (γ : em Γ) → U≡ (wf (k γ)) (unlvl₂ {ℓ = ℓ} j γ) (~ i)

-- rule Cumul
cumul : ∀ {Γ k ℓ} (j : Tm Γ ℓ (Level< k)) → Ty Γ (unlvl₁ {ℓ = ℓ} j) → Ty Γ k
cumul {ℓ = ℓ} j A = liftTy (unlvl₂ {ℓ = ℓ} j) A

cumul≡ : ∀ {Γ k ℓ} (j : Tm Γ ℓ (Level< k)) (A : Ty Γ (unlvl₁ {ℓ = ℓ} j)) → Tm Γ _ A ≡ Tm Γ _ (cumul {ℓ = ℓ} j A)
cumul≡ {ℓ = ℓ} j A = liftTm (unlvl₂ {ℓ = ℓ} j) A

{--------------
  Empty rules
--------------}

Bot : ∀ {Γ k} → Ty Γ k
Bot γ = ⊥̂

absurd : ∀ {Γ k ℓ} (A : Ty Γ k) → Tm Γ ℓ Bot → Tm Γ k A
absurd A b γ with () ← b γ

{-----------------
  Function rules
-----------------}

Pi : ∀ {Γ} {k : Lvl Γ} → (A : Ty Γ k) → Ty (cons Γ k A) (wkᴸ A k) → Ty Γ k
Pi A B γ = Π̂ (A γ) (λ a → B (γ , a))

lam : ∀ {Γ k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ A k)) →
  Tm (cons Γ k A) (wkᴸ A k) B → Tm Γ k (Pi A B)
lam A B b γ a = b (γ , a)

app : ∀ {Γ k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ A k)) →
  Tm Γ k (Pi A B) → (a : Tm Γ k A) → Tm Γ k (B ⟨ a ∈ A ⟩ᵀ)
app A B b a γ = b γ (a γ)

β : ∀ {Γ k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ A k))
  (a : Tm Γ k A) (b : Tm (cons Γ k A) (wkᴸ A k) B) →
  app A B (lam A B b) a ≡ b ∈ B ⟨ a ∈ A ⟩ᵗ
β A B a b = refl