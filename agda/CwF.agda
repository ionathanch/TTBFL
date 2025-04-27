{-# OPTIONS --lossy-unification --cubical #-}

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
  with acc< g ← acck
  = U' j (U< (accProp (wf j) (g j<k) i))

lift : ∀ {j k} → j < k → U j → U k
el≡  : ∀ {j k} (j<k : j < k) (u : U j) → el j u ≡ el k (lift j<k u)

lift j<k (Û i i<j) = Û i (trans< i<j j<k)
lift _ ⊥̂ = ⊥̂ 
lift j<k (Π̂ A B) = Π̂ (lift j<k A) (λ a → lift j<k (B (transport (sym (el≡ j<k A)) a)))
lift _ (L̂ ℓ) = L̂ ℓ

el≡ {j} {k} j<k (Û i i<j) ii
  with acc< f ← wf j
  with acc< g ← wf k
  = U' i (U< (accProp (f i<j) (g (trans< i<j j<k)) ii))
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

variable Γ : Ctxt

wkᴸ : ∀ {k} (A : Ty Γ k) → Lvl Γ → Lvl (cons Γ k A)
wkᴸ A ℓ (γ , _) = ℓ γ

wkᵀ : ∀ {k} (A : Ty Γ k) {ℓ : Lvl Γ} → Ty Γ ℓ → Ty (cons Γ k A) (wkᴸ A ℓ)
wkᵀ A B (γ , _) = B γ

wkᵗ : ∀ {k} (A : Ty Γ k) {ℓ : Lvl Γ} {B : Ty Γ ℓ} → Tm Γ ℓ B → Tm (cons Γ k A) (wkᴸ A ℓ) (wkᵀ A B)
wkᵗ A a (γ , _) = a γ

var : ∀ {k} (A : Ty Γ k) → Tm (cons Γ k A) (wkᴸ A k) (wkᵀ A A)
var A (_ , a) = a

substᴸ : ∀ {k} (A : Ty Γ k) → Lvl (cons Γ k A) → (a : Tm Γ k A) → Lvl Γ
substᴸ A ℓ a γ = ℓ (γ , a γ)
syntax substᴸ A ℓ a = ℓ ⟨ a ∈ A ⟩ᴸ

substᵀ : ∀ {k} (A : Ty Γ k) {ℓ : Lvl (cons Γ k A)} → Ty (cons Γ k A) ℓ → (a : Tm Γ k A) → Ty Γ (ℓ ⟨ a ∈ A ⟩ᴸ)
substᵀ A B a γ = B (γ , a γ)
syntax substᵀ A B a = B ⟨ a ∈ A ⟩ᵀ

substᵗ : ∀ {k} (A : Ty Γ k) {ℓ : Lvl (cons Γ k A)} (B : Ty (cons Γ k A) ℓ) → Tm (cons Γ k A) ℓ B → (a : Tm Γ k A) → Tm Γ (ℓ ⟨ a ∈ A ⟩ᴸ) (B ⟨ a ∈ A ⟩ᵀ)
substᵗ A B b a γ = b (γ , a γ)
syntax substᵗ A B b a = b ∈ B ⟨ a ∈ A ⟩ᵗ

{--------------
  Level rules
--------------}

Level< : ∀ {ℓ} → (k : Lvl Γ) → Ty Γ ℓ
Level< k γ = L̂ (k γ)

unlvl : ∀ {k ℓ} → Tm Γ ℓ (Level< k) → Σ[ j ∈ Lvl Γ ] Lt j k
unlvl j = (λ γ → let (j' , _) = j γ in j') , (λ γ → let (_ , j<k) = j γ in j<k)

unlvl₁ : ∀ {k ℓ} → Tm Γ ℓ (Level< k) → Lvl Γ
unlvl₁ j = unlvl j .fst

unlvl₂ : ∀ {k ℓ} (j : Tm Γ ℓ (Level< k)) → Lt (unlvl₁ j) k
unlvl₂ j = unlvl j .snd

-- rule Level<
Level<' : ∀ {k ℓ} → (j : Tm Γ ℓ (Level< k)) → Ty Γ ℓ
Level<' j = Level< (unlvl₁ j)

lvl : ∀ {k ℓ} (j : Lvl Γ) → Lt j k → Tm Γ ℓ (Level< k)
lvl j j<k γ = j γ , j<k γ

-- rule Lvl
lvl' : ∀ {j k ℓ} → j < k → Tm Γ ℓ (Level< (λ _ → k))
lvl' {j = j} j<k = lvl (λ _ → j) (λ _ → j<k)

-- rule Trans
trans : ∀ {ℓ k' j'} (k : Tm Γ k' (Level< ℓ)) (j : Tm Γ j' (Level< (unlvl₁ k))) → Tm Γ k' (Level< ℓ)
trans k j γ = unlvl₁ j γ , trans< (unlvl₂ j γ) (unlvl₂ k γ)

trans≡ : ∀ {ℓ k' j'} (k : Tm Γ k' (Level< ℓ)) (j : Tm Γ j' (Level< (unlvl₁ k))) →
  unlvl₁ j ≡ unlvl₁ (trans k j)
trans≡ k j = refl

{-----------------
  Universe rules
-----------------}

-- rule Univ
Univ : ∀ {k ℓ} → Tm Γ ℓ (Level< k) → Ty Γ k
Univ j γ with (j' , j<k) ← j γ = Û j' j<k

russell : ∀ {k ℓ} (j : Tm Γ ℓ (Level< k)) → Tm Γ k (Univ j) ≡ Ty Γ (unlvl₁ j)
russell {Γ} {k} j i = (γ : em Γ) → U≡ (wf (k γ)) (unlvl₂ j γ) (~ i)

-- rule Cumul
cumul : ∀ {k ℓ} (j : Tm Γ ℓ (Level< k)) → Ty Γ (unlvl₁ j) → Ty Γ k
cumul j A = liftTy (unlvl₂ j) A

cumul≡ : ∀ {k ℓ} (j : Tm Γ ℓ (Level< k)) (A : Ty Γ (unlvl₁ j)) → Tm Γ _ A ≡ Tm Γ _ (cumul j A)
cumul≡ j A = liftTm (unlvl₂ j) A

{------------------------------------------
  It seems like this needs to hold:

  Γ ⊢ j : Level< k
  Γ ⊢ k : Level< ℓ
  ---------------------------------------
  Γ ⊢ cumul k (U j) ≡ U (trans j k) : U ℓ
------------------------------------------}

cumulTrans : ∀ {ℓ k' j'} (k : Tm Γ k' (Level< ℓ)) (j : Tm Γ j' (Level< (unlvl₁ k))) →
  cumul k (Univ j) ≡ Univ (trans k j)
cumulTrans k j = refl

{--------------
  Empty rules
--------------}

-- rule Mty
Bot : ∀ {k} → Ty Γ k
Bot γ = ⊥̂

-- rule Abs
absurd : ∀ {k ℓ} (A : Ty Γ k) → Tm Γ ℓ Bot → Tm Γ k A
absurd A b γ with () ← b γ

{-----------------
  Function rules
-----------------}

-- rule Pi
Pi : ∀ {k : Lvl Γ} → (A : Ty Γ k) → Ty (cons Γ k A) (wkᴸ A k) → Ty Γ k
Pi A B γ = Π̂ (A γ) (λ a → B (γ , a))

-- rule Lam
lam : ∀ {k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ A k)) →
  Tm (cons Γ k A) (wkᴸ A k) B → Tm Γ k (Pi A B)
lam A B b γ a = b (γ , a)

-- rule App
app : ∀ {k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ A k)) →
  Tm Γ k (Pi A B) → (a : Tm Γ k A) → Tm Γ k (B ⟨ a ∈ A ⟩ᵀ)
app A B b a γ = b γ (a γ)

-- rule E-Beta
β : ∀ {k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ A k))
  (a : Tm Γ k A) (b : Tm (cons Γ k A) (wkᴸ A k) B) →
  app A B (lam A B b) a ≡ b ∈ B ⟨ a ∈ A ⟩ᵗ
β A B a b = refl