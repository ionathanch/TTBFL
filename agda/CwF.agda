{-# OPTIONS --lossy-unification --cubical #-}

import Acc
open import Data.Empty
open import Data.Unit
open import Data.Product.Base using (∃-syntax)
open import Function.Base
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

{--------------------------------------------------
  Some important properties:
  * Universes irrelevant in Acc
  * Universes can be lifted to higher levels
  * Interpretations of lifted universes unchanged
--------------------------------------------------}

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

_↑_ : ∀ {Γ Δ ℓ A} (σ : Γ ⇒ Δ) → Tm Γ (ℓ [ σ ]ᴸ) (A [ σ ]ᵀ) → Γ ⇒ cons Δ ℓ A
(σ ↑ a) γ = σ γ , a γ

variable Γ : Ctxt

⟨_⟩ : ∀ {ℓ A} → Tm Γ ℓ A → Γ ⇒ cons Γ ℓ A
⟨ a ⟩ = id ↑ a

wk : ∀ {ℓ A} → cons Γ ℓ A ⇒ Γ
wk = fst

wkᴸ : ∀ {ℓ A} → Lvl Γ → Lvl (cons Γ ℓ A)
wkᴸ k = k [ wk ]ᴸ

wkᵀ : ∀ {ℓ A k} → Ty Γ k → Ty (cons Γ ℓ A) (wkᴸ k)
wkᵀ A = A [ wk ]ᵀ

wkᵗ : ∀ {ℓ A k B} → Tm Γ k B → Tm (cons Γ ℓ A) (wkᴸ k) (wkᵀ B)
wkᵗ b = b [ wk ]ᵗ

var : ∀ {ℓ A} → Tm (cons Γ ℓ A) (wkᴸ ℓ) (wkᵀ A)
var = snd

wkᵀ₂ : ∀ {ℓ ℓ' A B k} → Ty (cons Γ ℓ A) (wkᴸ k) →
  Ty (cons (cons Γ ℓ' B) (wkᴸ ℓ) (wkᵀ A)) (wkᴸ (wkᴸ k))
wkᵀ₂ A = A [ (wk ∘ wk) ↑ var ]ᵀ

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

-- η for the empty type
η⊥ : ∀ {ℓ} → let Γ' = cons Γ ℓ Bot in
     ∀ {k A} (a : Tm Γ' k A) (b : Tm Γ ℓ Bot) →
     absurd (A [ ⟨ b ⟩ ]ᵀ) b ≡ a [ ⟨ b ⟩ ]ᵗ
η⊥ {Γ} _ b _ γ with () ← b γ

{-----------------
  Function rules
-----------------}

-- rule Pi
Pi : ∀ {k : Lvl Γ} → (A : Ty Γ k) → Ty (cons Γ k A) (wkᴸ k) → Ty Γ k
Pi A B γ = Π̂ (A γ) (λ a → B (γ , a))

-- rule Lam
lam : ∀ {k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ k)) →
  Tm (cons Γ k A) (wkᴸ k) B → Tm Γ k (Pi A B)
lam A B b γ a = b (γ , a)

-- rule App
app : ∀ {k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ k)) →
  Tm Γ k (Pi A B) → (a : Tm Γ k A) → Tm Γ k (B [ ⟨ a ⟩ ]ᵀ)
app A B b a γ = b γ (a γ)

-- rule E-Beta
βΠ : ∀ {k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ k))
  (a : Tm Γ k A) (b : Tm (cons Γ k A) (wkᴸ k) B) →
  app A B (lam A B b) a ≡ b [ ⟨ a ⟩ ]ᵗ
βΠ A B a b = refl

-- rule E-Eta
ηΠ : ∀ {k} (A : Ty Γ k) (B : Ty (cons Γ k A) (wkᴸ k)) (b : Tm Γ k (Pi A B)) →
  lam A B (app (wkᵀ A) (wkᵀ₂ B) (wkᵗ b) var) ≡ b
ηΠ A B b = refl

{--------------------------------------------------
  Every level k an inconsistent context Γ = x : ⊥
  has a strictly smaller level j
--------------------------------------------------}

nwf : ∀ {ℓ} → let Γ = cons nil ℓ Bot in (k : Lvl Γ) → ∃[ j ] Lt j k
nwf {ℓ} k = unlvl {ℓ = wkᴸ ℓ} (absurd (Level< k) var)