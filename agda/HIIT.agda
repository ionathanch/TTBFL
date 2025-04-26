{-# OPTIONS --cubical #-}

open import Cubical.Core.Primitives

interleaved mutual

  data Ctxt : Type
  data Lvl : Ctxt → Type
  data _<_ : ∀ {Γ} → Lvl Γ → Lvl Γ → Type
  data Ty : ∀ {Γ} → Lvl Γ → Type
  data _⇒_ : Ctxt → Ctxt → Type
  data Tm : ∀ {Γ : Ctxt} (ℓ : Lvl Γ) → Ty ℓ → Type

  data Ctxt where
    ∙ : Ctxt
    _∷_ : ∀ Γ {ℓ : Lvl Γ} → Ty ℓ → Ctxt

  data Lvl where
    _⟦_⟧ : ∀ {Γ Δ} → Lvl Δ → Γ ⇒ Δ → Lvl Γ

  data Ty where
    _⟦_⟧ : ∀ {Γ Δ} {ℓ : Lvl Δ} → Ty ℓ → (σ : Γ ⇒ Δ) → Ty (ℓ ⟦ σ ⟧)

  data _⇒_ where
    ε : ∀ {Γ} → Γ ⇒ ∙
    id : ∀ {Γ} → Γ ⇒ Γ
    _∘_ : ∀ {Γ Δ Ξ} → Δ ⇒ Ξ → Γ ⇒ Δ → Γ ⇒ Ξ
    _∷_ : ∀ {Γ Δ} {ℓ : Lvl Δ}  (σ : Γ ⇒ Δ) {A : Ty ℓ} → Tm (ℓ ⟦ σ ⟧) (A ⟦ σ ⟧) → Γ ⇒ (Δ ∷ A)
    εη : ∀ {Γ} (σ : Γ ⇒ ∙) → σ ≡ ε
    id∘ : ∀ {Γ Δ} (σ : Γ ⇒ Δ) → id ∘ σ ≡ σ
    ∘id : ∀ {Γ Δ} (σ : Γ ⇒ Δ) → σ ∘ id ≡ σ
    ∘∘ : ∀ {Γ Δ Ξ Θ} (σ : Ξ ⇒ Θ) (ρ : Δ ⇒ Ξ) (τ : Γ ⇒ Δ) → (σ ∘ ρ) ∘ τ ≡ σ ∘ (ρ ∘ τ)

  data _ where
    -- _⟦_⟧ : ∀ {Γ Δ} → Lvl Δ → Γ ⇒ Δ → Lvl Γ
    ⟦id⟧ : ∀ {Γ} (ℓ : Lvl Γ) → ℓ ⟦ id ⟧ ≡ ℓ
    ⟦∘⟧ : ∀ {Γ Δ Ξ} (ρ : Δ ⇒ Ξ) (σ : Γ ⇒ Δ) (ℓ : Lvl Ξ) → ℓ ⟦ ρ ⟧ ⟦ σ ⟧ ≡ ℓ ⟦ ρ ∘ σ ⟧

  data _<_ where
    <trans : ∀ {Γ} {j k ℓ : Lvl Γ} (p : j < k) (q : k < ℓ) → j < ℓ
    <prop : ∀ {Γ} {k ℓ : Lvl Γ} (p q : k < ℓ) → p ≡ q

  data _ where
    -- _⟦_⟧ : ∀ {Γ Δ} {ℓ : Lvl Δ} → Ty ℓ → (σ : Γ ⇒ Δ) → Ty (ℓ ⟦ σ ⟧)
    ⟦id⟧ : ∀ {Γ} {ℓ : Lvl Γ} (A : Ty ℓ) →
      (λ i → Ty (⟦id⟧ ℓ i)) [ A ⟦ id ⟧ ≡ A ]
    ⟦∘⟧ : ∀ {Γ Δ Ξ} (ρ : Δ ⇒ Ξ) (σ : Γ ⇒ Δ) {ℓ : Lvl Ξ} (A : Ty ℓ) →
      (λ i → Ty (⟦∘⟧ ρ σ ℓ i)) [ A ⟦ ρ ⟧ ⟦ σ ⟧ ≡ A ⟦ ρ ∘ σ ⟧ ]

  data Tm where
    _⟦_⟧ : ∀ {Γ Δ} {ℓ : Lvl Δ} {A : Ty ℓ} → Tm ℓ A → (σ : Γ ⇒ Δ) → Tm (ℓ ⟦ σ ⟧) (A ⟦ σ ⟧)
    ⟦id⟧ : ∀ {Γ} {ℓ : Lvl Γ} {A : Ty ℓ} (a : Tm ℓ A) →
      (λ i → Tm (⟦id⟧ ℓ i) (⟦id⟧ A i)) [ a ⟦ id ⟧ ≡ a ]
    ⟦∘⟧ : ∀ {Γ Δ Ξ} (ρ : Δ ⇒ Ξ) (σ : Γ ⇒ Δ) {ℓ : Lvl Ξ} {A : Ty ℓ} (a : Tm ℓ A) →
      (λ i → Tm (⟦∘⟧ ρ σ ℓ i) (⟦∘⟧ ρ σ A i)) [ a ⟦ ρ ⟧ ⟦ σ ⟧ ≡ a ⟦ ρ ∘ σ ⟧ ]
