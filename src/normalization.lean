import «src».typing
import «src».candidates

open Term
open Nat

variable [lc : LevelClass]

/-*------------------------------
  Renaming and weakening lemmas
------------------------------*-/

theorem semComp {ξ : ℕ → ℕ} {σ Γ Δ}
  (h : Δ ⊢ ξ ∶ Γ)
  (hζ : σ ⊨ Δ) :
  σ ∘ ξ ⊨ Γ := by
  intro x A mem
  rw [← substRename]
  exact hζ (ξ x) (rename ξ A) (h x A mem)

theorem semRename {ξ : ℕ → ℕ} {Γ Δ a A}
  (hξ : Δ ⊢ ξ ∶ Γ)
  (ha : Γ ⊨ a ∶ A) :
  Δ ⊨ rename ξ a ∶ rename ξ A := by
  intro σ hσ
  rw [substRename, substRename]
  exact ha (σ ∘ ξ) (semComp hξ hσ)

theorem semWeaken {Γ a A B}
  (ha : Γ ⊨ a ∶ A) :
  Γ ∷ B ⊨ rename succ a ∶ rename succ A := by
  exact semRename wRenameSucc ha

/-*---------------------------------------------
  Soundness of typing wrt the logical relation
---------------------------------------------*-/

theorem semWfCons {Γ A k} (hΓ : ⊨ Γ) (hA : Γ ⊨ A ∶ 𝒰 k) : ⊨ Γ ∷ A := by
  intros x A mem
  cases mem
  case here =>
    exists rename succ k
    exact semWeaken (A := 𝒰 k) hA
  case there x B mem =>
    let ⟨k, hB⟩ := hΓ x B mem
    exists rename succ k
    exact semWeaken (A := 𝒰 k) hB

theorem soundness {Γ} {a A : Term} (h : Γ ⊢ a ∶ A) : Γ ⊨ a ∶ A := by
  induction h using Wt.rec (motive_1 := λ Γ _ ↦ ⊨ Γ)
  case nil => intro x A mem; cases mem
  case cons k _ _ hΓ hA => exact semWfCons hΓ hA
  all_goals intro σ hσ
  case var x A wf mem h =>
    unfold semWf at h
    unfold semSubst at hσ
    let ⟨k, ih⟩ := h x A mem
    let ⟨_, _, h𝒰, hA⟩ := ih σ hσ
    let ⟨_, _, _, e⟩ := interps𝒰Inv h𝒰; subst e
    let ⟨_, hA⟩ := hA
    refine ⟨_, _, hA, hσ x A mem _ _ hA⟩
  case pi ihA ihB =>
    let ⟨_, _, h𝒰, hA⟩ := ihA σ hσ
    let ⟨_, _, ra, e⟩ := interps𝒰Inv h𝒰
    refine ⟨_, _, h𝒰, ?_⟩; subst e
    let ⟨PA, hA⟩ := hA
    constructor; apply interpsPi hA _ rfl
    intro x PAx; rw [← substUnion]
    let ⟨_, _, h𝒰, hB⟩ := ihB (x +: σ) (semSubstCons hA PAx hσ)
    let ⟨_, _, rb, e⟩ := interps𝒰Inv h𝒰
    subst e; rw [substRename] at rb
    let ⟨_, ra', rb'⟩ := confluence ra rb
    rw [parsLofInv ra'] at rb'
    injection (parsLofInv rb') with e
    simp_rw [e, hB]
  case abs ihpi _ ihb =>
    let ⟨_, _, h𝒰, hpi⟩ := ihpi σ hσ
    let ⟨_, _, _, e⟩ := interps𝒰Inv h𝒰
    subst e
    let ⟨_, hpi⟩ := hpi
    let ⟨_, hA, _, e⟩ := interpsPiInv hpi
    refine ⟨_, _, hpi, ?_⟩; subst e
    intro x Pb PAx hB; rw [← substUnion] at hB
    let ⟨_, _, hB', hb⟩ := ihb (x +: σ) (semSubstCons hA PAx hσ)
    rw [interpsDet hB hB']
    exact interpsBwdsP (parsβ σ) hB' hb
  case app ihb iha =>
    let ⟨_, _, hpi, hb⟩ := ihb σ hσ
    let ⟨_, PA, hA, ha⟩ := iha σ hσ
    let ⟨PA', hA', hB, e⟩ := interpsPiInv hpi
    rw [interpsDet hA hA'] at ha
    let ⟨_, hB⟩ := hB (subst σ _) ha
    subst e; rw [← substDist]
    exact ⟨_, _, hB, hb _ _ ha hB⟩
  case 𝒰 j k _ ih =>
    let ⟨_, P, hk, hj⟩ := ih σ hσ
    let ⟨wnfk, e⟩ := interpsLvlInv hk; subst e
    rcases hj with ⟨j, k, lt, rj, rk⟩ | wnej
    case inr ℓ => sorry
    case inl =>
    let ⟨ℓ, ltk⟩ := exists_gt k
    exact ⟨ℓ, _,
      interpsBwds (pars𝒰 rk) (interps𝒰 ltk),
      ⟨_, interpsBwds (pars𝒰 rj) (interps𝒰 lt)⟩⟩
  case mty ih =>
    let ⟨_, _, hj, hi⟩ := ih σ hσ
    let ⟨_, _, _, e⟩ := interps𝒰Inv hj; subst e
    let ⟨P, hi⟩ := hi
    let ⟨_, _, _, e⟩ := interps𝒰Inv hi; subst e
    exact ⟨_, _, hi, ⟨_, interpsMty⟩⟩
  case exf A b _ _ _ ihA ihb =>
    let ⟨k, _, hmty, hb⟩ := ihb σ hσ
    let ⟨_, _, h𝒰, hA⟩ := ihA σ hσ
    let ⟨_, _, _, e⟩ := interps𝒰Inv h𝒰; subst e
    let ⟨P, hA⟩ := hA
    let ⟨_, CRnf⟩ := adequacy h𝒰 (subst σ A)
    let ⟨CRne, _⟩ := adequacy hA (exf (subst σ A) (subst σ b))
    rw [interpsMtyInv hmty] at hb
    exact ⟨_, P, hA, CRne (wneExf (CRnf ⟨P, hA⟩) hb)⟩
  case lvl iha ihj =>
    let ⟨_, _, hj, hi⟩ := ihj σ hσ
    let ⟨j, _, _, e⟩ := interps𝒰Inv hj; subst e
    let ⟨P, hi⟩ := hi
    let ⟨_, _, _, e⟩ := interps𝒰Inv hi; subst e
    let ⟨_, P, hlvl, ha⟩ := iha σ hσ
    let ⟨_, e⟩ := interpsLvlInv hlvl
    refine ⟨_, _, hi, ?_⟩
    rw [e] at ha; rcases ha with ⟨k, _, _, r, _⟩ | wnea
    case inl ha => exact ⟨_, interpsBwds (parsLvl r) (interpsLvl ⟨⟩)⟩
    case inr =>
      let ⟨_, nea, r⟩ := wnea
      exact ⟨_, interpsBwds (parsLvl r) (interpsLvl (neNf nea))⟩
  case lof j k _ lt ih =>
    refine ⟨j, _,
      interpsLvl ⟨⟩,
      Or.inl ⟨_, k, lt, Pars.refl _, Pars.refl _⟩⟩
  case trans i j k _ _ ihj ihk =>
    let ⟨ℓ, Pj, hk, hPj⟩ := ihk σ hσ
    let ⟨wnfk, ePj⟩ := interpsLvlInv hk; subst ePj
    let ⟨_, nfk, r⟩ := wnfk
    let ⟨_, Pi, hj, hPi⟩ := ihj σ hσ
    let ⟨_, ePi⟩ := interpsLvlInv hj; subst ePi
    rcases hPi with ⟨i', j', ltij, ri', rj'⟩ | wnei
    case inr => exact ⟨ℓ, _, interpsBwds (parsLvl r) (interpsLvl nfk), Or.inr wnei⟩
    case inl =>
    rcases hPj with ⟨j'', k', ltjk, rj'', rk'⟩ | wnej
    case inr => cases wneLof rj' wnej
    case inl =>
    let ⟨lofj, rlofj', rlofj''⟩ := confluence rj' rj''
    have e' := parsLofInv rlofj'
    have e'' := parsLofInv rlofj''
    subst e'; cases e''
    let ⟨lofk, rlofk', rlofk''⟩ := confluence rk' r
    rw [parsLofInv rlofk'] at rlofk''
    refine ⟨ℓ, _,
      interpsBwds (parsLvl r) (interpsLvl nfk),
      Or.inl ⟨i', k', ?_, ri', rlofk''⟩⟩
    apply IsTrans.trans; repeat assumption
  case conv e _ _ iha _ =>
    let ⟨_, _, hA, ha⟩ := iha σ hσ
    exact ⟨_, _, interpsConv (convSubst σ (eqvConv e)) hA, ha⟩
  case sub ihj ihA =>
    let ⟨_, Pj, h𝒰, hA⟩ := ihA σ hσ
    let ⟨_, _, rj, e⟩ := interps𝒰Inv h𝒰
    subst e
    let ⟨P, hA⟩ := hA
    let ⟨_, Pk, hk, hj⟩ := ihj σ hσ
    let ⟨wnfk, e⟩ := interpsLvlInv hk
    subst e; rcases hj with ⟨_, k, ltj', rj', rk⟩ | wnej
    case inr => cases wneLof rj wnej
    case inl =>
    let ⟨_, rj, rj'⟩ := confluence rj rj'
    rw [parsLofInv rj'] at rj
    injection (parsLofInv rj) with e; subst e
    let ⟨_, ltk⟩ := exists_gt k
    exact ⟨_, _,
      interpsBwds (pars𝒰 rk) (interps𝒰 ltk),
      ⟨_, interpsCumul ltj' hA⟩⟩

/-*-----------------------------------
  Existence of weak normal forms for
  well typed terms and their types
-----------------------------------*-/

theorem normalization {Γ} {a A : Term} (h : Γ ⊢ a ∶ A) : wnf a ∧ wnf A := by
  let ⟨_, _, hA, ha⟩ := soundness h var ?_
  . rw [substId] at ha hA
    let ⟨_, CRnf⟩ := adequacy hA a
    exact ⟨CRnf ha, interpsWnf hA⟩
  . intros x A _ i P hA
    rw [substId] at hA
    let ⟨CRne, _⟩ := adequacy hA (var x)
    exact CRne wneVar
