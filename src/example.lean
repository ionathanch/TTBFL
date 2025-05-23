import «src».typing

open Term

set_option autoImplicit false
set_option pp.fieldNotation false

theorem wfMty : ⊢ ⬝ ∷ mty := by
  apply Wtf.cons
  apply Wtf.nil
  apply Wtf.mty
  apply Wtf.𝒰
  apply Wtf.lof (j := 69) (k := 70)
  apply Wtf.nil
  simp

theorem wtfMty : ⬝ ∷ mty ⊢ var 0 ∶ mty := by
  apply Wtf.var
  . exact wfMty
  . apply inHere; rfl

-- in an inconsistent context b : ⊥, absurd b : Level< (absurd b)
theorem loopLvl : ⬝ ∷ mty ⊢ exf (var 0) ∶ lvl (exf (var 0)) := by
  apply Wtf.exf
  . apply Wtf.lvl (j := lof 69)
    apply Wtf.exf
    apply Wtf.lvl (j := lof 69)
    apply Wtf.lof (j := 69) (k := 70)
    exact wfMty
    simp; simp
    apply Wtf.𝒰 (j := lof 69) (k := lof 70)
    apply Wtf.lof
    exact wfMty
    simp
    exact wtfMty
    apply Wtf.𝒰 (j := lof 69) (k := lof 70)
    apply Wtf.lof
    exact wfMty
    simp
  . exact wtfMty

-- loop : (b : ⊥) → 𝒰 (absurd b)
-- loop ≔ λ b. 𝒰 (absurd b)
-- in an inconsistent context b : ⊥, 𝒰 (absurd b) : 𝒰 (absurd b)
theorem loop : ⬝ ⊢ abs (𝒰 (exf (var 0))) ∶ pi mty (𝒰 (exf (var 0))) := by
  apply Wtf.abs
  apply Wtf.pi
  apply Wtf.mty
  apply Wtf.𝒰
  apply Wtf.lof (j := 69) (k := 70)
  apply Wtf.nil; simp
  apply Wtf.𝒰
  apply Wtf.exf
  apply Wtf.lvl (j := lof 69)
  apply Wtf.lof (k := 70)
  exact wfMty; simp
  apply Wtf.𝒰 (k := lof 70)
  apply Wtf.lof
  apply wfMty
  simp
  exact wtfMty
  apply Wtf.𝒰 loopLvl

@[simp]
def idType k := (pi (lvl (lof k)) (pi (𝒰 (var 0)) (pi (var 0) (var 1))))

-- idpoly : (j : Level< 69) → (A : 𝒰 j) → A → A
-- idpoly ≔ λ j A x. x
theorem idpoly : ⬝ ⊢ (abs (abs (abs (var 0)))) ∶ idType 69 := by
  apply Wtf.abs (k := lof 69)
  . apply Wtf.pi
    . apply Wtf.lvl
      . apply Wtf.lof (k := 70) Wtf.nil; simp
      . apply Wtf.𝒰 (k := lof 70) (Wtf.lof Wtf.nil ?_); simp
    . apply Wtf.pi
      . apply Wtf.𝒰
        apply Wtf.var
        . sorry
        . apply inHere; rfl
      . apply Wtf.pi
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inHere; rfl
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
  . apply Wtf.abs
    . apply Wtf.pi
      . apply Wtf.𝒰
        apply Wtf.var
        . sorry
        . apply inHere; rfl
      . apply Wtf.pi
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inHere; rfl
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
    . apply Wtf.abs
      . apply Wtf.pi
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inHere; rfl
        . apply Wtf.sub
          . apply Wtf.var
            . sorry
            . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
          . apply Wtf.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
      . apply Wtf.var
        . sorry
        . apply inHere; rfl

-- idid : ((j : Level< (lof 4)) → (A : 𝒰 j) → A → A) → ((j : Level< (lof 3)) → (A : 𝒰 j) → A → A)
-- idid ≔ λ id. id (lof 3) ((j : Level< (lof 3)) → (A : 𝒰 j) → A → A) (λ j. id j)
-- All of the `sorry`s are boring proofs about context well formedness
theorem idid : ⬝ ⊢ (abs (app (app ((app (var 0) (lof 3))) (idType 3)) (abs (app (var 1) (var 0))))) ∶ (pi (idType 4) (idType 3)) := by
  apply Wtf.abs (k := lof 4)
  . apply Wtf.pi
    . apply Wtf.pi
      . apply Wtf.lvl
        . apply Wtf.lof (k := 70) Wtf.nil; simp
        . apply Wtf.𝒰 (k := lof 70) (Wtf.lof Wtf.nil ?_); simp
      . apply Wtf.pi
        . apply Wtf.𝒰
          apply Wtf.var
          . sorry
          . apply inHere; rfl
        . apply Wtf.pi
          . apply Wtf.sub
            . apply Wtf.var
              . sorry
              . apply inThere; apply inHere; rfl; rfl
            . apply Wtf.var
              . sorry
              . apply inHere; rfl
          . apply Wtf.sub
            . apply Wtf.var
              . sorry
              . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
            . apply Wtf.var
              . sorry
              . apply inThere; apply inHere; rfl; rfl
    . apply Wtf.sub
      . apply @Wtf.lof _ _ 3; sorry; simp
      . apply Wtf.pi
        . apply Wtf.lvl
          . apply Wtf.lof (k := 4); sorry; simp
          . apply Wtf.𝒰 (k := lof 4); apply Wtf.lof; sorry; simp
        . apply Wtf.pi
          . apply Wtf.𝒰
            apply Wtf.var
            . sorry
            . apply inHere; rfl
          . apply Wtf.pi
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inHere; rfl
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
  . apply wtfApp
    . apply wtfApp
      . apply wtfApp
        . apply Wtf.var
          . sorry
          . apply inHere; rfl
        . apply Wtf.lof; sorry; simp
        . simp; exact ⟨rfl, rfl⟩
      . apply Wtf.pi
        . apply Wtf.lvl
          . apply Wtf.lof (k := 4); sorry; simp
          . apply Wtf.𝒰 (k := lof 4); apply Wtf.lof; sorry; simp
        . apply Wtf.pi
          . apply Wtf.𝒰
            apply Wtf.var
            . sorry
            . apply inHere; rfl
          . apply Wtf.pi
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inHere; rfl
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
      . simp; exact ⟨rfl, rfl⟩
    . apply Wtf.abs (k := lof 3)
      . apply Wtf.pi
        . apply Wtf.lvl
          . apply Wtf.lof (k := 4); sorry; simp
          . apply Wtf.𝒰 (k := lof 4); apply Wtf.lof; sorry; simp
        . apply Wtf.pi
          . apply Wtf.𝒰
            apply Wtf.var
            . sorry
            . apply inHere; rfl
          . apply Wtf.pi
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inHere; rfl
            . apply Wtf.sub
              . apply Wtf.var
                . sorry
                . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
              . apply Wtf.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
      . apply wtfApp
        . apply Wtf.var
          . sorry
          . apply inThere; apply inHere; rfl; rfl
        . apply Wtf.trans
          . apply Wtf.var
            . sorry
            . apply inHere; rfl
          . apply Wtf.lof; sorry; simp
        . simp
    . simp
