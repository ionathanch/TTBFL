import «src».typing

open Term

theorem wfMty : ⊢ ⬝ ∷ mty := by
  apply Wf.cons
  apply Wf.nil
  apply Wt.mty
  apply Wt.𝒰
  apply Wt.lof (j := 69) (k := 70)
  apply Wf.nil
  exact (by omega : 69 < 70)

theorem wtfMty : ⬝ ∷ mty ⊢ var 0 ∶ mty := by
  apply Wt.var
  . exact wfMty
  . apply inHere; rfl

/-
-- in an inconsistent context b : ⊥, absurd b : Level< (absurd b)
theorem loopLvl : ⬝ ∷ mty ⊢ exf (var 0) ∶ lvl (exf (var 0)) := by
  apply Wt.exf
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
-/

@[simp]
def idType k := (pi (lvl (lof k)) (pi (𝒰 (var 0)) (pi (var 0) (var 1))))

-- idpoly : (j : Level< 69) → (A : 𝒰 j) → A → A
-- idpoly ≔ λ j A x. x
theorem idpoly : ⬝ ⊢ (abs (lvl (lof 69)) (abs (𝒰 (var 0)) (abs (var 0) (var 0)))) ∶ idType 69 := by
  apply Wt.abs (k := lof 69)
  . apply Wt.pi
    . apply Wt.lvl
      . apply Wt.lof (k := 70) Wf.nil
        exact (by omega : 69 < 70)
      . apply Wt.𝒰 (k := lof 70) (Wt.lof Wf.nil ?_)
        exact (by omega : 69 < 70)
    . apply Wt.pi
      . apply Wt.𝒰
        apply Wt.var
        . sorry
        . apply inHere; rfl
      . apply Wt.pi
        . apply Wt.sub
          . apply Wt.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
          . apply Wt.var
            . sorry
            . apply inHere; rfl
        . apply Wt.sub
          . apply Wt.var
            . sorry
            . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
          . apply Wt.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
  . apply_rules [Wt.lvl, Wt.lof, Wt.𝒰, Wf.nil]
    repeat exact (by omega : 69 < 70)
  . apply Wt.abs
    . apply Wt.pi
      . apply Wt.𝒰
        apply Wt.var
        . sorry
        . apply inHere; rfl
      . apply Wt.pi
        . apply Wt.sub
          . apply Wt.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
          . apply Wt.var
            . sorry
            . apply inHere; rfl
        . apply Wt.sub
          . apply Wt.var
            . sorry
            . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
          . apply Wt.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
    . apply_rules [Wt.lvl, Wt.lof, Wt.𝒰, Wt.var, Wf.nil, Wf.cons, inThere, inHere]
      repeat exact (by omega : 69 < 70)
    . apply Wt.abs
      . apply Wt.pi
        . apply Wt.sub
          . apply Wt.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
          . apply Wt.var
            . sorry
            . apply inHere; rfl
        . apply Wt.sub
          . apply Wt.var
            . sorry
            . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
          . apply Wt.var
            . sorry
            . apply inThere; apply inHere; rfl; rfl
      . sorry
      . apply Wt.var
        . sorry
        . apply inHere; rfl

-- idid : ((j : Level< (lof 4)) → (A : 𝒰 j) → A → A) → ((j : Level< (lof 3)) → (A : 𝒰 j) → A → A)
-- idid ≔ λ id. id (lof 3) ((j : Level< (lof 3)) → (A : 𝒰 j) → A → A) (λ j. id j)
-- All of the `sorry`s are boring proofs about context well formedness
theorem idid : ⬝ ⊢ (abs (idType 4) (app (app ((app (var 0) (lof 3))) (idType 3)) (abs (lvl (lof 3)) (app (var 1) (var 0))))) ∶ (pi (idType 4) (idType 3)) := by
  apply Wt.abs (k := lof 4)
  . apply Wt.pi
    . apply Wt.pi
      . apply Wt.lvl
        . apply Wt.lof (k := 5) Wf.nil
          exact (by omega : 4 < 5)
        . apply Wt.𝒰 (k := lof 5) (Wt.lof Wf.nil ?_)
          exact (by omega : 4 < 5)
      . apply Wt.pi
        . apply Wt.𝒰
          apply Wt.var
          . sorry
          . apply inHere; rfl
        . apply Wt.pi
          . apply Wt.sub
            . apply Wt.var
              . sorry
              . apply inThere; apply inHere; rfl; rfl
            . apply Wt.var
              . sorry
              . apply inHere; rfl
          . apply Wt.sub
            . apply Wt.var
              . sorry
              . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
            . apply Wt.var
              . sorry
              . apply inThere; apply inHere; rfl; rfl
    . apply Wt.sub
      . apply @Wt.lof _ _ 3; sorry
        exact (by omega : 3 < 4)
      . apply Wt.pi
        . apply Wt.lvl
          . apply Wt.lof (k := 4); sorry
            exact (by omega : 3 < 4)
          . apply Wt.𝒰 (k := lof 4); apply Wt.lof; sorry
            exact (by omega : 3 < 4)
        . apply Wt.pi
          . apply Wt.𝒰
            apply Wt.var
            . sorry
            . apply inHere; rfl
          . apply Wt.pi
            . apply Wt.sub
              . apply Wt.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
              . apply Wt.var
                . sorry
                . apply inHere; rfl
            . apply Wt.sub
              . apply Wt.var
                . sorry
                . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
              . apply Wt.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
  . sorry
  . apply wtfApp
    . apply wtfApp
      . apply wtfApp
        . apply Wt.var
          . sorry
          . apply inHere; rfl
        . apply Wt.lof; sorry
          exact (by omega : 3 < 4)
        . simp; exact ⟨rfl, rfl⟩
      . apply Wt.pi
        . apply Wt.lvl
          . apply Wt.lof (k := 4); sorry
            exact (by omega : 3 < 4)
          . apply Wt.𝒰 (k := lof 4); apply Wt.lof; sorry
            exact (by omega : 3 < 4)
        . apply Wt.pi
          . apply Wt.𝒰
            apply Wt.var
            . sorry
            . apply inHere; rfl
          . apply Wt.pi
            . apply Wt.sub
              . apply Wt.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
              . apply Wt.var
                . sorry
                . apply inHere; rfl
            . apply Wt.sub
              . apply Wt.var
                . sorry
                . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
              . apply Wt.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
      . simp; exact ⟨rfl, rfl⟩
    . apply Wt.abs (k := lof 3)
      . apply Wt.pi
        . apply Wt.lvl
          . apply Wt.lof (k := 4); sorry
            exact (by omega : 3 < 4)
          . apply Wt.𝒰 (k := lof 4); apply Wt.lof; sorry
            exact (by omega : 3 < 4)
        . apply Wt.pi
          . apply Wt.𝒰
            apply Wt.var
            . sorry
            . apply inHere; rfl
          . apply Wt.pi
            . apply Wt.sub
              . apply Wt.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
              . apply Wt.var
                . sorry
                . apply inHere; rfl
            . apply Wt.sub
              . apply Wt.var
                . sorry
                . apply inThere; apply inThere; apply inHere; rfl; rfl; rfl
              . apply Wt.var
                . sorry
                . apply inThere; apply inHere; rfl; rfl
      . sorry
      . apply wtfApp
        . apply Wt.var
          . sorry
          . apply inThere; apply inHere; rfl; rfl
        . apply Wt.trans
          . apply Wt.var
            . sorry
            . apply inHere; rfl
          . apply Wt.lof; sorry
            exact (by omega : 3 < 4)
        . simp
    . simp
