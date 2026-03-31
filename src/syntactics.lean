import «src».level

open Nat

set_option autoImplicit false
set_option pp.fieldNotation false

variable [lc : LevelClass]

@[simp]
def cons {A : Type} (x : A) (ξ : Nat → A) : Nat → A
  | 0 => x
  | n + 1 => ξ n
infixr:50 "+:" => cons

/-*------
  Terms
------*-/

inductive Term : Type where
  | var : Nat → Term
  | 𝒰 : Term → Term
  | pi : Term → Term → Term
  | abs : Term → Term → Term
  | app : Term → Term → Term
  | mty : Term
  | exf : Term → Term → Term
  | lvl : Term → Term
  | lof : lc.L → Term
open Term

/-*------------------
  Lifting renamings
------------------*-/

@[simp]
def lift (ξ : Nat → Nat) : Nat → Nat :=
  zero +: (succ ∘ ξ)

-- Lifting respects renaming extensionality
omit lc in
theorem liftExt ξ ζ (h : ∀ x, ξ x = ζ x) : ∀ x, lift ξ x = lift ζ x := by
  intro x; cases x <;> simp [h]

-- Lifting identity renaming does nothing
omit lc in
theorem liftId ξ (h : ∀ x, ξ x = x) : ∀ x, lift ξ x = x := by
  intro x; cases x <;> simp [h]

-- Lifting composes
omit lc in
theorem liftComp ξ ζ ς (h : ∀ x, (ξ ∘ ζ) x = ς x) :
  ∀ x, (lift ξ ∘ lift ζ) x = lift ς x := by
  intro x; cases x <;> simp
  case succ => apply h

-- Lifting commutes with succ
omit lc in
theorem liftSucc ξ : ∀ x, (lift ξ ∘ succ) x = (succ ∘ ξ) x := by
  intro x; cases x <;> simp

/-*-------------------
  Applying renamings
-------------------*-/

@[simp]
def rename (ξ : Nat → Nat) : Term → Term
  | var s => var (ξ s)
  | 𝒰 a => 𝒰 (rename ξ a)
  | pi a b => pi (rename ξ a) (rename (lift ξ) b)
  | abs a b => abs (rename ξ a) (rename (lift ξ) b)
  | app b a => app (rename ξ b) (rename ξ a)
  | mty => mty
  | exf a b => exf (rename ξ a) (rename ξ b)
  | lvl a => lvl (rename ξ a)
  | lof k => lof k

-- Renaming extensionality
theorem renameExt ξ ζ (h : ∀ x, ξ x = ζ x) : ∀ s, rename ξ s = rename ζ s := by
  intro s; induction s generalizing ξ ζ
  all_goals simp; try constructor
  all_goals apply_rules [liftExt]

-- Applying identity renaming does nothing
theorem renameId s : rename id s = s := by
  induction s
  all_goals simp; try constructor
  all_goals try assumption
  all_goals rw [renameExt (0 +: succ) id]
  all_goals apply_rules [liftId]

-- Renamings compose
theorem renameComp' ξ ζ ς (h : ∀ x, (ξ ∘ ζ) x = ς x) : ∀ s, (rename ξ ∘ rename ζ) s = rename ς s := by
  intro s; induction s generalizing ξ ζ ς
  all_goals simp; try constructor
  all_goals apply_rules [liftComp]

-- Renamings compose (extensionally)
theorem renameComp ξ ζ s : rename ξ (rename ζ s) = rename (ξ ∘ ζ) s := by
  apply renameComp'; simp

/-*----------------------
  Lifting substitutions
----------------------*-/

@[simp]
def up (σ : Nat → Term) : Nat → Term :=
  var 0 +: (rename succ ∘ σ)
prefix:95 "⇑" => up

-- Lifting twice pushes renamings inwards
theorem upUp σ x : (⇑ ⇑ σ) x = (var 0 +: var 1 +: (rename succ ∘ rename succ ∘ σ)) x := by
  cases x; rfl
  case succ n => cases n <;> rfl

-- Lifting var "substitution" does nothing
theorem upId σ (h : ∀ x, σ x = var x) : ∀ x, (⇑ σ) x = var x := by
  intro n; cases n <;> simp [h]

-- Lifting respects subsitution extensionality
theorem upExt σ τ (h : ∀ x, σ x = τ x) : ∀ x, (⇑ σ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [h]

-- Lifting commutes with composition
theorem upLift ξ σ τ (h : ∀ x, (σ ∘ ξ) x = τ x) : ∀ x, (⇑ σ ∘ lift ξ) x = (⇑ τ) x := by
  intro n; cases n <;> simp [← h]

-- Lifting commutes with succ
theorem upSucc σ : ∀ x, (⇑ σ ∘ succ) x = (rename succ ∘ σ) x := by
  intro n; cases n <;> simp

-- Lifting commutes with injection of renamings into substitutions
theorem upVar ξ : ∀ x, (var ∘ lift ξ) x = (⇑ (var ∘ ξ)) x := by
  intro n; cases n <;> simp

-- Lifting commutes with renaming
theorem upRename ξ σ τ (h : ∀ x, (rename ξ ∘ σ) x = τ x) : ∀ x, (rename (lift ξ) ∘ ⇑ σ) x = (⇑ τ) x := by
  intro n; cases n; simp
  case succ n => calc
    (rename (lift ξ) ∘ rename succ) (σ n)
      = rename (lift ξ ∘ succ) (σ n)      := by simp [renameComp]
    _ = (rename (succ ∘ ξ)) (σ n)         := by rfl
    _ = (rename succ ∘ rename ξ) (σ n)    := by simp [renameComp]
    _ = (rename succ (rename ξ (σ n)))    := by rfl
    _ = rename succ (τ n)                 := by rw [← h]; rfl

/-*-----------------------
  Applying substitutions
-----------------------*-/

@[simp]
def subst (σ : Nat → Term) : Term → Term
  | var s => σ s
  | 𝒰 a => 𝒰 (subst σ a)
  | pi a b => pi (subst σ a) (subst (⇑ σ) b)
  | abs a b => abs (subst σ a) (subst (⇑ σ) b)
  | app b a => app (subst σ b) (subst σ a)
  | mty => mty
  | exf a b => exf (subst σ a) (subst σ b)
  | lvl a => lvl (subst σ a)
  | lof k => lof k

-- Substitution extensionality
theorem substExt σ τ (h : ∀ x, σ x = τ x) : ∀ s, subst σ s = subst τ s := by
  intro s; induction s generalizing σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upExt]

-- Applying var "substitution" does nothing
theorem substId' σ (h : ∀ x, σ x = var x) : ∀ s, subst σ s = s := by
  intro s; induction s generalizing σ
  all_goals simp; try constructor
  all_goals apply_rules [upId]

-- Substitution/renaming compositionality
theorem substRename' ξ σ τ (h : ∀ x, (σ ∘ ξ) x = τ x) : ∀ s, subst σ (rename ξ s) = subst τ s := by
  intro s; induction s generalizing ξ σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upLift]

-- Renaming/substitution compositionality
theorem renameSubst' ξ σ τ (h : ∀ x, (rename ξ ∘ σ) x = τ x) : ∀ s, rename ξ (subst σ s) = subst τ s := by
  intro s; induction s generalizing ξ σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upRename]

-- Lifting commutes with substitution
theorem upSubst ρ σ τ (h : ∀ x, (subst ρ ∘ σ) x = τ x) : ∀ x, (subst (⇑ ρ) ∘ (⇑ σ)) x = (⇑ τ) x := by
  intro n; cases n; rfl
  case succ n => calc
    (subst (⇑ ρ) ∘ rename succ) (σ n)
      = subst (⇑ ρ ∘ succ) (σ n)      := by rw [← substRename']; rfl; simp
    _ = subst (rename succ ∘ ρ) (σ n) := by rfl
    _ = (rename succ ∘ subst ρ) (σ n) := by rw [← renameSubst']; rfl; simp
    _ = rename succ (subst ρ (σ n))   := by rfl
    _ = rename succ (τ n)             := by rw [← h]; rfl

-- Substitution compositionality
theorem substComp' ρ σ τ (h : ∀ x, (subst ρ ∘ σ) x = τ x) : ∀ s, (subst ρ ∘ subst σ) s = subst τ s := by
  intro s; induction s generalizing ρ σ τ
  all_goals simp; try constructor
  all_goals apply_rules [upSubst]

/-*----------------------------------------------
  Substitution & renaming lemmas, extensionally
----------------------------------------------*-/

def substId : ∀ s, subst var s = s :=
  substId' var (by simp)

def substRename ξ σ : ∀ s, subst σ (rename ξ s) = subst (σ ∘ ξ) s :=
  substRename' _ _ (σ ∘ ξ) (by simp)

def renameSubst ξ σ : ∀ s, rename ξ (subst σ s) = subst (rename ξ ∘ σ) s :=
  renameSubst' _ _ (rename ξ ∘ σ) (by simp)

def substComp σ τ : ∀ s, (subst σ ∘ subst τ) s = subst (subst σ ∘ τ) s :=
  substComp' _ _ (subst σ ∘ τ) (by simp)

-- A renaming embeds into a substitution by
theorem renameToSubst ξ : ∀ s, rename ξ s = subst (var ∘ ξ) s := by
  intro s; induction s generalizing ξ
  all_goals simp [-up] <;> try constructor
  all_goals (try rw [← substExt _ _ (upVar ξ)]); apply_rules

/-*-------------------------------------------------
  Handy dandy derived renaming substitution lemmas
-------------------------------------------------*-/

theorem renameLiftRename ξ a : rename succ (rename ξ a) = rename (lift ξ) (rename succ a) := by
  calc
    rename succ (rename ξ a)
      = rename (succ ∘ ξ) a             := by rw [renameComp]
    _ = rename (lift ξ ∘ succ) a        := by rw [renameExt]; exact liftSucc ξ
    _ = rename (lift ξ) (rename succ a) := by rw [← renameComp]

theorem renameUpSubst σ a : rename succ (subst σ a) = subst (⇑ σ) (rename succ a) := by
  calc
    rename succ (subst σ a)
      = subst (rename succ ∘ σ) a   := by rw [renameSubst]
    _ = subst (⇑ σ ∘ succ) a        := by rw [substExt]; exact upSucc σ
    _ = subst (⇑ σ) (rename succ a) := by rw [substRename]

theorem renameDist ξ a s : subst (rename ξ a +: var) (rename (lift ξ) s) = rename ξ (subst (a +: var) s) := by
  calc
    subst (rename ξ a +: var) (rename (lift ξ) s)
    _ = subst ((rename ξ a +: var) ∘ lift ξ) s := by rw [substRename]
    _ = subst (rename ξ ∘ (a +: var)) s        := by apply substExt; intro n; cases n <;> rfl
    _ = rename ξ (subst (a +: var) s)          := by rw [← renameSubst]

theorem substDrop σ a b : subst (a +: σ) (rename succ b) = subst σ b := by
  calc
    subst (a +: σ) (rename succ b)
    _ = subst ((a +: σ) ∘ succ) b := by rw [substRename]

theorem substDropAll a b : b = subst (a +: var) (rename succ b) := by
  calc
    b = subst var b                      := by rw [substId]
    _ = subst (a +: var) (rename succ b) := by rw [substRename]; rfl

theorem substUnion σ a s : subst (a +: σ) s = subst (a +: var) (subst (⇑ σ) s) := by
  calc
    subst (a +: σ) s
      = subst (subst (a +: var) ∘ (var 0 +: (rename succ ∘ σ))) s :=
        by apply substExt; intro n; cases n <;> simp; rw [← substDropAll]
    _ = subst (a +: var) (subst (⇑ σ) s) :=
        by rw [← substComp]; rfl

theorem substDist σ a s : subst (subst σ a +: var) (subst (⇑ σ) s) = subst σ (subst (a +: var) s) := by
  calc
    subst (subst σ a +: var) (subst (⇑ σ) s)
      = subst (subst σ a +: σ) s       := by rw [← substUnion]
    _ = subst (subst σ ∘ (a +: var)) s := by apply substExt; intro n; cases n <;> rfl
    _ = (subst σ ∘ subst (a +: var)) s := by rw [← substComp]

theorem substToRename x s : subst (var x +: var) s = rename (x +: id) s := by
  calc
    subst (var x +: var) s
      = subst (var ∘ (x +: id)) s := by apply substExt; intro n; cases n <;> simp
    _ = rename (x +: id) s        := by rw [renameToSubst]

/-*------------------------
  Contexts and membership
------------------------*-/

inductive Ctxt : Type where
  | nil : Ctxt
  | cons : Ctxt → Term → Ctxt
notation:50 "⬝" => Ctxt.nil
infixl:50 "∷" => Ctxt.cons

inductive In : Nat → Term → Ctxt → Prop where
  | here {Γ A} : In 0 (rename succ A) (Γ ∷ A)
  | there {Γ x A B} : In x A Γ → In (succ x) (rename succ A) (Γ ∷ B)
notation:40 Γ:41 "∋" x:41 "∶" A:41 => In x A Γ

theorem inHere {Γ A A'} (e : A' = rename succ A) : (Γ ∷ A) ∋ 0 ∶ A' := by
  subst e; apply In.here

theorem inThere {Γ x A A' B} (h : Γ ∋ x ∶ A) (e : A' = rename succ A) : Γ ∷ B ∋ succ x ∶ A' := by
  subst e; apply In.there; assumption

/-*----------------------
  Well-scoped renamings
----------------------*-/

-- N.B. These used to be in the safety.lean file
-- but turns out they're needed for weakening semantic typing

def wRename ξ Γ Δ := ∀ x A, Γ ∋ x ∶ A → Δ ∋ ξ x ∶ rename ξ A
notation:40 Δ:41 "⊢" ξ:41 "∶" Γ:41 => wRename ξ Γ Δ

theorem wRenameSucc {Γ A} : Γ ∷ A ⊢ succ ∶ Γ := by
  intro x B mem; constructor; assumption

theorem wRenameLift {ξ : ℕ → ℕ} {Γ Δ A}
  (h : Δ ⊢ ξ ∶ Γ) :
  Δ ∷ (rename ξ A) ⊢ lift ξ ∶ Γ ∷ A := by
  intro x B mem
  cases mem with
  | here => apply inHere; simp [renameComp]; rfl
  | there => apply inThere; apply_rules [h]; simp [renameComp]; rfl
