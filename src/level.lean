import Mathlib.Order.RelClasses
import Mathlib.Order.BoundedOrder

set_option autoImplicit false
set_option pp.fieldNotation false

/-*----------------------------------------------------------
  Typeclass for levels and their required properties:
  * Wellfoundedness is needed to build the logical relation
  * Transitivity is needed for cumulativity of the LR
  * Trichotomy is needed for determinism of the LR
  * Cofinality is needed since every type has a type
----------------------------------------------------------*-/

class LevelClasses (L : Type)
  extends Preorder L, OrderBot L, IsWellOrder L lt, NoMaxOrder L
open LevelClasses

instance {L : Type} [lc : LevelClasses L] : WellFoundedRelation L :=
  lc.toWellFoundedRelation

class LevelClass where
  L : Type
  lc : LevelClasses L

attribute [instance] LevelClass.lc

/-*---------------------------------
  The naturals are suitable levels
---------------------------------*-/

instance instNoMaxOrderNat : NoMaxOrder Nat where
  exists_gt := λ i ↦ ⟨Nat.succ i, by omega⟩

@[simp]
instance : LevelClass where
  L := Nat
  lc := { bot := 0, bot_le := λ _ ↦ by simp }
