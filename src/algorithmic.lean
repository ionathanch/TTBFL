import «src».syntactics

open Nat
open Term

set_option autoImplicit false
set_option pp.fieldNotation false

variable [lc : LevelClass]
variable [teq : BEq Term]

def find (Γ : Ctxt) (x : Nat) : Option Term :=
  match Γ, x with
  | ⬝, _ => none
  | (_ ∷ A), 0 => some A
  | (Γ ∷ _), (succ x) => find Γ x

def getlvl (a : Term) : Option Term :=
  match a with
  | lvl k => k
  | _ => none

def getpi (a : Term) : Option (Term × Term) :=
  match a with
  | pi a b => some ⟨a, b⟩
  | _ => none

-- lvl 0 ≼ lvl 1 ≼ ... ⋠ lvl x

mutual
partial def subtype (Γ : Ctxt) (A B : Term) : Option Term :=
  if A == B then some B else
  match A, B with
  | 𝒰 (lof j), 𝒰 (lof k) | lvl (lof j), lvl (lof k) => sorry
  | 𝒰 j, 𝒰 k | lvl j, lvl k =>
    synth Γ j >>= (subtype Γ · (lvl k)) >>= λ _ ↦ some B
  | _, _ => none

partial def synth (Γ : Ctxt) (a : Term) : Option Term :=
  match a with
  | var x => find Γ x
  | 𝒰 j => Term.𝒰 <$> synth Γ j >>= getlvl
  | pi a b => do
    let 𝒰a ← synth Γ a
    let 𝒰b ← synth Γ b
    match subtype Γ 𝒰a 𝒰b, subtype Γ 𝒰b 𝒰a with
    | some A, _ | _, some A => some A
    | none, none => none
  | abs A b => synth (Γ ∷ A) b >>= (pi A ·)
  | app b a => do
    let ⟨A, B⟩ ← synth Γ b >>= getpi
    let _ ← synth Γ a >>= (subtype Γ · A)
    return subst (a +: var) B
  | mty => return (𝒰 sorry)
  | exf A b => do
    let _ ← synth Γ b >>= (subtype Γ · mty)
    let _ ← synth Γ A
    return A
  | lvl k => do
    let _ ← synth Γ k >>= getlvl
    return (𝒰 sorry)
  | lof i => return (lvl (lof sorry))
end
