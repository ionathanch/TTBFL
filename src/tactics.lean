module

public meta import Lean.Elab.Tactic
namespace Lean.Elab.Tactic
open Meta

/-- Return `true` if the expression is a function type
    whose first explicit argument is an equality. -/
private meta def firstArgEq? : Expr → Bool
  | .forallE _ bType _ .default => Expr.isEq bType
  | .forallE _ _ body _ => firstArgEq? body
  | _ => false

/-- The `specialize_rfls` tactic tries to specialize all hypotheses
    whose first explicit argument is an equality with `rfl`. -/
elab "specialize_rfls" : tactic =>
  withMainContext do
    for decl in (← getLCtx) do
      if firstArgEq? (← inferType decl.toExpr) then
        evalTactic
          (← `(tactic| try specialize $(mkIdent decl.userName) rfl))
