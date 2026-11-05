module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalSelectedPrimaryStrain.RawProfilesTemplate
public meta import Lean

/-! # Read the actual primary data from the published raw-profile interface

This is the same selected52/hAux/N/sample telescope already checked by the
actual full-source profile producer. Reading it directly avoids rebuilding
the upstream construction whenever a downstream original-data deduction is
published. No mathematical data or proof input is changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.DataTemplate

open Lean Meta

private def app (key : Name) (p : Array Expr) := mkAppN (mkConst key) p
/-- Retain the checked original selected source directly from the published
raw-profile telescope, with no re-run of the upstream construction. -/
def withData (next : RawProfilesTemplate.Data → MetaM Unit) : MetaM Unit :=
  RawProfilesTemplate.withData next

/-- Project the published full PSigma label into the same actual source data.
This changes neither the label type nor the order in which constants are fixed. -/
def withLabels
    (next : Array Expr → Expr → Expr → RawProfilesTemplate.Data → Expr → MetaM Unit) : MetaM Unit :=
  withData fun d =>
    withLocalDeclNoLocalInstanceUpdate `imaginary .default (mkConst ``Bool) fun q => do
      let fields := d.selected[33:].toArray ++ #[d.hAux,d.sample,q]
      unless fields.size == 22 do throwError "actual primary data: original label fields changed"
      let labels := app `JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.Labels d.fixed
      withLocalDeclNoLocalInstanceUpdate `sourceLabel .default labels fun t => do
        let mut values := #[]
        let mut rest := t
        for _ in fields do
          values := values.push (.proj ``PSigma 0 rest)
          rest := .proj ``PSigma 1 rest
        let replace (e : Expr) : MetaM Expr := do
          return (← mkLambdaFVars fields e).beta values
        let actual : RawProfilesTemplate.Data := {
          native := ← d.native.mapM replace
          selected := ← d.selected.mapM replace
          hAux := ← replace d.hAux
          steps := d.steps
          sample := ← replace d.sample
          sourceArgs := ← d.sourceArgs.mapM replace
          baselineArgs := ← d.baselineArgs.mapM replace
          baseline := ← replace d.baseline
          source := ← replace d.source
          hBaseline := ← replace d.hBaseline }
        next d.fixed labels t actual values.back!

end JanetCartan.PhysicalPrimary.OriginalSelectedPrimaryStrain.DataTemplate
end
