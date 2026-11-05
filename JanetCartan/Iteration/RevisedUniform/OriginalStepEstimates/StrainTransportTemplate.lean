module

public import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.StrainInput
public meta import JanetCartan.Iteration.RevisedUniform.OriginalStepEstimates.StrainInputTemplate
public meta import Lean

/-!
# Transport the exact raw primary strain at generic source data

The actual current identity and original core inclusion are applied before
the dimension/metric specialization. The input is precisely the frozen raw
strain statement; the actual root will supply `strain_bound` itself. No
new analytic or geometry premise is introduced (`main:eq:primary-strain`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

public meta section
namespace JanetCartan.RevisedUniform.OriginalStepStrainTransportTemplate

open Lean Meta Elab Command
open OriginalStepStrainInputTemplate

private def currentIdentity : Name :=
  `JanetCartan.RevisedUniform.OriginalStepFields.primary_current_eq_normalized_history

private def termWith (bindings : List (Name × Expr)) (code : String) : MetaM Expr :=
  withTransparency .default <| Term.TermElabM.run'
    (PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code)

private def changeCurrent (d : Data) (proof : Expr) : MetaM Expr := do
  let target := head (← inferType proof)
  unless (target.find? (· == d.rawCurrent)).isSome do
    throwError "original strain transport: the exact original current disappeared"
  let equality := app currentIdentity d.selected
  withLocalDeclNoLocalInstanceUpdate `currentMap .default (← inferType d.rawCurrent) fun F => do
    let predicate ← mkLambdaFVars #[F] (target.replace fun e =>
      if e == d.rawCurrent then some F else none)
    termWith [(`F,d.rawCurrent),(`G,d.current),(`eqFG,equality),(`pred,predicate),(`h,proof)]
      "Eq.mp (congrArg pred (show F = G from eqFG)) h"

private def changeScale (d : Data) (proof : Expr) : MetaM Expr := do
  let target := head (← inferType proof)
  unless target.isAppOfArity ``LE.le 4 do
    throwError "original strain transport: the pointwise inequality changed"
  let rhs := target.getAppArgs[3]!
  unless rhs.isAppOfArity ``HMul.hMul 6 &&
      rhs.getAppArgs[5]!.isAppOfArity ``HPow.hPow 6 do
    throwError "original strain transport: the exact original scale power changed"
  let originalScale := rhs.getAppArgs[5]!.getAppArgs[4]!
  let currentScale := d.source[4]!
  withLocalDeclNoLocalInstanceUpdate `R .default (mkConst ``Real) fun R => do
    let predicate ← mkLambdaFVars #[R] (target.replace fun e =>
      if e == originalScale then some R else none)
    termWith [(`Rold,originalScale),(`Rnew,currentScale),(`pred,predicate),(`h,proof)]
      "Eq.mp (congrArg pred (show Rold = Rnew from rfl)) h"

elab "transport_original_primary_strain_input" : command => liftTermElabM do
  let _ ← getConstInfo currentIdentity
  let currentAxioms ← collectAxioms currentIdentity
  unless currentAxioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original strain transport: unfinished current identity {currentAxioms}"
  withData fun d => do
    withLocalDeclNoLocalInstanceUpdate `hRawStrain .default d.rawStatement fun hRaw => do
      let args := inputArguments d d.cost
      let target := app (root ++ `primary_strain_input) args
      let pointwise ← bodyAt (root ++ `primary_strain_input) args
      let subset := Expr.proj ``And 1
        (app `JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCore.core_subsets
          d.native[:44].toArray)
      let proof ← forallBoundedTelescope pointwise (some 1) fun point rest => do
        unless point.size == 1 && rest.isForall do
          throwError "original strain transport: the exact common-core point changed"
        withLocalDeclNoLocalInstanceUpdate `hx .default rest.bindingDomain! fun hx => do
          let physical := mkAppN subset #[point[0]!,hx]
          let original := mkAppN hRaw #[point[0]!,physical]
          let atCurrent ← changeCurrent d original
          let atScale ← changeScale d atCurrent
          mkLambdaFVars (point.push hx) atScale
      for producer in #[currentIdentity,
          `JanetCartan.PhysicalMean.OriginalSelectedMeanResidualCore.core_subsets] do
        unless proof.getUsedConstants.contains producer do
          throwError "original strain transport: actual geometry producer was not applied {producer}"
      save `primary_strain_input_of_raw (d.parameters.push hRaw) proof target

end JanetCartan.RevisedUniform.OriginalStepStrainTransportTemplate
end
