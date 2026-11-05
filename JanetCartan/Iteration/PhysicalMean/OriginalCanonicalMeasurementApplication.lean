module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalMeasurementTemplate
public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalObservation
public import JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalBackgroundHermitianTemplate
import all JanetCartan.Iteration.PhysicalMean.OriginalCanonicalDerivativeTemplate
public meta import Lean

/-!
# Apply the same common physical measurement to the canonical source

The common measurement is retained by the original native50 data; the row is
not selected or changed. Its original support, already compact inside the cell,
gives the auxiliary periodic measurement, and its nonzero set lies in the
original source-observation plateau (`app:ch_mean_pairs:defn:mean-canonical`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalMean.OriginalCanonicalMeasurementApplication
open ContinuumRow

private theorem physical_measurement_box {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) {μ : ℝ} (hμ : 0 < μ) :
    tsupport (Sampling.canonicalSamplingMeasurement Q hμ) ⊆ {x | ∀ i, |x i| ≤ 4*μ} := by
  intro x hx i
  exact (PiLp.norm_apply_le x i).trans (mem_closedBall_zero_iff.mp
    (FixedCutoffs.physical_tsupport_four hμ 1
      (Sampling.tsupport_canonicalSamplingMeasurement Q hμ hx)))

private theorem physical_measurement_observation {n : ℕ}
    (Q : Euclidean n → Fin n → MetricTensor n) {μ : ℝ} (hμ : 0 < μ)
    (x : Euclidean n) (hx : Sampling.canonicalSamplingMeasurement Q hμ x ≠ 0) :
    FixedCutoffs.physical hμ 2 x = 1 :=
  (OriginalCanonicalDerivativeTemplate.source_germ_on_measurement_support hμ x
    (Sampling.tsupport_canonicalSamplingMeasurement Q hμ (subset_tsupport _ hx))).self_of_nhds

end JanetCartan.PhysicalMean.OriginalCanonicalMeasurementApplication
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalCanonicalMeasurementApplication
open Lean Meta Elab Command
open OriginalBackgroundHermitianTemplate

private def root := `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement
private def background := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
private def observation := `JanetCartan.PhysicalMean.OriginalCanonicalDerivative

private def save (name : Name) (params : Array Expr) (value : Expr)
    (data : Bool) (expected : Option Expr := none) : MetaM Expr := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  let env ← getEnv
  for closed in #[type,value] do
    let missing := closed.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "actual common measurement: missing producer constants {missing.toList}"
  if type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasLooseBVars || type.hasSorry ||
      value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasLooseBVars || value.hasSorry then
    throwError "actual common measurement: open or row-selected field {name}"
  let name := root ++ name
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The SAME original native50 common current measurement at centered representatives, with no new cutoff, row choice, or inverse (app:ch_mean_pairs:defn:mean-canonical)."
  return mkAppN (mkConst name) params

elab "construct_actual_canonical_measurement " mode:num : command => liftTermElabM do
  withTransparency .reducible <| withActualRow fun d => do
    let params := d.parameters[:50].toArray
    let n := d.raw13[0]!
    let C := mkAppN (mkConst (background ++ `commonC)) params
    let Cper := mkAppN (mkConst (root ++ `Cper)) params
    let value := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement.nativeMeasurement) #[n,C]
    let physical := d.mean70[37]!
    unless physical.isAppOfArity `JanetCartan.Sampling.canonicalSamplingMeasurement 4 do
      throwError "actual common measurement: changed literal original coefficient"
    let pa := physical.getAppArgs
    let original22 := d.native64[:22].toArray
    match mode.getNat with
    | 0 =>
      discard <| save `Cper params value true
      logInfo "actual common Cper50: literal SAME commonC at centered representatives; no row or new cutoff"
    | 1 =>
      let hC := mkAppN (mkConst (background ++ `commonC_smooth)) params
      let hcell := mkAppN (mkConst (observation ++ `observation_cell)) original22
      let cellType ← inferType hcell
      unless cellType.isAppOfArity ``LT.lt 4 do throwError "actual common measurement: changed cell gap"
      let b := cellType.getAppArgs[2]!
      let box := mkAppN (mkConst ``physical_measurement_box) pa
      let proof := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement.nativeMeasurement_smooth)
        #[n,C,hC,b,hcell,box]
      let target := (← inferType proof).replace fun e => if e == value then some Cper else none
      discard <| save `Cper_smooth params proof false (some target)
      logInfo "actual common Cper_smooth50: original smooth commonC and original support gap; no extra factor"
    | 2 =>
      withLocalDeclNoLocalInstanceUpdate `z .default (mkApp (mkConst `JanetCartan.Torus) n) fun z => do
        let proof := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalCanonicalMeasurement.nativeMeasurement_apply) #[n,C,z]
        let target := (← inferType proof).replace fun e => if e == value then some Cper else none
        discard <| save `Cper_native (params.push z) proof false (some target)
    | 3 =>
      let observationProof := mkAppN (mkConst ``physical_measurement_observation) pa
      forallBoundedTelescope (← inferType observationProof) (some 2) fun xh _ => do
        unless xh.size == 2 do throwError "actual common measurement: missing physical nonzero premise"
        discard <| save `observation_eq_one (params ++ xh) (mkAppN observationProof xh) false
        logInfo "actual common measurement observation52: SAME physical source cutoff equals one wherever commonC is nonzero"
    | _ => throwError "actual common measurement: unknown publication stage"

end JanetCartan.PhysicalMean.OriginalCanonicalMeasurementApplication
end
