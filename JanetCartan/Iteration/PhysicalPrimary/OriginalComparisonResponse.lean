module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalComparisonResponseBase
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalObservation
public import JanetCartan.Iteration.PhysicalPrimary.OriginalFullResponseSupported

/-! # Same original response on every admitted full tensor
The fixed comparison cutoff is proof-only; the globally uncut native response
has the same values on the whole physical space for each parameter in V. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalComparisonResponseTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalPhysicalPhaseTemplate OriginalLocalWaveGeometryTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalComparisonResponse
private def rec := `JanetCartan.PhysicalPrimary.OriginalFullResponse
private def out := `JanetCartan.PhysicalPrimary.OriginalFullResponseCompact
private def phy := `JanetCartan.PhysicalPrimary.OriginalPhysicalObservation
private def fam := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def source := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def wave := `JanetCartan.PhysicalPrimary.OriginalLocalWaves
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def support := `JanetCartan.PhysicalPrimary.OriginalSolverSupport
private def appl (k : Name) (xs : Array Expr) := mkAppN (mkConst k) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ k) xs v data t
  addDocStringCore (ns ++ k) "This same physical response agrees with the proof localization on genuinely admitted native tensors only; the original whole-space operator is not recut (app:ch_response:eq:response-actual-solver-formula)."
  return h
elab "compare_original_uncut_response_on_tensors" : command => liftTermElabM do
  withPhysicalPhaseInputs fun xs base s ph => do
    let pt := appl (ind ++ `point) xs
    let r ← bodyAt (fam ++ `Point.R) (base.push pt)
    let weak := r.getAppArgs[:32].toArray ++ #[s[39]!,r.getAppArgs[33]!] ++ s[41:45].toArray
    let d := (← bodyAt (rec ++ `B) weak).getAppArgs
    unless d.size == 14 do throwError "native uncut comparison: expected exact original response"
    let fixed := s[:23].toArray
    let patch := ph[32]!
    let n := d[0]!
    let ξ := appl (ns ++ `proofCutoff) #[n,s[1]!,patch]
    let raw := appl (source ++ `Physical.Raw.Q) s
    let Q := Expr.proj ``Subtype 0 raw
    let ht := Expr.proj ``And 0 (.proj ``Subtype 1 raw)
    let U := (← inferType ht).appArg!
    let hU ← mkFreshExprMVar (← mkAppM `IsOpen #[U])
    unless (← hU.mvarId!.apply (← mkConstWithFreshMVarLevels `Metric.isOpen_ball)).isEmpty do
      throwError "native uncut comparison: retained raw open domain changed"
    let hU ← instantiateMVars hU
    let hQ := appl (phy ++ `raw_components) #[n,U,Q,ht]
    let hS := appl (phy ++ `support_in_chart) xs
    let hframes := appl (phy ++ `frames_on_tensor_support) xs
    let hOut := appl (source ++ `Actual.outputSupport_in_source) (fixed.push patch)
    let hSol := appl (out ++ `uncut_solver_support) weak
    let hSol ← forallBoundedTelescope (← inferType hSol) (some 1) fun vv _ => do
      mkLambdaFVars vv (← mkAppM ``Set.Subset.trans #[mkAppN hSol vv,hOut])
    let hSc ← mkAppM ``Set.Subset.trans #[appl (support ++ `χ₂_support_output) fixed,hOut]
    let B := appl (rec ++ `B) weak
    let rawFixed ← mkAppM `JanetCartan.CorrectedAtoms.fixedSmoothSolverAmbientExtension
      #[d[2]!,Q,d[4]!,hU,hQ,d[10]!,hS,d[12]!,d[13]!,ξ]
    let B' ← emit `fixed xs rawFixed true
    let proof ← mkAppM (ns ++ `admitted_eq) #[d[2]!,d[3]!,Q,d[4]!,d[8]!,hU,d[9]!,hQ,d[10]!,d[11]!,hS,hframes,d[12]!,d[13]!,ξ,hSol,hSc]
    let orig ← bodyAt (rec ++ `B) weak
    let t := (← inferType proof).replace fun e => if e == rawFixed then some B' else if e == orig then some B else none
    let he ← emit `on_admitted xs proof false (some t)
    let V := appl (geo ++ `parameter_window) s
    let Z := (← inferType (appl (ind ++ `phase) xs)).bindingDomain!
    withLocalDeclD `c Z fun c => do
      withLocalDeclD `hc (← mkAppM `Membership.mem #[V,c]) fun hc => do
        let hh := appl (wave ++ `source_quadratures) (s ++ #[c,hc])
        let tensor := mkApp (appl (phy ++ `tensor) xs) c
        let result ← mkAppM (ns ++ `complex_agreement) #[B,B',he,tensor,.proj ``And 0 hh,.proj ``And 1 hh]
        let χ := (← inferType (appl `JanetCartan.PhysicalPrimary.OriginalSourceMasks.χ₂_smooth fixed)).appArg!
        let primary (b : Expr) := mkAppM `JanetCartan.CorrectedAtoms.fullPrimaryResponse
          ((#[`T,`Q,`F,`row,`col,`Φ,`Y].map fun k => appl (wave ++ k) s) ++ #[χ,b,s[47]!,appl (wave ++ `scalar) s,c])
        let v ← primary B
        let v' ← primary B'
        discard <| emit `whole_response_eq (xs ++ #[c,hc]) result false (some (← mkEq v v'))
  logInfo "all admitted real tensors and both true raw quadratures on the doubled parameter window give the same global response under the proof-only cutoff; no output recut of the original operator"

end JanetCartan.PhysicalPrimary.OriginalComparisonResponseTemplate
end

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 16000
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
compare_original_uncut_response_on_tensors
