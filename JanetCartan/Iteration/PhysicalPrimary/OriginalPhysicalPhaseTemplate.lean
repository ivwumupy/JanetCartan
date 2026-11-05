module

public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalPrimaryInverseIndex
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSourceTemplate

/-! The phase comparison is constructed on two *small* native spines before
specializing to the physical carrier.  In particular, no proof searches through
an expanded family index to rediscover equality of the two finite-map fields. -/

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalPhaseTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalLocalWaveGeometryTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalUncutSource.Physical
private def obs := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def strong := `JanetCartan.PhysicalPrimary.OriginalRetardedCurrent
private def index := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def family := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def reg := `JanetCartan.PhysicalInitialization.OriginalRegular
private def source := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def appl (name : Name) (xs : Array Expr) := mkAppN (mkConst name) xs
private def emit (name : Name) (xs : Array Expr) (v : Expr) (data := false)
    (t : Option Expr := none) : MetaM Expr := do
  let h ← store (ns ++ name) xs v data t
  addDocStringCore (ns ++ name) "The actual raw/extended phase on the original physical carrier, using the same finite map, fixed reference and source plateau (app:ch_response:eq:response-actual-solver-formula)."
  return h
private def body (value : Expr) : MetaM Expr := do
  let some v := (← getConstInfo value.getAppFn.constName!).value? (allowOpaque := true)
    | throwError "physical phase: missing native body {value.getAppFn}"
  Core.betaReduce (v.beta value.getAppArgs)

elab "retain_source53_observation39_phase_frames" : command => liftTermElabM do
  withSourcePrefix 53 fun s => do
    let sc ← sourceCurrent s
    let da := sc.dataArgs
    let q := appl `JanetCartan.PhysicalPrimary.LeadingData.Q (da.push sc.datum)
    let F ← emit `Raw.F s da[30]! true
    let Q ← emit `Raw.Q s q true
    let projected ← mkAppM `JanetCartan.ProjectedStressFrame.projectedStress #[F]
    discard <| emit `Raw.frame s (← mkEqRefl projected) false
      (some (← mkEq (.proj ``Subtype 0 Q) projected))
    logInfo "native Source53 raw projected frame retained"
  forallBoundedTelescope (← getConstInfo (obs ++ `φ_eq_retained)).type (some 39) fun ph _ => do
    let he := appl (obs ++ `φ_eq_retained) ph
    let eq ← body he
    unless eq.isAppOfArity (obs ++ `canonical_phase_eq_retained) 5 do
      throwError "physical phase: lost the explicit retained phase"
    let Qext := eq.getAppArgs[4]!
    unless Qext.isAppOfArity (strong ++ `sourceFrame) 39 do
      throwError "physical phase: lost current38 frame in its retained patch"
    let hQ := appl (strong ++ `sourceFrame_val) Qext.getAppArgs
    let q := (← inferType hQ).getAppArgs[2]!
    let q ← body q
    unless q.isAppOf `JanetCartan.ProtectedFlow.extendedProjectedStress do
      throwError "physical phase: actual normalized current is {q.getAppFn}, not the prescribed extension"
    let F ← emit `Observed.F ph q.getAppArgs.back! true
    let Q ← emit `Observed.Q ph Qext true
    let extended ← mkAppM `JanetCartan.ProtectedFlow.extendedProjectedStress #[ph[4]!,F]
    discard <| emit `Observed.frame ph hQ false (some (← mkEq (.proj ``Subtype 0 Q) extended))
    logInfo "native Observation39 extended frame retained"

/-- Source input order is already native here. Normalize only the dynamic
projections of the concrete physical index, not its entire dependent telescope. -/
def withPhysicalPhaseInputs (go : Array Expr → Array Expr → Array Expr → Array Expr → MetaM Unit) : MetaM Unit :=
  OriginalPrimaryInverseIndex.withPhysicalInputs fun xs base s member _ => do
    let phase ← body (appl (family ++ `Point.φ) (base.push member))
    unless phase.isAppOfArity (obs ++ `φ) 39 do throwError "physical phase: lost observation39"
    let ph := phase.getAppArgs[:33].toArray ++ #[s[39]!,phase.getAppArgs[34]!] ++ s[41:45].toArray
    go xs base s ph

elab "construct_original_physical_source_phase" : command => liftTermElabM do
  withPhysicalPhaseInputs fun xs _ s ph => do
    let fixed := s[:23].toArray
    let patch := ph[32]!
    let F := appl (ns ++ `Raw.F) s
    let Q := appl (ns ++ `Raw.Q) s
    let Qext := appl (ns ++ `Observed.Q) ph
    let hraw := appl (ns ++ `Raw.frame) s
    let hext := appl (ns ++ `Observed.frame) ph
    let phase (key : Name) := appl (reg ++ `Phase ++ key) (fixed.push patch)
    let φ := appl (index ++ `phase) xs
    let he := appl (obs ++ `φ_eq_retained) ph
    let n := mkApp (mkConst ``Nat.succ) s[0]!
    let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
    let result := appl (source ++ `phase_on_native_source_rectangle)
      #[n,N,s[1]!,patch,F,s[4]!,s[5]!,s[6]!,Q,Qext,hraw,hext,phase `χ,phase `fact3,φ,he]
    discard <| emit `phase_on_source_rectangle xs result
  logInfo "same physical raw/extended frames, full cutoff, phase and inverse rate: original protected rectangle"

elab "restrict_original_physical_source_phase" : command => liftTermElabM do
  withPhysicalPhaseInputs fun xs _ s ph => do
    let fixed := s[:23].toArray
    let patch := ph[32]!
    let v := (← body (appl (geo ++ `parameter_window) s)).getAppArgs
    unless v.size == 25 do throwError "physical phase: lost selected cell"
    let V := appl (masks ++ `V) v
    let hVC := appl (masks ++ `V_closure_Csrc) v
    let whole := appl (ns ++ `phase_on_source_rectangle) xs
    let hs (name : Name) := appl (source ++ `Actual ++ name) (fixed.push patch)
    let hchart := hs `chart_in_source
    let mkSub (name : Name) := mkAppM `Set.Subset.trans #[appl (masks ++ name) fixed,hchart]
    for (key,h) in #[( `phase_on_chart,hchart),( `phase_on_source,← mkSub `χ₂_support_chart),
        (`phase_on_solver_source,← mkSub `χ₃_support_chart),
        (`phase_on_physical_ball,hs `physical_ball_in_source),(`phase_on_output,hs `outputSupport_in_source)] do
      let h ← forallBoundedTelescope (← inferType whole) (some 1) fun z _ => do
        let c := z[0]!
        withLocalDeclD `hc (← mkAppM `Membership.mem #[V,c]) fun hc => do
          let hC := mkAppN hVC #[c,← mkAppM `subset_closure #[hc]]
          let result ← mkAppM `Set.EqOn.mono #[h,mkAppN whole #[c,hC]]
          mkLambdaFVars #[c,hc] result
      discard <| emit key xs h
  logInfo "physical phase on same source, chi3 shoulders, chart, whole physical ball and uncut output"

end JanetCartan.PhysicalPrimary.OriginalPhysicalPhaseTemplate
end
