module

public import JanetCartan.Iteration.PhysicalPrimary.OriginalObservedSolver
public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSourceApplication
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.ExtendedSourceAgreement
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.InitializedDecayApplication.MeanCorrectedSource.ObservedCore.Coordinates
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalPhysicalPhaseTemplate

/-! # Actual uncut solutions of the native stress and their ordered parameter classes
The physical source has already been identified on its original plateau. Apply
the full solver to those exact quadratures. No `hsource`, ordinary inverse
estimate, global solver bound, or phase extension is supplied by the caller. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalObservation
open PhysicalInitialization PhysicalSeed

/-- Coordinates on the literal initial-spin/direction parameter product. -/
def parameterDimension (d : ℕ) := Module.finrank ℝ (Euclidean 3 × Euclidean d)

def parameterCoordinates (d : ℕ) :
    Euclidean (parameterDimension d) ≃L[ℝ] Euclidean 3 × Euclidean d :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin

/-- A supported stress only needs the original open immersion chart. -/
theorem source_rectangle_in_chart {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn) :
    OriginalProtected.Xsrc hn a ⊆ ball (0 : Euclidean n) (OriginalBoundary.R hn) :=
  closedBall_subset_ball ((OriginalProtected.sourceRadius_lt_b hn).trans (OriginalBoundary.b_lt_R hn))

/-- The uncut normalized response uses the extended frame and the raw wave
uses the projected frame. They agree on the WHOLE tensor support, independently
of the cutoff shoulders, so the same smooth-source solver can be used. -/
theorem frames_on_rectangle {n N : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (F : Euclidean n → Euclidean N) (p : BallExtension.Parameters (Euclidean n))
    (hc : p.center = 0) (hr : p.radius = OriginalBoundary.b hn)
    (Qext Q : Euclidean n → Fin n → MetricTensor n)
    (hext : Qext = ProtectedFlow.extendedProjectedStress p F)
    (hraw : Q = ProjectedStressFrame.projectedStress F) :
    EqOn Qext Q (OriginalProtected.Xsrc hn a) := by
  rw [hext,hraw]
  apply (ProtectedFlow.affineFrameExtension_eqOn p _).mono
  rw [hc,hr]
  exact closedBall_subset_closedBall (OriginalProtected.sourceRadius_lt_b hn).le

theorem raw_components {n : ℕ} {U : Set (Euclidean n)}
    (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U) :
    ∀ j, ContDiffOn ℝ ∞ (fun x ↦ Q x j) U := contDiffOn_pi.mp hQ

end JanetCartan.PhysicalPrimary.OriginalPhysicalObservation
end

public meta section
namespace JanetCartan.PhysicalPrimary.OriginalPhysicalObservationTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate OriginalPhysicalPhaseTemplate
private def ns := `JanetCartan.PhysicalPrimary.OriginalPhysicalObservation
private def frame := `JanetCartan.PhysicalPrimary.OriginalUncutSource.Physical
private def source := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Source
private def family := `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Family
private def obs := `JanetCartan.PhysicalPrimary.OriginalObservationPhase
private def ind := `JanetCartan.PhysicalPrimary.OriginalPrimaryInverseIndex
private def geo := `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry
private def masks := `JanetCartan.PhysicalPrimary.OriginalSourceMasks
private def cmp := `JanetCartan.PhysicalPrimary.OriginalUncutSource
private def stress := `JanetCartan.PhysicalPrimary.OriginalPhysicalStress
private def solver := `JanetCartan.PhysicalPrimary.OriginalObservedSolver
private def uncut := `JanetCartan.PhysicalPrimary.OriginalUncutSolver
private def co := `JanetCartan.ArbitraryAccuracy.SelectedLocalization.MeanCorrectedSource.ObservedCore.Coordinates
private def target := `JanetCartan.PhysicalPrimary.OriginalUncutObservation.fixedSolverParameterEnvelope_joint_and_parameter_classes_of_uncut
private def appl (n : Name) (xs : Array Expr) := mkAppN (mkConst n) xs
private def emit (k : Name) (xs : Array Expr) (v : Expr) (data := false) (t : Option Expr := none) : MetaM Expr := do
  let r ← store (ns ++ k) xs v data t
  addDocStringCore (ns ++ k) "Actual solution of the same original real and imaginary stress admissions with the uncut full inverse, and its ordered Fourier representatives; no analytic solver or class assumption (app:ch_response:eq:response-actual-solver-formula)."
  return r
private def byLemma (goal : Expr) (name : Name) : MetaM Expr := do
  let g ← mkFreshExprMVar goal
  unless (← g.mvarId!.apply (← mkConstWithFreshMVarLevels name)).isEmpty do
    throwError "native observed application: {name} left goals"
  instantiateMVars g

/-- Assemble only the existing theorem's declared arguments. Explicit
arguments are read by NAME, including the physical/parameter dimensions;
the only synthesized components are ordinary product typeclass instances. -/
private def application (name : Name) (v : Array (Name × Expr)) : MetaM Expr := do
  let mut t := (← getConstInfo name).type
  let mut r := mkConst name
  while let .forallE key dom b bi := t do
    let x ← if let some (_,x) := v.find? (·.1 == key) then pure x
      else if bi == .instImplicit then synthInstance dom
      else throwError "native observed application: argument {key} of {name}"
    r := mkApp r x
    t := b.instantiate1 x
  pure r

elab "construct_original_physical_observation_part " st:num : command => liftTermElabM do
  let st := st.getNat
  withPhysicalPhaseInputs fun xs base s ph => do
    let fixed := s[:23].toArray
    let d := s[0]!
    let n := mkApp (mkConst ``Nat.succ) d
    let mask (k : Name) := appl (masks ++ k) fixed
    let va := (← OriginalLocalWaveGeometryTemplate.bodyAt (geo ++ `parameter_window) s).getAppArgs
    let cn := #[n,s[1]!,va[23]!,va[24]!]
    let W := appl (cmp ++ `parameterComparisonWindow) cn
    let w := appl (cmp ++ `parameterComparisonWindow_spec) cn
    let φ := appl (ind ++ `phase) xs
    let Z := (← inferType φ).bindingDomain!
    let hU₀ := appl (cmp ++ `Actual.chart_in_source) (fixed.push va[23]!)
    let hrect ← mkAppM ``Set.Subset.trans #[mask `χ₂_support_chart,hU₀]
    let Q := appl (frame ++ `Raw.Q) s
    let Qext := appl (frame ++ `Observed.Q) ph
    let Qv := Expr.proj ``Subtype 0 Q
    let tQ := Expr.proj ``And 0 (.proj ``Subtype 1 Q)
    let hQ := appl (ns ++ `raw_components) #[n,(← inferType tQ).appArg!,Qv,tQ]
    let hp := appl (ns ++ `source_rectangle_in_chart) #[n,s[1]!,va[23]!]
    let hSU ← mkAppM ``Set.Subset.trans #[hrect,hp]
    if st == 0 then
      let F := appl (frame ++ `Raw.F) s
      let N := mkApp (mkConst `JanetCartan.embeddingDimension) n
      let eq := appl (ns ++ `frames_on_rectangle) #[n,N,s[1]!,va[23]!,F,s[4]!,s[5]!,s[6]!,
        .proj ``Subtype 0 Qext,Qv,appl (frame ++ `Observed.frame) ph,appl (frame ++ `Raw.frame) s]
      discard <| emit `frames_on_tensor_support xs (← mkAppM `Set.EqOn.mono #[hrect,eq])
      discard <| emit `support_in_chart xs hSU
      return
    if st != 1 then throwError "unknown observation part"
    let member := appl (ind ++ `point) xs
    let point (k : Name) := appl (family ++ `Point ++ k) (base.push member)
    let r ← OriginalLocalWaveGeometryTemplate.bodyAt (family ++ `Point.R) (base.push member)
    unless r.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.Native.Rcomplex 38 do
      throwError "native observation: lost normalized residual"
    let weak := r.getAppArgs[:32].toArray ++ #[s[39]!,r.getAppArgs[33]!] ++ s[41:45].toArray
    let op (k : Name) := appl (solver ++ k) weak
    let classicalOp (k : Name) := appl (uncut ++ k) weak
    let stc (k : Name) := appl (family ++ `Static ++ k) base[:41].toArray
    let stressField (k : Name) := appl (stress ++ k) xs
    let hη := mask `χsrc_smooth
    let hW := stc `hW
    let U := (← inferType tQ).appArg!
    let openU ← byLemma (← mkAppM `IsOpen #[U]) `Metric.isOpen_ball
    let χ := (← inferType (mask `χ₂_smooth)).appArg!
    let raw := appl `JanetCartan.PhysicalPrimary.OriginalLocalWaves.raw s
    let F := appl `JanetCartan.PhysicalPrimary.OriginalLocalWaves.F s
    let tensor ← withLocalDeclD `c Z fun c => do
      let field ← withLocalDeclD `y (← inferType F).bindingDomain! fun y => do
        mkLambdaFVars #[y] (mkApp raw (← mkAppM ``Prod.mk #[y,c]))
      mkLambdaFVars #[c] (← mkAppM `JanetCartan.CorrectedAtoms.complexAtomicSource #[F,χ,field])
    let tensor ← emit `tensor xs tensor true
    let coords := appl (ns ++ `parameterCoordinates) #[d]
    let p := appl (ns ++ `parameterDimension) #[d]
    let hφ := appl (obs ++ `joint_smooth) ph
    let xType := (← inferType φ).bindingBody!.bindingDomain!
    let total ← mkAppOptM ``Set.univ #[some xType]
    let domain ← mkAppM `Set.prod #[W,total]
    let mut restrictTy := (← getConstInfo `ContDiff.contDiffOn).type
    let mut restrictArgs : Array (Option Expr) := #[]
    while let .forallE key _ b _ := restrictTy do
      restrictArgs := restrictArgs.push (if key == `s then some domain else none)
      restrictTy := b
    let hφ ← mkAppOptM `ContDiff.contDiffOn (restrictArgs.set! (restrictArgs.size-1) (some hφ))
    let hphaseSupport := appl (obs ++ `support) ph
    let hsφ ← withLocalDeclD `c Z fun c => do
      withLocalDeclD `hc (← mkAppM `Membership.mem #[W,c]) fun hc =>
        mkLambdaFVars #[c,hc] (mkApp hphaseSupport c)
    let χ₃ := appl `JanetCartan.PhysicalInitialization.OriginalRegular.χ₃ fixed
    let center := (← inferType χ₃).appArg!
    let sourceSupport := (← inferType hrect).getAppArgs[(← inferType hrect).getAppArgs.size-2]!
    let v := #[( `d,d),(`p,p),(`Z,Z),(`Q,Qv),(`η,(← inferType hη).appArg!),(`sourceSupport,sourceSupport),
      (`U,U),(`W,stc `W),(`hU,openU),(`hW,hW),(`hQ,hQ),(`hη,hη),(`hSU,appl (ns ++ `support_in_chart) xs),
      (`solver,classicalOp `uncut_solver),(`S,point `Op),(`hSreal,op `solver_real),(`R,point `R),
      (`hRreal,point `hreal),(`hR,point `hR),(`center,center),(`χ₃,χ₃),(`hsolverAE,op `smooth_solver_ae),
      (`V,W),(`hV,Expr.proj ``And 0 w),(`tensor,tensor),(`hre,stressField `real_admission),
      (`him,stressField `imag_admission),(`τ,s[47]!),(`φ,φ),(`hφ,hφ),(`g,stressField `forcing),
      (`hm,stressField `forcing_memLp),(`hsource,stressField `uncut_class),
      (`hsolver,classicalOp `uncut_solver_smooth),(`hs₃,classicalOp `source_support),
      (`CI,op `I.cost),(`highI,op `I.high),(`CS,op `S.cost),(`highS,op `S.high),
      (`hCI,op `I.cost_nonneg),(`hhighI,op `I.high_nonneg),(`hCS,op `S.cost_nonneg),(`hhighS,op `S.high_nonneg),
      (`hInv,op `I.bound),(`hS,op `S.bound),(`e,appl (co ++ `Jcoord) #[d]),
      (`he,appl (co ++ `measurePreserving_Jcoord) #[d]),(`coords,coords),(`X,stc `X),(`Xφ,stc `Xφ),
      (`hX,stc `hX),(`hXφ,stc `hXφ),(`hg,stressField `forcing_smooth),(`hgs,stressField `forcing_support),(`hsφ,hsφ)]
    let proof ← application target v
    let result ← emit `joint_and_classes xs proof
    discard <| emit `solver_joint_smooth xs (.proj ``And 0 result)
    discard <| emit `observation_smooth xs (.proj ``And 0 (.proj ``And 1 result))
    discard <| emit `ordered_classes xs (.proj ``And 1 (.proj ``And 1 result))
    withLocalDeclD `c Z fun c => do
      withLocalDeclD `hc (← mkAppM `Membership.mem #[W,c]) fun hc => do
        let ae ← application `JanetCartan.PhysicalPrimary.OriginalUncutObservation.fixedSolverParameterEnvelope_ae_uncut_complex_inverse
          (v ++ #[(`c,c),(`hc,hc)])
        discard <| emit `reduced_ae (xs ++ #[c,hc]) ae
    logInfo "original physical stress through uncut full inverse: jointly smooth actual reduced envelope and ordered scalar representatives with literal Fourier norm identities"

end JanetCartan.PhysicalPrimary.OriginalPhysicalObservationTemplate
end
