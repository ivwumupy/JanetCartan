module

public import JanetCartan.Iteration.PhysicalNormalInverse.MeasurementProfiles
public import JanetCartan.Iteration.PhysicalInitialization.CurrentInverse
public import JanetCartan.Iteration.PhysicalInitialization.OriginalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumInverse.IncidenceSourceDomain
public meta import Lean

/-!
# Actual common-measurement profiles on the native original current

The SAME original H/source dilation and once-capped measurement radius supply
the physical measurement producer. A single budget is chosen at reserve
`rStar - 2`, before any history, selected row or density. Lower reserves keep
that identical budget. The actual current frame supplies the literal stress
coefficient, not a profile-success premise. Consumers are the SAME Mean and
Comparison continuations on the original sampling radius.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.PhysicalNormalInverse.OriginalMeasurementProfilesApplication
open Set

private theorem lower_reserve {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set E} {f : E → F}
    {rStar rpar : ℕ} {L : ℝ} {C : ℕ → ℝ}
    (hreserve : 2 + rpar ≤ rStar) (hL : 1 ≤ L) (hC : ∀ j, 0 < C j)
    (hp : HasDerivativeProfile K f (rStar - 2) L C) :
    HasDerivativeProfile K f rpar L C := by
  intro j
  exact (hp j).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hL (by omega : j - (rStar - 2) ≤ j - rpar)) (hC j).le)

private theorem available_reserve {rStar : ℕ} (h : 14 ≤ rStar) :
    8 ≤ rStar ∧ 2 + (rStar - 2) ≤ rStar := by omega

private theorem measurement_inside {n : ℕ} (hn : 5 ≤ n) {μ R : ℝ} (hμ : 0 < μ)
    (hSource : Metric.closedBall (0 : Euclidean n) (6 * μ) ⊆ Metric.ball 0 R) :
    4 * μ < R := by
  let i : Fin n := ⟨0, by omega⟩
  let x := EuclideanSpace.single i (4 * μ)
  have hx : ‖x‖ = 4 * μ := by
    simp only [x, EuclideanSpace.single, PiLp.norm_single, Real.norm_of_nonneg (by positivity : 0 ≤ 4 * μ)]
  have hmem : x ∈ Metric.closedBall (0 : Euclidean n) (6 * μ) := by
    rw [Metric.mem_closedBall, dist_zero_right, hx]
    linarith
  simpa only [Metric.mem_ball, dist_zero_right, hx] using hSource hmem

end JanetCartan.PhysicalNormalInverse.OriginalMeasurementProfilesApplication
end

public meta section
namespace JanetCartan.PhysicalNormalInverse.OriginalMeasurementProfilesApplication
open Lean Meta Elab Command Term

private def root := `JanetCartan.PhysicalNormalInverse.OriginalMeasurement
private def currentNS := `JanetCartan.PhysicalInitialization.OriginalCurrent
private def selectedNS := `JanetCartan.PhysicalSeed.SelectedBoundary
private def originalNS := `JanetCartan.PhysicalSeed.OriginalBoundary
private def chartNS := `JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart

private def store (name : Name) (params : Array Expr) (value : Expr)
    (data := false) (target : Option Expr := none) : MetaM Expr := do
  let resultType := target.getD (← inferType value)
  unless ← isDefEq resultType (← inferType value) do
    throwError "original measurement: target mismatch {name}"
  let type ← instantiateMVars (← mkForallFVars params resultType)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  if value.hasFVar || value.hasMVar || value.hasLevelMVar || value.hasSorry ||
      type.hasFVar || type.hasMVar || type.hasLevelMVar || type.hasSorry then
    throwError "original measurement: incomplete declaration {name}"
  let name := root ++ name
  if data then
    addDecl (.defnDecl {name, levelParams := [], type, value, hints := .abbrev, safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name, levelParams := [], type, value}) (forceExpose := true)
  return mkAppN (mkConst name) params

private def component (proof : Expr) (index : Nat) : MetaM Expr := do
  let mut proof := proof
  for _ in [:index] do proof ← mkAppM ``And.right #[proof]
  let type ← whnf (← inferType proof)
  if type.isAppOfArity ``And 2 then mkAppM ``And.left #[proof] else pure proof

private def selectedArgs (fixed : Array Expr) : Array Expr :=
  fixed[:21].toArray.set! 20
    (mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[fixed[0]!, fixed[1]!, fixed[20]!])

private def chartArgument (application : Expr) (name : Name) : MetaM Expr := do
  let info ← getConstInfo application.getAppFn.constName!
  forallBoundedTelescope info.type (some application.getAppNumArgs) fun args _ => do
    let some index ← (List.range args.size).findM? (fun i =>
        return (← getFVarLocalDecl args[i]!).userName == name)
      | throwError "original measurement: missing actual chart input {name}"
    return application.getAppArgs[index]!

/-- Cache one actual common-cutoff measurement budget at the strongest available
reserve, independently of the later row, density, history and desired reserve. -/
elab "cache_original_measurement_profiles" : command => liftTermElabM do
  let info ← getConstInfo (currentNS ++ `current)
  forallBoundedTelescope info.type (some 31) fun fixed _ => do
    unless fixed.size == 31 do throwError "original measurement: expected original31"
    let n := fixed[0]!
    let hn := fixed[1]!
    let selected := selectedArgs fixed
    let field (name : Name) := mkAppN (mkConst (selectedNS ++ name)) selected
    let boundary (name : Name) := mkAppN (mkConst (originalNS ++ name)) #[n, hn]
    let hSigma ← mkAppM ``And.left #[fixed[22]!]
    let hSigmaOne ← mkAppM `le_trans #[← mkAppM ``And.right #[fixed[22]!],
      mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.StrongCurrent.Cap.fact2) fixed[:21].toArray]
    let H := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.H) fixed[:18].toArray
    let G ← mkAppM ``JanetCartan.sourceDilationReference #[H, hSigma, hSigmaOne]
    let domainEq := mkAppN (mkConst `JanetCartan.PhysicalSeed.ReferenceBoundary.fact5) fixed[:18].toArray
    let radiusEq ← mkAppM ``congrArg #[mkConst ``JanetCartan.LocalDomain.chartRadius, domainEq]
    let hR ← mkAppM `lt_of_lt_of_eq #[boundary `R_lt_chartRadius, ← mkAppM ``Eq.symm #[radiusEq]]
    let mu := field `rMeasure
    let hMu := field `hrMeasure
    let hNonempty ← mkAppM `JanetCartan.ContinuumInverse.retained_incidence_channel_nonempty
      #[hn, ← component (boundary `hD) 0, field `centers, field `εcover, field `fact5, field `fact7]
    let outer := field `fact23
    let (z, V, hOuter, hRU, ham) ← forallBoundedTelescope (← inferType outer) (some 1) fun indices _ => do
      let i := indices[0]!
      let hOuter ← component (mkApp outer i) 1
      let outerType ← inferType hOuter
      let some domain := outerType.find? (fun e =>
          e.isAppOfArity `JanetCartan.ContinuumRow.CanonicalConic.coefficientDomain 4)
        | throwError "original measurement: missing original coefficientDomain in {outerType}"
      let z := domain.getAppArgs[1]!
      let product := outerType.getAppArgs.back!.headBeta
      unless product.isAppOf `Set.prod || product.isAppOf `SProd.sprod do
        throwError "original measurement: missing original product target {product.getAppFn} ({product.getAppNumArgs}): {product}"
      let V := product.getAppArgs.back!
      let q ← mkAppM ``Subtype.val #[← mkAppM ``Sigma.fst #[i]]
      let qpair ← mkAppM ``Subtype.val #[q]
      let chart ← mkAppM ``Prod.fst #[qpair]
      let l ← mkAppM ``Sigma.snd #[i]
      let cell := mkAppN (field `cell) #[q, l]
      let productType ← whnf (← inferType (boundary `density_product_geometry))
      let patchType ← whnf productType.bindingDomain!
      unless patchType.isAppOfArity ``Sigma 2 do
        throwError "original measurement: expected original dependent patch index"
      let patch := mkAppN (mkConst ``Sigma.mk [.zero, .zero])
        (patchType.getAppArgs ++ #[chart, l])
      let productFact := mkAppN (boundary `density_product_geometry) #[patch, cell]
      let hRU ← component productFact 4
      let ham ← component (mkApp outer i) 3
      return (← mkLambdaFVars indices z, ← mkLambdaFVars indices V,
        ← mkLambdaFVars indices hOuter, ← mkLambdaFVars indices hRU, ← mkLambdaFVars indices ham)
    let hSource ← mkAppOptM `JanetCartan.ContinuumInverse.retained_measured_source_ball_subset
      #[some n, none, some hNonempty, none, some z, none, none, none, none,
        some (field `_hr), some (field `_ha), some V, some hOuter, some hRU, some ham,
        some mu, some hMu, some (field `fact60)]
    let hSource ← store `source_ball_inside_original_chart fixed hSource
    let hFour ← store `measurement_inside_original_chart fixed
      (← mkAppM ``measurement_inside #[hn, hMu, hSource])
    let hFourteen ← mkAppM ``Nat.le_trans
      #[mkAppN (mkConst `JanetCartan.PhysicalInitialization.leading_reserve_le_canonical_low_order) #[n], fixed[28]!]
    let reserves ← mkAppM ``available_reserve #[hFourteen]
    let hEight ← mkAppM ``And.left #[reserves]
    let hReserve ← mkAppM ``And.right #[reserves]
    let reserve := mkApp2 (mkConst ``Nat.sub) fixed[26]! (mkNatLit 2)
    let producer := mkAppN
      (mkConst `JanetCartan.PhysicalNormalInverse.exists_physical_history_sampling_measurement_profiles)
      #[n, G, mu, boundary `R, hMu, field `hMeasureCell, hFour, hR, fixed[24]!, fixed[25]!,
        fixed[26]!, reserve, fixed[27]!, hEight, hReserve, fixed[29]!]
    let initialized ← store `initialized fixed producer
    let threshold ← store `Budgets.threshold fixed (← mkAppM ``Classical.choose #[initialized]) true
    let spec ← mkAppM ``Classical.choose_spec #[initialized]
    let thresholdType ← whnf (← inferType initialized)
    let spec ← store `Budgets.threshold_spec fixed spec false (some (thresholdType.appArg!.beta #[threshold]))
    let hThreshold ← store `Budgets.hthreshold fixed (← mkAppM ``And.left #[spec])
    let budgetExists ← mkAppM ``And.right #[spec]
    let Cmeasure ← store `Budgets.Cmeasure fixed (← mkAppM ``Classical.choose #[budgetExists]) true
    let budgetType ← whnf (← inferType budgetExists)
    let budgetSpec ← store `Budgets.spec fixed (← mkAppM ``Classical.choose_spec #[budgetExists])
      false (some (budgetType.appArg!.beta #[Cmeasure]))
    discard <| store `Budgets.positive fixed (← mkAppM ``And.left #[budgetSpec])
    discard <| store `Budgets.continuation fixed (← mkAppM ``And.right #[budgetSpec])
    let nativeS := mkAppN (mkConst (currentNS ++ `S)) fixed
    discard <| store `S fixed (← mkAppM ``Max.max #[nativeS, threshold]) true
    discard <| store `S_native fixed (← mkAppM `le_max_left #[nativeS, threshold])
    let hProfiles ← store `S_profiles fixed (← mkAppM `le_max_right #[nativeS, threshold])
    discard <| store `hS fixed (← mkAppM `le_trans #[hThreshold, hProfiles])
    logInfo "kernel-checked actual original31 common measurement budget at rStar-2 before histories and rows"

/-- Apply the selected measurement budget to the literal native current frame;
all geometric and profile hypotheses come from the actual original producer. -/
elab "apply_original_current_measurement_profiles" : command => liftTermElabM do
  let info ← getConstInfo (currentNS ++ `current)
  forallBoundedTelescope info.type (some 38) fun all _ => do
    unless all.size == 38 do throwError "original measurement: expected native38"
    let fixed := all[:31].toArray
    let field (name : Name) := mkAppN (mkConst (root ++ name)) fixed
    let reachedType ← mkAppM ``LE.le #[field `S, all[31]!]
    withLocalDeclD `hReached reachedType fun hReached => do
      let nativeReached ← mkAppM `le_trans #[field `S_native, hReached]
      let profilesReached ← mkAppM `le_trans #[field `S_profiles, hReached]
      let actualArgs := all.set! 32 nativeReached
      let current := mkAppN (mkConst (currentNS ++ `current)) actualArgs
      let currentType ← inferType current
      unless currentType.getAppFn.isConstOf chartNS do
        throwError "original measurement: expected actual current chart"
      let Q ← mkAppM (chartNS ++ `Q) #[current]
      let hQ ← mkAppM (chartNS ++ `frame_eq) #[current]
      let forward ← mkAppM (chartNS ++ `forward) #[current]
      let inverse ← mkAppM (chartNS ++ `inverse) #[current]
      let mut inputs := #[all[31]!, profilesReached] ++ all[33:37].toArray
      for name in #[`P, `T] do inputs := inputs.push (← chartArgument currentType name)
      inputs := inputs ++ #[Q, hQ]
      for name in #[`row, `col] do inputs := inputs.push (← chartArgument currentType name)
      inputs := inputs ++ #[forward, inverse]
      let mut applied := mkAppN (field `Budgets.continuation) inputs
      for _ in [:4] do
        let type ← whnf (← inferType applied)
        unless type.isForall do throwError "original measurement: expected irrelevant amplitude argument"
        let placeholder ← Term.elabTermEnsuringType (← `(0)) type.bindingDomain!
        Term.synthesizeSyntheticMVarsNoPostponing
        applied := mkApp applied (← instantiateMVars placeholder)
      let params := fixed ++ #[all[31]!, hReached] ++ all[33:38].toArray
      let proof ← store `on_current params applied
      let hTwo ← mkAppM `le_trans #[field `hS, hReached]
      let one ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkNatLit 1), none]
      let two ← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (mkNatLit 2), none]
      let oneLeTwo ← Term.elabTermEnsuringType (← `(by norm_num)) (← mkAppM ``LE.le #[one, two])
      Term.synthesizeSyntheticMVarsNoPostponing
      let hL ← mkAppM `JanetCartan.one_le_currentCoefficientScale
        #[← mkAppM `le_trans #[oneLeTwo, hTwo], all[33]!]
      withLocalDeclD `rpar (mkConst ``Nat) fun rpar => do
        let hReserveType ← mkAppM ``LE.le
          #[mkApp2 (mkConst ``Nat.add) (mkNatLit 2) rpar, fixed[26]!]
        withLocalDeclD `hreserve hReserveType fun hReserve => do
          let physical ← component proof 1
          let joint ← component proof 2
          let weaken (source : Expr) : TermElabM Expr := do
            forallBoundedTelescope (← inferType source) (some 1) fun sets _ => do
              let profile := mkApp source sets[0]!
              let profileType ← inferType profile
              unless profileType.isAppOfArity `JanetCartan.HasDerivativeProfile 11 do
                throwError "original measurement: expected literal measured derivative profile"
              let data := profileType.getAppArgs
              let weakened ← mkAppOptM ``lower_reserve
                (data[:8].toArray.map some ++ #[some fixed[26]!, some rpar,
                  some data[9]!, some data[10]!, some hReserve, some hL,
                  some (field `Budgets.positive), some profile])
              mkLambdaFVars sets weakened
          let result ← mkAppM ``And.intro #[← component proof 0,
            ← mkAppM ``And.intro #[← weaken physical, ← weaken joint]]
          discard <| store `at_reserve (params ++ #[rpar, hReserve]) result
      logInfo "kernel-checked actual native38 common measurement, smooth and profiled on arbitrary physical/joint sets; SAME budget at every lower reserve"

end JanetCartan.PhysicalNormalInverse.OriginalMeasurementProfilesApplication
