module

public import JanetCartan.Iteration.PhysicalBackground.NativeMeasuredCancellation
public import JanetCartan.Geometry.IsometricEmbedding.Mean.PositiveBackground.RetainedDensityMean
public meta import JanetCartan.Iteration.PhysicalNormalInverse.StrongToleranceApplication
public meta import JanetCartan.Iteration.PhysicalBackground.NativeReferenceSourceTemplate
public meta import Lean

/-!
# The actual positive-normal interpretation of the cancelled tensor

On the original full exterior-weight support, the very same current chart
transports the single admitted positive initial `σ√(1+v)` and squares its
normal against `χ²`. Identify this literal tensor with the affine measured
mean and then apply the same native base-variation cancellation. No new
carrier, initial, positive operator or physical core is selected
(`app:ch_background:eq:bg-affine-mean`, `app:ch_background:eq:bg-current-identity`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
open JanetCartan JanetCartan.PhysicalBackground JanetCartan.PositiveBackground JanetCartan.ContinuumRow

@[expose] public noncomputable section
namespace JanetCartan.PhysicalBackground

/-- Substitute the actual retained positive tensor only on the domain where
its full exterior-weight transport has been proved. -/
theorem native_affine_to_retained_cancellation {n N : ℕ}
    (F V : Euclidean n → Euclidean N) (affine positive : MetricField n)
    (core W : Set (Euclidean n)) (hcore : core ⊆ W) (heq : EqOn affine positive W)
    (hc : ∀ x ∈ core, ∀ j, tensorPairing (ProjectedStressFrame.projectedStress F x j)
      (linearizedMetric F V x + affine x) = 0) :
    ∀ x ∈ core, ∀ j, tensorPairing (ProjectedStressFrame.projectedStress F x j)
      (linearizedMetric F V x + positive x) = 0 := by
  intro x hx j
  rw [← heq (hcore hx)]
  exact hc x hx j

end JanetCartan.PhysicalBackground
end

public meta section
namespace JanetCartan.PhysicalBackground.NativePositiveCancellationApplication
open Lean Meta Elab Command Term

private def localTerm (bindings : List (Name × Expr)) (code : String) (target? : Option Expr := none) : TermElabM Expr :=
  _root_.JanetCartan.PhysicalBackground.NativeReferenceSourceTemplate.termWith bindings code target?

private def store (name : Name) (params : Array Expr) (value : Expr) (data := false)
    (target? : Option Expr := none) : MetaM Expr := do
  let actual ← inferType value
  let target := target?.getD actual
  unless ← isDefEq actual target do throwError "native positive cancellation: target changed {name}"
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params value)
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar || type.hasLevelMVar ||
      value.hasLevelMVar || type.hasSorry || value.hasSorry then throwError "native positive cancellation: dependence in {name}"
  let name := `JanetCartan.PhysicalBackground.NativePositiveCancellation ++ name
  if data then
    addDecl (.defnDecl {name, type, value, levelParams := [], hints := .abbrev, safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name, type, value, levelParams := []}) (forceExpose := true)
  return mkAppN (mkConst name) params

/-- Use the source producer's own stricter 3/2 patch inclusion. The full
output domain is unchanged; neither history nor a later source scale may
enter this geometric proof. -/
private def strictPatchGeometry : TermElabM Expr := do
  let ns := `JanetCartan.PhysicalNormalInverse
  let inst := (← getConstInfo (ns ++ `StrongSource.exists_history_coercivity)).type
  forallBoundedTelescope inst (some 29) fun p _ => do
    let args ← PhysicalNormalInverse.StrongToleranceApplication.actualSourceArguments p
    let fields ← NativeReferenceSourceTemplate.namedInputs
      (ns ++ `exists_prescribed_source_history_coercivity) args[:133].toArray
    let raw ← NativeReferenceSourceTemplate.lookup fields `hΩpatch
    let mut val := raw
    for _ in [:4] do
      let result ← mkLambdaFVars p[:21].toArray val
      if !result.hasFVar then return result
      let some name := val.getAppFn.constName? | throwError "nonstatic actual positive chart bound"
      unless (ns ++ `StrongSource.Arguments).isPrefixOf name do throwError "nonstatic actual chart parameter bound {name}"
      val := (((← getConstInfo name).value! (allowOpaque := true)).beta val.getAppArgs).headBeta
    throwError "the actual stricter chart geometry retained a nongermane parameter"

elab "realize_native_positive_normal_cancellation" : command => liftTermElabM do
  let measured := `JanetCartan.PhysicalBackground.NativeMeasuredCancellation
  let admission := `JanetCartan.PhysicalBackground.NativeAdmission
  let original := `JanetCartan.PhysicalInverseContinuity.StrongDatum.Original
  let native := `JanetCartan.PhysicalBackground.NativeDensity
  let old := `JanetCartan.PhysicalBackground.retained_measured_physical_core_cancellation
  let want := `JanetCartan.PositiveBackground.physicalDensityMean_eq_retained_positive_mean
  let oldInfo ← getConstInfo (measured ++ `on_exterior_plateau)
  let strictGeometry ← strictPatchGeometry
  forallBoundedTelescope oldInfo.type (some 39) fun all _ => do
    let fixed21 := all[:21].toArray
    let n := all[0]!
    let selected := fixed21.set! 20 (mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[n, fixed21[1]!, fixed21[20]!])
    let cancel := (((oldInfo.value! (allowOpaque := true)).beta all).headBeta)
    unless cancel.isAppOfArity old 64 do throwError "native positive cancellation: the actual 60+4-argument cancellation changed"
    let inputs ← NativeReferenceSourceTemplate.namedInputs old cancel.getAppArgs[:60].toArray
    let get := NativeReferenceSourceTemplate.lookup inputs
    let adm (nm : Name) := mkAppN (mkConst (admission ++ nm)) all
    let rawInfo ← getConstInfo (admission ++ `raw)
    let raw := ((rawInfo.value! (allowOpaque := true)).beta all).headBeta
    unless raw.isAppOfArity (original ++ `rawCurrent) 47 do throwError "native positive cancellation: changed raw row"
    let na := raw.getAppArgs
    let den (nm : Name) := mkAppN (mkConst (native ++ nm)) na
    let index ← get `ι
    let U ← get `U₀
    let mu ← get `r
    let hr ← get `hr
    let hU ← get `hU₀
    let F ← get `F
    let chi ← get `χ
    let c ← get `chart
    let W ← store `window fixed21 (← localTerm [(`n,n),(`mu,mu)] "ball (0 : Euclidean n) (5 * mu)") true
    let hKU ← localTerm [(`U,U)] "(Subset.rfl : U ⊆ U)"
    let hΩ := mkAppN strictGeometry selected
    let hV ← get `hχV
    let hflow ← get `hflow
    let hv ← localTerm [(`h,adm `range)] "fun i p ↦ (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (h i p).1"
    let masks ← withLocalDeclD `i index fun i => do
      let d := mkApp (den `carrier) i
      let angular ← mkAppM `JanetCartan.ContinuumRow.CarrierData.angularCutoff #[d]
      let high ← mkAppM `JanetCartan.ContinuumRow.CarrierData.highCutoff #[d]
      return (← mkLambdaFVars #[i] angular, ← mkLambdaFVars #[i] high)
    let aliases := [(`n,n), (`N,← get `N), (`A,index), (`P,← get `P), (`U,U), (`hU,hU), (`T,← get `T),
      (`Ω,← get `Ω), (`Kc,← get `K), (`p₀,← get `p₀), (`Rc,← get `Rc), (`M,← get `M), (`τ,← get `τ),
      (`row,← get `row), (`col,← get `col), (`F,F), (`c,c), (`cP,← get `cP), (`CP,← get `CP),
      (`hP,← get `hP), (`hF,den `current_hF_on), (`hrank,den `current_fullNormalRank), (`K,U), (`hKU,hKU),
      (`hτ,← get `hτ), (`σ,all[21]!), (`χ,chi), (`v,adm `v), (`hv,hv), (`W,W),
      (`r,mu), (`hr,hr), (`hcell,← get `hcell), (`angular,masks.1), (`high,masks.2)]
    let mut ty := (← getConstInfo want).type
    let mut args := #[]
    while let .forallE nm domain next _ := ty do
      let nm := nm.eraseMacroScopes
      let val ← if domain.isAppOf `Fintype then get `inst
        else if nm == `hΩ then
          localTerm [(`ho,hΩ),(`hU,hU)]
            "by intro a p hp; have hh := ho a hp; exact ⟨⟨hh.1.2, by simpa only [hU.interior_eq] using hh.1.1⟩,hh.2⟩" (some domain)
        else if nm == `hflow then
          localTerm [(`flow,hflow),(`supp,hV)]
            "by intro a p hp; exact @flow a p ⟨hp.1, supp a hp.2⟩" (some domain)
        else if let some (_,v) := aliases.find? (fun p => p.1 == nm) then pure v
        else throwError "native positive cancellation: missing retained geometry {nm}"
      unless ← isDefEq (← inferType val) domain do throwError "native positive cancellation: changed argument {nm}"
      args := args.push val
      ty := next.instantiate1 val
    let eq := mkAppN (mkConst want) args
    let result ← inferType eq
    unless result.isAppOf `Set.EqOn do throwError "native positive cancellation: missing retained EqOn"
    let ea := result.getAppArgs
    let positive ← store `positiveMean all ea[ea.size-2]! true
    let affine := adm `physicalMean
    let eqType ← localTerm [(`H,affine),(`P,positive),(`W,W)] "Set.EqOn H P W"
    let eq ← store `affine_eq_positive all eq false (some eqType)
    let core := mkAppN (mkConst (measured ++ `core)) fixed21
    let hsub ← localTerm [(`K,core),(`W,W),(`mu,mu),(`hr,hr),(`hk,mkAppN (mkConst (measured ++ `core_plateau)) fixed21)]
      "(fun x hx ↦ closedBall_subset_ball (show mu < 5 * mu by linarith only [(show 0 < mu from hr)]) (hk x hx).1 : K ⊆ W)"
    let V := mkAppN (mkConst (measured ++ `Vbase)) all
    let hPlateau := Expr.proj ``And 1 (mkAppN (mkConst (measured ++ `on_exterior_plateau)) all)
    let hb := [(`n,n),(`mu,mu),(`hr,hr),(`W,W),(`F,F),(`V,V),(`P,positive),(`psi,← get `ψ),(`he,eq),(`cancel,hPlateau)]
    let plateauType ← localTerm hb ("∀ x ∈ closedBall (0 : Euclidean n) mu, torusQuotient x ∈ interior {z | psi z = 1} → ∀ j, " ++
      "tensorPairing (ProjectedStressFrame.projectedStress F x j) (linearizedMetric F V x + P x) = 0")
    let fullPlateau ← localTerm hb ("by\n  intro x hx hp j\n" ++
      "  have hxW : x ∈ W := closedBall_subset_ball (show mu < 5 * mu by linarith only [(show 0 < mu from hr)]) hx\n" ++
      "  rw [← he hxW]\n  exact cancel x hx hp j") (some plateauType)
    discard <| store `on_exterior_plateau all fullPlateau false (some plateauType)
    let hc := mkAppN (mkConst (measured ++ `cancellation)) all
    discard <| store `cancellation all (mkAppN (mkConst `JanetCartan.PhysicalBackground.native_affine_to_retained_cancellation)
      #[n,← get `N,F,V,affine,positive,core,W,hsub,eq,hc])
  logInfo "same measured residual vanishes on the original half-core for the actual positive σ√(1+v) transported-normal mean; one χ²"

end JanetCartan.PhysicalBackground.NativePositiveCancellationApplication
end

realize_native_positive_normal_cancellation
