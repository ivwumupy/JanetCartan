module
public import JanetCartan.Iteration.PhysicalPairs.OriginalBaselineNodeNative
public import JanetCartan.Iteration.PhysicalPrimary.OriginalPdoProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.PhaseJets
import all JanetCartan.Iteration.PhysicalBackground.CanonicalDensity
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication
public meta import Lean
/-!
# The original unweighted baseline and its fixed coefficient budget

Consumers: the same-phase complete/pair amplitude and the FULL sampled Hermitian
self tensor (`main:eq:primary`, `main:prop:mean`, `new:sec:order-of-choices`).
The baseline is the literal phase-cancelled derivative of the original unscaled
positive atom, with no angular factor or sample weight. Its data does not require
an outer nonzero-weight proof. Its budget sums only the fixed original rows and
is closed before the initial scale, history, sampling prefix, and source.

The original outer admission now puts every whole-chart point in the genuine
parent compact, and `parent_slice_profile` proves local smoothness and the full
coefficient-scale jet bound there. The raw positive-atom demodulation transfer
is separate; none of the shared data is replaced by the parent slice.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
@[expose] public noncomputable section
open Set Metric Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Calculus
open RawPrimary.AmplitudeGrades
/-- Original outer closed-cell admission and the physical chart give the joint
parent compact, without an inner angular gate (`main:prop:mean`). -/
theorem point_mem_parent {n : ℕ} {x : Euclidean n}
    {c c₀ : Euclidean 3 × Euclidean (n-1)} {ρ : ℝ}
    (hx : x ∈ ball 0 ρ) (hc : c ∈ closedBall c₀ ρ) :
    (x,c) ∈ closedBall ((0 : Euclidean n),c₀) ρ := by
  rw [← closedBall_prod_same]
  exact ⟨ball_subset_closedBall hx,hc⟩
/-- Restrict the unchanged full parent to an admitted outer node. The original
row budget dominates its coefficient-scale jets, on the whole open chart and
with no sampled-label count (`main:prop:mean`, `new:sec:order-of-choices`). -/
theorem baseline_profile_of_parent {n N : ℕ}
    {X : Set (Euclidean n)} (hX : IsOpen X)
    {J Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1)))}
    (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    (A : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ)
    (hA : ContDiffOn ℝ ∞ A Ω)
    (B : Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (c : Euclidean 3 × Euclidean (n-1))
    (heq : EqOn B (fun x ↦ A (x,c)) X)
    (hXJ : ∀ x ∈ X, (x,c) ∈ J)
    (C D : ℕ → ℝ) (hC : ∀ q, 0 ≤ C q) (hCD : ∀ q, C q ≤ D q)
    {T : ℝ} (hT : 1 ≤ T) (rpar : ℕ)
    (hjet : ∀ q, ∀ w ∈ J, ‖iteratedFDeriv ℝ q A w‖ ≤ C q*T^(q-rpar)) :
    ContDiffOn ℝ ∞ B X ∧ ∀ q, ∀ x ∈ X,
      ‖iteratedFDeriv ℝ q B x‖ ≤ D q*T^q := by
  have hs : ContDiffOn ℝ ∞ (fun x ↦ A (x,c)) X :=
    hA.comp (contDiffOn_id.prodMk contDiffOn_const) (fun x hx ↦ hJΩ (hXJ x hx))
  refine ⟨hs.congr (fun x hx ↦ heq hx), ?_⟩
  intro q x hx
  have hg : B =ᶠ[𝓝 x] (fun y ↦ A (y,c)) := by
    filter_upwards [hX.mem_nhds hx] with y hy using heq hy
  rw [(hg.iteratedFDeriv ℝ q).eq_of_nhds]
  exact ((norm_iteratedFDeriv_physical_slice_le hΩ hA (hJΩ (hXJ x hx)) q).trans
    (hjet q (x,c) (hXJ x hx))).trans
      ((mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (Nat.sub_le q rpar)) (hC q)).trans
        (mul_le_mul_of_nonneg_right (hCD q) (pow_nonneg (zero_le_one.trans hT) q)))
end JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles.Calculus
end
public meta section
namespace JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles
open Lean Meta
private def root := `JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles
private def parent := `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native
private def app (name : Name) (p : Array Expr) := mkAppN (mkConst name) p
private def save (key : Name) (p : Array Expr) (value target : Expr)
    (doc : String) (data := false) : MetaM Unit := do
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  let env ← getEnv
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLooseBVars || e.hasSorry then
      throwError "original baseline: unresolved field {key}"
    unless (e.getUsedConstants.filter fun n => (env.find? n).isNone).isEmpty do
      throwError "original baseline: missing constant in {key}"
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  let name := root ++ key
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name doc
  let ax ← collectAxioms name
  unless ax.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "original baseline: nonstandard axioms in {name}: {ax}"
  logInfo m!"PASS original baseline {name}/{p.size}/std3: {ax}"
private def withBudget (next : Array Expr → Expr → Array Expr → MetaM Unit) : MetaM Unit := do
  forallBoundedTelescope (← getConstInfo (parent ++ `A)).type (some 44) fun p rest => do
    unless p.size == 44 && rest.isForall do throwError "original baseline: parent static44/row changed"
    let rows := app (parent ++ `A) p
    let index := rest.bindingDomain!
    let indexInfo ← getConstInfo index.getAppFn.constName!
    let some indexBody := indexInfo.value? (allowOpaque := true)
      | throwError "original baseline: original static index body unavailable"
    let concrete := (indexBody.beta index.getAppArgs).headBeta
    let fintype ← synthInstance (mkApp (mkConst ``Fintype [.zero]) concrete)
    let args := #[index,fintype,rows]
    let total := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalPdoProfiles.finite_profile_majorant [.zero]) args
    next p total args
run_meta do
  let name := `JanetCartan.PhysicalPairs.OriginalBaselineNode.amplitude_on_original_statement
  let ci ← getConstInfo name
  forallBoundedTelescope ci.type (some 57) fun p _ => do
    unless p.size == 57 do throwError "original baseline: changed native52/outer5 ABI"
    forallBoundedTelescope ((ci.value! (allowOpaque := true)).beta p) (some 2) fun _ eq => do
      unless eq.isAppOfArity ``Eq 3 do throwError "original baseline: lost actual chart equality"
      let lhs := eq.getAppArgs[1]!
      unless lhs.isAppOfArity `JanetCartan.UniformStep.sampledDerivativeAmplitude 7 do
        throwError "original baseline: not the original sampled derivative amplitude"
      let B := lhs.appFn!
      save `baselineAmplitude p[:56].toArray B (← inferType B)
        "The SAME unweighted unscaled positive baseline's sampledDerivativeAmplitude, with the original carrier/tau phase and outer node. Native52 plus outer4; no nonzero-weight or angular-support proof is used as data (main:eq:primary; main:prop:mean)." true
run_meta do
  withBudget fun p total _ => do
    save `Cbaseline p total (← inferType total)
      "One plus the sum of absolute Parent.Native.A costs over the ORIGINAL fixed row type only. Exactly prehistory44, before every initial scale, history, sampling prefix, source and accuracy; no sampled-label cardinality (new:sec:order-of-choices; main:prop:mean)." true
run_meta do
  withBudget fun p total args => do
    let h := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalPdoProfiles.finite_profile_majorant_nonneg [.zero]) args
    let target := (← inferType h).replace fun e => if e == total then some (app (root ++ `Cbaseline) p) else none
    save `Cbaseline_nonneg p h target
      "The fixed original-row baseline budget is nonnegative at every derivative order (main:prop:mean)."
run_meta do
  withBudget fun p total args => do
    let h := mkAppN (mkConst `JanetCartan.PhysicalPrimary.OriginalPdoProfiles.le_finite_profile_majorant [.zero]) args
    let target := (← inferType h).replace fun e => if e == total then some (app (root ++ `Cbaseline) p) else none
    save `row_le_Cbaseline p h target
      "Every actual parent row's full derivative-amplitude cost is bounded by the SAME prehistory44 baseline majorant, without a sampling-family count (main:prop:mean)."
private def bodyAt (key : Name) (p : Array Expr) : MetaM Expr := do
  let some value := (← getConstInfo key).value? (allowOpaque := true)
    | throwError "original baseline: unavailable cached declaration {key}"
  return (value.beta p).headBeta
private def body (e : Expr) : MetaM Expr := bodyAt e.getAppFn.constName! e.getAppArgs
private def withBaseline
    (next : Array Expr → Array Expr → Expr → Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  let key := `JanetCartan.PhysicalPairs.OriginalBaselineNode.amplitude_on_original_statement
  forallBoundedTelescope (← getConstInfo key).type (some 57) fun p _ => do
    forallBoundedTelescope (← bodyAt key p) (some 2) fun xy t => do
      unless t.isAppOfArity ``Eq 3 && xy.size == 2 do
        throwError "original baseline: changed exact chart equality"
      let rhs := t.getAppArgs[2]!
      unless rhs.isAppOfArity (parent ++ `amplitude) 53 do
        throwError "original baseline: changed parent amplitude"
      let w := rhs.appArg!
      unless w.isAppOfArity ``Prod.mk 4 do throwError "original baseline: not physical/outer point"
      let c := w.getAppArgs[3]!
      let mut native ← bodyAt `JanetCartan.PhysicalPairs.OriginalBaselineNode.native_demodulation_statement p
      for x in xy do native := native.bindingBody!.instantiate1 x
      unless native.isAppOfArity ``Eq 3 do throwError "original baseline: native demodulation changed"
      let fn := native.getAppArgs[1]!
      unless fn.isAppOfArity `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude 17 do
        throwError "original baseline: native full derivative changed"
      let T := fn.getAppArgs[5]!
      unless T.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalLocalWaves.T 53 do
        throwError "original baseline: not original source53 geometry"
      next p xy c T.getAppArgs fn.getAppArgs[0]!
/- Kernel projections discard only redundant implicit predicate/type arguments.
They neither change the actual selected data nor assert any record equality. -/
private def projections (value : Expr) : Expr := Id.run do
  let mut result := value
  for _ in [:6] do
    result := result.replace fun e =>
      if e.isAppOfArity ``Subtype.val 3 then some (.proj ``Subtype 0 e.appArg!)
      else if e.isAppOfArity ``Sigma.fst 3 then some (.proj ``Sigma 0 e.appArg!)
      else if e.isAppOfArity ``Sigma.snd 3 then some (.proj ``Sigma 1 e.appArg!)
      else if e.isAppOfArity ``Prod.fst 3 then some (.proj ``Prod 0 e.appArg!)
      else if e.isAppOfArity ``Prod.snd 3 then some (.proj ``Prod 1 e.appArg!)
      else none
  return result
private def withPoint (next : Array Expr → Array Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  withBaseline fun p xy c source n => do
    let hc ← bodyAt `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.outer_weight_closed_cell
      (source ++ p[52:57].toArray)
    let mem ← Core.betaReduce (← zetaReduce (← inferType hc))
    unless mem.isAppOfArity ``Membership.mem 5 do
      throwError "original baseline: missing outer closed-cell admission"
    let ball := mem.getAppArgs[3]!
    unless ball.isAppOfArity ``Metric.closedBall 4 do
      throwError "original baseline: not original closed carrier cell"
    let b := ball.getAppArgs
    let radius := b[3]!
    unless radius.isAppOfArity `JanetCartan.PhysicalSeed.OriginalBoundary.σcover 4 do
      throwError "original baseline: not original parent cover radius"
    let cp := radius.getAppArgs
    let hX := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_in_cell
      (source[:23].toArray ++ cp[2:4].toArray)
    let hx := mkAppN hX xy
    let proof := app (root ++ `Calculus.point_mem_parent)
      #[n,xy[0]!,c,b[2]!,radius,hx,hc]
    let J := app (parent ++ `J) (p[:44].toArray.push p[50]!)
    next p xy proof J
run_meta do
  withPoint fun p xy proof J => do
    let t ← inferType proof
    let nativeJ := t.getAppArgs[3]!
    let w := t.getAppArgs[4]!
    let parentJ ← bodyAt (parent ++ `J) (p[:44].toArray.push p[50]!)
    let nativeN := nativeJ.getAppArgs[3]!.getAppArgs[0]!
    let parentN := parentJ.getAppArgs[3]!.getAppArgs[0]!
    unless ← isDefEq nativeN parentN do throwError "original baseline: compact changed dimension"
    let callback ← getConstInfo `JanetCartan.PhysicalPrimary.OriginalLocalWaves.source_extra_on_graph
    let normalize (value : Expr) : Expr :=
      let value := value.replace fun e =>
        if e.isAppOfArity callback.name 22 then
          some (((callback.value! (allowOpaque := true)).beta e.getAppArgs).headBeta)
        else none
      projections (value.replace fun e => if e == nativeN then some parentN else none)
    let normal := normalize nativeJ
    let parentNormal := projections parentJ
    let reference (ball : Expr) : Expr :=
      ball.getAppArgs[2]!.getAppArgs[3]!.getAppArgs[3]!.getAppArgs[2]!
    let nz := (reference normal).getAppArgs[2]!.getAppArgs[2]!
    let pz := (reference parentNormal).getAppArgs[2]!.getAppArgs[2]!
    unless nz.isAppOfArity ``OfNat.ofNat 3 && pz.isAppOfArity ``OfNat.ofNat 3 do
      throwError "original baseline: changed original zero center"
    unless ← isDefEq nz pz do throwError "original baseline: different original zero centers"
    let normalize (value : Expr) : Expr :=
      (normalize value).replace fun e => if e == nz then some pz else none
    unless normalize nativeJ == parentNormal do
      throwError "original baseline: compact differs beyond callback/dimension/projection/zero aliases"
    let value := normalize proof
    let target ← mkAppM ``Membership.mem #[J,w]
    save `original_chart_point p (← mkLambdaFVars xy value) (← mkForallFVars xy target)
      "The ORIGINAL whole source-chart point and SAME outer sampling node belong to the genuine Parent.Native.J compact. The only sample restriction is its original outer nonzero weight; no inner angular membership is assumed (main:prop:mean)."
run_meta do
  let pointName := root ++ `original_chart_point
  forallBoundedTelescope (← getConstInfo pointName).type (some 57) fun p rest => do
    unless p.size == 57 do throwError "original baseline: parent-slice native57 changed"
    forallBoundedTelescope rest (some 2) fun xy membership => do
      unless xy.size == 2 && membership.isAppOfArity ``Membership.mem 5 do
        throwError "original baseline: missing exact chart-point membership"
      let actualX := (← inferType xy[1]!).getAppArgs[3]!
      let nativeStatement ← body (app `JanetCartan.PhysicalPairs.OriginalBaselineNode.native_demodulation_statement p)
      let mut nativeAt := nativeStatement
      for x in xy do nativeAt := nativeAt.bindingBody!.instantiate1 x
      let full := nativeAt.getAppArgs[1]!
      unless full.isAppOfArity `JanetCartan.CorrectedAtoms.fullCorrectedDerivativeAmplitude 17 do
        throwError "original baseline: lost cached original native function"
      let source := full.getAppArgs[5]!.getAppArgs
      unless source.size == 53 do throwError "original baseline: lost original source53"
      let X := app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart source[:23].toArray
      unless actualX == (← body X) do
        unless ← isDefEq actualX X do throwError "original baseline: not on whole SourceMasks.chart23"
      let w := membership.getAppArgs[4]!
      unless w.isAppOfArity ``Prod.mk 4 do throwError "original baseline: lost physical/outer point"
      let c := w.getAppArgs[3]!
      let fixed := p[:44].toArray
      let row := fixed.push p[50]!
      let native := p[:52].toArray
      let A := app (parent ++ `amplitude) native
      let fa := (← body A).getAppArgs
      let J := app (parent ++ `J) row
      let Ω := app (parent ++ `Ω) row
      let B ← mkLambdaFVars #[xy[0]!] (mkApp A w)
      let heq ← mkLambdaFVars xy (← mkEqRefl (mkApp A w))
      let hjet := app (parent ++ `jets) native
      let T := app `JanetCartan.currentCoefficientScale #[p[44]!,p[46]!]
      let rpar ← forallBoundedTelescope (← inferType hjet) (some 3) fun qp inequality => do
        unless inequality.isAppOfArity ``LE.le 4 do throwError "original baseline: parent jet inequality changed"
        let power := inequality.appArg!.appArg!
        let exponent := power.appArg!
        unless exponent.appFn!.appArg! == qp[0]! do throwError "original baseline: parent reserve exponent changed"
        unless ← isDefEq power.appFn!.appArg! T do throwError "original baseline: not actual coefficient scale"
        return exponent.appArg!
      let hR ← mkAppM ``le_trans #[app `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS fixed,p[45]!]
      let hT := app `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le
        #[p[44]!,hR,p[46]!]
      let h := app (root ++ `Calculus.baseline_profile_of_parent)
        #[fa[0]!,fa[1]!,X,
          app `JanetCartan.PhysicalPrimary.OriginalSourceMasks.chart_open X.getAppArgs,
          J,Ω,app (parent ++ `Ω_open) row,app (parent ++ `J_in_Ω) row,
          A,app (parent ++ `smooth) native,B,c,heq,app pointName p,
          app (parent ++ `A) row,app (root ++ `Cbaseline) fixed,
          app (parent ++ `A_nonneg) row,app (root ++ `row_le_Cbaseline) row,
          T,hT,rpar,hjet]
      save `parent_slice_profile p h (← inferType h)
        "The SAME original full parent derivative amplitude at its actual outer node is ContDiffOn infinity on the WHOLE SourceMasks.chart, with every physical jet bounded by Cbaseline44(q)*currentCoefficientScale^q. Native57 uses only the original outer nonzero weight; Cbaseline precedes all scale/history/accuracy choices (main:prop:mean; new:sec:order-of-choices)."
end JanetCartan.PhysicalPairs.OriginalBaselineAmplitudeProfiles
end
