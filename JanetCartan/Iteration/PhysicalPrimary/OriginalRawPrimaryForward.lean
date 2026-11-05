module
public import JanetCartan.Iteration.PhysicalPrimary.OriginalRawPrimaryAmplitude
public import JanetCartan.Iteration.PhysicalMean.OriginalMeasuredHermitianProfiles
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeGradedEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeSourceRowsApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalNativeInitialEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalPositiveEventApplication
import all JanetCartan.Iteration.PhysicalSampling.OriginalCommonThresholdApplication
public import JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalSampling.OriginalBareScale
import all JanetCartan.Iteration.PhysicalSampling.OriginalMeasuredFamilyApplication

/-! The SAME original coefficient κ times the actual BEFORE-B derivative
amplitude. This is an auxiliary forward-kernel amplitude, not an output recut
of the physical primary. The consuming native half-moment field keeps the
original scalar operator, phase difference, detector, adjoint and fixed prefix
(main:eq:primary-strain; app:ch_regular:eq:source-tail). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPrimary.OriginalRawPrimaryForwardApplication
open RawPrimary.AmplitudeGrades.Polynomial

private theorem cutoff_in_parent {n : ℕ}
    (x y : Euclidean n × (Euclidean 3 × Euclidean (n-1))) (r R : ℝ)
    (κ : (Euclidean n × (Euclidean 3 × Euclidean (n-1))) → ℝ)
    (hr : 0 < r) (hκ : tsupport κ ⊆ closedBall x r)
    (hp : closedBall x (2*r) ⊆ ball y R) : tsupport κ ⊆ closedBall y R := by
  exact hκ.trans ((closedBall_subset_closedBall (by linarith only [hr])).trans
    (hp.trans ball_subset_closedBall))

private def cutCost (n N : ℕ)
    (J : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1))))
    (κ : (Euclidean n × (Euclidean 3 × Euclidean (n-1))) → ℝ)
    (C : ℕ → ℝ) : ℕ → ℝ :=
  productProfile (ContinuousLinearMap.lsmul ℝ ℝ (E := Matrix (Fin N) (Fin n) ℂ))
    (fun j ↦ cNorm J j κ) C

private theorem cutCost_nonneg (n N : ℕ)
    (J : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1))))
    (κ : (Euclidean n × (Euclidean 3 × Euclidean (n-1))) → ℝ)
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) : ∀ j, 0 ≤ cutCost n N J κ C j :=
  productProfile_nonneg _ (fun j ↦ cNorm_nonneg J j κ) hC

private theorem cut_raw {n N : ℕ}
    (J Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n-1))))
    (hJ : IsCompact J) (hΩ : IsOpen Ω) (hJΩ : J ⊆ Ω)
    (κ : (Euclidean n × (Euclidean 3 × Euclidean (n-1))) → ℝ)
    (hκ : ContDiff ℝ ∞ κ) (hκJ : tsupport κ ⊆ J)
    (A : (Euclidean n × (Euclidean 3 × Euclidean (n-1))) → Matrix (Fin N) (Fin n) ℂ)
    (hA : ContDiffOn ℝ ∞ A Ω) (rpar : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hjets : ∀ j, ∀ w ∈ J, ‖iteratedFDeriv ℝ j A w‖ ≤ C j*L^(j-rpar)) :
    ContDiff ℝ ∞ (fun w ↦ κ w • A w) ∧
      ∀ j w, ‖iteratedFDeriv ℝ j (fun v ↦ κ v • A v) w‖ ≤
        cutCost n N J κ C j*L^(j-rpar) := by
  let f := fun w ↦ κ w • A w
  have hz (w) (hw : w ∉ tsupport κ) : f =ᶠ[𝓝 w] 0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hw] with y hy
    simp only [f,hy,Pi.zero_apply,zero_smul]
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro w
    by_cases hw : w ∈ tsupport κ
    · exact hκ.contDiffAt.smul (hA.contDiffAt (hΩ.mem_nhds (hJΩ (hκJ hw))))
    · exact contDiffAt_const.congr_of_eventuallyEq (hz w hw)
  · intro j w
    by_cases hw : w ∈ tsupport κ
    · have hj := hκJ hw
      have hbκ (k : ℕ) : ‖iteratedFDeriv ℝ k κ w‖ ≤ cNorm J k κ*L^(k-rpar) :=
        (norm_iteratedFDeriv_le_cNorm hJ (hκ.of_le (by simp)) hj le_rfl).trans
          (le_mul_of_one_le_right (cNorm_nonneg J k κ) (one_le_pow₀ hL))
      exact jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ (E := Matrix (Fin N) (Fin n) ℂ))
        hΩ hκ.contDiffOn hA (hJΩ hj) hL (fun k ↦ cNorm_nonneg J k κ) hC hbκ
        (fun k ↦ hjets k w hj) j
    · rw [((hz w hw).iteratedFDeriv ℝ j).eq_of_nhds]
      simp only [iteratedFDeriv_zero,Pi.zero_apply,norm_zero]
      exact mul_nonneg (cutCost_nonneg n N J κ C hC j) (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.PhysicalPrimary.OriginalRawPrimaryForwardApplication
end

public meta section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
namespace JanetCartan.PhysicalPrimary.OriginalRawPrimaryForwardApplication
open Lean Meta Elab Command
open PhysicalMean.OriginalParentCorrectedProfilesTemplate (withActualParent)
private def ns := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward
private def raw := `JanetCartan.PhysicalPrimary.OriginalRawPrimaryAmplitude
private def parent := `JanetCartan.PhysicalMean.OriginalParentCorrectedProfiles.Native
private def cut := `JanetCartan.PhysicalMean.OriginalMeasuredHermitianProfiles
private def ps := `JanetCartan.PhysicalSampling
private def app (key : Name) (xs : Array Expr) := mkAppN (mkConst key) xs
private def part (h : Expr) (j : Nat) := Expr.proj ``And 0 (Nat.repeat (fun e => Expr.proj ``And 1 e) j h)
private def save (key : Name) (p : Array Expr) (value : Expr) (data := false)
    (expected : Option Expr := none) : MetaM Unit := do
  let target ← match expected with | some t => pure t | none => inferType value
  let type ← instantiateMVars (← mkForallFVars p target)
  let value ← instantiateMVars (← mkLambdaFVars p value)
  for e in #[type,value] do
    if e.hasFVar || e.hasMVar || e.hasLevelMVar || e.hasLevelParam || e.hasLooseBVars || e.hasSorry then
      throwError "actual raw forward: unresolved field {key}"
  let name := ns ++ key
  let (type,value) := Lean.ShareCommon.shareCommon (type,value)
  liftM <| IO.eprintln s!"actual raw forward: checking {key}/{p.size}"
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe}) (forceExpose := true)
  else addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "SAME original coefficient cutoff times the independently proved before-B raw derivative amplitude. Global smoothness and all joint jets use the original doubled-ball containment into the closed sigma-cover parent; the cost is fixed before history, color and sampled node. This is an auxiliary native forward kernel, not a new physical output cutoff (main:eq:primary-strain; app:ch_regular:eq:source-tail)."
  logInfo m!"actual raw forward: checked {key}/{p.size}"

elab "check_actual_raw_cut_amplitude " which:num : command => liftTermElabM <| withActualParent fun d => do
  let mode := which.getNat
  unless mode < 5 do throwError "actual raw forward: unknown field"
  let p := d.params52
  let n := d.raw13[0]!
  let N := d.raw13[1]!
  let sampler ← PhysicalSampling.OriginalBareScaleApplication.originalSampler p[:24].toArray
  let row := sampler.push p[50]!
  let κ := app (cut ++ `coefficientCutoff) row
  let C := app (raw ++ `C) d.static45
  let hC := app (raw ++ `C_nonneg) d.static45
  let J := app (parent ++ `J) d.static45
  let cost := app ``cutCost #[n,N,J,κ,C]
  if mode == 0 then
    save `cutCost d.static45 cost true
    return
  if mode == 1 then
    let proof := app ``cutCost_nonneg #[n,N,J,κ,C,hC]
    let target := (← inferType proof).replace fun e => if e == cost then some (app (ns ++ `cutCost) d.static45) else none
    save `cutCost_nonneg d.static45 proof false (some target)
    return
  let A := app (raw ++ `amplitude) p
  let hA := app (raw ++ `smooth) p
  let Ω := app (parent ++ `Ω) d.static45
  let hκ := app (cut ++ `coefficientCutoff_contDiff) row
  let hsupport := app (cut ++ `coefficientCutoff_tsupport_subset) row
  let s := d.source53
  let info ← getConstInfo `JanetCartan.PhysicalPrimary.OriginalLocalWaveGeometry.parameter_window
  let V := (info.value! (allowOpaque := true)).beta s
  unless V.isAppOfArity `JanetCartan.PhysicalPrimary.OriginalSourceMasks.V 25 do
    throwError "actual raw forward: source parameter window changed"
  let cell := V.getAppArgs[24]!
  unless cell.isAppOfArity `JanetCartan.PhysicalSeed.SelectedBoundary.cell 23 do
    throwError "actual raw forward: original selected cell changed"
  let ca := cell.getAppArgs
  let hroot := app (ps ++ `OriginalAdmission.root_mem) (sampler ++ #[ca[21]!,ca[22]!])
  let radiusArgs := #[n,s[1]!,ca[21]!,ca[22]!,cell]
  let radius := app (ps ++ `originalSamplingRadius) radiusArgs
  let hparent := part (app (ps ++ `originalSamplingRadius_spec) (radiusArgs.push hroot)) 0
  let ht ← inferType hparent
  let sets := ht.getAppArgs
  let small := sets[sets.size-2]!
  let large := sets.back!
  unless small.isAppOfArity ``Metric.closedBall 4 && large.isAppOfArity ``Metric.ball 4 do
    throwError "actual raw forward: original doubled-parent containment changed"
  let hκJ := app ``cutoff_in_parent #[n,small.getAppArgs[2]!,large.getAppArgs[2]!,
    Expr.proj ``Subtype 0 radius,large.getAppArgs[3]!,κ,Expr.proj ``Subtype 1 radius,hsupport,hparent]
  let hTwo ← mkAppM `le_trans #[app (ps ++ `OriginalNativeGradedEvent.hS) p[:44].toArray,p[45]!]
  let hL ← mkAppM `JanetCartan.PhysicalPrimary.OriginalParameterRemainders.coefficient_scale_one_le_of_two_le #[hTwo,p[46]!]
  let bound := app ``cut_raw #[n,N,J,Ω,app (parent ++ `J_compact) d.static45,
    app (parent ++ `Ω_open) d.static45,app (parent ++ `J_in_Ω) d.static45,κ,hκ,hκJ,A,hA,
    d.full60[42]!,d.full60[50]!,hL,C,hC,app (raw ++ `jets) p]
  let hb ← inferType bound
  let left := hb.getAppArgs[0]!
  unless left.isAppOfArity ``ContDiff 10 do throwError "actual raw forward: global smoothness shape changed"
  let amplitude := left.getAppArgs[9]!
  if mode == 2 then save `cutAmplitude p amplitude true
  else if mode == 3 then
    let target := left.replace fun e => if e == amplitude then some (app (ns ++ `cutAmplitude) p) else none
    save `cutSmooth p (Expr.proj ``And 0 bound) false (some target)
  else
    let value := Expr.proj ``And 1 bound
    let target := (← inferType value).replace fun e =>
      if e == amplitude then some (app (ns ++ `cutAmplitude) p)
      else if e == cost then some (app (ns ++ `cutCost) d.static45) else none
    save `cutJets p value false (some target)

check_actual_raw_cut_amplitude 0
check_actual_raw_cut_amplitude 1
check_actual_raw_cut_amplitude 2
check_actual_raw_cut_amplitude 3
check_actual_raw_cut_amplitude 4
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.cutCost
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.cutCost_nonneg
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.cutAmplitude
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.cutSmooth
#print axioms JanetCartan.PhysicalPrimary.OriginalRawPrimaryForward.cutJets
end JanetCartan.PhysicalPrimary.OriginalRawPrimaryForwardApplication
end
