module

public import JanetCartan.Iteration.PhysicalMean.JointHermitianPeriodization
public import JanetCartan.Iteration.PhysicalMean.WeightedForcingProfiles
import all JanetCartan.Iteration.PhysicalMean.WeightedForcingProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalWindow
public import JanetCartan.Geometry.IsometricEmbedding.Scales.Revised
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ScaleGap
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.DifferentiatedAmplitudes.Bounds
public meta import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalSampledApplication

/-!
# Periodization of the actual weighted positive baseline

This module keeps the original outer weight and the original centered
representative.  Smoothness is obtained from the weighted field directly; no
unweighted global smoothness premise is introduced.  The support-gap input is
the existing physical support theorem and the original cell-gap theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean.OriginalPeriodicBackground
open SeparatedSampling CurrentMean Sampling.Realization Sampling.BackgroundQuadrature

variable {n : ℕ}

/-- The literal centered-representative periodization of one physical baseline. -/
def periodicH (H : Euclidean n × Point → Euclidean n) :
    Torus n × Point → Euclidean n :=
  fun w => jointHermitianPeriodization H w

/-- A measurement zero germ transfers its compact support to any weighted
baseline that vanishes when the measurement operator vanishes. -/
theorem weighted_support_of_zero
    {X : Set (Euclidean n)} {ψ : Point → ℝ}
    {K : Euclidean n × Point → Euclidean n}
    {C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n}
    (hC : tsupport C ⊆ X)
    (hzero : ∀ x z, C x = 0 → K (x,z) = 0) :
    ∀ z x, (ψ z • K (x,z)) ≠ 0 → x ∈ X := by
  intro z x h
  by_contra hx
  have hC0 : C x = 0 := by
    by_contra hn
    exact hx (hC (subset_tsupport C hn))
  exact h (by rw [hzero x z hC0, smul_zero])

theorem support_gap_of_closedBall {r : ℝ}
    {H : Euclidean n × Point → Euclidean n}
    (hH : ∀ z x, H (x,z) ≠ 0 → x ∈ Metric.closedBall (0 : Euclidean n) r) :
    ∀ z x, H (x,z) ≠ 0 → ∀ i, |x i| ≤ r := by
  intro z x hx i
  have hnorm : ‖x‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hH z x hx
  have hcoord : |x i| ≤ ‖x‖ := by
    rw [EuclideanSpace.norm_eq]
    let S : ℝ := ∑ j, ‖x.ofLp j‖ ^ 2
    have hS : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun j _ ↦ sq_nonneg (‖x.ofLp j‖)
    have hterm : ‖x.ofLp i‖ ^ 2 ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (‖x.ofLp j‖)) (Finset.mem_univ i)
    have hs : (Real.sqrt S)^2 = S := Real.sq_sqrt hS
    have hc : ‖x.ofLp i‖ ≤ Real.sqrt S := by
      nlinarith [norm_nonneg (x.ofLp i), Real.sqrt_nonneg S]
    dsimp [S] at hc ⊢
    simpa only [Real.norm_eq_abs] using hc
  exact hcoord.trans hnorm

/-- The actual baseline factors through its common measurement. This form
lets the application discharge the zero germ by the literal H body, with no
unweighted smoothness or support premise added. -/
theorem weighted_support_of_factor
    {X : Set (Euclidean n)}
    (ψ : Point → ℝ)
    {K : Euclidean n × Point → Euclidean n}
    {C : Euclidean n → MetricTensor n →L[ℝ] Euclidean n}
    (M : Euclidean n × Point → MetricTensor n)
    (hC : tsupport C ⊆ X)
    (hfactor : ∀ x z, K (x,z) = C x (M (x,z))) :
    ∀ z x, (ψ z • K (x,z)) ≠ 0 → x ∈ X := by
  apply weighted_support_of_zero hC
  intro x z hzero
  rw [hfactor x z, hzero, zero_apply]

theorem weighted_periodic_smooth
    {r : ℝ} {ψ : Point → ℝ} {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, (ψ z • H (x,z)) ≠ 0 → ∀ i, |x i| ≤ r)
    (hψH : ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦ ψ w.2 • H w))
    (hr : r < 1 / 2) :
    ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      ψ w.2 • periodicH H (torusQuotient w.1, w.2)) := by
  simpa only [periodicH, jointHermitianPeriodization] using
    (contDiff_jointHermitianPeriodization_lift (n := n) (H := fun w : Euclidean n × Point ↦
      ψ w.2 • H w) hr hs hψH)

/-- The weighted periodic value is the original weighted value on the whole
closed cell, including faces (app:ch_mean_pairs:eq:comparison-input). -/
theorem weighted_periodic_eq
    {r : ℝ} {ψ : Point → ℝ} {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, (ψ z • H (x,z)) ≠ 0 → ∀ i, |x i| ≤ r)
    (hr : r < 1 / 2) :
    ∀ x, x ∈ fundamentalCell n → ∀ z,
      ψ z • periodicH H (torusQuotient x,z) = ψ z • H (x,z) := by
  intro x hx z
  simpa only [periodicH,jointHermitianPeriodization] using
    (jointHermitianPeriodization_lift_eq (H := fun w : Euclidean n × Point ↦
      ψ w.2 • H w) hr hs hx z)

/-- Every weighted derivative of the centered periodization agrees with the
original weighted derivative above the closed fundamental cell. -/
theorem weighted_periodic_jets_eq
    {r : ℝ} {ψ : Point → ℝ} {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, (ψ z • H (x,z)) ≠ 0 → ∀ i, |x i| ≤ r)
    (k : ℕ) {x : Euclidean n} (hx : x ∈ fundamentalCell n) (z : Point)
    (hr : r < 1 / 2) :
    iteratedFDeriv ℝ k (fun w : Euclidean n × Point ↦
      ψ w.2 • periodicH H (torusQuotient w.1, w.2)) (x,z) =
      iteratedFDeriv ℝ k (fun w : Euclidean n × Point ↦
        ψ w.2 • H w) (x,z) := by
  simpa only [periodicH, jointHermitianPeriodization, one_smul] using
    (iteratedFDeriv_weighted_jointHermitianPeriodization_lift_eq
      (n := n) (H := fun w : Euclidean n × Point ↦ ψ w.2 • H w)
      (ψ := fun _ : Point ↦ 1) hr hs k hx z)

/-- The original weighted derivative budget survives literal periodization
unchanged on the closed fundamental cell (app:ch_waves:eq:background-quadrature). -/
theorem weighted_periodic_jets
    {r : ℝ} {ψ : Point → ℝ} {H : Euclidean n × Point → Euclidean n}
    (hs : ∀ z x, (ψ z • H (x,z)) ≠ 0 → ∀ i, |x i| ≤ r)
    (hr : r < 1 / 2) {D : ℕ → ℝ} {T : ℝ} {r₀ : ℕ}
    (hjets : ∀ k w, ‖iteratedFDeriv ℝ k
      (fun w : Euclidean n × Point ↦ ψ w.2 • H w) w‖ ≤ D k * T^(k-r₀)) :
    ∀ k x, x ∈ fundamentalCell n → ∀ z,
      ‖iteratedFDeriv ℝ k (fun w : Euclidean n × Point ↦
        ψ w.2 • periodicH H (torusQuotient w.1,w.2)) (x,z)‖ ≤ D k * T^(k-r₀) := by
  intro k x hx z
  rw [weighted_periodic_jets_eq hs k hx z hr]
  exact hjets k (x,z)

/-- Pointwise periodization of a finite color family. -/
def periodicFamily {p : ℕ}
    (H : (Fin 3 → Fin (p+1)) → Euclidean n × Point → Euclidean n) :
    (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n :=
  fun c w => periodicH (H c) w

/-- The frozen weighted quadrature estimate with its full mesh power retained.
This uses the unchanged Sobolev conversion and original constants; no relation
between the sampling order and the coefficient reserve is assumed here
(app:ch_mean_pairs:eq:comparison-input). -/
theorem weighted_forcing_sobolev_sharp
    {I : Type} [Fintype I] {κ : ℝ → ℝ} (hκc : HasCompactSupport κ)
    (hκ : ContDiff ℝ ∞ κ) (hκint : ∫ t, κ t = 1) (hκ0 : ∀ t, 0 ≤ κ t)
    (hκsupp : Function.support κ ⊆ Icc (-(1/4)) (1/4))
    {p : ℕ} (hp : 0 < p) {B : ℝ} (hB : 0 ≤ B) {P : I → ℝ} {ψ : I → Point → ℝ}
    (hpatch : ∀ i, PatchBounds (ψ i) B (P i))
    (hψc : ∀ i, HasCompactSupport (ψ i))
    (C : I → ℕ → ℝ) (hC : ∀ i q, 0 ≤ C i q)
    (r₀ : ℕ) {T : ℝ} (hT : 1 ≤ T)
    (H : I → (Fin 3 → Fin (p+1)) → Torus n × Point → Euclidean n)
    (hweighted : ∀ i c, ContDiff ℝ ∞ (fun w : Euclidean n × Point ↦
      ψ i w.2 • H i c (torusQuotient w.1,w.2))) (s : ℕ)
    (hjoint : ∀ q ≤ s, ∀ x ∈ fundamentalCell n, ∀ i c z, ‖iteratedFDeriv ℝ (p+q)
      (fun w : Euclidean n × Point ↦ ψ i w.2 • H i c (torusQuotient w.1,w.2)) (x,z)‖ ≤
        C i (p+q)*T^(p+q-r₀))
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1) (U : I → Lattice → Point)
    (hU : ∀ i a j, 0 ≤ U i a j ∧ U i a j < h) :
    residualSobolevSeminorm n s
      (weightedOriginalBackgroundQuadratureForcing hκc hκ p B h ψ hψc U H hweighted) ≤
        (sobolevPeriodicJetConstant n s * (s+1) *
          (backgroundQuadratureConstant p B *
            (∑ q ∈ Finset.range (s+1), ∑ i, C i (p+q)*T^(p+q-r₀)))) * h^p := by
  let f : Torus n → Euclidean n := fun x ↦ familyBackgroundError p B ψ
    (LatticeQuadrature.convolvedBoxWindow κ p) h U (fun i c z ↦ H i c (x,z))
  have hf : IsSmoothPeriodic f :=
    isSmoothPeriodic_originalBackgroundError_of_weighted hκc hκ p B h ψ hψc U H hweighted
  have hquad := originalBackgroundError_cNorm_le_of_weighted hκc hκ hκint hκ0 hκsupp
    hp hB hpatch hψc (fun i c w ↦ H i c (torusQuotient w.1,w.2)) hweighted
    s (fundamentalCell n) (fun q i ↦ C i (p+q)*T^(p+q-r₀))
    (fun q _ i ↦ mul_nonneg (hC i (p+q)) (pow_nonneg (zero_le_one.trans hT) _))
    hjoint hh hh₁ U hU
  have hpref : 0 ≤ sobolevPeriodicJetConstant n s * (s+1) :=
    mul_nonneg (zero_le_one.trans (one_le_sobolevPeriodicJetConstant n s)) (by positivity)
  unfold weightedOriginalBackgroundQuadratureForcing
  rw [map_neg_eq_map (residualSobolevSeminorm n s), residualSobolevSeminorm,
    DensityDiscrepancy.densitySobolevSeminorm_eq_norm,
    DensityDiscrepancy.norm_densitySobolevRealization]
  change periodicSobolevNorm s f ≤ _
  exact (weightedForcingSobolev_le_physicalCNorm hf s).trans
    ((mul_le_mul_of_nonneg_left hquad hpref).trans_eq (by ring))

/-- Reached original thresholds give the three numerical inputs used by the
frozen quadrature theorem, with the unchanged h and coefficient scale. -/
theorem original_scale_facts {S R₀ : ℝ} (hS : 2 ≤ S) (hR : S ≤ R₀) (j : ℕ) :
    1 ≤ currentCoefficientScale R₀ j ∧
      0 < historyScale R₀ growthExponent j ^ (-separationExponent) ∧
        historyScale R₀ growthExponent j ^ (-separationExponent) ≤ 1 := by
  have hR1 : 1 ≤ R₀ := (by norm_num : (1 : ℝ) ≤ 2).trans (hS.trans hR)
  have hj := hR1.trans (le_historyScale hR1 j)
  exact ⟨one_le_currentCoefficientScale hR1 j,
    Real.rpow_pos_of_pos (zero_lt_one.trans_le hj) _,
    Real.rpow_le_one_of_one_le_of_nonpos hj (by norm_num [separationExponent])⟩

/-- Sampling order one fits the original fixed reserve before every graph,
cutoff, σ and sample choice. This does NOT change an already selected order. -/
theorem sampling_order_one_reserve (n : ℕ) :
    RevisedScales.sourceOrder n + 1 ≤ RawPrimary.SliceBounds.rawSliceParameterOrder n := by
  dsimp [RevisedScales.sourceOrder, RevisedScales.baselineOrder,
    RawPrimary.SliceBounds.rawSliceParameterOrder, RawPrimary.SliceBounds.rawSliceJetOrder]
  omega

/-- An already fixed order equal to one satisfies the source reserve. -/
theorem sampling_order_one_reserve_of_eq (n p : ℕ) (hp : p = 1) :
    RevisedScales.sourceOrder n + p ≤ RawPrimary.SliceBounds.rawSliceParameterOrder n := by
  subst p
  exact sampling_order_one_reserve n

end JanetCartan.PhysicalMean.OriginalPeriodicBackground

public meta section
namespace JanetCartan.PhysicalMean.OriginalPeriodicBackgroundTemplate
open Lean Meta Elab Command
open JanetCartan.PhysicalMean.OriginalBackgroundHermitianTemplate
open JanetCartan.PhysicalMean.OriginalCanonicalSampledApplication

def ns := `JanetCartan.PhysicalMean.OriginalPeriodicBackground

partial def findProofOfType (proof target : Expr) : MetaM Expr := do
  let tp ← whnf (← inferType proof)
  if ← isDefEq tp target then
    return proof
  unless tp.isAppOfArity ``And 2 do
    throwError "original periodic background: existing event proof shape changed"
  let left ← mkAppM ``And.left #[proof]
  let right ← mkAppM ``And.right #[proof]
  let l ← try? (findProofOfType left target)
  if let some p := l then return p
  let r ← try? (findProofOfType right target)
  if let some p := r then return p
  throwError "original periodic background: required existing event fact was not found"

/-- Read the sole named original event and its existing shift bounds. -/
def withActualCanonicalSample
    (next : Array Expr → Expr → Expr → Expr → Expr → Expr → Expr → MetaM Unit) : MetaM Unit := do
  withTransparency .reducible <| withActualRow fun d => do
    let xs := d.parameters[:50].toArray
    let ξ := mkAppN (mkConst
      `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift) xs
    let hξ := mkAppN (mkConst
      `JanetCartan.PhysicalMean.OriginalCanonicalSelection.event) xs
    let ht ← inferType hξ
    let some si := ht.find? (·.isAppOfArity
      `JanetCartan.CanonicalRowComparison.SampleIndex 7)
      | throwError "original periodic background: SampleIndex7 missing"
    let some deviation := ht.find? (·.isAppOfArity
      `JanetCartan.Sampling.Realization.familyDeviation 17)
      | throwError "original periodic background: familyDeviation17 missing"
    let some fI ← deviation.getAppArgs.findM? (fun arg => do
      if arg.hasLooseBVars then return false
      return (← inferType arg).isAppOfArity ``Fintype 1)
      | throwError "original periodic background: original Fintype missing"
    let some bare := ht.find? (·.isAppOfArity
      `JanetCartan.PhysicalSampling.OriginalScalarFamily.kernel 46)
      | throwError "original periodic background: original scalar46 missing"
    let J := bare.getAppArgs[43]!
    let I := si.getAppArgs[0]!
    let U := si.getAppArgs[6]!
    let h := si.getAppArgs[5]!
    let utype := (← inferType U).consumeMData
    let lattice := utype.bindingBody!.bindingDomain!
    let fin3 := mkApp (mkConst ``Fin) (mkNatLit 3)
    let zero ← mkNumeral (mkConst ``Real) 0
    let hUType ← withLocalDeclNoLocalInstanceUpdate `i .default I fun i =>
      withLocalDeclNoLocalInstanceUpdate `q .default lattice fun q =>
        withLocalDeclNoLocalInstanceUpdate `j .default fin3 fun j => do
          let u := mkAppN U #[i,q,j]
          let lo ← mkAppM ``LE.le #[zero,u]
          let hi ← mkAppM ``LT.lt #[u,h]
          let both ← mkAppM ``And #[lo,hi]
          mkForallFVars #[i,q,j] both
    let hU ← findProofOfType hξ hUType
    next xs ξ si J fI hU hξ

def saveDecl (short : Name) (params : Array Expr) (term : Expr)
    (data := false) (expected : Option Expr := none) : MetaM Unit := do
  let env ← getEnv
  let missing := term.getUsedConstants.filter (fun n => (env.find? n).isNone)
  unless missing.isEmpty do
    throwError "original periodic background: missing producers {missing.toList}"
  let target ← match expected with | some t => pure t | none => inferType term
  let type ← instantiateMVars (← mkForallFVars params target)
  let value ← instantiateMVars (← mkLambdaFVars params term)
  for e in #[type,value] do
    let missing := e.getUsedConstants.filter (fun n => (env.find? n).isNone)
    unless missing.isEmpty do
      throwError "original periodic background: missing constants {missing.toList}"
  if type.hasFVar || value.hasFVar || type.hasMVar || value.hasMVar ||
      type.hasLevelMVar || value.hasLevelMVar || type.hasLooseBVars || value.hasLooseBVars ||
      type.hasSorry || value.hasSorry then
    throwError "original periodic background: open declaration {short}"
  let name := ns ++ short
  if data then
    addDecl (.defnDecl {name,levelParams := [],type,value,hints := .abbrev,safety := .safe})
      (forceExpose := true)
  else
    addDecl (.thmDecl {name,levelParams := [],type,value}) (forceExpose := true)
  addDocStringCore name "The exact centered-representative periodization of the original weighted positive baseline; no new cutoff, sample, shift or scalar."
  logInfo m!"checked original periodic background {short} at {params.size} inputs"

elab "publish_original_periodic_background_periodicH" : command => liftTermElabM <|
  withTransparency .reducible <| withActualRow fun d => do
    let xs := d.parameters[:50].toArray
    let rowType ← inferType d.row
    let colorType := (← inferType d.native64[61]!).bindingDomain!
    let n := d.raw13[0]!
    let torusType := mkApp (mkConst ``Torus) n
    let pointType := mkConst `JanetCartan.SeparatedSampling.Point
    let euclidType := mkApp (mkConst `JanetCartan.Euclidean) n
    let pairType ← mkAppM ``Prod #[euclidType,pointType]
    let wType ← mkAppM ``Prod #[torusType,pointType]
    withLocalDeclNoLocalInstanceUpdate `i .default rowType fun i =>
      withLocalDeclNoLocalInstanceUpdate `color .default colorType fun color =>
        withLocalDeclNoLocalInstanceUpdate `w .default wType fun w =>
          withLocalDeclNoLocalInstanceUpdate `v .default pairType fun v => do
            let vx ← mkAppM ``Prod.fst #[v]
            let vz ← mkAppM ``Prod.snd #[v]
            let Hbody := mkAppN (mkConst
              `JanetCartan.PhysicalMean.OriginalBackgroundHermitian.H)
              (xs.push i |>.push color |>.push vx |>.push vz)
            let Hfun ← mkLambdaFVars #[v] Hbody
            let value ← mkAppM (ns ++ `periodicH) #[Hfun,w]
            let term ← mkLambdaFVars #[i,color,w] value
            saveDecl `actual_periodicH xs term true


/-- The unchanged uncurried physical field, not an amplitude-scaled surrogate. -/
def physicalH (d : ActualRow) (color : Expr) : MetaM Expr := do
  let n := d.raw13[0]!
  let pairType := mkApp2 (mkConst ``Prod [.zero,.zero])
    (mkApp (mkConst `JanetCartan.Euclidean) n)
    (mkConst `JanetCartan.SeparatedSampling.Point)
  withLocalDeclNoLocalInstanceUpdate `v .default pairType fun v => do
    let value := mkAppN (mkConst `JanetCartan.PhysicalMean.OriginalBackgroundHermitian.H)
      (d.parameters ++ #[color,.proj ``Prod 0 v,.proj ``Prod 1 v])
    mkLambdaFVars #[v] value

/-- Publish the support gap before the periodic smoothness/jet consumers. -/
elab "publish_original_periodic_background_support" : command => liftTermElabM <|
  withTransparency .reducible <| withActualRow fun d => do
    let bg := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
    let p := d.parameters
    let n := d.raw13[0]!
    let C := mkAppN (mkConst (bg ++ `C)) p
    let X := mkAppN (mkConst (bg ++ `X)) p
    let ψ := mkAppN (mkConst (bg ++ `ψ)) p
    let hC := mkAppN (mkConst (bg ++ `C_support_X)) p
    let physical := (← inferType C).bindingDomain!
    let point := mkConst `JanetCartan.SeparatedSampling.Point
    let pair := mkApp2 (mkConst ``Prod [.zero,.zero]) physical point
    let colorType := (← inferType d.native64[61]!).bindingDomain!
    withLocalDeclNoLocalInstanceUpdate `color .default colorType fun color => do
      let pc := p.push color
      let K ← physicalH d color
      let Hbody ← bodyAt (bg ++ `H) pc
      let M ← withLocalDeclNoLocalInstanceUpdate `v .default pair fun v => do
        let expanded := Hbody.beta #[.proj ``Prod 0 v,.proj ``Prod 1 v]
        let tensor := expanded.appArg!
        unless tensor.isAppOf `JanetCartan.hermitianTensor do
          throwError "original periodic background: baseline no longer factors through actual Hermitian tensor"
        mkLambdaFVars #[v] tensor
      let hfactor ← withLocalDeclNoLocalInstanceUpdate `x .default physical fun x =>
        withLocalDeclNoLocalInstanceUpdate `z .default point fun z => do
          let Hxz := mkAppN (mkConst (bg ++ `H)) (pc ++ #[x,z])
          mkLambdaFVars #[x,z] (← mkEqRefl Hxz)
      let hsX := mkAppN (mkConst (ns ++ `weighted_support_of_factor))
        #[n,X,ψ,K,C,M,hC,hfactor]
      let Xbody ← bodyAt (bg ++ `X) p
      unless Xbody.isAppOf ``Metric.closedBall do
        throwError "original periodic background: original support ball changed"
      let r := Xbody.appArg!
      let weighted ← withLocalDeclNoLocalInstanceUpdate `v .default pair fun v => do
        let value ← mkAppM ``HSMul.hSMul #[mkApp ψ (.proj ``Prod 1 v),mkApp K v]
        mkLambdaFVars #[v] value
      let gap := mkAppN (mkConst (ns ++ `support_gap_of_closedBall)) #[n,r,weighted,hsX]
      saveDecl `weighted_support pc gap

/-- Weighted smoothness and all jets of the SAME centered periodization. -/
elab "publish_original_periodic_background_profile " mode:num : command => liftTermElabM <|
  withTransparency .reducible <| withActualRow fun d => do
    let p := d.parameters
    let bg := `JanetCartan.PhysicalMean.OriginalBackgroundHermitian
    let weighted := `JanetCartan.PhysicalMean.OriginalWeightedHermitianProfiles
    let colorType := (← inferType d.native64[61]!).bindingDomain!
    withLocalDeclNoLocalInstanceUpdate `color .default colorType fun color => do
      let pc := p.push color
      let support := mkAppN (mkConst (ns ++ `weighted_support)) pc
      let gap := mkAppN (mkConst (bg ++ `X_cell_gap)) p
      let H ← physicalH d color
      let n := d.raw13[0]!
      let r := (← bodyAt (bg ++ `X) p).appArg!
      let ψ := mkAppN (mkConst (bg ++ `ψ)) p
      let rawPeriod := mkApp2 (mkConst (ns ++ `periodicH)) n H
      let namedPeriod := mkAppN (mkConst (ns ++ `actual_periodicH)) pc
      let (short,proof) ← match mode.getNat with
        | 0 => do
          let h := mkAppN (mkConst (weighted ++ `weighted_smooth)) pc
          pure (`weighted_smooth, mkAppN (mkConst (ns ++ `weighted_periodic_smooth))
            #[n,r,ψ,H,support,h,gap])
        | 1 => do
          let h := mkAppN (mkConst (weighted ++ `weighted_jets)) pc
          let D := mkAppN (mkConst (weighted ++ `D)) (p[:44].toArray.push d.row)
          pure (`weighted_jets, mkAppN (mkConst (ns ++ `weighted_periodic_jets))
            #[n,r,ψ,H,support,gap,D,d.mean70[60]!,d.mean70[61]!,h])
        | 2 => pure (`weighted_eq, mkAppN (mkConst (ns ++ `weighted_periodic_eq))
            #[n,r,ψ,H,support,gap])
        | _ => throwError "original periodic background: unknown profile field"
      let target := (← inferType proof).replace fun e =>
        if e == rawPeriod then some namedPeriod else none
      unless (target.find? (·.isAppOf (ns ++ `actual_periodicH))).isSome do
        throwError "original periodic background: actual periodization missing from profile target"
      saveDecl short pc proof false (some target)

/-- Data forcing for every original trial shift ξ, with exactly its extended U,
original outer B/ψ and original window. No shift bounds are needed for data. -/
elab "publish_original_periodic_background_forcing" : command => liftTermElabM <|
  withTransparency .reducible <| withActualSample fun xs ξ sa _J fI => do
    let I := sa[0]!
    unless I.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
      throwError "original periodic background: original static22 index missing"
    let fixed := I.getAppArgs
    let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
    let B := mkAppN (mkConst (outer ++ `B)) fixed
    let ψ := mkAppN (mkConst (outer ++ `ψ)) fixed
    let hψc := mkAppN (mkConst (outer ++ `compact)) fixed
    let hκc := mkConst `JanetCartan.PhysicalSampling.OriginalWindow.compact
    let hκ := mkConst `JanetCartan.PhysicalSampling.OriginalWindow.smooth
    let κ := mkConst `JanetCartan.PhysicalSampling.OriginalWindow.mollifier
    let p := sa[1]!
    let h := sa[5]!
    let U := sa[6]!
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let H := mkAppN (mkConst (ns ++ `actual_periodicH)) xs
    let smooth := mkAppN (mkConst (ns ++ `weighted_smooth)) xs
    let forcing := mkAppN (mkConst
      `JanetCartan.PhysicalMean.weightedOriginalBackgroundQuadratureForcing)
      #[n,I,fI,κ,hκc,hκ,p,B,h,ψ,hψc,U,H,smooth]
    saveDecl `forcing (xs.push ξ) forcing true

/-- The same forcing data specialized to the ONE released original shift. -/
elab "publish_original_periodic_background_selected_forcing" : command => liftTermElabM <|
  withTransparency .reducible <| withActualRow fun d => do
    let xs := d.parameters[:50].toArray
    let shift := mkAppN (mkConst
      `JanetCartan.PhysicalMean.OriginalCanonicalSelection.shift) xs
    let value := mkAppN (mkConst (ns ++ `forcing)) (xs.push shift)
    saveDecl `selected_forcing xs value true

/-- All analytic inputs are the actual frozen producers. Mode zero retains
h^p for every original positive order. Mode one uses ONLY the stated static
arithmetic guard sourceOrder+p ≤ rawSliceParameterOrder. -/
elab "publish_original_periodic_background_estimate " mode:num : command => liftTermElabM <|
  withTransparency .reducible <| withActualCanonicalSample fun xs ξ si _J fI hU _hξ => do
    let sa := si.getAppArgs
    let I := sa[0]!
    unless I.isAppOfArity `JanetCartan.PhysicalSampling.OriginalWeights.Index 22 do
      throwError "original periodic background: changed original static22 index"
    let fixed := I.getAppArgs
    let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
    let weighted := `JanetCartan.PhysicalMean.OriginalWeightedHermitianProfiles
    let n := mkApp (mkConst ``Nat.succ) xs[0]!
    let p := sa[1]!
    let rawForcing ← bodyAt (ns ++ `forcing) (xs.push ξ)
    unless rawForcing.isAppOfArity
        `JanetCartan.PhysicalMean.weightedOriginalBackgroundQuadratureForcing 14 do
      throwError "original periodic background: changed exact forcing constructor"
    let fa := rawForcing.getAppArgs
    unless fa[0]! == n && fa[1]! == I && fa[2]! == fI && fa[6]! == p && fa[11]! == sa[6]! do
      throwError "original periodic background: forcing changed dimension, index, Fintype, p or shift"
    let hBpos := mkAppN (mkConst (outer ++ `hB)) fixed
    let hB ← mkAppM ``le_of_lt #[hBpos]
    let hpatch := mkAppN (mkConst (outer ++ `patchBounds)) fixed
    let one ← mkNumeral (mkConst ``Real) 1
    let P ← withLocalDeclNoLocalInstanceUpdate `i .default I fun i =>
      mkLambdaFVars #[i] one
    let C ← withLocalDeclNoLocalInstanceUpdate `i .default I fun i =>
      mkLambdaFVars #[i] (mkAppN (mkConst (weighted ++ `D)) (xs[:44].toArray.push i))
    let hC ← withLocalDeclNoLocalInstanceUpdate `i .default I fun i =>
      mkLambdaFVars #[i] (mkAppN (mkConst (weighted ++ `D_nonneg)) (xs[:44].toArray.push i))
    let r₀ := mkApp (mkConst `JanetCartan.RawPrimary.SliceBounds.rawSliceParameterOrder) n
    let T := mkApp2 (mkConst `JanetCartan.currentCoefficientScale) xs[44]! xs[46]!
    let s₀ := mkApp (mkConst `JanetCartan.RevisedScales.sourceOrder) n
    let hTwo := mkAppN (mkConst `JanetCartan.PhysicalSampling.OriginalNativeGradedEvent.hS)
      xs[:44].toArray
    let facts ← mkAppM (ns ++ `original_scale_facts) #[hTwo,xs[45]!,xs[46]!]
    let hT := .proj ``And 0 facts
    let hh := .proj ``And 0 (.proj ``And 1 facts)
    let hh₁ := .proj ``And 1 (.proj ``And 1 facts)
    let physical := mkApp (mkConst `JanetCartan.Euclidean) n
    let point := mkConst `JanetCartan.SeparatedSampling.Point
    let colorType ← mkArrow (mkApp (mkConst ``Fin) (mkNatLit 3))
      (mkApp (mkConst ``Fin) (mkApp (mkConst ``Nat.succ) p))
    let cell := mkApp (mkConst `JanetCartan.fundamentalCell) n
    let finish (shortName : Name) (params : Array Expr) (reserve : Option Expr) : MetaM Unit := do
      withLocalDeclNoLocalInstanceUpdate `s .default (mkConst ``Nat) fun s => do
        let hjoint ← withLocalDeclNoLocalInstanceUpdate `q .default (mkConst ``Nat) fun q => do
          let hqType ← mkAppM ``LE.le #[q,s]
          withLocalDeclNoLocalInstanceUpdate `hq .default hqType fun hq =>
            withLocalDeclNoLocalInstanceUpdate `x .default physical fun x => do
              let hxType ← mkAppM ``Membership.mem #[cell,x]
              withLocalDeclNoLocalInstanceUpdate `hx .default hxType fun hx =>
                withLocalDeclNoLocalInstanceUpdate `i .default I fun i =>
                  withLocalDeclNoLocalInstanceUpdate `c .default colorType fun c =>
                    withLocalDeclNoLocalInstanceUpdate `z .default point fun z => do
                      let pq := mkApp2 (mkConst ``Nat.add) p q
                      let proof := mkAppN (mkConst (ns ++ `weighted_jets))
                        (xs ++ #[i,c,pq,x,hx,z])
                      mkLambdaFVars #[q,hq,x,hx,i,c,z] proof
        let common := #[n,I,fI,fa[3]!,fa[4]!,fa[5]!,
          mkConst `JanetCartan.PhysicalSampling.OriginalWindow.mass,
          mkConst `JanetCartan.PhysicalSampling.OriginalWindow.nonneg,
          mkConst `JanetCartan.PhysicalSampling.OriginalWindow.support,
          p,xs[43]!,fa[7]!,hB,P,fa[9]!,hpatch,fa[10]!,C,hC]
        let (_short,proof) := match reserve with
          | none => (`forcing_sharp, mkAppN (mkConst (ns ++ `weighted_forcing_sobolev_sharp))
              (common ++ #[r₀,T,hT,fa[12]!,fa[13]!,s,hjoint,fa[8]!,hh,hh₁,fa[11]!,hU]))
          | some hr => (`forcing_source_profile, mkAppN (mkConst
                `JanetCartan.PhysicalMean.weightedOriginalBackgroundQuadratureForcing_source_profile)
              (common ++ #[s₀,r₀,hr,fa[12]!,fa[13]!,s,T,hT,hjoint,fa[8]!,hh,hh₁,fa[11]!,hU]))
        let selected := mkAppN (mkConst (ns ++ `selected_forcing)) xs
        let target := (← inferType proof).replace fun e =>
          if e == rawForcing then some selected else none
        unless (target.find? (·.isAppOf (ns ++ `selected_forcing))).isSome do
          throwError "original periodic background: selected forcing missing from estimate target"
        saveDecl shortName (params.push s) proof false (some target)
    match mode.getNat with
    | 0 => finish `forcing_sharp xs none
    | 1 =>
      let hpType ← mkAppM ``LE.le #[mkApp2 (mkConst ``Nat.add) s₀ p,r₀]
      withLocalDeclNoLocalInstanceUpdate `hpReserve .default hpType fun hpReserve =>
        finish `forcing_source_profile (xs.push hpReserve) (some hpReserve)
    | 2 =>
      let hpType ← mkEq p (mkNatLit 1)
      withLocalDeclNoLocalInstanceUpdate `hOrderOne .default hpType fun hpOne => do
        let hr := mkAppN (mkConst (ns ++ `sampling_order_one_reserve_of_eq)) #[n,p,hpOne]
        finish `forcing_source_profile_order_one (xs.push hpOne) (some hr)
    | _ => throwError "original periodic background: unknown estimate field"

end JanetCartan.PhysicalMean.OriginalPeriodicBackgroundTemplate
end

