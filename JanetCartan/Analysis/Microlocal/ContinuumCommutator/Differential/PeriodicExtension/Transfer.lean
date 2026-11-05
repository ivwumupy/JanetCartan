module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.Differential.Chart.WeakTransfer
public import JanetCartan.Analysis.Fourier.Periodic.SobolevScale.Distribution

/-!
# Independent extension of the operator on a first derivative

The actual full-amplitude kernel transfer identity constructs `T D_i : L² → H⁻¹`
independently of the higher commutator in `app:ch_background:eq:bg-commutator`.
-/

@[expose] public noncomputable section
open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap
open JanetCartan.AmplitudeBound JanetCartan.PeriodicLocalL2
set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.Pseudodifferential.DifferentialChart
open PeriodicSobolevSpace
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

variable (hd : 0 < d) (r : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (M : ℝ)
  (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)

/-- The transferred amplitude operator retains both physical positions and all
source derivatives (`app:ch_background:eq:bg-commutator`). -/
def torusTransferOperator (hd : 0 < d) (r : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (M : ℝ)
  (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)
 (i : Fin d) : PeriodicL2 d ℂ →L[ℂ] PeriodicL2 d ℂ :=
  torusL2Operator hd r (transferAmplitude b i)
    (contDiff_uncurry_transferAmplitude hb i)
    (supportedInCenteredBox_transferAmplitude b r hs i) (2 * M)
    (hasAmplitudeDerivativeBound_transferAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ M hM)

/-- First-order transfer on the unit torus, derived from the actual Euclidean
kernel identity using compact source extension and physical support
(`app:ch_background:eq:bg-commutator`). -/
theorem torusL2Operator_coordinate_transfer (hr : r < 1 / 2)
    (i : Fin d) (f : Torus d → ℂ) (hf : IsSmoothPeriodic f) :
    HasPeriodicWeakDerivative i
      (torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
        (toL2 0 (ofSmooth 0 f hf)))
      (torusTransferOperator hd r b hb hs M hM i (toL2 0 (ofSmooth 0 f hf)) +
        torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
          (toL2 0 (ofSmooth 0 (periodicCoordinateDeriv i f) (hf.coordinateDeriv i)))) := by
  obtain ⟨χ⟩ := nonempty_sourceCutoff (d := d) hr
  let A := twoPositionL2Operator hd r b hb hs M
    (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
  let B := twoPositionL2Operator hd r (transferAmplitude b i)
    (contDiff_uncurry_transferAmplitude hb i)
    (supportedInCenteredBox_transferAmplitude b r hs i) (2 * M)
    (hasAmplitudeDerivativeBound_transferAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ M hM)
  let u := χ.extendL2 hf
  let v := χ.extendL2 (hf.coordinateDeriv i)
  have he : orderedTransferAction (fun j ↦ lineDerivOp (EuclideanSpace.single j 1 : E))
      [i] (A u : 𝓢'(E, ℂ)) = ((B u + A v : EuclideanL2 d ℂ) : 𝓢'(E, ℂ)) := by
    have h := twoPositionL2Operator_lineDeriv_transfer hd r b hb hs M hM i
      (χ.extend f) (χ.smooth_extend hf) (χ.compact_extend f)
    have hd' := twoPositionL2Operator_derivative_extension hd r b hb hs M
      (amplitudeDerivativeBound_of_le hM (Nat.le_succ _)) χ hf [i]
    dsimp only at h hd'
    change A _ = A v at hd'
    rw [show ((B u + A v : EuclideanL2 d ℂ) : 𝓢'(E, ℂ)) =
      (B u : 𝓢'(E, ℂ)) + (A v : 𝓢'(E, ℂ)) from
        (Lp.toTemperedDistributionCLM ℂ volume 2).map_add _ _]
    change lineDerivOp (EuclideanSpace.single i 1 : E) (A u : 𝓢'(E, ℂ)) = _
    convert h using 1
    · rfl
    · rw [← hd']
      rfl
  have ha : ∀ᵐ x ∂volume, x ∉ chartBox r → A u x = 0 :=
    twoPositionL2Operator_supported hd r b hb hs M _ u
  have hav : ∀ᵐ x ∂volume, x ∉ chartBox r → A v x = 0 :=
    twoPositionL2Operator_supported hd r b hb hs M _ v
  have hb' : ∀ᵐ x ∂volume, x ∉ chartBox r → B u x = 0 :=
    twoPositionL2Operator_supported hd r (transferAmplitude b i) _ _ (2 * M) _ u
  have h := hasPeriodicWeakDerivativeList_of_chart hr χ [i] (A u) (B u + A v) ha he
  rw [χ.localize_add, χ.localize_eq _ hb', χ.localize_eq _ hav, map_add] at h
  rw [hasPeriodicWeakDerivativeList_singleton] at h
  have hA := torusL2Operator_eq_extension hd hr b hb hs M
    (amplitudeDerivativeBound_of_le hM (Nat.le_succ _)) χ hf
    (hf.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hAv := torusL2Operator_eq_extension hd hr b hb hs M
    (amplitudeDerivativeBound_of_le hM (Nat.le_succ _)) χ (hf.coordinateDeriv i)
    ((hf.coordinateDeriv i).1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hB := torusL2Operator_eq_extension hd hr (transferAmplitude b i)
    (contDiff_uncurry_transferAmplitude hb i)
    (supportedInCenteredBox_transferAmplitude b r hs i) (2 * M)
    (hasAmplitudeDerivativeBound_transferAmplitude b
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) i _ M hM) χ hf
    (hf.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  change HasPeriodicWeakDerivative i (toTorus (𝕜 := ℂ) (A u))
    (toTorus (𝕜 := ℂ) (B u) + toTorus (𝕜 := ℂ) (A v)) at h
  change HasPeriodicWeakDerivative i (torusL2Operator hd r b hb hs M _ _) (_ + _)
  change HasPeriodicWeakDerivative i (torusL2Operator hd r b hb hs M _ ((hf.1.memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).toLp f))
    (torusTransferOperator hd r b hb hs M hM i ((hf.1.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).toLp f) +
      torusL2Operator hd r b hb hs M _ (((hf.coordinateDeriv i).1.memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).toLp (periodicCoordinateDeriv i f)))
  rw [hA, show torusTransferOperator hd r b hb hs M hM i =
    torusL2Operator hd r (transferAmplitude b i) _ _ (2 * M) _ from rfl, hB, hAv]
  exact h

/-- The independently constructed distributional extension of `T D_i`. It uses
only the low primitive budget and the actual first-order transfer operator
(`app:ch_background:eq:bg-commutator`). -/
def torusOnCoordinateDerivative (hd : 0 < d) (r : ℝ)
  (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
  (hb : ContDiff ℝ ∞ (Function.uncurry b))
  (hs : ∀ ξ, SupportedInCenteredBox r (b ξ)) (M : ℝ)
  (hM : HasAmplitudeDerivativeBound b (2 * (d + 1) + 1) M)
 (i : Fin d) :
    PeriodicL2 d ℂ →L[ℝ] PeriodicSobolevNegativeOne d ℂ :=
  (PeriodicSobolevNegativeOne.coordinateDerivative i).comp
    ((torusL2Operator hd r b hb hs M
      (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))).restrictScalars ℝ) -
  PeriodicSobolevNegativeOne.ofL2.comp
    ((torusTransferOperator hd r b hb hs M hM i).restrictScalars ℝ)

/-- The first-order extension equals `T D_i` on every smooth input; this is a
consequence of kernel transfer, with no highest-order commutator in its definition
(`app:ch_background:eq:bg-commutator`). -/
theorem torusOnCoordinateDerivative_ofSmooth (hr : r < 1 / 2)
    (i : Fin d) (f : Torus d → ℂ) (hf : IsSmoothPeriodic f) :
    torusOnCoordinateDerivative hd r b hb hs M hM i (toL2 0 (ofSmooth 0 f hf)) =
      PeriodicSobolevNegativeOne.ofL2
        (torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
          (toL2 0 (ofSmooth 0 (periodicCoordinateDeriv i f) (hf.coordinateDeriv i)))) := by
  have h := (PeriodicSobolevNegativeOne.coordinateDerivative_eq_ofL2_iff _ _ _).mpr
    (torusL2Operator_coordinate_transfer hd r b hb hs M hM hr i f hf)
  simp only [torusOnCoordinateDerivative, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars']
  rw [h, map_add, add_sub_cancel_left]

/-- Smooth L² density uniquely characterizes the independent first-order
extension (`app:ch_background:eq:bg-commutator`). -/
theorem torusOnCoordinateDerivative_unique (hr : r < 1 / 2) (i : Fin d)
    (S : PeriodicL2 d ℂ →L[ℝ] PeriodicSobolevNegativeOne d ℂ)
    (hS : ∀ (f : Torus d → ℂ) (hf : IsSmoothPeriodic f),
      S (toL2 0 (ofSmooth 0 f hf)) = PeriodicSobolevNegativeOne.ofL2
        (torusL2Operator hd r b hb hs M (amplitudeDerivativeBound_of_le hM (Nat.le_succ _))
          (toL2 0 (ofSmooth 0 (periodicCoordinateDeriv i f) (hf.coordinateDeriv i))))) :
    S = torusOnCoordinateDerivative hd r b hb hs M hM i := by
  apply DFunLike.coe_injective
  apply (denseRange_toL2_ofSmooth 0).equalizer S.continuous
    (torusOnCoordinateDerivative hd r b hb hs M hM i).continuous
  funext f
  exact (hS f.val f.property).trans
    (torusOnCoordinateDerivative_ofSmooth hd r b hb hs M hM hr i f.val f.property).symm

end JanetCartan.Pseudodifferential.DifferentialChart
