module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.CanonicalGap.RadialSupport

/-!
# Radial scaling of the actual full chart and its differential

The input dilation fixes incidence and scales the covector. The full quotient
also changes epsilon to `epsilon * a`. These identities transfer normalized
comparison to the complete radial support in `exists_actual_radial_chart_comparison`,
the C¹ input to the full sampling inverse construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.FullNormalGeometry.RadialComparison
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualPhase ActualComparison NormalComparison
open ContinuumRow.CanonicalConic ContinuumRow.CanonicalCarrier
open MeanNormalBound.CanonicalGap ContinuumNormalReduction.ConicChart

variable {m : ℕ}

private def radialCoordinateEquiv (a : ℝ) (ha : a ≠ 0) :
    (ℝ × Euclidean m) ≃L[ℝ] (ℝ × Euclidean m) :=
  ContinuousLinearEquiv.equivOfInverse
    (radialLinearMap a) (radialLinearMap a⁻¹)
    (by intro w; ext <;> simp [radialScale, smul_smul, ha])
    (by intro w; ext <;> simp [radialScale, smul_smul, ha])

private theorem fderiv_radialScale_of_eq {a : ℝ} (ha : a ≠ 0)
    {f g : (ℝ × Euclidean m) → ℝ × Euclidean m}
    (h : ∀ w, f (radialScale a w) = a • g w) (u : ℝ × Euclidean m) :
    fderiv ℝ f (radialScale a u) =
      a • (fderiv ℝ g u).comp (radialLinearMap a⁻¹) := by
  let R := radialCoordinateEquiv (m := m) a ha
  have he : f ∘ R = a • g := funext h
  have hd : (fderiv ℝ f (R u)).comp R.toContinuousLinearMap = a • fderiv ℝ g u := by
    rw [← R.comp_right_fderiv, he, fderiv_const_smul_field]
    rfl
  have hc := congrArg (fun L : (ℝ × Euclidean m) →L[ℝ] (ℝ × Euclidean m) ↦
    L.comp R.symm.toContinuousLinearMap) hd
  have hinv : R.toContinuousLinearMap.comp R.symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ (ℝ × Euclidean m) := by
    apply ContinuousLinearMap.ext
    intro v
    exact R.apply_symm_apply v
  rw [ContinuousLinearMap.comp_assoc, hinv, ContinuousLinearMap.comp_id,
    ContinuousLinearMap.smul_comp] at hc
  exact hc

/-- The inverse radial coordinate differential has a uniform norm bound on
the prescribed positive radial interval. This controls the C¹ transfer in
`exists_actual_radial_chart_comparison` (`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_radialLinearMap_inv_le {a amin : ℝ} (hamin : 0 < amin) (ha : amin ≤ a) :
    ‖radialLinearMap (E := Euclidean m) a⁻¹‖ ≤ 1 + amin⁻¹ := by
  have hapos : 0 < a := hamin.trans_le ha
  have hi : a⁻¹ ≤ amin⁻¹ := inv_anti₀ hamin ha
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  change max ‖w.1‖ ‖a⁻¹ • w.2‖ ≤ _
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos)]
  apply max_le
  · calc
      ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
      _ ≤ (1 + amin⁻¹) * ‖w‖ :=
        le_mul_of_one_le_left (norm_nonneg _) (by linarith [inv_pos.mpr hamin])
  · exact mul_le_mul (hi.trans (by linarith)) (norm_snd_le w) (norm_nonneg _)
      (by positivity)

/-- The frozen triangular chart scales in all output coordinates when only
the input covector is scaled (`app:ch_seed:prop:seed-phase-charts`). -/
theorem frozenChart_radialScale (v : ℝ → Euclidean m) (a : ℝ) (u : ℝ × Euclidean m) :
    frozenChart v (radialScale a u) = a • frozenChart v u := by
  ext <;> simp [frozenChart, radialScale, inner_smul_right]

/-- Exact radial differential of the frozen comparison map, used alongside
the actual epsilon-shifted differential (`app:ch_seed:prop:seed-phase-charts`). -/
theorem fderiv_frozenChart_radialScale (v : ℝ → Euclidean m) {a : ℝ}
    (ha : a ≠ 0) (u : ℝ × Euclidean m) :
    fderiv ℝ (frozenChart v) (radialScale a u) =
      a • (fderiv ℝ (frozenChart v) u).comp (radialLinearMap a⁻¹) :=
  fderiv_radialScale_of_eq ha (frozenChart_radialScale v a) u

variable {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})

/-- The SAME retained full chart obeys the exact radial law with epsilon
replaced by `epsilon * a`, including at zero. This follows from the published
physical-phase identification and quotient identity, with both endpoints and
spectators retained (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem fullChartFamily_radialScale
    (p : ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean m) × WithLp 2 (ℝ × Euclidean m))
    (a : ℝ) (u : ℝ × Euclidean m) :
    fullChartFamily (current T Q) (spatialCarrier T) p (radialScale a u) =
      a • fullChartFamily (current T Q) (spatialCarrier T) (p.1 * a, p.2) u := by
  have h := congrArg (adaptedSliceCoordinates T).equiv
    (averagedGradient_radialInput T Q p.2.1 p.1 a
      ((physicalCoordinates T).symm p.2.2.1) ((physicalCoordinates T).symm p.2.2.2)
      ((adaptedSliceCoordinates T).equiv.symm u))
  simp only [map_smul] at h
  rw [adaptedSliceCoordinates_apply, adaptedSliceCoordinates_apply,
    averagedGradient_normalizedFullPhase, averagedGradient_normalizedFullPhase] at h
  simpa only [fullPhaseParameters, radialInput, ContinuousLinearEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply, Prod.eta] using h

/-- Normalized differentiability at the shifted epsilon gives actual
differentiability on the complete radial support. The producer in
`exists_actual_radial_chart_comparison` is the actual open-box smoothness
theorem (`app:ch_seed:prop:seed-phase-charts`). -/
theorem differentiableAt_fullChartFamily_radialScale
    (p : ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean m) × WithLp 2 (ℝ × Euclidean m))
    {a : ℝ} (ha : a ≠ 0) {u : ℝ × Euclidean m}
    (hd : DifferentiableAt ℝ
      (fullChartFamily (current T Q) (spatialCarrier T) (p.1 * a, p.2)) u) :
    DifferentiableAt ℝ (fullChartFamily (current T Q) (spatialCarrier T) p)
      (radialScale a u) := by
  let R := radialCoordinateEquiv (m := m) a ha
  have he : fullChartFamily (current T Q) (spatialCarrier T) p ∘ R =
      a • fullChartFamily (current T Q) (spatialCarrier T) (p.1 * a, p.2) :=
    funext (fullChartFamily_radialScale T Q p a)
  apply R.comp_right_differentiableAt_iff.mp
  rw [he]
  exact hd.const_smul a

/-- Exact radial differential scaling for the actual full quotient, with the
essential epsilon shift. It holds for total derivatives without an additional
regularity hypothesis (`app:ch_seed:eq:seed-quotient-integral`). -/
theorem fderiv_fullChartFamily_radialScale
    (p : ℝ × Euclidean 2 × WithLp 2 (ℝ × Euclidean m) × WithLp 2 (ℝ × Euclidean m))
    {a : ℝ} (ha : a ≠ 0) (u : ℝ × Euclidean m) :
    fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T) p) (radialScale a u) =
      a • (fderiv ℝ (fullChartFamily (current T Q) (spatialCarrier T)
        (p.1 * a, p.2)) u).comp (radialLinearMap a⁻¹) :=
  fderiv_radialScale_of_eq ha (fullChartFamily_radialScale T Q p a) u

end JanetCartan.Sampling.FullNormalGeometry.RadialComparison
