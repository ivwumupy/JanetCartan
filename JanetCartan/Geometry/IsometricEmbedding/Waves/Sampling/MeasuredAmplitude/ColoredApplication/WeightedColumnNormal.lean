module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.ColumnNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.ReassembledDisintegration

/-!
# Weighted full-input normal identification on the actual phase domain

The input domain of the retained normal need not be a Cartesian product.
First extend its compactly supported columns to the full input space, then
restrict to the original full band and use its proved coordinate and dilation
identities. The original patch weight is an input multiplier. Only the smooth
auxiliary cutoff belongs to the amplitude. This supplies the weighted kernel
identification for `app:ch_waves:eq:colored-normal-comparison`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 3200000
open MeasureTheory Set InnerProductSpace
open scoped ENNReal

namespace JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
open SamplingKernelBounds ContinuumRow NormalComparison RawInputPartition Pseudodifferential
open ColoredNormalComparison ColoredNormalComparison.EuclideanDisintegration
open MeanNormalBound MeanNormalBound.NormalizedFullPhase

private theorem conjugate_coordinate_rankOne {n : ℕ} (k : SamplingKernelBounds.Output n) :
    samplingOutputConjugation n (rankOne ℂ (finiteL2CoordinateIsometry volume k)
      (finiteL2CoordinateIsometry volume k)) = rankOne ℂ k k := by
  let e := finiteL2CoordinateIsometry (I := Fin n) (volume : Measure (Euclidean n))
  ext1 f
  change e.symm (inner ℂ (e k) (e f) • e k) = inner ℂ k f • k
  rw [e.inner_map_map, map_smul, e.symm_apply_apply]

private theorem rankOne_real_smul {n : ℕ} (c : ℝ) (k : SamplingKernelBounds.Output n) :
    rankOne ℂ (c • k) (c • k) = c ^ 2 • rankOne ℂ k k := by
  ext1 f
  simp only [rankOne_apply, smul_apply, inner_smul_left_eq_smul, smul_assoc, pow_two]
  rw [smul_comm (inner ℂ k f) c k, smul_smul]

private theorem weighted_conjugate_normalized_column {n : ℕ}
    (a jac : ℝ) (hjac : 0 ≤ jac) (k : SamplingKernelBounds.Output n) :
    samplingOutputConjugation n ((a : ℂ) •
      rankOne ℂ (finiteL2CoordinateIsometry volume (Real.sqrt jac • k))
        (finiteL2CoordinateIsometry volume (Real.sqrt jac • k))) =
      jac • (a • rankOne ℂ k k) := by
  rw [map_smul, conjugate_coordinate_rankOne, rankOne_real_smul, Real.sq_sqrt hjac]
  calc
    _ = a • (jac • rankOne ℂ k k) :=
      (RCLike.real_smul_eq_coe_smul (K := ℂ) a (jac • rankOne ℂ k k)).symm
    _ = _ := smul_comm a jac _

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {m : ℕ}

/-- The supported phase and full-input column identities identify the weighted
normal without any product-domain hypothesis on `G.D`. Both sharp pieces
have already been reassembled into the smooth wide band. Bochner
integrability of the slice normal is a conclusion of the same continuous
columns (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem samplingNormal_eq_weighted_fullBand_slices
    (D : BandKernelData P (m + 1)) (q : SeparatedSampling.Point → P)
    (hq : Continuous q) (ψ : SeparatedSampling.Point → ℝ) (hψ : Continuous ψ)
    (β : SeparatedSampling.Point → ℝ) (hβ : Continuous β)
    (j : ℕ) (B : ℝ) (v : Euclidean 2)
    {G : UniformNormalGeometry (m + 1) (m + 1)} {C : ℕ → ℝ}
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (hphase : ∀ u ∈ Icc (-B) B ×ˢ wideBand (m + 1) 0, ∀ x,
      F.amplitude ε x (fullInputCoordinates m u) ≠ 0 →
      D.phase ((q (carrierSamplingEquiv (u.1, v)), (2 : ℝ) ^ j • u.2), x) =
        (2 : ℝ) ^ j * F.phase ε x (fullInputCoordinates m u))
    (hamplitude : ∀ u ∈ Icc (-B) B ×ˢ wideBand (m + 1) 0, ∀ x i,
      (Real.sqrt (((2 : ℝ) ^ j) ^ m) : ℂ) * (ψ (carrierSamplingEquiv (u.1, v)) : ℂ) *
        (Real.sqrt ‖(2 : ℝ) ^ j • u.2‖ : ℂ) * D.mask ((2 : ℝ) ^ j • u.2) *
          D.amplitude ((q (carrierSamplingEquiv (u.1, v)), (2 : ℝ) ^ j • u.2), x) i =
      (normalOperatorScale (m + 1) ((2 : ℝ) ^ j) : ℂ) *
        F.amplitude ε x (fullInputCoordinates m u) i)
    (hsupport : ∀ u, u ∉ fullInputDomain m 0 B → ∀ x, F.amplitude ε x u = 0)
    (g : Lp ℂ ∞ (volume.restrict G.D))
    (hg : g =ᵐ[volume.restrict G.D] fun u ↦
      (β (carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)) : ℂ)) :
    let f := fun s ↦ (β (carrierSamplingEquiv (s, v)) *
      ψ (carrierSamplingEquiv (s, v)) ^ 2) •
        atomNormal (wideBandKernelOperator D j (q (carrierSamplingEquiv (s, v))))
    Integrable f (volume.restrict (Icc (-B) B)) ∧
      samplingOutputConjugation (m + 1)
        (F.uniformOscillatoryNormalOperator ((2 : ℝ) ^ j) g ε) = ∫ s in Icc (-B) B, f s := by
  let k := uniformCoordinateColumn F ((2 : ℝ) ^ j) hε
  let ζ := fun u : Euclidean (m + 1) ↦
    carrierSamplingEquiv (((fullInputCoordinates m).symm u).1, v)
  let jac : ℝ := ((2 : ℝ) ^ j) ^ m
  have hjac : 0 < jac := by dsimp [jac]; positivity
  have hkzero (u : Euclidean (m + 1)) (hu : ∀ x, F.amplitude ε x u = 0) : k u = 0 := by
    ext i
    filter_upwards [uniformCoordinateColumn_coe F ((2 : ℝ) ^ j) hε u i,
      Lp.coeFn_zero ℂ 2 (volume : Measure (Euclidean (m + 1)))] with x hx hz
    change (k u i) x = (0 : Lp ℂ 2 (volume : Measure (Euclidean (m + 1)))) x
    rw [hx, hz]
    simp only [normalizedOscillatoryKernel, hu x, Pi.zero_apply, mul_zero]
  have hcol (u : ℝ × Euclidean m) (hu : u ∈ Icc (-B) B ×ˢ wideBand (m + 1) 0) :
      k (fullInputCoordinates m u) = finiteL2CoordinateIsometry volume
        (Real.sqrt jac • fullBandColumn D q ψ v (u.1, (2 : ℝ) ^ j • u.2)) := by
    ext i
    exact (uniformCoordinateColumn_coe F ((2 : ℝ) ^ j) hε _ i).trans
      (normalizedFullBandColumn_coordinate_ae_of_supported_phase D q ψ j v F ε u
        (hphase u hu) (hamplitude u hu) i).symm
  have hext : (∫ u in G.D, (β (ζ u) : ℂ) • rankOne ℂ (k u) (k u)) =
      ∫ u in fullInputDomain m 0 B, (β (ζ u) : ℂ) • rankOne ℂ (k u) (k u) := by
    trans ∫ u, (β (ζ u) : ℂ) • rankOne ℂ (k u) (k u)
    · apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      rw [hkzero u (fun x ↦ F.amplitude_eq_zero_off_carrier hε (z := (x, u))
        (fun hxu ↦ hu (G.D₀_subset hxu.2)))]
      rw [rankOne_eq_zero.mpr (Or.inl rfl), smul_zero]
    · symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro u hu
      rw [hkzero u (hsupport u hu)]
      rw [rankOne_eq_zero.mpr (Or.inl rfl), smul_zero]
  let H := fun u : ℝ × Euclidean m ↦ β (carrierSamplingEquiv (u.1, v)) •
    rankOne ℂ (fullBandColumn D q ψ v u) (fullBandColumn D q ψ v u)
  have hi : Integrable H (fullBandMeasure (m + 1) j B) := by
    rw [fullBandMeasure, Measure.prod_restrict]
    have hrc : Continuous (fun k : SamplingKernelBounds.Output (m + 1) ↦ rankOne ℂ k k) :=
      ((ContinuousLinearMap.smulRightL ℂ (SamplingKernelBounds.Output (m + 1))
        (SamplingKernelBounds.Output (m + 1))).continuous.comp (innerSL ℂ).continuous).clm_apply
        continuous_id
    have hH : Continuous H :=
      (hβ.comp (continuous_carrierSamplingEquiv.comp
        (continuous_fst.prodMk continuous_const))).smul
        (hrc.comp (continuous_fullBandColumn D q hq ψ hψ v))
    exact hH.continuousOn.integrableOn_compact
      (isCompact_Icc.prod (isCompact_samplingWideBand (m + 1) j))
  have hslice (s : ℝ) : (∫ η in wideBand (m + 1) j, H (s, η)) =
      (β (carrierSamplingEquiv (s, v)) * ψ (carrierSamplingEquiv (s, v)) ^ 2) •
        atomNormal (wideBandKernelOperator D j (q (carrierSamplingEquiv (s, v)))) := by
    simp only [H, fullBandColumn, rankOne_real_smul, smul_smul, integral_smul]
    exact congrArg (fun A ↦
      (β (carrierSamplingEquiv (s, v)) * ψ (carrierSamplingEquiv (s, v)) ^ 2) • A)
      (kernelSynthesis_normal_eq_integral_rankOne
        (MeanNormalBound.memLp_wideBand_column D j (q (carrierSamplingEquiv (s, v))))).symm
  refine ⟨?_, ?_⟩
  · exact hi.integral_prod_left.congr (Filter.Eventually.of_forall hslice)
  · rw [uniformOscillatoryNormalOperator_eq_integral_columns F ((2 : ℝ) ^ j) hε g]
    have hreplace : (∫ u in G.D, g u • rankOne ℂ (k u) (k u)) =
        ∫ u in G.D, (β (ζ u) : ℂ) • rankOne ℂ (k u) (k u) :=
      integral_congr_ae (hg.mono fun u hu ↦
        congrArg (fun t : ℂ ↦ t • rankOne ℂ (k u) (k u)) hu)
    change samplingOutputConjugation (m + 1)
      (∫ u in G.D, g u • rankOne ℂ (k u) (k u)) = _
    have hcoordinates := integral_fullInputCoordinates m 0 B
      (fun u ↦ (β (ζ u) : ℂ) • rankOne ℂ (k u) (k u))
    rw [hreplace, hext, ← hcoordinates,
      samplingOutputConjugation_integral (fullBandMeasure (m + 1) 0 B)
        (fun u ↦ (β (ζ (fullInputCoordinates m u)) : ℂ) •
          rankOne ℂ (k (fullInputCoordinates m u)) (k (fullInputCoordinates m u)))]
    have hpoint : (∫ u, samplingOutputConjugation (m + 1)
        ((β (ζ (fullInputCoordinates m u)) : ℂ) •
          rankOne ℂ (k (fullInputCoordinates m u)) (k (fullInputCoordinates m u)))
          ∂fullBandMeasure (m + 1) 0 B) =
        jac • ∫ u, H (fullInputDilation (m + 1) j u) ∂fullBandMeasure (m + 1) 0 B := by
      rw [← integral_smul]
      apply integral_congr_ae
      have hmem : ∀ᵐ u ∂fullBandMeasure (m + 1) 0 B,
          u ∈ Icc (-B) B ×ˢ wideBand (m + 1) 0 := by
        rw [fullBandMeasure, Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Icc.prod (measurableSet_wideBand _ _))
      filter_upwards [hmem] with u hu
      rw [hcol u hu]
      have hdilu : fullInputDilation (m + 1) j u = (u.1, (2 : ℝ) ^ j • u.2) := rfl
      simpa only [ζ, MeasurableEquiv.symm_apply_apply, hdilu, H] using
        weighted_conjugate_normalized_column (β (carrierSamplingEquiv (u.1, v))) jac hjac.le
          (fullBandColumn D q ψ v (u.1, (2 : ℝ) ^ j • u.2))
    rw [hpoint, integral_fullBand_dilation (m + 1) j B H, smul_smul]
    change (jac * jac⁻¹) • (∫ u, H u ∂fullBandMeasure (m + 1) j B) = _
    rw [mul_inv_cancel₀ hjac.ne', one_smul]
    exact (integral_prod H hi).trans (integral_congr_ae (Filter.Eventually.of_forall hslice))

end JanetCartan.Sampling.MeasuredAmplitude.ColoredApplication
