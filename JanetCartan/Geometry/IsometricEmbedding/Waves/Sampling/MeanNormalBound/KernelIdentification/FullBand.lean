module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.ColumnNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.CarrierIntegral

/-!
# Full Euclidean band before phase-coordinate normalization

For `app:ch_waves:eq:sampling-prefix-normal`, combine the real slice parameter
and the original wide transverse band into one literal product Lebesgue input.
The kernel is constructed from the original measured sampling columns. A real
weight `ω` can be the continuous square root of the original `ψ`, or a fixed
smooth cutoff for a positive majorant. No smoothness of `sqrt ψ` is used.

The remaining consumer is the forward identification with
`NormalComparison.UniformNormalData.uniformOscillatoryOperator`: its producers
are `RawPrimary.Construction.fullPrimaryWave`, the leading amplitude, and the
actual `FullPhaseCharts`. It must preserve the input dilation and Fourier scalar.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped BigOperators

namespace JanetCartan.Sampling.MeanNormalBound
open RawInputPartition SamplingKernelBounds SeparatedSampling ContinuumRow

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n : ℕ}

/-- Continuity of the already constructed literal carrier coordinate change
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem continuous_carrierSamplingEquiv : Continuous carrierSamplingEquiv :=
  carrierSamplingLinearEquiv.toLinearMap.continuous_of_finiteDimensional

/-- Full-band input measure before dilation: the slice and transverse measures
are literal Lebesgue restrictions (`app:ch_waves:eq:sampling-prefix-normal`). -/
def fullBandMeasure (n j : ℕ) (B : ℝ) : Measure (ℝ × Euclidean (n - 1)) :=
  (volume.restrict (Set.Icc (-B) B)).prod (volume.restrict (wideBand n j))

/-- Both complex quadratures of the complete full-band input
(`app:ch_waves:eq:sampling-prefix-normal`). -/
abbrev FullBandInput (n j : ℕ) (B : ℝ) := Lp ℂ 2 (fullBandMeasure n j B)

/-- The full-band column retains the original physical kernel and real angular
weight (`app:ch_waves:eq:sampling-prefix-normal`). -/
def fullBandColumn (D : BandKernelData P n) (q : Point → P) (ω : Point → ℝ)
    (v : Euclidean 2) (u : ℝ × Euclidean (n - 1)) : SamplingKernelBounds.Output n :=
  ω (carrierSamplingEquiv (u.1, v)) • D.column (q (carrierSamplingEquiv (u.1, v))) u.2

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- The physical representative of the full-band column is the original
weighted sampling kernel, on literal Euclidean Lebesgue output
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullBandColumn_coe (D : BandKernelData P n) (q : Point → P) (ω : Point → ℝ)
    (v : Euclidean 2) (u : ℝ × Euclidean (n - 1)) :
    fullBandColumn D q ω v u =ᵐ[volume] fun x ↦
      ω (carrierSamplingEquiv (u.1, v)) • D.kernel (q (carrierSamplingEquiv (u.1, v))) u.2 x := by
  filter_upwards [Lp.coeFn_smul (ω (carrierSamplingEquiv (u.1, v)))
    (D.column (q (carrierSamplingEquiv (u.1, v))) u.2),
    D.column_coe (q (carrierSamplingEquiv (u.1, v))) u.2] with x hx hk
  exact hx.trans (congrArg (ω (carrierSamplingEquiv (u.1, v)) • ·) hk)

/-- Continuity of the full-band columns follows from the primitive continuous
phase, measured amplitude and weight (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem continuous_fullBandColumn (D : BandKernelData P n) (q : Point → P)
    (hq : Continuous q) (ω : Point → ℝ) (hω : Continuous ω) (v : Euclidean 2) :
    Continuous (fullBandColumn D q ω v) := by
  have hz : Continuous (fun u : ℝ × Euclidean (n - 1) ↦
      carrierSamplingEquiv (u.1, v)) :=
    continuous_carrierSamplingEquiv.comp (continuous_fst.prodMk continuous_const)
  exact (hω.comp hz).smul (D.continuous_column.comp ((hq.comp hz).prodMk continuous_snd))

/-- Compact full input bounds prove square integrability, with no operator
norm or normal identity assumed (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem memLp_fullBandColumn (D : BandKernelData P n) (q : Point → P)
    (hq : Continuous q) (ω : Point → ℝ) (hω : Continuous ω)
    (j : ℕ) (B : ℝ) (v : Euclidean 2) :
    MemLp (fullBandColumn D q ω v) 2 (fullBandMeasure n j B) := by
  rw [fullBandMeasure, Measure.prod_restrict]
  have hS : IsCompact (Set.Icc (-B) B ×ˢ wideBand n j) := isCompact_Icc.prod
    ((isCompact_closedBall (0 : Euclidean (n - 1)) (4 * dyadicScale j)).diff
      Metric.isOpen_ball)
  let : IsFiniteMeasure ((volume.prod volume).restrict
      (Set.Icc (-B) B ×ˢ wideBand n j)) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hS.measure_lt_top (μ := volume.prod volume)⟩
  have hc := continuous_fullBandColumn D q hq ω hω v
  obtain ⟨C, hC⟩ := hS.bddAbove_image hc.norm.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with u hu
  exact hC (Set.mem_image_of_mem _ hu)

/-- The actual Euclidean full-band operator before input-coordinate dilation
(`app:ch_waves:eq:sampling-prefix-normal`). -/
def fullBandKernelOperator (D : BandKernelData P n) (q : Point → P)
    (hq : Continuous q) (ω : Point → ℝ) (hω : Continuous ω)
    (j : ℕ) (B : ℝ) (v : Euclidean 2) :
    FullBandInput n j B →L[ℂ] SamplingKernelBounds.Output n :=
  kernelSynthesis (memLp_fullBandColumn D q hq ω hω j B v)

/-- Literal forward formula defining the full-band operator, keeping the
original slice parameter, frequency and physical columns
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullBandKernelOperator_apply (D : BandKernelData P n) (q : Point → P)
    (hq : Continuous q) (ω : Point → ℝ) (hω : Continuous ω)
    (j : ℕ) (B : ℝ) (v : Euclidean 2) (f : FullBandInput n j B) :
    fullBandKernelOperator D q hq ω hω j B v f =
      ∫ u, f u • fullBandColumn D q ω v u ∂fullBandMeasure n j B :=
  kernelSynthesis_apply (memLp_fullBandColumn D q hq ω hω j B v) f

/-- The full-band adjoint is derived from its actual forward kernel
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullBandKernelOperator_adjoint_ae (D : BandKernelData P n) (q : Point → P)
    (hq : Continuous q) (ω : Point → ℝ) (hω : Continuous ω)
    (j : ℕ) (B : ℝ) (v : Euclidean 2) (f : SamplingKernelBounds.Output n) :
    (fullBandKernelOperator D q hq ω hω j B v).adjoint f =ᵐ[fullBandMeasure n j B]
      fun u ↦ inner ℂ (fullBandColumn D q ω v u) f :=
  kernelSynthesis_hasAdjointKernel (memLp_fullBandColumn D q hq ω hω j B v) f

/-- The adjoint uses the conjugate physical kernel and the whole Euclidean
output. This is the matching interface for the normalized full-phase operator,
derived from the columns rather than assumed
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem fullBandKernelOperator_adjoint_ae_integral
    (D : BandKernelData P n) (q : Point → P) (hq : Continuous q)
    (ω : Point → ℝ) (hω : Continuous ω) (j : ℕ) (B : ℝ) (v : Euclidean 2)
    (f : SamplingKernelBounds.Output n) :
    (fullBandKernelOperator D q hq ω hω j B v).adjoint f =ᵐ[fullBandMeasure n j B]
      fun u ↦ ∫ x, inner ℂ
        (ω (carrierSamplingEquiv (u.1, v)) • D.kernel (q (carrierSamplingEquiv (u.1, v))) u.2 x)
        (f x) := by
  filter_upwards [fullBandKernelOperator_adjoint_ae D q hq ω hω j B v f] with u hu
  rw [hu, L2.inner_def]
  exact integral_congr_ae ((fullBandColumn_coe D q ω v u).mono
    (fun x hx ↦ congrArg (fun k ↦ inner ℂ k (f x)) hx))

private theorem rankOne_real_smul (c : ℝ) (k : SamplingKernelBounds.Output n) :
    InnerProductSpace.rankOne ℂ (c • k) (c • k) =
      c ^ 2 • InnerProductSpace.rankOne ℂ k k := by
  ext1 f
  simp only [InnerProductSpace.rankOne_apply, smul_apply,
    inner_smul_left_eq_smul, smul_assoc, pow_two]
  rw [smul_comm (inner ℂ k f) c k, smul_smul]

set_option maxHeartbeats 800000 in
/-- Reassembly and Fubini identify the actual full-band normal with the
weighted slice normals. Operator-norm Bochner integrability follows from
`memLp_fullBandColumn`, rather than being supplied as a premise
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullBandKernelOperator_normal_eq_slice (D : BandKernelData P n) (q : Point → P)
    (hq : Continuous q) (ω : Point → ℝ) (hω : Continuous ω)
    (j : ℕ) (B : ℝ) (v : Euclidean 2) :
    atomNormal (fullBandKernelOperator D q hq ω hω j B v) =
      ∫ s in Set.Icc (-B) B, ω (carrierSamplingEquiv (s, v)) ^ 2 •
        atomNormal (wideBandKernelOperator D j (q (carrierSamplingEquiv (s, v)))) := by
  rw [fullBandKernelOperator, kernelSynthesis_normal_eq_integral_rankOne]
  rw [show fullBandMeasure n j B =
    (volume.restrict (Set.Icc (-B) B)).prod (volume.restrict (wideBand n j)) from rfl]
  rw [integral_prod _ (integrable_rankOne_column (memLp_fullBandColumn D q hq ω hω j B v))]
  apply integral_congr_ae
  filter_upwards [] with s
  simp_rw [fullBandColumn, rankOne_real_smul, integral_smul]
  rw [wideBandKernelOperator, kernelSynthesis_normal_eq_integral_rankOne]

/-- The auxiliary slice interval disappears when it contains the actual
angular support (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullBandKernelOperator_normal_eq_integral (D : BandKernelData P n) (q : Point → P)
    (hq : Continuous q) (ω : Point → ℝ) (hω : Continuous ω)
    (j : ℕ) (B : ℝ) (v : Euclidean 2)
    (hs : ∀ z, ω z ≠ 0 → |z 0| ≤ B) :
    atomNormal (fullBandKernelOperator D q hq ω hω j B v) =
      ∫ s : ℝ, ω (carrierSamplingEquiv (s, v)) ^ 2 •
        atomNormal (wideBandKernelOperator D j (q (carrierSamplingEquiv (s, v)))) := by
  rw [fullBandKernelOperator_normal_eq_slice]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro s hs'
  have hz : ω (carrierSamplingEquiv (s, v)) = 0 := by
    by_contra hne
    have h := hs (carrierSamplingEquiv (s, v)) hne
    simp only [carrierSamplingEquiv_apply, Fin.cons_zero] at h
    exact hs' (abs_le.mp h)
  simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

/-- The original nonnegative weight has an exact full-band normal realization.
Only continuity of its square root is used; this operator is not asserted to
have a smooth amplitude (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem fullBandKernelOperator_sqrt_normal (D : BandKernelData P n) (q : Point → P)
    (hq : Continuous q) {ψ : Point → ℝ} {B C : ℝ}
    (hψ : PatchBounds ψ B C) (hc : Continuous ψ)
    (j : ℕ) (v : Euclidean 2) :
    atomNormal (fullBandKernelOperator D q hq (fun z ↦ Real.sqrt (ψ z))
      (Real.continuous_sqrt.comp hc) j B v) =
      ∫ s : ℝ, ψ (carrierSamplingEquiv (s, v)) •
        atomNormal (wideBandKernelOperator D j (q (carrierSamplingEquiv (s, v)))) := by
  rw [fullBandKernelOperator_normal_eq_integral D q hq _ _ j B v
    (fun z hz ↦ hψ.support z ((Real.sqrt_ne_zero (hψ.nonneg z)).mp hz) 0)]
  simp_rw [Real.sq_sqrt (hψ.nonneg _)]

end JanetCartan.Sampling.MeanNormalBound
