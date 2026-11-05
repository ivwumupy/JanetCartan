module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.SourceDensityLimitRealization.Weights
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Kernel

/-!
# Finite-kernel inputs from local zero-density primitives

The raw limit carrier requires only local smoothness on the existing mask
support. Prove its measurability by local zero extension and its finite-band
bound by compactness. Consumer: the supported-shell L² construction for the
genuine source-density limit (`bg-Nsigma`, `bg-T`, `bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.SourceDensityLimitRealization
open ContinuumRow AmplitudeBound PeriodicLocalL2
variable {n N : ℕ}

/-- Local primitives on the SAME measured support give a measurable raw
kernel, with no assumptions on off-support extensions (`bg-T`, `bg-Nsigma`). -/
theorem supported_kernel_stronglyMeasurable (d : CarrierData n N)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (hout : d.outputChart = torusChart (closedBall 0 (4 * r)))
    (hpoint : d.chartPoint = centeredTorusRepresentative)
    (hmeas : d.measurementCutoff = FixedCutoffs.periodic hr hcell 1)
    (hangularEq : d.angularCutoff = angular) (hhigh : d.highCutoff = FixedCutoffs.highFrequency)
    {O : Set (Euclidean n × CarrierParameter)} (hO : IsOpen O)
    (hpos : ContinuousOn (Function.uncurry d.transportedPosition) O)
    (hν : ContinuousOn (Function.uncurry d.normalField) O)
    (hq : ContinuousOn (fun p : Euclidean n × CarrierParameter ↦
      reducedCovector d p.1 (d.covector p.1 p.2)) O)
    (hang : Continuous (Function.uncurry angular))
    {Zp : Set CarrierParameter} (hangular : ∀ z ∉ Zp, ∀ η, angular z η = 0)
    (hsupport : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ Zp ⊆ O) :
    StronglyMeasurable (Function.uncurry (carrierKernel d)) := by
  classical
  let ν := Function.uncurry d.normalField
  let q := fun p : Euclidean n × CarrierParameter ↦
    reducedCovector d p.1 (d.covector p.1 p.2)
  let ψ := fun p : Torus n × CarrierVariable n ↦ (centeredTorusRepresentative p.1, p.2.1)
  have hψ : Measurable ψ :=
    (measurable_centeredTorusRepresentative.comp measurable_fst).prodMk measurable_snd.fst
  have hp0 : Measurable (O.indicator (Function.uncurry d.transportedPosition)) :=
    hpos.measurable_piecewise continuousOn_const hO.measurableSet
  have hn0 : Measurable (O.indicator ν) :=
    hν.measurable_piecewise continuousOn_const hO.measurableSet
  have hq0 : Measurable (O.indicator q) :=
    hq.measurable_piecewise continuousOn_const hO.measurableSet
  let v := fun p : Torus n × CarrierVariable n ↦
    ((FixedCutoffs.periodic hr hcell 1 p.1 *
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) * FixedCutoffs.highFrequency ‖p.2.2‖ *
      Real.sqrt ‖p.2.2‖ * ‖O.indicator ν (ψ p)‖ ^ 2) • O.indicator q (ψ p))
  have hη : Measurable (fun p : Torus n × CarrierVariable n ↦ p.2.2) := measurable_snd.snd
  have hang' : Measurable (fun p : Torus n × CarrierVariable n ↦
      angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2)) :=
    hang.measurable.comp (measurable_snd.fst.prodMk (hη.norm.inv.smul hη))
  have hv : Measurable v :=
    (((((FixedCutoffs.periodic hr hcell 1).continuous.measurable.comp measurable_fst).mul hang').mul
      (FixedCutoffs.highFrequency_smooth.continuous.measurable.comp hη.norm)).mul
        (Real.continuous_sqrt.measurable.comp hη.norm)).mul
          ((hn0.comp hψ).norm.pow_const 2) |>.smul (hq0.comp hψ)
  let k := fun p : Torus n × CarrierVariable n ↦
    Complex.exp (Complex.I * (inner ℝ (O.indicator (Function.uncurry d.transportedPosition) (ψ p)) p.2.2 : ℂ)) •
      euclideanComplexInclusion (v p)
  have hk : Measurable k := by
    dsimp only [k]
    apply Measurable.smul (M := ℂ) (X := EuclideanSpace ℂ (Fin n))
    · exact Complex.continuous_exp.measurable.comp
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          ((continuous_fst.inner continuous_snd).measurable.comp ((hp0.comp hψ).prodMk hη))))
    · exact euclideanComplexInclusion.continuous.measurable.comp hv
  have hchart : MeasurableSet (torusChart (closedBall (0 : Euclidean n) (4 * r))) :=
    measurableSet_torusChart isClosed_closedBall.measurableSet
  have he : Function.uncurry (carrierKernel
      d) =
      ((torusChart (closedBall (0 : Euclidean n) (4 * r))) ×ˢ univ).indicator k := by
    funext p
    simp only [Function.uncurry]
    by_cases hx : p.1 ∈ torusChart (closedBall (0 : Euclidean n) (4 * r))
    · by_cases hm : FixedCutoffs.physical hr 1 (centeredTorusRepresentative p.1) = 0
      · simp [carrierKernel, carrierAmplitude, hout, hmeas, hangularEq, hhigh, hpoint, hx, k, v, hm]
      · by_cases ha : angular p.2.1 (‖p.2.2‖⁻¹ • p.2.2) = 0
        · simp [carrierKernel, carrierAmplitude, hout, hmeas, hangularEq, hhigh, hpoint, hx, k, v, ha]
        · have hz : p.2.1 ∈ Zp := by
            by_contra hh
            exact ha (hangular _ hh _)
          have hp : ψ p ∈ O := hsupport ⟨subset_tsupport _ hm, hz⟩
          simp only [carrierKernel, carrierPhase, carrierAmplitude]
          simp [hmeas, hangularEq, hhigh, hpoint, hout, hx, k, v, hp, ψ, ν, q]
    · simp [carrierKernel, hout, hx]
  rw [he]
  exact (hk.indicator (hchart.prod MeasurableSet.univ)).stronglyMeasurable

/-- Compactness supplies the finite-kernel half-order bound for the literal
weighted normal. This is only the integrability input; the uniform L² constant
comes from the sharp zero-density coefficient controls (`bg-T`, `bg-frame`). -/
theorem exists_supported_carrierAmplitude_bound (d : CarrierData n N)
    {r : ℝ} (hr : 0 < r) (hcell : 4 * r < 1 / 2)
    (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
    (hpoint : d.chartPoint = centeredTorusRepresentative)
    (hmeas : d.measurementCutoff = FixedCutoffs.periodic hr hcell 1)
    (hangularEq : d.angularCutoff = angular) (hhigh : d.highCutoff = FixedCutoffs.highFrequency)
    {K : Set (Euclidean n × CarrierParameter)} (hK : IsCompact K)
    (hν : ContinuousOn (Function.uncurry d.normalField) K)
    (hq : ContinuousOn (fun p : Euclidean n × CarrierParameter ↦
      reducedCovector d p.1 (d.covector p.1 p.2)) K)
    (hang : Continuous (Function.uncurry angular))
    {Zp : Set CarrierParameter} (hZp : IsCompact Zp)
    (hangular : ∀ z ∉ Zp, ∀ η, angular z η = 0)
    (hsupport : tsupport (FixedCutoffs.physical (n := n) hr 1) ×ˢ Zp ⊆ K) :
    ∃ Cmask ≥ (0 : ℝ), ∀ x z, ‖carrierAmplitude d x z‖ ≤ Cmask * Real.sqrt ‖z.2‖ := by
  obtain ⟨Bn, hn⟩ := hK.exists_bound_of_continuousOn hν
  obtain ⟨Bq, hqbound⟩ := hK.exists_bound_of_continuousOn hq
  obtain ⟨Ba, habound⟩ := (hZp.prod (isCompact_closedBall (0 : Euclidean (n - 1)) 1)).exists_bound_of_continuousOn hang.continuousOn
  let Mn := max 0 Bn
  let Mq := max 0 Bq
  let Ma := max 0 Ba
  have hMn : 0 ≤ Mn := le_max_left _ _
  have hMq : 0 ≤ Mq := le_max_left _ _
  have hMa : 0 ≤ Ma := le_max_left _ _
  refine ⟨Ma * Mn ^ 2 * Mq, by positivity, ?_⟩
  intro x z
  have hRHS : 0 ≤ Ma * Mn ^ 2 * Mq * Real.sqrt ‖z.2‖ := by positivity
  by_cases hm : FixedCutoffs.physical hr 1 (d.chartPoint x) = 0
  · rw [hpoint] at hm
    simpa [carrierAmplitude, hmeas, hm] using hRHS
  by_cases ha : angular z.1 (‖z.2‖⁻¹ • z.2) = 0
  · simpa [carrierAmplitude, hangularEq, ha] using hRHS
  have hz : z.1 ∈ Zp := by
    by_contra hh
    exact ha (hangular _ hh _)
  have hp : (d.chartPoint x, z.1) ∈ K := hsupport ⟨subset_tsupport _ hm, hz⟩
  have hn' : ‖d.normalField (d.chartPoint x) z.1‖ ≤ Mn :=
    (hn _ hp).trans (le_max_right _ _)
  have hq' : ‖reducedCovector d (d.chartPoint x) (d.covector (d.chartPoint x) z.1)‖ ≤ Mq :=
    (hqbound _ hp).trans (le_max_right _ _)
  have hdir : ‖z.2‖⁻¹ • z.2 ∈ closedBall (0 : Euclidean (n - 1)) 1 := by
    rw [mem_closedBall_zero_iff]
    by_cases h : z.2 = 0
    · simp [h]
    · exact (norm_smul_inv_norm h).le
  have hang' : ‖angular z.1 (‖z.2‖⁻¹ • z.2)‖ ≤ Ma :=
    (habound (z.1, ‖z.2‖⁻¹ • z.2) ⟨hz, hdir⟩).trans (le_max_right _ _)
  have hm' : ‖d.measurementCutoff x‖ ≤ 1 := by
    rw [hmeas, Real.norm_eq_abs, abs_of_nonneg (FixedCutoffs.periodic_mem_Icc hr hcell 1 x).1]
    exact (FixedCutoffs.periodic_mem_Icc hr hcell 1 x).2
  have hh : ‖d.highCutoff ‖z.2‖‖ ≤ 1 := by
    rw [hhigh, Real.norm_eq_abs, abs_of_nonneg (FixedCutoffs.highFrequency_mem_Icc _).1]
    exact (FixedCutoffs.highFrequency_mem_Icc _).2
  rw [carrierAmplitude, norm_smul, norm_mul, norm_mul, norm_mul, norm_mul,
    Real.norm_eq_abs (Real.sqrt _), abs_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_eq_abs (_ ^ 2), abs_of_nonneg (sq_nonneg _), hangularEq]
  calc
    _ ≤ (1 * Ma * 1 * Real.sqrt ‖z.2‖ * Mn ^ 2) * Mq := by
      apply mul_le_mul _ hq' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ (sq_le_sq₀ (norm_nonneg _) hMn |>.mpr hn') (sq_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul hm' hang' (norm_nonneg _) zero_le_one) hh
          (norm_nonneg _) (by positivity)) (Real.sqrt_nonneg _)
    _ = _ := by ring

end JanetCartan.ContinuumNormal.SourceDensityLimitRealization
