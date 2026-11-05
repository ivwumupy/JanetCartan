module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.FixedCutoff
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampledMetric
public import JanetCartan.Geometry.IsometricEmbedding.Response.CurrentStrain

/-!
# Quantitative synthesis for the same sampled primary

The sample count and total weight in `main:eq:sampling` give the square-root
weight bound in `main:eq:primary-strain`. Apply it to the literal final family
in `SampledStage`, retaining the fixed physical cutoff. The per-atom strain
estimate must come from the corrected-atom producer on the final mean-updated
inputs; these deductions do not construct that family or the sample event.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.UniformStep

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- `main:eq:sampling` and `app:ch_pairs:eq:pairs-weighted-U`: the complete
signed-product coefficient mass costs one sample count. The constants are
unchanged for zero weights and the empty family. Consumed by the pair estimates
for the literal `ProductSum.offSelfSource` in `SampledStage`. -/
theorem sampled_coefficientMass_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {R Ccount Cmass : ℝ} (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass) :
    ProductSum.coefficientMass μ ≤ (Ccount * Cmass) * R ^ (1 + samplingSlack) := by
  calc
    _ ≤ (Fintype.card ι : ℝ) * Cmass :=
      ProductSum.coefficientMass_le_card_mul μ hμ hmass
    _ ≤ (Ccount * R ^ (1 + samplingSlack)) * Cmass :=
      mul_le_mul_of_nonneg_right hcount hCmass
    _ = _ := by ring

/-- `main:eq:primary-strain`: the actual finite sample weights have the
required square-root count loss. This is the weight input to
`sampled_primary_strain_le`, with constants preceding the stage scale. -/
theorem sampled_weight_sum_le (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {R Ccount Cmass : ℝ} (hR : 0 < R) (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass) :
    ∑ i, Real.sqrt (μ i) ≤
      Real.sqrt (Ccount * Cmass) * R ^ ((1 + samplingSlack) / 2) := by
  have h := Real.le_sqrt_of_sq_le
    (sampled_coefficientMass_le μ hμ hCmass hcount hmass)
  change (∑ i, Real.sqrt (μ i)) ≤ _ at h
  apply h.trans_eq
  rw [Real.sqrt_mul (mul_nonneg hCcount hCmass),
    Real.sqrt_eq_rpow (R ^ (1 + samplingSlack)),
    ← Real.rpow_mul hR.le]
  congr 2
  ring

/-- `main:eq:primary-strain` for the actual primary synthesis. The per-atom
real-quadrature strain is supplied by `both-corrected-atoms`, using the bounded
input measures from `both-current-mean`; `both-sampling` supplies the same
family's count and mass. No bound on the synthesized primary is a premise. -/
theorem sampled_primary_strain_le (F : Euclidean n → Euclidean N)
    (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)} {x : Euclidean n}
    (hZ : ∀ i, DifferentiableAt ℝ (Z i) x)
    {R δ C Ccount Cmass : ℝ} (q : ℕ)
    (hR : 0 < R) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hatom : ∀ i, ‖linearizedMetric F (euclideanRealPart ∘ Z i) x‖ ≤
      C * (R ^ carrierExponent) ^ (-(q : ℝ))) :
    ‖linearizedMetric F (sampledPrimary (δ * R ^ forcingExponent n) μ Z) x‖ ≤
      ((Real.sqrt 2 * C * Real.sqrt (Ccount * Cmass)) * δ) *
        (R ^ (forcingExponent n + (1 + samplingSlack) / 2) *
          (R ^ carrierExponent) ^ (-(q : ℝ))) := by
  have hr (i : ι) : DifferentiableAt ℝ (euclideanRealPart ∘ Z i) x :=
    euclideanRealPart.differentiableAt.comp x (hZ i)
  have hw := sampled_weight_sum_le μ hμ hR hCcount hCmass hcount hmass
  have hsum :
      ‖∑ i, Real.sqrt (μ i) • linearizedMetric F (euclideanRealPart ∘ Z i) x‖ ≤
        (∑ i, Real.sqrt (μ i)) * (C * (R ^ carrierExponent) ^ (-(q : ℝ))) := by
    exact WeightedFamily.norm_sum_weight_smul_le_of_norm_le Finset.univ
      (fun i ↦ Real.sqrt (μ i)) (fun _ _ ↦ Real.sqrt_nonneg _)
      (fun i ↦ linearizedMetric F (euclideanRealPart ∘ Z i) x) (fun i _ ↦ hatom i)
  rw [sampledPrimary,
    linearizedMetric_smul_apply (DifferentiableAt.sum
      (fun i _ ↦ (hr i).const_smul (Real.sqrt (μ i)))),
    linearizedMetric_sum_smul_apply Finset.univ _ _ (fun i _ ↦ hr i),
    norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (δ * R ^ forcingExponent n * Real.sqrt 2) *
        ((∑ i, Real.sqrt (μ i)) * (C * (R ^ carrierExponent) ^ (-(q : ℝ)))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (δ * R ^ forcingExponent n * Real.sqrt 2) *
        ((Real.sqrt (Ccount * Cmass) * R ^ ((1 + samplingSlack) / 2)) *
          (C * (R ^ carrierExponent) ^ (-(q : ℝ)))) := by
      gcongr
    _ = _ := by rw [Real.rpow_add hR]; ring

/-- `StageConstants.ComponentEstimates.strain` for exactly the cut primary
used in `identities_sampled_history_fields`. The physical cutoff changes no
core derivative; its choice is fixed before the sampled family. -/
theorem cut_sampled_primary_strain_le_of_contDiffOn (D : LocalDomain)
    (F : Euclidean n → Euclidean N) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n))
    {R δ C Ccount Cmass : ℝ} (q : ℕ)
    (hR : 0 < R) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hatom : ∀ i, ∀ x ∈ D.core n,
      ‖linearizedMetric F (euclideanRealPart ∘ Z i) x‖ ≤
        C * (R ^ carrierExponent) ^ (-(q : ℝ))) :
    ∀ x ∈ D.core n,
      ‖linearizedMetric F (periodicLift (Periodization.cutToTorus (physicalCutoff D)
        (sampledPrimary (δ * R ^ forcingExponent n) μ Z))) x‖ ≤
        ((Real.sqrt 2 * C * Real.sqrt (Ccount * Cmass)) * δ) *
          (R ^ (forcingExponent n + (1 + samplingSlack) / 2) *
            (R ^ carrierExponent) ^ (-(q : ℝ))) := by
  obtain ⟨_, _, hs, hcore, hone⟩ := physicalCutoff_properties (n := n) D
  intro x hx
  rw [Periodization.linearizedMetric_cutToTorus_eqOn D D.chartRadius_lt_half hs
    Metric.isOpen_ball hcore hone F _ hx]
  have hxc : x ∈ D.chart n := Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius hx
  exact sampled_primary_strain_le F μ hμ
    (fun i ↦ ((hZ i).contDiffAt (Metric.isOpen_ball.mem_nhds hxc)).differentiableAt (by simp))
    q hR hδ hC hCcount hCmass
    hcount hmass (fun i ↦ hatom i x hx)

/-- `main:eq:primary-strain`: preserve the global-smoothness API as a
specialization of the same local-field strain theorem. -/
theorem cut_sampled_primary_strain_le (D : LocalDomain)
    (F : Euclidean n → Euclidean N) (μ : ι → ℝ) (hμ : ∀ i, 0 ≤ μ i)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i))
    {R δ C Ccount Cmass : ℝ} (q : ℕ)
    (hR : 0 < R) (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hCcount : 0 ≤ Ccount) (hCmass : 0 ≤ Cmass)
    (hcount : (Fintype.card ι : ℝ) ≤ Ccount * R ^ (1 + samplingSlack))
    (hmass : ∑ i, μ i ≤ Cmass)
    (hatom : ∀ i, ∀ x ∈ D.core n,
      ‖linearizedMetric F (euclideanRealPart ∘ Z i) x‖ ≤
        C * (R ^ carrierExponent) ^ (-(q : ℝ))) :
    ∀ x ∈ D.core n,
      ‖linearizedMetric F (periodicLift (Periodization.cutToTorus (physicalCutoff D)
        (sampledPrimary (δ * R ^ forcingExponent n) μ Z))) x‖ ≤
        ((Real.sqrt 2 * C * Real.sqrt (Ccount * Cmass)) * δ) *
          (R ^ (forcingExponent n + (1 + samplingSlack) / 2) *
            (R ^ carrierExponent) ^ (-(q : ℝ))) :=
  cut_sampled_primary_strain_le_of_contDiffOn D F μ hμ (fun i ↦ (hZ i).contDiffOn) q
    hR hδ hC hCcount hCmass hcount hmass hatom

end JanetCartan.UniformStep
