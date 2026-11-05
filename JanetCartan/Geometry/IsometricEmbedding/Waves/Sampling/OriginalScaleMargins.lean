module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RetainedPhaseMargins
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ScaleGap
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CurrentNormalComparison.Decay

/-!
# The retained sampling margins at the original iteration scales

Use the unchanged ceiling `H = R^(1+θ)`, carrier `λ = R^a` and
mesh `h = R^(-β)`. The sampling slack in units of `H` is
`(ε-θ)/(1+θ)`. The fixed strict power gap absorbs the retained phase
constant before the initial frequency, stage, radial labels or history.
These are the numerical inputs of the actual retained product event;
the geometric and current-field constructions remain separate obligations.
-/

@[expose] public noncomputable section
open Set Filter
namespace JanetCartan.Sampling
open ActualCarriers FrozenMenu CurrentFullPhase NormalComparison RawInputPartition
open SeparatedSampling MeasuredAmplitude

/-- The actual sampling mesh at the original mean ceiling is the unchanged
stage mesh (`app:ch_mean_pairs:eq:mean-stage-window`). -/
theorem samplingMesh_originalScale {R : ℝ} (hR : 0 ≤ R) :
    samplingMesh ((samplingSlack - meanSlack) / (1 + meanSlack)) (R ^ (1 + meanSlack)) =
      R ^ (-separationExponent) := by
  rw [samplingMesh, ← Real.rpow_mul hR]
  congr 1
  norm_num [samplingSlack, meanSlack, separationExponent]

/-- Rescaling the event tolerance by the original ceiling gives the original
sampling error exponent (`app:ch_mean_pairs:eq:mean-stage-normal-errors`). -/
theorem samplingTolerance_originalScale {R : ℝ} (hR : 0 ≤ R) :
    samplingTolerance ((samplingSlack - meanSlack) / (1 + meanSlack)) (R ^ (1 + meanSlack)) =
      R ^ (-(samplingSlack - meanSlack) / 4) := by
  rw [samplingTolerance, ← Real.rpow_mul hR]
  congr 1
  norm_num [samplingSlack, meanSlack]

/-- The retained colored-to-transport error uses exactly the original
carrier/ceiling/mesh power, with no replacement exponent
(`app:ch_mean_pairs:eq:mean-stage-normal-errors`). -/
theorem retainedTransportError_originalScale {R : ℝ} (hR : 0 < R) :
    (R ^ carrierExponent)⁻¹ * R ^ (1 + meanSlack) /
      samplingMesh ((samplingSlack - meanSlack) / (1 + meanSlack)) (R ^ (1 + meanSlack)) =
      R ^ (-carrierExponent + 1 + meanSlack + separationExponent) := by
  rw [samplingMesh_originalScale hR.le, ← Real.rpow_neg hR.le,
    ← Real.rpow_add hR, ← Real.rpow_sub hR]
  congr 1
  ring

/-- The actual two errors returned by the retained event satisfy the
original canonical decay, with the SAME transport constant
(`app:ch_mean_pairs:eq:mean-stage-normal-errors`, `main:eq:canonical-range`). -/
theorem retainedSamplingError_originalScale_le {R Ccompare : ℝ}
    (hR : 1 ≤ R) (hCcompare : 0 ≤ Ccompare) :
    samplingTolerance ((samplingSlack - meanSlack) / (1 + meanSlack))
        (R ^ (1 + meanSlack)) +
      Ccompare * (R ^ carrierExponent)⁻¹ * R ^ (1 + meanSlack) /
        samplingMesh ((samplingSlack - meanSlack) / (1 + meanSlack)) (R ^ (1 + meanSlack)) ≤
      (1 + Ccompare) * (R ^ (1 + meanSlack)) ^
        (-CurrentNormalComparison.normalDecayExponent
          samplingSlack meanSlack separationExponent carrierExponent) := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hfactor : Ccompare * (R ^ carrierExponent)⁻¹ * R ^ (1 + meanSlack) /
      samplingMesh ((samplingSlack - meanSlack) / (1 + meanSlack)) (R ^ (1 + meanSlack)) =
      Ccompare * ((R ^ carrierExponent)⁻¹ * R ^ (1 + meanSlack) /
        samplingMesh ((samplingSlack - meanSlack) / (1 + meanSlack)) (R ^ (1 + meanSlack))) :=
    by ring
  rw [samplingTolerance_originalScale hRpos.le, hfactor,
    retainedTransportError_originalScale hRpos,
    CurrentNormalComparison.fixed_normalDecayExponent_eq, ← Real.rpow_mul hRpos.le]
  have heq : -(samplingSlack - meanSlack) / 4 = (1 + meanSlack) * -(1 / 260 : ℝ) := by
    norm_num [samplingSlack, meanSlack]
  rw [heq]
  have htransport : R ^ (-carrierExponent + 1 + meanSlack + separationExponent) ≤
      R ^ ((1 + meanSlack) * -(1 / 260 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hR
      (by norm_num [carrierExponent, meanSlack, separationExponent])
  calc
    _ ≤ R ^ ((1 + meanSlack) * -(1 / 260 : ℝ)) +
        Ccompare * R ^ ((1 + meanSlack) * -(1 / 260 : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left htransport hCcompare)
    _ = _ := by ring

/-- One original initial-frequency threshold supplies the actual retained
phase margins at every stage. Its choice precedes all radial labels and
finite histories, and also enforces the supplied sampling-event threshold
(`app:ch_waves:thm:sampling`, `app:ch_mean_pairs:eq:mean-stage-window`). -/
theorem exists_retained_sampling_originalScale_threshold
    {m : ℕ} {J : Type*} [Fintype J]
    {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    (ρ : J → ℝ) (hρ : ∀ a, 0 < ρ a)
    (G : J → UniformNormalGeometry (m + 1) (m + 1))
    {Rmin : ℝ} (hRmin : 0 < Rmin) (eventThreshold : ℝ) :
    ∃ initialThreshold : ℝ, 2 ≤ initialThreshold ∧
      ∀ R : ℝ, initialThreshold ≤ R → ∀ stage : ℕ,
        let Rstage := historyScale R growthExponent stage
        eventThreshold ≤ Rstage ^ (1 + meanSlack) ∧
        1 ≤ Rstage ^ (1 + meanSlack) ∧ 1 ≤ Rstage ^ carrierExponent ∧
        1 ≤ Rmin * Rstage ^ carrierExponent ∧
        (∀ a, 2 * Rstage ^ (1 + meanSlack) / (Rmin * Rstage ^ carrierExponent) ≤ (G a).ε₀) ∧
        ∀ (p : ℕ) (radial : J → (Fin 3 → Fin (p + 1)) → ℝ),
          (∀ a color, Rmin ≤ radial a color) → ∀ a color,
          (radial a color * Rstage ^ carrierExponent)⁻¹ ∈ Icc (-1 : ℝ) 1 ∧
          (radial a color * Rstage ^ carrierExponent)⁻¹ ≠ 0 ∧
          ∀ j : Fin (cutoffCount (Rstage ^ (1 + meanSlack))),
            |(radial a color * Rstage ^ carrierExponent)⁻¹| * (2 : ℝ) ^ j.val ≤
              measuredPhaseRadius T hP (ρ := ρ a) ∧
            (radial a color * Rstage ^ carrierExponent)⁻¹ * (2 : ℝ) ^ j.val ∈
              Icc 0 (G a).ε₀ := by
  obtain ⟨Cscale, _, hmargin⟩ :=
    exists_retained_sampling_phase_margin_constant T hP ρ hρ G hRmin
  obtain ⟨S, hS⟩ := eventually_atTop.1
    (eventually_mul_rpow_le_of_exponent_lt Cscale
      (by norm_num [meanSlack, carrierExponent] : 1 + meanSlack < carrierExponent))
  refine ⟨max 2 (max S eventThreshold), le_max_left _ _, ?_⟩
  intro R hR stage
  have hRone : 1 ≤ R := (by norm_num : (1 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hR)
  have hstage : R ≤ historyScale R growthExponent stage := le_historyScale hRone stage
  have hstageOne : 1 ≤ historyScale R growthExponent stage := hRone.trans hstage
  have hlarge : S ≤ historyScale R growthExponent stage :=
    ((le_max_left S eventThreshold).trans ((le_max_right _ _).trans hR)).trans hstage
  have hceiling : historyScale R growthExponent stage ≤
      historyScale R growthExponent stage ^ (1 + meanSlack) :=
    Real.self_le_rpow_of_one_le hstageOne (by norm_num [meanSlack])
  exact ⟨((le_max_right S eventThreshold).trans
    ((le_max_right _ _).trans hR)).trans (hstage.trans hceiling),
    hstageOne.trans hceiling,
    hmargin _ (hstageOne.trans hceiling) _ (hS _ hlarge)⟩

end JanetCartan.Sampling
