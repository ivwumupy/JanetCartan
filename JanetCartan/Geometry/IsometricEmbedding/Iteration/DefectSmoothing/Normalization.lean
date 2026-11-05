module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.DefectSmoothing.History

/-!
# The actual normalized source for the current mean

The paragraph following `main:eq:smoothing-combined` uses the same smoothed
signed defect divided by the actual square of `b = δ R^A`. Its estimates follow
already from the small-input bound and do not require the high-tail argument.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open Set

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.DefectSmoothing

variable {n : ℕ}

/-- Both physical Cʳ and periodic Hʳ bounds for the same normalized source
used by the current mean. The constant precedes all targets and histories;
only primitive smoothness, admissibility and the genuine zeroth defect bound
are assumed (`main:lem:smoothing`, after `main:eq:smoothing-combined`). -/
theorem exists_normalizedHistorySource_bound (D : LocalDomain) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R → ∀ δ : ℝ, 0 < δ →
      ∀ (g : MetricField n), ContDiffOn ℝ ∞ g (D.chart n) →
      ∀ (G : FlatReference n) (R₀ : ℝ) (kMin j : ℕ)
        (u : Fin j → Torus n → Euclidean (embeddingDimension n)) (ell : Fin j → ℕ),
      IsAdmissibleHistory R₀ kMin u ell →
      cNorm (D.core n) 0 (historyDefect g G.map u) ≤ δ ^ 2 →
      ∀ K : Set (Euclidean n),
      cNorm K r (periodicLift (normalizedHistorySource D R δ g G.map u)) +
        periodicSobolevNorm (r : ℝ) (normalizedHistorySource D R δ g G.map u) ≤
          C * R ^ ((r : ℝ) - 2 * forcingExponent n) := by
  obtain ⟨C, hC, hc⟩ := exists_periodicCutoff_cNorm_bound_of_bound n r
  refine ⟨(C + Real.sqrt 5 ^ r) * extensionZeroConstant,
    mul_nonneg (add_nonneg hC (by positivity)) extensionZeroConstant_pos.le, ?_⟩
  intro R hR δ hδ g hg G R₀ kMin j u ell hu hsmall K
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  let e := historyDefect g G.map u
  have he : ContDiffOn ℝ ∞ e (D.chart n) := contDiffOn_historyDefect hg G.contDiff hu
  have hf := isSmoothPeriodic_extendToTorus D
    (he.mono (Metric.closedBall_subset_ball D.coreRadius_lt_chartRadius))
  let a : ℝ := ((δ * R ^ forcingExponent n) ^ 2)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hcancel : a * δ ^ 2 = R ^ (-(2 * forcingExponent n)) := by
    have hp : (R ^ forcingExponent n) ^ 2 = R ^ (2 * forcingExponent n) := by
      rw [mul_comm 2, Real.rpow_mul hR0.le, Real.rpow_two]
    dsimp [a]
    rw [mul_pow, hp, mul_inv_rev, mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hδ.ne'),
      mul_one, Real.rpow_neg hR0.le]
  let f : Torus n → MetricTensor n := a • extendToTorus D e
  have hfc : Continuous f := continuous_const.smul hf.1
  have hbound : ∀ z, ‖f z‖ ≤ extensionZeroConstant * R ^ (-(2 * forcingExponent n)) := by
    intro z
    have hz : ‖extendToTorus D e z‖ ≤ extensionZeroConstant * δ ^ 2 :=
      (hf.norm_le_cNorm_zero z).trans ((cNorm_zero_extendToTorus_le D he).trans
        (mul_le_mul_of_nonneg_left hsmall extensionZeroConstant_pos.le))
    calc
      ‖f z‖ = a * ‖extendToTorus D e z‖ := by
        simp only [f, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
      _ ≤ a * (extensionZeroConstant * δ ^ 2) := mul_le_mul_of_nonneg_left hz ha.le
      _ = extensionZeroConstant * R ^ (-(2 * forcingExponent n)) := by
        rw [← hcancel]; ring
  have hsame : normalizedHistorySource D R δ g G.map u = periodicCutoff R f :=
    (periodicCutoff_smul hf.1 R a).symm
  rw [hsame]
  have hM : 0 ≤ extensionZeroConstant * R ^ (-(2 * forcingExponent n)) :=
    mul_nonneg extensionZeroConstant_pos.le (Real.rpow_nonneg hR0.le _)
  calc
    _ ≤ cNorm (fundamentalCell n) r (periodicLift (periodicCutoff R f)) +
        periodicSobolevNorm (r : ℝ) (periodicCutoff R f) :=
      add_le_add (BandHistory.cNorm_periodicLift_le_cell K r
        (isSmoothPeriodic_periodicCutoff R f)) le_rfl
    _ ≤ C * R ^ r * (extensionZeroConstant * R ^ (-(2 * forcingExponent n))) +
        Real.sqrt 5 ^ r * R ^ r * (extensionZeroConstant * R ^ (-(2 * forcingExponent n))) :=
      add_le_add (hc hR hfc hM hbound)
        (periodicSobolevNorm_periodicCutoff_le_of_bound hfc hR hM hbound r)
    _ = ((C + Real.sqrt 5 ^ r) * extensionZeroConstant) *
        (R ^ r * R ^ (-(2 * forcingExponent n))) := by ring
    _ = _ := by rw [← Real.rpow_natCast R r, ← Real.rpow_add hR0, sub_eq_add_neg]

end JanetCartan.DefectSmoothing
