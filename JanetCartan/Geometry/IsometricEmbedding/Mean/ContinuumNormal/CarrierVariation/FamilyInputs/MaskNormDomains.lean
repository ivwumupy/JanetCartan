module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalBudgets.Masks
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SupportBuffers

/-!
# Fixed mask norm domains on the normalized conic input

For `app:ch_osc:prop:osc-normal`, Step 4', and
`app:ch_background:eq:bg-full-complex-amplitude`. Complete the three mask
components of the coefficient norm charts after fixing the compact conic
input and the primitive field chart. The high-frequency chart concerns this
normalized compact input; the uncut cone is handled by conic homogeneity.
Consumer: `exists_finite_same_seed_primitive_inputs` and inverse comparison.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ContinuumNormalReduction.TransportSymbol ContinuumRow

/-- Complete a prescribed primitive field chart with compact norm domains for
all three original masks. The normalized angular argument has norm at most
one, including at zero, so no continuity of normalization at zero is needed.
The domains precede all coefficients, scales, densities and histories.
Source: `app:ch_background:eq:bg-full-complex-amplitude`.
This compact statement does not put the uncut cone in a bounded radial shell. -/
theorem exists_coefficientNormCharts_on_compact {n : ℕ}
    (D : PrimitiveNormChart (Euclidean n × CarrierParameter))
    {K : Set (InputVariables n)} (hK : IsCompact K)
    (hend : ∀ p ∈ K, (p.1.1, p.2.1) ∈ D.carrier ∧ (p.1.2, p.2.1) ∈ D.carrier) :
    ∃ E : CoefficientNormCharts n, E.field = D ∧
      E.measurement.region = univ ∧ E.angular.region = univ ∧ E.high.region = univ ∧
      (∀ p ∈ K, E.Contains p) ∧
      ∀ {r : ℝ} (hr : 0 < r) (angular : CarrierParameter → Euclidean (n - 1) → ℝ),
        ContDiff ℝ ∞ (Function.uncurry angular) →
        ∃ M ≥ 0, ∃ B : ℕ → ℝ, (∀ m, 1 ≤ B m) ∧
          ∀ m H, 1 ≤ H →
            E.measurement.Controls m M (B m) H (FixedCutoffs.physical hr 1) ∧
            E.angular.Controls m M (B m) H (Function.uncurry angular) ∧
            E.high.Controls m M (B m) H FixedCutoffs.highFrequency := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 1 0
  have hR0 : 0 < R := zero_lt_one.trans hR
  let E : CoefficientNormCharts n :=
    { measurement := ⟨0, R, hR0, univ, isOpen_univ, subset_univ _⟩
      angular := ⟨0, R, hR0, univ, isOpen_univ, subset_univ _⟩
      high := ⟨0, R, hR0, univ, isOpen_univ, subset_univ _⟩
      field := D }
  refine ⟨E, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro p hp
    have hnorm : (‖p.1.1‖ ≤ R ∧ ‖p.1.2‖ ≤ R) ∧
        (‖p.2.1‖ ≤ R ∧ ‖p.2.2‖ ≤ R) := by
      simpa only [mem_closedBall_zero_iff, Prod.norm_def, max_le_iff] using hKR hp
    have hang : ‖‖p.2.2‖⁻¹ • p.2.2‖ ≤ (1 : ℝ) := by
      by_cases hzero : p.2.2 = 0
      · simp [hzero]
      · exact (norm_smul_inv_norm (𝕜 := ℝ) hzero).le
    refine ⟨?_, ?_, ?_, ?_, (hend p hp).1, (hend p hp).2⟩
    · exact mem_closedBall_zero_iff.mpr hnorm.1.1
    · exact mem_closedBall_zero_iff.mpr hnorm.1.2
    · apply mem_closedBall_zero_iff.mpr
      exact max_le hnorm.2.1 (hang.trans hR.le)
    · apply mem_closedBall_zero_iff.mpr
      simpa only [norm_norm] using hnorm.2.2
  · intro r hr angular hang
    exact CanonicalCarrier.exists_fixedMask_controls E hr angular hang.contDiffOn

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
