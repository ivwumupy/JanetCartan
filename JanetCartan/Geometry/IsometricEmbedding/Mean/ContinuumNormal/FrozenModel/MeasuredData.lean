module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.FourierIdentity.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs

/-!
# The literal measured Euclidean datum

The finite frozen-model assembly needs L¹, L² and support for the same measured
zero extension in its Fourier identity (`app:ch_background:prop:bg-frame`).
These follow from the actual compact measurement cutoff for every torus L² datum.
-/

@[expose] public noncomputable section
open MeasureTheory Metric
open scoped ENNReal
namespace JanetCartan.ContinuumNormal.FrozenModel
open ContinuumRow PeriodicLocalL2

/-- Integrability, L² membership and exact physical support of the measured
zero extension used by `exists_finite_realized_frozen_model_energy`
(`app:ch_background:prop:bg-frame`). No regularity of the torus datum is needed. -/
theorem frozen_measured_zero_extension_integrable_memLp_support {n : ℕ} {μ : ℝ} (hμ : 0 < μ) (w : OutputL2 n) :
    let f := fun x ↦ euclideanComplexInclusion
      (FixedCutoffs.physical hμ 1 x • toEuclidean (𝕜 := ℝ) w x)
    Integrable f ∧ MemLp f 2 volume ∧
      (∀ x, x ∉ ball (0 : Euclidean n) (3 * μ) → f x = 0) := by
  let χ := FixedCutoffs.physical (n := n) hμ 1
  have hχ : MemLp (fun x ↦ (χ x : ℂ)) ∞ volume :=
    (Complex.continuous_ofReal.comp χ.continuous).memLp_top_of_hasCompactSupport
      (χ.hasCompactSupport.comp_left (g := fun t : ℝ ↦ (t : ℂ)) (by simp)) volume
  have heq := frozenMeasurementOperator_toEuclidean_coeFn χ hχ w
  refine ⟨(frozenMeasurementOperator_integrable χ hχ χ.continuous χ.hasCompactSupport
    (toEuclidean (𝕜 := ℂ) (l2ComplexInclusion volume w))).congr heq,
    (memLp_congr_ae heq).mp (Lp.memLp _), ?_⟩
  intro x hx
  have hz : FixedCutoffs.physical hμ 1 x = 0 := by
    by_contra h
    apply hx
    convert FixedCutoffs.physical_tsupport hμ 1 (subset_tsupport _ h) using 1
    norm_num
  simp [hz]

end JanetCartan.ContinuumNormal.FrozenModel
