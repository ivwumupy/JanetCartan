module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.MinorBounds.Algebra

/-!
# The actual inverse Gram bound

The fixed frame admission in `app:ch_waves:eq:WKB-residual` supplies a
positive energy gap. It bounds the literal inverse Gram in the Frobenius
norm, uniformly over the same admitted immersions and construction set.
This is the low inverse input to the joint strain grade; no inverse bound
is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.RawPrimary
open ProjectedStressFrame

/-- The energy estimate controls every column of the actual inverse, hence
its Frobenius norm. Used only for the Gram multiplier in
`app:ch_waves:eq:WKB-strain`. -/
private theorem frobenius_inverse_le_of_gram_energy {n : ℕ}
    (A : MetricTensor n) (hA : IsUnit A) {γ : ℝ} (hγ : 0 < γ)
    (henergy : ∀ c : Euclidean n, γ * (∑ i, (c i)^2) ≤
      ∑ i, ∑ j, c i * c j * A i j) :
    ‖A⁻¹‖ ≤ n * γ⁻¹ := by
  apply ActualCarriers.frobenius_le_card_mul_entry_bound _ (inv_nonneg.mpr hγ.le)
  intro i j
  let v : Euclidean n := WithLp.toLp 2 (fun k ↦ A⁻¹ k j)
  have hmul : A *ᵥ (fun k ↦ v k) = Pi.single j 1 := by
    ext k
    change (A * A⁻¹) k j = _
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA)]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have heq : (∑ k, ∑ l, v k * v l * A k l) = v j := by
    calc
      _ = ∑ k, v k * (A *ᵥ (fun l ↦ v l)) k := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by rw [hmul]; simp [Pi.single_apply, eq_comm]
  have hsq : ‖v‖^2 = ∑ k, (v k)^2 := by
    simp [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs]
  have hv : γ * ‖v‖^2 ≤ ‖v‖ := by
    rw [hsq]
    exact (henergy v).trans (heq.le.trans
      ((le_abs_self _).trans (PiLp.norm_apply_le v j)))
  have hnorm : ‖v‖ ≤ γ⁻¹ := by
    by_cases hz : ‖v‖ = 0
    · rw [hz]
      exact inv_nonneg.mpr hγ.le
    · have hp : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      rw [← one_div]
      apply (le_div_iff₀ hγ).mpr
      nlinarith
  exact (PiLp.norm_apply_le v i).trans hnorm

/-- Actual inverse-Gram invertibility and the uniform Frobenius bound follow
from the SAME retained frame threshold and gap. This discharges the low
inverse premise of the reconstruction grade in `app:ch_waves:eq:WKB-strain`.
The threshold must still be intersected by the parent's single initializer. -/
theorem projectedStress_inverseGram_bound_of_cNorm_closeness {n : ℕ} (hn : 5 ≤ n)
    {F : Euclidean n → Euclidean (embeddingDimension n)}
    {s K : Set (Euclidean n)} (hs : IsOpen s) (hK : IsCompact K) (hKs : K ⊆ s)
    (hF : ContDiffOn ℝ ∞ F s) (hi : IsImmersionOn F s)
    (hrank : HasFullNormalRankOn F s)
    (hclose : ∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) <
      ambientStrainFrameThreshold hn)
    {x : Euclidean n} (hx : x ∈ K) :
    IsUnit (WKB.stressGram (projectedStress F x)) ∧
      ‖(WKB.stressGram (projectedStress F x))⁻¹‖ ≤ n * (ambientStrainFrameGramGap hn)⁻¹ := by
  have hind := (projectedStress_tensorFrame_of_cNorm_closeness
    hn hs hK hKs hF hi hrank hclose hx).2.1
  have hunit : IsUnit (WKB.stressGram (projectedStress F x)) :=
    (Matrix.posDef_gram_of_linearIndependent hind).isUnit
  exact ⟨hunit, frobenius_inverse_le_of_gram_energy _ hunit (ambientStrainFrameGramGap_pos hn)
    (projectedStress_gram_energy_of_cNorm_closeness hn hs hK hKs hF hi hrank hclose hx)⟩

end JanetCartan.RawPrimary
