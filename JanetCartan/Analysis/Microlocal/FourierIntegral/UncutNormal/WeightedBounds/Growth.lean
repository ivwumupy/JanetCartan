module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.UncutNormal.WeightedBounds.Support

/-!
# Global growth from original zeroth bounds

The complete buffered mask makes original chart bounds sufficient for global
order-zero growth of both graphs in `app:ch_regular_base:eq:actual-matrix-inverse`.
The density and inverse bounds are conclusions of the coefficient estimate.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.UncutNormal
open NormalComparison WholeImageGeometry
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Original mask/matrix values and the original mixed second phase derivative
suffice for global boundedness. Constants precede the fields; the two gaps are
only on the buffered chart, with no transformed norm hypothesis. This supplies
polynomial growth (degree zero) to the whole-image graph theorem for
`app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem exists_maskedAmplitudes_global_bound (M B₀ : ℝ)
    {δJ δU : ℝ} (hδJ : 0 < δJ) (hδU : 0 < δU) :
    ∃ P > 0, ∀ (X D : Set E) (S : E → E → ℝ) (c : E → E → ℝ) (U : E → E → Mat),
      IsOpen X → IsOpen D → Convex ℝ X →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      tsupport (Function.uncurry c) ⊆ X ×ˢ D →
      (∀ x ∈ X, ∀ u ∈ D, ‖c x u‖ ≤ M) →
      (∀ x ∈ X, ∀ u ∈ D, ‖U x u‖ ≤ M) →
      (∀ x ∈ X, ∀ u ∈ D,
        ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B₀) →
      (∀ x ∈ X, ∀ u ∈ D, δJ ≤ phaseJacobian S x u) →
      (∀ x ∈ X, ∀ u ∈ D, δU ≤ ‖(U x u).det‖) →
      ∀ x u, ‖maskedTransportAmplitude c U x u‖ ≤ P ∧
        ‖maskedWeightedAmplitude S c U x u‖ ≤ P := by
  obtain ⟨C, hC, hb⟩ := exists_weightedPrimitiveCoefficient_jet_bound (n := n) (r := r)
    0 (max M B₀) hδJ hδU
  refine ⟨max C (max 1 M ^ 2), hC.trans_le (le_max_left _ _), ?_⟩
  intro X D S c U hX hD hcX hS hbuffer hc hU hmix hJ hdet x u
  by_cases hz : c x u = 0
  · have he := maskedAmplitudes_eq_zero_of_mask_eq_zero S c U hz
    rw [he.1, he.2, norm_zero]
    exact ⟨(hC.trans_le (le_max_left _ _)).le, (hC.trans_le (le_max_left _ _)).le⟩
  · have hq : (x, u) ∈ X ×ˢ D := hbuffer (subset_tsupport (Function.uncurry c) hz)
    constructor
    · apply le_trans _ (le_max_right _ _)
      rw [maskedTransportAmplitude, norm_smul, Complex.norm_real]
      calc
        ‖c x u‖ * ‖U x u‖ ≤ max 1 M * max 1 M :=
          mul_le_mul ((hc x hq.1 u hq.2).trans (le_max_right _ _))
            ((hU x hq.1 u hq.2).trans (le_max_right _ _))
            (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _))
        _ = _ := (pow_two _).symm
    · let p : WeightedPrimitiveCoefficients n r :=
        (c x u, weightedPhaseDifferential S x u, U x u)
      have hp : ‖p‖ ≤ max M B₀ := by
        exact max_le ((hc x hq.1 u hq.2).trans (le_max_left _ _))
          (max_le ((norm_weightedPhaseDifferential_le hX hD hcX hS hmix hq.1 hq.2).trans
            (le_max_right _ _)) ((hU x hq.1 u hq.2).trans (le_max_left _ _)))
      have hgap : δJ ≤ |p.2.1.det| := by
        dsimp [p]
        rw [← phaseJacobian_eq_abs_weightedPhaseDifferential hX hD hcX hS hq.1 hq.2]
        exact hJ x hq.1 u hq.2
      have h := hb p hp hgap (hdet x hq.1 u hq.2) 0 le_rfl
      rw [norm_iteratedFDeriv_zero] at h
      have he : weightedPrimitiveCoefficient p = maskedWeightedAmplitude S c U x u := by
        dsimp [weightedPrimitiveCoefficient, p, maskedWeightedAmplitude]
        rw [phaseJacobian_eq_abs_weightedPhaseDifferential hX hD hcX hS hq.1 hq.2]
      rw [he] at h
      exact h.trans (le_max_left _ _)

end JanetCartan.FourierIntegral.UncutNormal
