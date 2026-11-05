module

public import JanetCartan.Geometry.IsometricEmbedding.Basic

/-!
# The fixed final rescaling

The last rescaling in Section 9, following `main:eq:final-Cr`.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology Matrix.Norms.Frobenius
open Filter

namespace JanetCartan

/-- Section 9 after `main:eq:final-Cr`: the fixed rescaling F(x) = a M(x/a)
cancels the two derivative scale factors. In the manuscript a = sρ. -/
theorem inducedMetric_rescale {n N : ℕ} {F : Euclidean n → Euclidean N}
    {a : ℝ} (ha : a ≠ 0) {x : Euclidean n}
    (hF : DifferentiableAt ℝ F (a⁻¹ • x)) :
    inducedMetric (fun y ↦ a • F (a⁻¹ • y)) x = inducedMetric F (a⁻¹ • x) := by
  have hd : fderiv ℝ (fun y ↦ a • F (a⁻¹ • y)) x = fderiv ℝ F (a⁻¹ • x) := by
    have h := ((hF.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul a⁻¹)).const_smul a).fderiv
    change fderiv ℝ (fun y ↦ a • F (a⁻¹ • y)) x = _ at h
    rw [h]
    ext z
    simp [smul_smul, ha]
  ext i j
  simp only [inducedMetric, partialDeriv, hd]

/-- Section 9 after `main:eq:final-Cr`: undo the target dilation on the inverse-image
domain; the rescaled map induces the original metric. -/
theorem isIsometricOn_rescale {n N : ℕ} {F : Euclidean n → Euclidean N}
    {g : MetricField n} {s : Set (Euclidean n)} {a : ℝ} (ha : a ≠ 0)
    (hF : DifferentiableOn ℝ F s) (hs : IsOpen s)
    (hmetric : IsIsometricOn (fun y ↦ g (a • y)) F s) :
    IsIsometricOn g (fun x ↦ a • F (a⁻¹ • x)) ((fun x ↦ a⁻¹ • x) ⁻¹' s) := by
  intro x hx
  rw [inducedMetric_rescale ha ((hF _ hx).differentiableAt (hs.mem_nhds hx)), hmetric hx]
  simp [smul_smul, ha]

/-- Section 9 after `main:eq:final-Cr`: rescaling gives a smooth isometry on the
one fixed domain a • s. Apply with a = sρ and the interior of the fixed core. -/
theorem smooth_isometric_rescale {n N : ℕ} {F : Euclidean n → Euclidean N}
    {g : MetricField n} {s : Set (Euclidean n)} {a : ℝ} (ha : a ≠ 0)
    (hF : ContDiffOn ℝ ∞ F s) (hs : IsOpen s)
    (hmetric : IsIsometricOn (fun y ↦ g (a • y)) F s) :
    ContDiffOn ℝ ∞ (fun x ↦ a • F (a⁻¹ • x)) ((fun y ↦ a • y) '' s) ∧
      IsIsometricOn g (fun x ↦ a • F (a⁻¹ • x)) ((fun y ↦ a • y) '' s) := by
  have hmaps : Set.MapsTo (fun x : Euclidean n ↦ a⁻¹ • x)
      ((fun y ↦ a • y) '' s) s := by
    rintro _ ⟨y, hy, rfl⟩
    simpa [smul_smul, ha] using hy
  refine ⟨(hF.comp (contDiff_id.const_smul a⁻¹).contDiffOn hmaps).const_smul a, ?_⟩
  intro x hx
  exact isIsometricOn_rescale ha (hF.differentiableOn (by simp)) hs hmetric (hmaps hx)

end JanetCartan
