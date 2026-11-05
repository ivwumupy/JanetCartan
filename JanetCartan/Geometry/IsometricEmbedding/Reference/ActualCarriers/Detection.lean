module

public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.LinearAlgebra.DetectorGram

import Mathlib.Tactic.FunProp

/-!
# Stability of the full carrier detector inequality

The last continuity argument in `app:ch_seed:prop:seed-actual-menu`, Step 3.
Both the image channel and the selected quadratic carrier vectors are retained.
The input is algebraic frozen detection; selecting the carriers and continuing
their incidence roots are separate geometric obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace
open scoped Topology
open Filter

namespace JanetCartan.ActualCarriers

variable {n : ℕ} {ι : Type*} [Fintype ι]

/-- The image channel `Mᵀs` in `app:ch_seed:eq:seed-actual-detection`. -/
def imageChannel (M : MetricTensor n) (s : Euclidean n) : Euclidean n :=
  WithLp.toLp 2 (M.transpose *ᵥ (fun j ↦ s j))

/-- The image and carrier channels as one finite family of real functionals
(`app:ch_seed:eq:seed-actual-detection`). -/
def detectors (M : MetricTensor n) (q : ι → Euclidean n) :
    Fin n ⊕ ι → Euclidean n →L[ℝ] ℝ
  | .inl i => innerSL ℝ (WithLp.toLp 2 (fun j ↦ M j i))
  | .inr a => innerSL ℝ (q a)

omit [Fintype ι] in
/-- The left block of the detector family is exactly the image channel
(`app:ch_seed:eq:seed-actual-detection`). -/
@[simp] theorem detectors_inl_apply (M : MetricTensor n) (q : ι → Euclidean n)
    (s : Euclidean n) (i : Fin n) :
    detectors M q (.inl i) s = imageChannel M s i := by
  simp [detectors, imageChannel, PiLp.inner_apply, Matrix.mulVec, dotProduct,
    mul_comm]

omit [Fintype ι] in
/-- The right block consists of the quadratic carrier pairings
(`app:ch_seed:eq:seed-actual-detection`). -/
@[simp] theorem detectors_inr_apply (M : MetricTensor n) (q : ι → Euclidean n)
    (s : Euclidean n) (a : ι) : detectors M q (.inr a) s = ⟪q a, s⟫_ℝ := rfl

/-- The Gram form of these functionals is the full detection expression
(`app:ch_seed:eq:seed-actual-detection`). -/
theorem inner_detectorGram (M : MetricTensor n) (q : ι → Euclidean n) (s : Euclidean n) :
    ⟪s, DetectorGram.weightedGram (detectors M q) (fun _ ↦ 1) s⟫_ℝ =
      ‖imageChannel M s‖ ^ 2 + ∑ a, ⟪q a, s⟫_ℝ ^ 2 := by
  rw [DetectorGram.inner_weightedGram_self, EuclideanSpace.real_norm_sq_eq]
  simp [Fintype.sum_sum_type]

omit [Fintype ι] in
/-- Common-kernel detection on the nullspace of `Mᵀ` is equivalent to full
finite-family detection (`app:ch_seed:prop:seed-frozen-menu`, Step 4). -/
theorem detects_of_imageChannel_kernel (M : MetricTensor n) (q : ι → Euclidean n)
    (hdet : ∀ s, imageChannel M s = 0 → (∀ a, ⟪q a, s⟫_ℝ = 0) → s = 0) :
    DetectorGram.Detects (detectors M q) := by
  intro s hs
  apply hdet s
  · ext i
    simpa using hs (.inl i)
  · intro a
    exact hs (.inr a)

omit [Fintype ι] in
/-- The detector family depends continuously on the Frobenius matrix and the
finite list of carrier vectors (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem continuous_detectors :
    Continuous (fun p : MetricTensor n × (ι → Euclidean n) ↦ detectors p.1 p.2) := by
  apply continuous_pi
  intro i
  cases i with
  | inl j =>
    change Continuous (fun p : MetricTensor n × (ι → Euclidean n) ↦
      innerSL ℝ (WithLp.toLp 2 (fun k ↦ p.1 k j)))
    exact (innerSL ℝ).continuous.comp
      ((PiLp.continuous_toLp 2 _).comp (by fun_prop))
  | inr a =>
    change Continuous (fun p : MetricTensor n × (ι → Euclidean n) ↦ innerSL ℝ (p.2 a))
    fun_prop

/-- A frozen detecting matrix and carrier list have a positive neighborhood
on which the complete actual detector inequality holds. The neighborhood is
in the Frobenius matrix norm and the supremum of the Euclidean carrier norms
(`app:ch_seed:eq:seed-actual-detection`). This proves stability, not the
geometric existence of the frozen list or the continued roots. -/
theorem exists_detection_perturbation_radius (M : MetricTensor n) (q : ι → Euclidean n)
    (hdet : ∀ s, imageChannel M s = 0 → (∀ a, ⟪q a, s⟫_ℝ = 0) → s = 0) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
      ∀ (M' : MetricTensor n) (q' : ι → Euclidean n),
        ‖M' - M‖ < δ → ‖q' - q‖ < δ → ∀ s : Euclidean n,
          c * ‖s‖ ^ 2 ≤ ‖imageChannel M' s‖ ^ 2 + ∑ a, ⟪q' a, s⟫_ℝ ^ 2 := by
  obtain ⟨c, hc, ε, hε, hgap⟩ := DetectorGram.exists_weightedGram_perturbation_radius
    (detects_of_imageChannel_kernel M q hdet) (w := fun _ ↦ 1) (fun _ ↦ zero_lt_one)
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp
    (continuous_detectors.continuousAt (x := (M, q))) ε hε
  refine ⟨c, δ, hc, hδ, ?_⟩
  intro M' q' hM' hq' s
  have hd : dist (M', q') (M, q) < δ := by
    simpa [Prod.dist_eq, dist_eq_norm, max_lt_iff] using And.intro hM' hq'
  have hf : ‖detectors M' q' - detectors M q‖ < ε := by
    simpa [dist_eq_norm] using hclose hd
  simpa only [inner_detectorGram] using
    hgap (detectors M' q') (fun _ ↦ 1) hf (by simpa using hε) s

/-- A compact family of frozen detecting data has one common perturbation
radius and one common positive lower bound
(`app:ch_seed:eq:seed-actual-detection`). The perturbed matrices and carrier
vectors can vary arbitrarily over the family, provided they stay in that radius. -/
theorem exists_uniform_detection_perturbation_radius
    {K : Set (MetricTensor n × (ι → Euclidean n))} (hK : IsCompact K)
    (hdet : ∀ p ∈ K, ∀ s, imageChannel p.1 s = 0 →
      (∀ a, ⟪p.2 a, s⟫_ℝ = 0) → s = 0) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧
      ∀ p ∈ K, ∀ (M' : MetricTensor n) (q' : ι → Euclidean n),
        ‖M' - p.1‖ < δ → ‖q' - p.2‖ < δ → ∀ s : Euclidean n,
          c * ‖s‖ ^ 2 ≤ ‖imageChannel M' s‖ ^ 2 + ∑ a, ⟪q' a, s⟫_ℝ ^ 2 := by
  let G := fun p : MetricTensor n × (ι → Euclidean n) ↦
    DetectorGram.weightedGram (detectors p.1 p.2) (fun _ ↦ 1)
  have hG : Continuous G := by
    apply continuousOn_univ.mp
    exact DetectorGram.continuousOn_weightedGram
      (fun i ↦ ((continuous_apply i).comp continuous_detectors).continuousOn)
      (fun _ ↦ continuousOn_const)
  obtain ⟨a, ha, hgap⟩ := DetectorGram.exists_uniform_weightedGram_lower_bound
    hK (fun p ↦ detectors p.1 p.2) (fun _ _ ↦ 1)
    (fun i ↦ ((continuous_apply i).comp continuous_detectors).continuousOn)
    (fun _ ↦ continuousOn_const)
    (fun p hp ↦ detects_of_imageChannel_kernel p.1 p.2 (hdet p hp))
    (fun _ _ _ ↦ zero_lt_one)
  have hcont : Continuous (fun z : (MetricTensor n × (ι → Euclidean n)) ×
      (MetricTensor n × (ι → Euclidean n)) ↦ ‖G (z.2 + z.1) - G z.2‖) :=
    ((hG.comp (continuous_snd.add continuous_fst)).sub (hG.comp continuous_snd)).norm
  have hev : ∀ᶠ e in 𝓝 (0 : MetricTensor n × (ι → Euclidean n)),
      ∀ p ∈ K, ‖G (p + e) - G p‖ < a / 2 := by
    apply hK.eventually_forall_of_forall_eventually
    intro p _
    have hzero : ‖G (p + 0) - G p‖ < a / 2 := by
      simpa only [add_zero, sub_self, norm_zero] using half_pos ha
    exact (hcont.continuousAt (x := (0, p))).eventually (gt_mem_nhds hzero)
  obtain ⟨δ, hδ, hclose⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨a / 2, δ, half_pos ha, hδ, ?_⟩
  intro p hp M' q' hM' hq' s
  have hd : dist ((M', q') - p) 0 < δ := by
    rw [dist_eq_norm, sub_zero, Prod.norm_def]
    exact max_lt hM' hq'
  have hop : ‖G (M', q') - G p‖ ≤ a / 2 := by
    have heq : p + ((M', q') - p) = (M', q') := by
      rw [← add_sub_assoc, add_sub_cancel_left]
    simpa only [heq] using (hclose hd p hp).le
  have h := DetectorGram.lower_bound_of_norm_sub_le (hgap p hp) hop s
  rw [show a - a / 2 = a / 2 by ring] at h
  exact h.trans_eq (inner_detectorGram M' q' s)

end JanetCartan.ActualCarriers
