module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Frequency.Homogeneity

/-!
# Uniform whole-chart frequency comparison

The original mixed second-jet bound controls the averaged Jacobian. Euler's
identity and the determinant-gap inverse estimate then compare source and
normal frequencies. The constants are chosen before the phase, as required
by `app:ch_regular_base:thm:actual-calculus`, Step 1.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n : ℕ}
local notation "E" => Euclidean n

private theorem phaseDifferential_contDiffAt
    {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {x u : E} (hx : x ∈ X) (hu : u ∈ D) :
    ContDiffAt ℝ ∞ (fun q : E × E ↦ fderiv ℝ (fun z ↦ S z q.2) q.1) (x, u) := by
  have hp := hS.contDiffAt (x := (x, u)) ((hX.prod hD).mem_nhds ⟨hx, hu⟩)
  have ha : ContDiffAt ℝ ∞ (fun q : (E × E) × E ↦ S q.2 q.1.2) ((x, u), x) :=
    hp.comp ((x, u), x) (f := fun q : (E × E) × E ↦ (q.2, q.1.2))
      (contDiffAt_snd.prodMk contDiffAt_fst.snd)
  exact ha.fderiv contDiffAt_fst (by simp)

/-- The original mixed phase second-jet bound controls the averaged Jacobian
on the entire chart. Only a small convex neighborhood of each source point is
used, so the source chart need not be convex. This supplies the matrix norm
input for frequency comparison in `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem norm_averagedJacobian_le_of_mixed_bound
    {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    {B : ℝ} (hb : ∀ x ∈ X, ∀ u ∈ D,
      ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B)
    {x y u : E} (hx : x ∈ X) (hy : y ∈ X) (hu : u ∈ D) :
    ‖averagedJacobian S x y u‖ ≤ B := by
  have hB : 0 ≤ B := le_trans (norm_nonneg
    (fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u)) (hb x hx u hu)
  obtain ⟨r, hr, hrD⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hu)
  have hcont (v : E) (hv : v ∈ D) :
      ContinuousOn (fun t : ℝ ↦ fderiv ℝ (fun z ↦ S z v) (y + t • (x - y)))
        (uIcc (0 : ℝ) 1) := by
    intro t ht
    have hz : y + t • (x - y) ∈ X := hcX.add_smul_sub_mem hy hx (by simpa using ht)
    exact ((phaseDifferential_contDiffAt hX hD hS hz hv).continuousAt.comp
      (f := fun t : ℝ ↦ (y + t • (x - y), v))
      ((continuousAt_const.add (continuousAt_id.smul continuousAt_const)).prodMk
        continuousAt_const)).continuousWithinAt
  change ‖fderiv ℝ (averagedGradient S x y) u‖ ≤ B
  apply norm_fderiv_le_of_lip' ℝ hB
  filter_upwards [Metric.ball_mem_nhds u hr] with v hv
  unfold averagedGradient
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  unfold averagedPhaseDifferential
  rw [← intervalIntegral.integral_sub (hcont v (hrD hv)).intervalIntegrable
    (hcont u hu).intervalIntegrable]
  have hbound : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖fderiv ℝ (fun z ↦ S z v) (y + t • (x - y)) -
        fderiv ℝ (fun z ↦ S z u) (y + t • (x - y))‖ ≤ B * ‖v - u‖ := by
    intro t ht
    have hz : y + t • (x - y) ∈ X :=
      hcX.add_smul_sub_mem hy hx (by simpa using uIoc_subset_uIcc ht)
    apply (convex_ball u r).norm_image_sub_le_of_norm_fderiv_le
      (fun w hw ↦ ?_) (fun w hw ↦ hb _ hz w (hrD hw))
      (Metric.mem_ball_self hr) hv
    exact ((phaseDifferential_contDiffAt hX hD hS hz (hrD hw)).comp w
      (f := fun w : E ↦ (y + t • (x - y), w))
      (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- Two-sided whole-chart frequency comparison, with positive constants chosen
from the original mixed second-jet bound and determinant gap before choosing
the phase. The reverse inequality is consumed by
`primitiveNormalGeometry_of_frequency_bound`; both inequalities supply the
normalized shell range for `app:ch_regular_base:eq:actual-normal-amplitude`.
Injectivity is only needed later to construct the whole-image inverse. -/
theorem exists_frequency_comparison_of_mixed_bound (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ F > 0, ∃ C > 0, ∀ (S : E → E → ℝ) (X D : Set E),
      IsOpen X → IsOpen D → Convex ℝ X →
      ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D) →
      (∀ x ∈ X, ∀ u ∈ D, ∀ t : ℝ, 0 < t → t • u ∈ D →
        S x (t • u) = t * S x u) →
      (∀ x ∈ X, ∀ u ∈ D,
        ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B) →
      (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) →
      ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
        ‖averagedGradient S x y u‖ ≤ F * ‖u‖ ∧
        ‖u‖ ≤ C * ‖averagedGradient S x y u‖ := by
  obtain ⟨C, hC, hinv⟩ := exists_norm_inverse_le_of_det_gap («E» := Euclidean n) B hδ
  refine ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), C, hC, ?_⟩
  intro S X D hX hD hcX hS hhom hb hgap x hx y hy u hu
  have he := averagedJacobian_apply_self_of_homogeneous hX hD hcX hS hhom hx hy hu
  have hJ := norm_averagedJacobian_le_of_mixed_bound hX hD hcX hS hb hx hy hu
  have hdet := hgap x hx y hy u hu
  constructor
  · rw [← he]
    exact ((averagedJacobian S x y u).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (hJ.trans (le_max_right _ _)) (norm_nonneg _))
  · have huinv : (averagedJacobian S x y u).inverse (averagedGradient S x y u) = u := by
      rw [← he]
      exact (isInvertible_of_det_gap hδ hdet).inverse_apply_self u
    calc
      ‖u‖ = ‖(averagedJacobian S x y u).inverse (averagedGradient S x y u)‖ := by rw [huinv]
      _ ≤ ‖(averagedJacobian S x y u).inverse‖ * ‖averagedGradient S x y u‖ :=
        (averagedJacobian S x y u).inverse.le_opNorm _
      _ ≤ C * ‖averagedGradient S x y u‖ :=
        mul_le_mul_of_nonneg_right (hinv _ hJ hdet) (norm_nonneg _)

end JanetCartan.FourierIntegral.WholeImageGeometry
