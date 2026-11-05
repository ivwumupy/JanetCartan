module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition

/-! # Loss-two comparison of the actual stress jets

The C8-to-C6 step needed by `app:ch_seed:rem:seed-map-topology`.
All seminorm comparisons use compact domains and local smoothness.
-/

@[expose] public noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius Topology
open JanetCartan.ProjectedStressFrame
namespace JanetCartan.CurrentGeometricNeighborhood

/-- Subtraction commutes with the literal second jet on a smooth open domain
(`app:ch_seed:rem:seed-map-topology`). -/
theorem stressJet_sub_on_open {n N : ℕ} {F G : Euclidean n → Euclidean N}
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    {x : Euclidean n} (hx : x ∈ U) :
    stressJet (F - G) x = stressJet F x - stressJet G x := by
  have hf (y) (hy : y ∈ U) := hF.contDiffAt (hU.mem_nhds hy)
  have hg (y) (hy : y ∈ U) := hG.contDiffAt (hU.mem_nhds hy)
  have he : fderiv ℝ (F - G) =ᶠ[𝓝 x] fderiv ℝ F - fderiv ℝ G := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_sub ((hf y hy).differentiableAt (by simp))
      ((hg y hy).differentiableAt (by simp))
  apply Prod.ext
  · exact he.eq_of_nhds
  · change fderiv ℝ (fderiv ℝ (F - G)) x = _
    rw [he.fderiv_eq, fderiv_sub
      (((hf x hx).fderiv_right (show ∞ + 1 ≤ ∞ by simp)).differentiableAt (by simp))
      (((hg x hx).fderiv_right (show ∞ + 1 ≤ ∞ by simp)).differentiableAt (by simp))]
    rfl

/-- The C6 difference of actual second jets costs only the C8 difference of
maps (`app:ch_seed:rem:seed-map-topology`). -/
theorem cNorm_stressJet_sub_le {n N : ℕ} {F G : Euclidean n → Euclidean N}
    {K U : Set (Euclidean n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U) (m : ℕ) :
    cNorm K m (stressJet F - stressJet G) ≤ 2 * cNorm K (m + 2) (F - G) := by
  have he : cNorm K m (stressJet F - stressJet G) = cNorm K m (stressJet (F - G)) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro x hx
    filter_upwards [hU.mem_nhds (hKU hx)] with y hy
    exact (stressJet_sub_on_open hU hF hG hy).symm
  rw [he]
  exact cNorm_stressJet_le hK
    (fun x hx ↦ (hF.sub hG).contDiffAt (hU.mem_nhds (hKU hx))) m

/-- Compact C8 control bounds the pointwise jet error, including at the outer
closed-ball boundary (`app:ch_seed:rem:seed-map-topology`). -/
theorem norm_stressJet_sub_le {n N : ℕ} {F G : Euclidean n → Euclidean N}
    {K U : Set (Euclidean n)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) (hG : ContDiffOn ℝ ∞ G U)
    {x : Euclidean n} (hx : x ∈ K) :
    ‖stressJet F x - stressJet G x‖ ≤ 2 * cNorm K 8 (F - G) := by
  rw [← stressJet_sub_on_open hU hF hG (hKU hx)]
  exact (norm_stressJet_le_cNorm_four hK
    (fun y hy ↦ (hF.sub hG).contDiffAt (hU.mem_nhds (hKU hy))) hx).trans
      (mul_le_mul_of_nonneg_left (cNorm_mono_order (by norm_num : 4 ≤ 8)) (by norm_num))

end JanetCartan.CurrentGeometricNeighborhood
