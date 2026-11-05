module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Basic
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Euler's equation for the averaged gradient

The original phase's local degree-one homogeneity gives the averaged Euler
identity used in the frequency comparison for actual-calculus Step 1,
`app:ch_regular_base:eq:actual-normal-amplitude`. No conic invariance of the
entire source chart is required.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison LowBounds
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Homogeneity passes from the original phase to its averaged gradient on
any two points of the same positive ray in the original source chart.
This is the radial identity for `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem averagedGradient_smul_of_phase_homogeneous
    {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hhom : ∀ x ∈ X, ∀ u ∈ D, ∀ t : ℝ, 0 < t → t • u ∈ D →
      S x (t • u) = t * S x u)
    {x y u : E} (hx : x ∈ X) (hy : y ∈ X) (hu : u ∈ D)
    {t : ℝ} (ht : 0 < t) (htu : t • u ∈ D) :
    averagedGradient S x y (t • u) = t • averagedGradient S x y u := by
  unfold averagedGradient averagedPhaseDifferential
  rw [← map_smul, ← intervalIntegral.integral_smul]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hz : y + s • (x - y) ∈ X := hcX.add_smul_sub_mem hy hx (by simpa using hs)
  have he : (fun z ↦ S z (t • u)) =ᶠ[𝓝 (y + s • (x - y))] (fun z ↦ t * S z u) := by
    filter_upwards [hX.mem_nhds hz] with z hz
    exact hhom z hz u hu t ht htu
  have hd : DifferentiableAt ℝ (fun z ↦ S z u) (y + s • (x - y)) :=
    ((hS.contDiffAt ((hX.prod hD).mem_nhds ⟨hz, hu⟩)).comp _
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  exact he.fderiv_eq.trans (fderiv_const_mul hd t)

/-- Euler's equation for the original averaged Jacobian on the whole chart.
Together with its norm and determinant bounds this yields two-sided frequency
comparison in actual-calculus Step 1 (`app:ch_regular_base:eq:actual-normal-amplitude`). -/
theorem averagedJacobian_apply_self_of_homogeneous
    {S : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (X ×ˢ D))
    (hhom : ∀ x ∈ X, ∀ u ∈ D, ∀ t : ℝ, 0 < t → t • u ∈ D →
      S x (t • u) = t * S x u)
    {x y u : E} (hx : x ∈ X) (hy : y ∈ X) (hu : u ∈ D) :
    averagedJacobian S x y u u = averagedGradient S x y u := by
  have hf := (averagedGradient_contDiffOn hX hD hcX hS).contDiffAt
    (x := (x, (y, u))) ((hX.prod (hX.prod hD)).mem_nhds ⟨hx, hy, hu⟩)
  have hd : DifferentiableAt ℝ (averagedGradient S x y) u :=
    (hf.comp u (contDiffAt_const.prodMk
      (contDiffAt_const.prodMk contDiffAt_id))).differentiableAt (by simp)
  have hmem : ∀ᶠ t : ℝ in 𝓝 1, t • u ∈ D :=
    (continuousAt_id.smul continuousAt_const) (by simpa using hD.mem_nhds hu)
  have he : (fun t : ℝ ↦ averagedGradient S x y (t • u)) =ᶠ[𝓝 1]
      (fun t ↦ t • averagedGradient S x y u) := by
    filter_upwards [hmem, eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)] with t htu ht
    exact averagedGradient_smul_of_phase_homogeneous hX hD hcX hS hhom hx hy hu ht htu
  simpa [averagedJacobian] using hd.hasFDerivAt.apply_self_eq_smul_of_eventuallyEq
    (hasDerivAt_id (1 : ℝ)) he

end JanetCartan.FourierIntegral.WholeImageGeometry
