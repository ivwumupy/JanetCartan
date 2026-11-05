module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Normalization
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InputJacobian

/-!
# Input Jacobian jets on the actual source chart

The local-phase version of the input-Jacobian restriction estimate, for the
whole-image shell construction in actual-calculus Step 1. Its consumer is
`exists_normalizedWholeImage_jet_bounds`; no common target is required.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.FourierIntegral.WholeImageGeometry
open NormalComparison
variable {n : ℕ}
local notation "E" => Euclidean n

/-- Restricting the joint averaged-gradient derivative to its covector input
costs one derivative and no norm factor. This is the local-source variant of
`UniformNormalData.norm_iteratedFDeriv_inputJacobian_le`, used for
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem norm_iteratedFDeriv_averagedJacobian_le
    {φ : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (X ×ˢ D))
    {z : NormalVariables n} (hz : z ∈ X ×ˢ (X ×ˢ D)) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      averagedJacobian φ q.1 q.2.1 q.2.2) z‖ ≤
    ‖iteratedFDeriv ℝ (k + 1) (fun q : NormalVariables n ↦
      averagedGradient φ q.1 q.2.1 q.2.2) z‖ := by
  let S := E × (E × E)
  let U := X ×ˢ (X ×ˢ D)
  let f : S → E := fun q ↦ averagedGradient φ q.1 q.2.1 q.2.2
  let L : E →L[ℝ] S := (ContinuousLinearMap.inr ℝ E (E × E)).comp
    (ContinuousLinearMap.inr ℝ E E)
  let R : (S →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E S E).flip L
  have hU : IsOpen U := hX.prod (hX.prod hD)
  have hf (q) (hq : q ∈ U) : ContDiffAt ℝ ∞ f q :=
    (averagedGradient_contDiffOn hX hD hcX hφ).contDiffAt (hU.mem_nhds hq)
  have hL : ‖L‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by
      simpa using mul_le_mul (ContinuousLinearMap.norm_inr_le_one ℝ E (E × E))
        (ContinuousLinearMap.norm_inr_le_one ℝ E E) (norm_nonneg _) zero_le_one)
  have hR : ‖R‖ ≤ 1 := by
    apply R.opNorm_le_bound zero_le_one
    intro A
    change ‖A.comp L‖ ≤ 1 * ‖A‖
    exact (ContinuousLinearMap.opNorm_comp_le A L).trans
      (by simpa using mul_le_mul_of_nonneg_left hL (norm_nonneg A))
  have heq : EqOn (fun q : S ↦ fderiv ℝ (averagedGradient φ q.1 q.2.1) q.2.2)
      (R ∘ fderiv ℝ f) U := by
    intro q hq
    have hd : HasFDerivAt (fun u : E ↦ (q.1, (q.2.1, u))) L q.2.2 :=
      (hasFDerivAt_prodMk_right q.1 q.2).comp q.2.2
        (hasFDerivAt_prodMk_right q.2.1 q.2.2)
    exact ((hf q hq).differentiableAt (by simp) |>.hasFDerivAt.comp q.2.2 hd).fderiv
  have heqjet := iteratedFDerivWithin_congr (𝕜 := ℝ) heq hz k
  rw [iteratedFDerivWithin_of_isOpen k hU hz,
    iteratedFDerivWithin_of_isOpen k hU hz] at heqjet
  change ‖iteratedFDeriv ℝ k (fun q : S ↦ fderiv ℝ (averagedGradient φ q.1 q.2.1) q.2.2) z‖ ≤ _
  rw [heqjet]
  calc
    _ ≤ ‖R‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ f) z‖ :=
      R.norm_iteratedFDeriv_comp_left ((hf z hz).fderiv_right (m := ∞) (by simp)) (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ f) z‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- The original normalized phase jets through `N+2` control the joint
averaged-gradient jets through `N+1`, with a constant fixed before the phase
or source chart. This supplies the forward input to the inverse induction in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem averagedGradient_jets_le_of_phase_jets (N : ℕ) (B : ℝ)
    {φ : E → E → ℝ} {X D : Set E}
    (hX : IsOpen X) (hD : IsOpen D) (hcX : Convex ℝ X)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (X ×ˢ D))
    (hb : ∀ z ∈ X ×ˢ D, ∀ k ≤ N + 2,
      ‖iteratedFDeriv ℝ k (Function.uncurry φ) z‖ ≤ B)
    {z : NormalVariables n} (hz : z ∈ X ×ˢ (X ×ˢ D)) {k : ℕ} (hk : k ≤ N + 1) :
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      averagedGradient φ q.1 q.2.1 q.2.2) z‖ ≤ (3 : ℝ)^(N + 1) * |B| := by
  apply (norm_iteratedFDeriv_averagedGradient_le hX hD hcX hφ
    (C := fun _ ↦ B) (N := N + 2) (fun i hi z hz ↦ hb z hz i hi) (by omega) hz).trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) (abs_nonneg B)

end JanetCartan.FourierIntegral.WholeImageGeometry
