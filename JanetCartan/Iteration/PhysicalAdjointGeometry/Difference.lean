module

public import JanetCartan.Iteration.PhysicalAdjointGeometry.Jets
public import JanetCartan.Analysis.Operator.InverseStability

/-!
# Primitive phase comparison controls the actual mixed inverse

The consumer is the original current-phase geometry construction in
`app:ch_mean_pairs:eq:raw-adjoint-moments`. The coefficient error is derived
from two primitive phase derivatives; no inverse gap or inverse jet profile is
assumed as a substitute for that construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.PhysicalAdjointGeometry

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

/-- The fixed covector extraction is linear in the locally smooth phase
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem covectorGradient_sub {S S₀ : X × Euclidean m → ℝ}
    {p : X × Euclidean m} (hS : DifferentiableAt ℝ S p) (hS₀ : DifferentiableAt ℝ S₀ p) :
    covectorGradient (S - S₀) p = covectorGradient S p - covectorGradient S₀ p := by
  simp only [covectorGradient, fderiv_sub hS hS₀, ContinuousLinearMap.sub_comp, map_sub]

/-- Averaging the actual phase difference subtracts the actual averaged
coefficients, on the unchanged original segment
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem averagedCovector_sub {S S₀ : X × Euclidean m → ℝ}
    {Ω : Set (X × Euclidean m)} (hΩ : IsOpen Ω)
    (hS : ContDiffOn ℝ ∞ S Ω) (hS₀ : ContDiffOn ℝ ∞ S₀ Ω)
    {q : Point X m} (hseg : ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω) :
    averagedCovector (S - S₀) q = averagedCovector S q - averagedCovector S₀ q := by
  have hmap : Continuous (fun t : ℝ ↦ segment t q) := by
    change Continuous (fun t : ℝ ↦ (q.1, q.2.1 + t • q.2.2))
    fun_prop
  have hi := (((contDiffOn_covectorGradient hΩ hS).continuousOn).comp hmap.continuousOn
    hseg).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  have hi₀ := (((contDiffOn_covectorGradient hΩ hS₀).continuousOn).comp hmap.continuousOn
    hseg).intervalIntegrable_of_Icc (μ := volume) zero_le_one
  dsimp only [Function.comp_def] at hi hi₀
  unfold averagedCovector
  rw [← intervalIntegral.integral_sub hi hi₀]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  exact covectorGradient_sub
    ((hS.contDiffAt (hΩ.mem_nhds (hseg t (by simpa using ht)))).differentiableAt (by simp))
    ((hS₀.contDiffAt (hΩ.mem_nhds (hseg t (by simpa using ht)))).differentiableAt (by simp))

/-- The actual mixed transpose respects the primitive phase difference,
including all physical-time derivatives
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem mixedTranspose_averaged_sub [FiniteDimensional ℝ X]
    (W : Euclidean m →L[ℝ] X) {S S₀ : X × Euclidean m → ℝ}
    {Ω : Set (X × Euclidean m)} {V : Set (Point X m)}
    (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ S Ω) (hS₀ : ContDiffOn ℝ ∞ S₀ Ω)
    (hseg : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω)
    {q : Point X m} (hq : q ∈ V) :
    mixedTranspose W (averagedCovector (S - S₀)) q =
      mixedTranspose W (averagedCovector S) q - mixedTranspose W (averagedCovector S₀) q := by
  have he : averagedCovector (S - S₀) =ᶠ[𝓝 q] averagedCovector S - averagedCovector S₀ := by
    filter_upwards [hV.mem_nhds hq] with w hw
    exact averagedCovector_sub hΩ hS hS₀ (hseg w hw)
  have hs := (contDiffOn_averagedCovector hΩ hV hS hseg).contDiffAt (hV.mem_nhds hq)
  have hs₀ := (contDiffOn_averagedCovector hΩ hV hS₀ hseg).contDiffAt (hV.mem_nhds hq)
  simp only [mixedTranspose, he.fderiv_eq,
    fderiv_sub (hs.differentiableAt (by simp)) (hs₀.differentiableAt (by simp)),
    ContinuousLinearMap.sub_comp]

/-- Only two primitive phase orders control the actual transverse mixed
coefficient error. The constant is independent of the displacement frequency
(`app:ch_seed:prop:seed-phase-charts`). -/
theorem norm_mixedTranspose_sub_le [FiniteDimensional ℝ X]
    {W : Euclidean m →L[ℝ] X} (hW : ‖W‖ ≤ 1) {S S₀ : X × Euclidean m → ℝ}
    {Ω : Set (X × Euclidean m)} {V : Set (Point X m)}
    (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hS : ContDiffOn ℝ ∞ S Ω) (hS₀ : ContDiffOn ℝ ∞ S₀ Ω)
    (hseg : ∀ q ∈ V, ∀ t ∈ Icc (0 : ℝ) 1, segment t q ∈ Ω)
    {ε : ℝ} (hjet : ∀ j ≤ 2, ∀ p ∈ Ω, ‖iteratedFDeriv ℝ j (S - S₀) p‖ ≤ ε)
    {q : Point X m} (hq : q ∈ V) :
    ‖mixedTranspose W (averagedCovector S) q -
      mixedTranspose W (averagedCovector S₀) q‖ ≤ 2 * ε := by
  rw [← mixedTranspose_averaged_sub W hΩ hV hS hS₀ hseg hq]
  have hs := (contDiffOn_averagedCovector hΩ hV (hS.sub hS₀) hseg).contDiffAt
    (hV.mem_nhds hq)
  have hb := norm_jet_mixedTranspose_le hW hs 0
  rw [norm_iteratedFDeriv_zero] at hb
  exact hb.trans (by simpa using
    (norm_jet_averagedCovector_le hΩ hV (hS.sub hS₀) hseg hjet hq (k := 1)))

/-- The uniform inverse value bound follows from the proved mixed error
relative to the identity (`app:ch_mean_pairs:eq:raw-adjoint-moments`). -/
theorem inverse_of_mixed_near_one (A : Euclidean m →L[ℝ] Euclidean m)
    (hA : ‖A - 1‖ ≤ 1 / 2) : IsUnit A ∧ ‖Ring.inverse A‖ ≤ 2 := by
  have hI : ‖Ring.inverse (1 : Euclidean m →L[ℝ] Euclidean m)‖ ≤ (1 : ℝ) := by
    rw [Ring.inverse_one]
    change ‖ContinuousLinearMap.id ℝ (Euclidean m)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  have hb := OperatorInverse.inverse_stability_half 1 A isUnit_one hI (by simpa using hA)
  exact ⟨hb.1, by simpa using hb.2.1⟩

end JanetCartan.PhysicalAdjointGeometry
