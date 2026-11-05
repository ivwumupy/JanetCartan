module

public import JanetCartan.Analysis.PhysicalSobolev.Cartesian
public import JanetCartan.Analysis.PhysicalSobolev.Embedding

/-!
# Physical interpolation of the same finite-iteration residual

Paper-v2 `new:lem:interpolation` is used at the fixed source order
`s₀ = 2 m₀`, not at an accuracy-dependent derivative order. Cauchy--Schwarz
on the actual radian-weighted vector Fourier transform gives the half-order
estimate. The existing physical embedding and Cartesian endpoint comparison
then give the exact square-root bound for the SAME real Schwartz field.
The consumer is Step 5 of `app:ch_mean_pairs:prop:mean-iteration`; actual source
construction and its finite-iteration norm estimates remain separate inputs.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory FourierTransform
open scoped SchwartzMap

namespace JanetCartan.PhysicalSobolev

open PhysicalCutoff Pseudodifferential LocalSobolev RevisedScales

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "W" => EuclideanSpace ℂ (Fin N)

/-- Half-order interpolation for the actual vector-valued physical Fourier
norm. Plancherel identifies the low endpoint with the SAME field's Lebesgue
L² norm, including zero data and all real orders (`new:lem:interpolation`). -/
theorem physicalWeightedNorm_interpolate_half (s : ℝ) (u : 𝓢(E, V)) :
    (eLpNorm (fun ξ ↦ euclideanSobolevWeight s ((2 * Real.pi) • ξ) •
      𝓕 (complexify u) ξ) 2 volume).toReal ≤
      Real.sqrt ((eLpNorm (u : E → V) 2 volume).toReal) *
        Real.sqrt ((eLpNorm (fun ξ ↦ euclideanSobolevWeight (2 * s) ((2 * Real.pi) • ξ) •
          𝓕 (complexify u) ξ) 2 volume).toReal) := by
  let g : 𝓢(E, W) := 𝓕 (complexify u)
  let vm (ξ : E) := euclideanSobolevWeight s ((2 * Real.pi) • ξ) • g ξ
  let vh (ξ : E) := euclideanSobolevWeight (2 * s) ((2 * Real.pi) • ξ) • g ξ
  have hm : MemLp vm 2 volume := memLp_physicalWeightedFourier s u
  have hh : MemLp vh 2 volume := memLp_physicalWeightedFourier (2 * s) u
  have hg : MemLp (g : E → W) 2 volume := g.memLp 2 volume
  have hp (ξ : E) : ‖vm ξ‖ ^ 2 = ‖g ξ‖ * ‖vh ξ‖ := by
    dsimp only [vm, vh]
    rw [norm_smul, norm_smul,
      Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le,
      Real.norm_of_nonneg (euclideanSobolevWeight_pos _ _).le,
      show 2 * s = s + s by ring, euclideanSobolevWeight_add]
    ring
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume)
    Real.HolderConjugate.two_two
    (f := fun ξ : E ↦ ‖g ξ‖) (g := fun ξ : E ↦ ‖vh ξ‖)
    (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    (by simpa using hg.norm) (by simpa using hh.norm)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hcs
  rw [← eLpNorm_toReal_sq_eq_integral_norm_sq hg,
    ← eLpNorm_toReal_sq_eq_integral_norm_sq hh,
    Real.sqrt_sq ENNReal.toReal_nonneg, Real.sqrt_sq ENNReal.toReal_nonneg] at hcs
  have hlow : (eLpNorm (g : E → W) 2 volume).toReal =
      (eLpNorm (u : E → V) 2 volume).toReal := by
    rw [← SchwartzMap.norm_toLp]
    exact (SchwartzMap.norm_fourier_toL2_eq (complexify u)).trans (norm_complexify_toLp u)
  have hsq : (eLpNorm vm 2 volume).toReal ^ 2 ≤
      (eLpNorm (u : E → V) 2 volume).toReal * (eLpNorm vh 2 volume).toReal := by
    rw [eLpNorm_toReal_sq_eq_integral_norm_sq hm]
    simp_rw [hp]
    exact hcs.trans_eq (congrArg (fun a ↦ a * (eLpNorm vh 2 volume).toReal) hlow)
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg, Real.sq_sqrt ENNReal.toReal_nonneg]
  exact hsq

/-- Paper-v2 `new:lem:interpolation` at its actual fixed source order. One
positive constant is chosen before every field, history, iteration count and
accuracy. There is no derivative loss, source reselection, or periodic norm
identification: both endpoints belong to the SAME real Schwartz field. -/
theorem exists_norm_le_sqrt_L2_mul_sqrt_cartesian_sourceOrder (n N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N)),
      ∀ x, ‖u x‖ ≤ C * Real.sqrt ((eLpNorm (u : _ → _) 2 volume).toReal) *
        Real.sqrt (cartesianJetNorm univ (sourceOrder n) (fun j ↦ iteratedFDeriv ℝ j u)) := by
  obtain ⟨C, hC, hcartesian⟩ := exists_physicalWeightedNorm_le_cartesianJetNorm n N (sourceOrder n)
  let B : ℝ := embeddingConstant n + 1
  have hB : 0 < B := by dsimp [B]; linarith [embeddingConstant_nonneg n]
  refine ⟨B * Real.sqrt C, mul_pos hB (Real.sqrt_pos.2 hC), ?_⟩
  intro u x
  have hi := physicalWeightedNorm_interpolate_half (baselineOrder n : ℝ) u
  have horder : (sourceOrder n : ℝ) = 2 * (baselineOrder n : ℝ) := by
    simp only [sourceOrder, Nat.cast_mul, Nat.cast_ofNat]
  rw [← horder] at hi
  have hsqrt := Real.sqrt_le_sqrt (hcartesian u)
  rw [Real.sqrt_mul hC.le] at hsqrt
  calc
    ‖u x‖ ≤ embeddingConstant n *
        (eLpNorm (fun ξ ↦ euclideanSobolevWeight (baselineOrder n : ℝ) ((2 * Real.pi) • ξ) •
          𝓕 (complexify u) ξ) 2 volume).toReal := norm_le u x
    _ ≤ B * (eLpNorm (fun ξ ↦ euclideanSobolevWeight (baselineOrder n : ℝ) ((2 * Real.pi) • ξ) •
          𝓕 (complexify u) ξ) 2 volume).toReal :=
      mul_le_mul_of_nonneg_right (by dsimp [B]; linarith) ENNReal.toReal_nonneg
    _ ≤ B * (Real.sqrt ((eLpNorm (u : _ → _) 2 volume).toReal) *
        Real.sqrt ((eLpNorm (fun ξ ↦ euclideanSobolevWeight (sourceOrder n : ℝ) ((2 * Real.pi) • ξ) •
          𝓕 (complexify u) ξ) 2 volume).toReal)) := mul_le_mul_of_nonneg_left hi hB.le
    _ ≤ B * (Real.sqrt ((eLpNorm (u : _ → _) 2 volume).toReal) *
        (Real.sqrt C * Real.sqrt (cartesianJetNorm univ (sourceOrder n)
          (fun j ↦ iteratedFDeriv ℝ j u)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg _)) hB.le
    _ = _ := by ring

/-- Step 5 of `app:ch_mean_pairs:prop:mean-iteration`: the actual L² profile
`A ε` and Cartesian source-order profile `A` of the SAME physical residual give
`C A √ε` pointwise. The numerical precision theorem then chooses the finite
iteration count and tail order. This does not assume or construct a successful
source, and the constant is chosen before both profiles and the field. -/
theorem exists_norm_le_of_source_residual_profiles (n N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N)),
      ∀ A ε : ℝ, 0 ≤ A →
        (eLpNorm (u : _ → _) 2 volume).toReal ≤ A * ε →
        cartesianJetNorm univ (sourceOrder n) (fun j ↦ iteratedFDeriv ℝ j u) ≤ A →
        ∀ x, ‖u x‖ ≤ C * A * Real.sqrt ε := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_le_sqrt_L2_mul_sqrt_cartesian_sourceOrder n N
  refine ⟨C, hC, ?_⟩
  intro u A ε hA hlo hhi x
  calc
    ‖u x‖ ≤ C * Real.sqrt ((eLpNorm (u : _ → _) 2 volume).toReal) *
        Real.sqrt (cartesianJetNorm univ (sourceOrder n)
          (fun j ↦ iteratedFDeriv ℝ j u)) := hbound u x
    _ ≤ C * Real.sqrt (A * ε) * Real.sqrt A := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hlo) hC.le)
        (Real.sqrt_le_sqrt hhi) (Real.sqrt_nonneg _) (mul_nonneg hC.le (Real.sqrt_nonneg _))
    _ = C * A * Real.sqrt ε := by
      rw [Real.sqrt_mul hA]
      calc
        _ = C * (Real.sqrt A * Real.sqrt A) * Real.sqrt ε := by ring
        _ = _ := by rw [Real.mul_self_sqrt hA]

end JanetCartan.PhysicalSobolev
