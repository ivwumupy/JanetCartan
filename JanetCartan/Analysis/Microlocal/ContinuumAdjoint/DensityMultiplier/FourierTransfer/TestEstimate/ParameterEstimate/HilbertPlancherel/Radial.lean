module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.FourierTransfer.TestEstimate.ParameterEstimate.HilbertPlancherel.Directional
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Radial parameter Plancherel

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, the unweighted term and the powers
along every direction of an orthonormal parameter basis dominate the radial
Sobolev weight. Directional Plancherel then gives both weighted membership and
the quantitative bound consumed by `exists_iteratedParameterFourier_compact_bound`.
All derivatives are in the three-dimensional parameter space; the transverse
Hilbert fiber is never differentiated.
-/

@[expose] public noncomputable section

open MeasureTheory FourierTransform
open scoped RealInnerProductSpace ContDiff

namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev

/-- The radial weight in `app:ch_background:eq:bg-density-adjoint` is bounded
by the unweighted term and all orthonormal directional powers. This pointwise
bound supplies the majorant for `exists_parameterFourierIntegral_compact_bound`. -/
private theorem parameterRadialWeight_le_orthonormalPowers (s : ℕ) (ξ : ParameterSpace) :
    Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ^ s ≤
      ((Module.finrank ℝ ParameterSpace : ℝ) + 1) ^ s *
        (1 + ∑ i, (2 * Real.pi * |inner ℝ ξ (stdOrthonormalBasis ℝ ParameterSpace i)|) ^ s) := by
  classical
  let b := stdOrthonormalBasis ℝ ParameterSpace
  let a : Option (Fin (Module.finrank ℝ ParameterSpace)) → ℝ
    | none => 1
    | some i => 2 * Real.pi * |inner ℝ ξ (b i)|
  have ha (i) : 0 ≤ a i := by cases i <;> simp [a, Real.pi_nonneg, mul_nonneg]
  have hn : ‖ξ‖ ≤ ∑ i, |inner ℝ ξ (b i)| := by
    calc
      _ = ‖∑ i, inner ℝ (b i) ξ • b i‖ := by rw [b.sum_repr']
      _ ≤ ∑ i, ‖inner ℝ (b i) ξ • b i‖ := norm_sum_le _ _
      _ = _ := by
        simp only [norm_smul, b.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs,
          real_inner_comm]
  have hr : Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ≤ ∑ i, a i := by
    rw [Fintype.sum_option]
    change _ ≤ 1 + ∑ i, 2 * Real.pi * |inner ℝ ξ (b i)|
    rw [← Finset.mul_sum]
    calc
      _ ≤ 1 + 2 * Real.pi * ‖ξ‖ := by
        apply (Real.sqrt_le_iff).2
        constructor
        · positivity
        · nlinarith [Real.pi_pos, norm_nonneg ξ]
      _ ≤ _ := by gcongr
  have hc : (1 : ℝ) ≤ (Finset.univ : Finset (Option (Fin (Module.finrank ℝ ParameterSpace)))).card := by
    simp
  have hp : (∑ i, a i) ^ s ≤
      ((Finset.univ : Finset (Option (Fin (Module.finrank ℝ ParameterSpace)))).card : ℝ) ^ s *
        ∑ i, a i ^ s := by
    cases s with
    | zero => simp
    | succ r =>
      exact (pow_sum_le_card_mul_sum_pow (fun i _ => ha i) r).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc (Nat.le_succ r))
          (Finset.sum_nonneg (fun i _ => pow_nonneg (ha i) _)))
  have h := (pow_le_pow_left₀ (Real.sqrt_nonneg _) hr s).trans hp
  simpa [a, b, Fintype.sum_option] using h

/-- Compact smooth Hilbert-valued parameter tests have weighted Fourier L²
membership and a bound by their parameter jets. This radial Plancherel estimate
is consumed by `exists_iteratedParameterFourier_compact_bound` in the proof of
`app:ch_background:eq:bg-density-adjoint` and retains the exact `2π` normalization. -/
theorem exists_parameterFourierIntegral_compact_bound {n : ℕ} (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (ψ : ParameterSpace → TransverseL2 n),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      MemLp (fun ξ : ParameterSpace =>
        Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ^ s • 𝓕 ψ ξ) 2 volume ∧
      lpNorm (fun ξ : ParameterSpace =>
        Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ^ s • 𝓕 ψ ξ) 2 volume ≤
        B * (∑ k ∈ Finset.range (s + 1), lpNorm (iteratedFDeriv ℝ k ψ) 2 volume) := by
  classical
  let b := stdOrthonormalBasis ℝ ParameterSpace
  let d : ℝ := (Module.finrank ℝ ParameterSpace : ℝ) + 1
  let C : ℝ := d ^ s
  have hC : 0 ≤ C := by dsimp [C, d]; positivity
  refine ⟨C * d, mul_nonneg hC (by dsimp [d]; positivity), ?_⟩
  intro ψ hψ hc
  let S := ∑ k ∈ Finset.range (s + 1), lpNorm (iteratedFDeriv ℝ k ψ) 2 volume
  have hj (k : ℕ) (hk : k ≤ s) : lpNorm (iteratedFDeriv ℝ k ψ) 2 volume ≤ S :=
    Finset.single_le_sum (fun _ _ => lpNorm_nonneg) (Finset.mem_range.mpr (by omega))
  have hzero : MemLp (fun ξ => ‖𝓕 ψ ξ‖) 2 volume ∧
      lpNorm (fun ξ => ‖𝓕 ψ ξ‖) 2 volume ≤ S := by
    have h := parameterFourier_directional_power_bound ψ hψ hc 0 0 (by simp)
    simp only [pow_zero, one_mul] at h
    exact ⟨h.1, h.2.trans (hj 0 (Nat.zero_le s))⟩
  let q : Option (Fin (Module.finrank ℝ ParameterSpace)) → ParameterSpace → ℝ
    | none => fun ξ => ‖𝓕 ψ ξ‖
    | some i => fun ξ => (2 * Real.pi * |inner ℝ ξ (b i)|) ^ s * ‖𝓕 ψ ξ‖
  have hq (i) : MemLp (q i) 2 volume ∧ lpNorm (q i) 2 volume ≤ S := by
    cases i with
    | none => exact hzero
    | some i =>
      have h := parameterFourier_directional_power_bound ψ hψ hc s (b i)
        (by rw [b.orthonormal.norm_eq_one])
      exact ⟨h.1, h.2.trans (hj s le_rfl)⟩
  let g : ParameterSpace → ℝ := C • ∑ i, q i
  have hg : MemLp g 2 volume :=
    (memLp_finsetSum' Finset.univ (fun i _ => (hq i).1)).const_smul C
  have hpoint (ξ : ParameterSpace) :
      ‖Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ^ s • 𝓕 ψ ξ‖ ≤ g ξ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]
    have h := mul_le_mul_of_nonneg_right (parameterRadialWeight_le_orthonormalPowers s ξ)
      (norm_nonneg (𝓕 ψ ξ))
    convert h using 1
    simp [g, q, C, d, b, Fintype.sum_option, Pi.smul_apply, Finset.sum_apply,
      Finset.sum_mul, add_mul, mul_assoc]
    ring
  have hfm : MemLp (𝓕 ψ) 2 volume := Localization.fourierIntegral_memLp_two
    (hψ.continuous.integrable_of_hasCompactSupport hc)
    (hψ.continuous.memLp_of_hasCompactSupport hc)
  have hw : Continuous (fun ξ : ParameterSpace =>
      Real.sqrt (1 + (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2) ^ s) := by fun_prop
  refine ⟨hg.mono' (hw.aestronglyMeasurable.smul hfm.aestronglyMeasurable)
    (Filter.Eventually.of_forall hpoint), ?_⟩
  calc
    _ ≤ lpNorm g 2 volume := lpNorm_mono_real hg hpoint
    _ = C * lpNorm (∑ i, q i) 2 volume := by
      rw [lpNorm_const_smul]
      simp only [NNReal.coe_mk, Real.nnnorm_of_nonneg hC]
    _ ≤ C * ∑ i, lpNorm (q i) 2 volume :=
      mul_le_mul_of_nonneg_left (lpNorm_sum_le (fun i _ => (hq i).1) (by norm_num)) hC
    _ ≤ C * ∑ _i : Option (Fin (Module.finrank ℝ ParameterSpace)), S :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => (hq i).2)) hC
    _ = (C * d) * S := by simp [d]; ring

end JanetCartan.ContinuumAdjoint.DensityMultiplier
