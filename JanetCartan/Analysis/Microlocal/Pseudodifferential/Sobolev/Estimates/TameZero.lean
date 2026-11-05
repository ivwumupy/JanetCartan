module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Estimates.Mixed
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.PhysicalInterpolation
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.Adjoint

/-!
# One-high integer estimates for actual order-zero amplitudes

Step 3 of `app:ch_regular_base:thm:actual-calculus`: interpolation of primitive
physical derivatives and Fourier norms collapses the proved mixed estimate.
The high amplitude bound multiplies only the input L² norm.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff
open JanetCartan.AmplitudeBound

namespace JanetCartan.Pseudodifferential
variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The simultaneous geometric budgets needed by the mixed estimate in
`app:ch_regular_base:eq:fio-input`. The constant depends on the fixed low bound,
dimension and order, and is chosen before the amplitude and high bound. -/
theorem exists_physicalAmplitude_geometric_budget (d μ n : ℕ) (hn : 0 < n) (M : ℝ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → ℂ),
        (∀ ξ, ContDiff ℝ ∞ (b ξ)) → ∀ H : ℝ,
        HasAmplitudeDerivativeBound b μ M → HasAmplitudeDerivativeBound b (μ + n) H →
        ∀ j, j ≤ n → HasAmplitudeDerivativeBound b (μ + j)
          (K * (max 1 H) ^ ((j : ℝ) / n)) := by
  choose C hC hi using fun j : Fin (n + 1) ↦
    exists_physicalAmplitude_interpolation_constant (X := EuclideanSpace ℝ (Fin d))
      (2 * d) μ n j.val hn (by omega)
  let K := (∑ j, C j) * max 1 M
  have hsum : 0 < ∑ j, C j := Finset.sum_pos (fun j _ ↦ hC j) Finset.univ_nonempty
  refine ⟨K, mul_pos hsum (lt_of_lt_of_le zero_lt_one (le_max_left _ _)), ?_⟩
  intro b hb H hM hH j hj ξ is his z
  let j' : Fin (n + 1) := ⟨j, by omega⟩
  have h := hi j' b hb M H hM hH ξ is his z
  have hCle : C j' ≤ ∑ k, C k := Finset.single_le_sum (fun k _ ↦ (hC k).le)
    (Finset.mem_univ j')
  have hpow : (max 1 M) ^ (1 - (j : ℝ) / n) ≤ max 1 M := by
    calc
      _ ≤ (max 1 M) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _)
        (by
          have : 0 ≤ (j : ℝ) / n := by positivity
          linarith)
      _ = _ := Real.rpow_one _
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hCle hpow (Real.rpow_nonneg (by positivity) _) hsum.le)
    (Real.rpow_nonneg (by positivity) _))

/-- Weighted Fourier interpolation collapses every summand to one high
amplitude factor times L², for `app:ch_regular_base:eq:fio-input`. -/
theorem mixedAmplitudeSobolevSum_geometric_le (n : ℕ) (hn : 0 < n)
    (K H : ℝ) (hK : 0 ≤ K) (hH : 0 ≤ H)
    {f : Lp ℂ 2 (volume : Measure E)} (hf : MemFourierSobolev (n : ℝ) f) :
    mixedAmplitudeSobolevSum n (fun j ↦ K * H ^ ((j : ℝ) / n)) f ≤
      (n + 1 : ℕ) * K * (fourierSobolevNorm (n : ℝ) f + H * ‖f‖) := by
  unfold mixedAmplitudeSobolevSum
  calc
    _ ≤ ∑ _k ∈ Finset.range (n + 1),
        K * (fourierSobolevNorm (n : ℝ) f + H * ‖f‖) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
      have he : ((n - k : ℕ) : ℝ) / n = 1 - (k : ℝ) / n := by
        rw [Nat.cast_sub hkn, sub_div, div_self (by exact_mod_cast hn.ne')]
      dsimp only
      rw [he, mul_assoc]
      apply mul_le_mul_of_nonneg_left _ hK
      simpa only [fourierSobolevNorm_zero, add_comm] using
        fourierSobolevNorm_weighted_interpolate (by positivity)
          (show (k : ℝ) ≤ n by exact_mod_cast hkn) hH hf
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `app:ch_regular_base:eq:fio-input`, order zero, every positive integer
index, with fixed shift `μ = 2 * (d + 1)`. The output membership and one-high
estimate are proved from the primitive low and high budgets. The constant is
independent of the amplitude and its high bound. -/
theorem exists_twoPositionL2Operator_integer_tame_constant
    (hd : 0 < d) (R : ℝ) (n : ℕ) (hn : 0 < n) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : HasAmplitudeDerivativeBound b (2 * (d + 1)) M),
        HasAmplitudeDerivativeBound b (2 * (d + 1) + n) H →
        ∀ (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u),
        let f := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
        let v := twoPositionL2Operator hd R b hb hs M hM f
        MemFourierSobolev (n : ℝ) v ∧
          fourierSobolevNorm (n : ℝ) v ≤ C *
            (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨K, hK, hbudget⟩ := exists_physicalAmplitude_geometric_budget d (2 * (d + 1)) n hn M
  refine ⟨integerAmplitudeSobolevConstant d R n * ((n + 1 : ℕ) * K),
    mul_nonneg (integerAmplitudeSobolevConstant_nonneg ..) (by positivity), ?_⟩
  intro b hb hs H hM hH u hu hus
  let B := fun j : ℕ ↦ K * (max 1 H) ^ ((j : ℝ) / n)
  have hB : ∀ j, 0 ≤ B j := fun j ↦ mul_nonneg hK.le (Real.rpow_nonneg (by positivity) _)
  have hmono : Monotone B := by
    intro j k hjk
    apply mul_le_mul_of_nonneg_left _ hK.le
    exact Real.rpow_le_rpow_of_exponent_le (le_max_left _ _)
      (div_le_div_of_nonneg_right (by exact_mod_cast hjk) (by positivity))
  have hout := twoPositionL2Operator_integer_mixed_bound hd R n b hb hs B hB hmono
    (hbudget b (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) H hM hH) u hu hus
  refine ⟨hout.1, hout.2.trans ?_⟩
  calc
    _ ≤ integerAmplitudeSobolevConstant d R n *
        ((n + 1 : ℕ) * K * (fourierSobolevNorm (n : ℝ)
          ((hu.continuous.memLp_of_hasCompactSupport hus).toLp u) + max 1 H *
            ‖(hu.continuous.memLp_of_hasCompactSupport hus).toLp u‖)) :=
      mul_le_mul_of_nonneg_left
        (mixedAmplitudeSobolevSum_geometric_le n hn K (max 1 H) hK.le (by positivity)
          (memFourierSobolev_nat_toLp n u hu hus))
        (integerAmplitudeSobolevConstant_nonneg ..)
    _ = _ := by ring

/-- The same fixed-shift, one-high integer estimate for the literal Hilbert
adjoint in `app:ch_regular_base:eq:fio-input`. No extra symbol estimates are
assumed for the adjoint. -/
theorem exists_twoPositionL2Operator_adjoint_integer_tame_constant
    (hd : 0 < d) (R : ℝ) (n : ℕ) (hn : 0 < n) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : E → EuclideanSpace ℝ (Fin (2 * d)) → ℂ)
        (hb : ContDiff ℝ ∞ (Function.uncurry b))
        (hs : ∀ ξ, SupportedInCenteredBox R (b ξ)) (H : ℝ)
        (hM : HasAmplitudeDerivativeBound b (2 * (d + 1)) M),
        HasAmplitudeDerivativeBound b (2 * (d + 1) + n) H →
        ∀ (u : E → ℂ) (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u),
        let f := (hu.continuous.memLp_of_hasCompactSupport hus).toLp u
        let v := (twoPositionL2Operator hd R b hb hs M hM).adjoint f
        MemFourierSobolev (n : ℝ) v ∧
          fourierSobolevNorm (n : ℝ) v ≤ C *
            (fourierSobolevNorm (n : ℝ) f + max 1 H * ‖f‖) := by
  obtain ⟨C, hC, he⟩ := exists_twoPositionL2Operator_integer_tame_constant hd R n hn M
  refine ⟨C, hC, ?_⟩
  intro b hb hs H hM hH u hu hus
  dsimp only
  rw [twoPositionL2Operator_adjoint]
  exact he (adjointAmplitude b) (contDiff_adjointAmplitude hb)
    (supportedInCenteredBox_adjointAmplitude hs) H
    (hasAmplitudeDerivativeBound_adjointAmplitude
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hM)
    (hasAmplitudeDerivativeBound_adjointAmplitude
      (fun _ ↦ hb.comp (contDiff_const.prodMk contDiff_id)) hH) u hu hus

end JanetCartan.Pseudodifferential
