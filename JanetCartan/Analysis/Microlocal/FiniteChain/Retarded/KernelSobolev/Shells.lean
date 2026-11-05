module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Bounds
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# Summing the finite-chain shell estimates

Absolute operator convergence and the fixed integrability threshold in
`app:ch_regular:eq:chain-tail`. The amplitude prefactor is independent of the
requested decay order; only the number of integrations increases.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.RetardedSobolev.Spaces

namespace JanetCartan.FiniteChain.Retarded.KernelSobolev

/-- Shell volume growth of degree `a`, followed by `q + a + 1` integrations
with inverse larger-frequency gain (`app:ch_regular:lem:finite-chain`). -/
def dyadicShellWeight (a q : ℕ) (θ : ℝ) (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ n) ^ a * (θ / (2 : ℝ) ^ n) ^ (q + a + 1)

/-- The fixed shell threshold leaves a geometric majorant independent of the
requested order `q` (`app:ch_regular:eq:chain-tail`). -/
theorem dyadicShellWeight_le (a q n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    dyadicShellWeight a q θ n ≤ θ ^ q * (1 / 2 : ℝ) ^ n := by
  have hn : (0 : ℝ) < 2 ^ n := by positivity
  have he : dyadicShellWeight a q θ n = θ ^ (q + a + 1) / (2 ^ n) ^ (q + 1) := by
    unfold dyadicShellWeight
    rw [div_pow, show q + a + 1 = a + (q + 1) by omega, pow_add ((2 : ℝ) ^ n)]
    field_simp
  rw [he]
  calc
    θ ^ (q + a + 1) / ((2 : ℝ) ^ n) ^ (q + 1) ≤ θ ^ q / (2 : ℝ) ^ n :=
      div_le_div₀ (by positivity) (pow_le_pow_of_le_one hθ hθ' (by omega)) hn
        (by
          have hbase : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
          simpa using pow_le_pow_right₀ hbase (show 1 ≤ q + 1 by omega))
    _ = θ ^ q * (1 / 2 : ℝ) ^ n := by rw [div_pow, one_pow, div_eq_mul_inv, one_div]

/-- All shells are summable after the fixed threshold; no amplitude offset
depends on `q` (`app:ch_regular:lem:finite-chain`). -/
theorem summable_dyadicShellWeight (a q : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    Summable (dyadicShellWeight a q θ) := by
  apply Summable.of_nonneg_of_le (fun n ↦ by unfold dyadicShellWeight; positivity)
    (fun n ↦ dyadicShellWeight_le a q n hθ hθ')
  exact (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)).mul_left _

/-- The explicit dyadic summation constant is two
(`app:ch_regular:eq:chain-tail`). -/
theorem tsum_dyadicShellWeight_le (a q : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    ∑' n, dyadicShellWeight a q θ n ≤ 2 * θ ^ q := by
  have hs := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  calc
    ∑' n, dyadicShellWeight a q θ n ≤ ∑' n, θ ^ q * (1 / 2 : ℝ) ^ n :=
      (summable_dyadicShellWeight a q hθ hθ').tsum_le_tsum
        (fun n ↦ dyadicShellWeight_le a q n hθ hθ') (hs.mul_left _)
    _ = 2 * θ ^ q := by
      rw [tsum_mul_left, (hasSum_geometric_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).tsum_eq]
      ring

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Absolute convergence and the bound for a countable (or arbitrary-index)
family of bounded shell operators (`app:ch_regular:eq:chain-tail`). -/
theorem operator_hasSum_of_summable_bounds (A : ι → E →L[ℂ] F) (c : ι → ℝ)
    (hc : Summable c) (hb : ∀ i, ‖A i‖ ≤ c i) :
    HasSum A (∑' i, A i) ∧ ‖∑' i, A i‖ ≤ ∑' i, c i := by
  have hn : Summable (fun i ↦ ‖A i‖) := hc.of_norm_bounded (by simpa using hb)
  exact ⟨hn.of_norm.hasSum,
    (norm_tsum_le_tsum_norm hn).trans (hn.tsum_le_tsum hb hc)⟩

/-- Summation with an arbitrary fixed amplitude prefactor. Applying this with
`P = C * ρ^(m+C_A) * L^b` and `θ = L/ρ` keeps `C_A,b` independent of `q`
(`app:ch_regular:eq:chain-tail`). -/
theorem operator_dyadic_hasSum (A : ℕ → E →L[ℂ] F) (a q : ℕ)
    {P θ : ℝ} (hP : 0 ≤ P) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hb : ∀ n, ‖A n‖ ≤ P * dyadicShellWeight a q θ n) :
    HasSum A (∑' n, A n) ∧ ‖∑' n, A n‖ ≤ 2 * P * θ ^ q := by
  have h := operator_hasSum_of_summable_bounds A _
    ((summable_dyadicShellWeight a q hθ hθ').mul_left P) hb
  refine ⟨h.1, h.2.trans ?_⟩
  rw [tsum_mul_left]
  calc
    P * ∑' n, dyadicShellWeight a q θ n ≤ P * (2 * θ ^ q) :=
      mul_le_mul_of_nonneg_left (tsum_dyadicShellWeight_le a q hθ hθ') hP
    _ = 2 * P * θ ^ q := by ring

/-- Simultaneous extension and summation from summable pointwise kernel-jet
bounds. The derivative-integral formulas remain explicit until the smooth-kernel
regularity theorem is applied (`app:ch_regular:eq:chain-tail`). -/
theorem exists_shell_extensions_of_kernelJet_formulas {d e m : ℕ}
    (K : ι → SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) (ν : Measure ((Fin e → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (T : ι → Test d →ₗ[ℂ] Test e)
    (hformula : ∀ j (f : Test d) (i : JetIndex e m) p, jet i (T j f) p =
      ∫ y, kernelJet (K j) i p y * f.val (y.2, y.1) ∂μ)
    (hmeas : ∀ j (i : JetIndex e m) p, AEStronglyMeasurable (kernelJet (K j) i p) μ)
    (C : ι → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hb : ∀ j (i : JetIndex e m) p y, ‖kernelJet (K j) i p y‖ ≤ C j)
    (hs : Summable (fun j ↦ C j * compactSupportFactor μ ν
      (K j).inputSupport (Prod.swap ⁻¹' (K j).outputSupport))) :
    ∃ A : ι → Sobolev 0 μ →L[ℂ] Sobolev m ν,
      (∀ j f, A j (ofTest 0 μ f) = ofTest m ν (T j f)) ∧
      HasSum A (∑' j, A j) ∧
      ‖∑' j, A j‖ ≤ ∑' j, C j * compactSupportFactor μ ν
        (K j).inputSupport (Prod.swap ⁻¹' (K j).outputSupport) := by
  choose A hnorm htest _ using fun j ↦
    exists_extension_of_kernelJet_formula (K j) μ ν (T j) (hformula j) (hmeas j) (hC j) (hb j)
  exact ⟨A, htest, operator_hasSum_of_summable_bounds A _ hs hnorm⟩

end JanetCartan.FiniteChain.Retarded.KernelSobolev
