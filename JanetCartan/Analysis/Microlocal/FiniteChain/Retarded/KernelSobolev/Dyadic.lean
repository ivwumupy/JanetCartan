module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Summation

/-!
# Dyadic kernel-to-Sobolev summation

The fixed shell-volume threshold in `app:ch_regular:eq:chain-tail` is absorbed
by taking `q + a + 1` integrations. The amplitude prefactor `P` is unchanged;
in the paper it is `C_{m,q} ρ^(m+C_A) L^b`, with fixed `C_A,b`, and `θ = L/ρ`.
-/

@[expose] public noncomputable section

open MeasureTheory
open JanetCartan.RetardedSobolev.Spaces

namespace JanetCartan.FiniteChain.Retarded.KernelSobolev

/-- Summable dyadic output-derivative estimates produce the actual summed
kernel operator, with the fixed support factor and amplitude prefactor unchanged
(`app:ch_regular:eq:chain-tail`). All input hypotheses concern the kernels.
The series converges in the existing Sobolev space, and every component of its
completed jet is the corresponding integral of summed kernel derivatives. -/
theorem exists_dyadic_kernel_extension {d e m : ℕ}
    (K : ℕ → SupportedSmoothKernel d e)
    (μ : Measure ((Fin d → ℝ) × ℝ)) (ν : Measure ((Fin e → ℝ) × ℝ))
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
    (s : Set ((Fin d → ℝ) × ℝ)) (t : Set (ℝ × (Fin e → ℝ)))
    (hinput : ∀ n, (K n).inputSupport = s) (houtput : ∀ n, (K n).outputSupport = t)
    (a q : ℕ) {P θ : ℝ} (hP : 0 ≤ P) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hb : ∀ n (i : JetIndex e m) p y,
      ‖kernelJet (K n) i p y‖ ≤ P * dyadicShellWeight a q θ n) :
    ∃ B : Sobolev 0 μ →L[ℂ] Sobolev m ν,
      ‖B‖ ≤ 2 * P * compactSupportFactor μ ν s (Prod.swap ⁻¹' t) * θ ^ q ∧
      (∀ f, HasSum (fun n ↦ ofTest m ν (kernelIntegralLinear (K n) μ f))
        (B (ofTest 0 μ f))) ∧
      (∀ (f : Test d) (i : JetIndex e m), MemLp
        (fun p ↦ ∫ y, (∑' n, kernelJet (K n) i p y) * f.val (y.2, y.1) ∂μ) 2 ν) ∧
      ∀ f (i : JetIndex e m), (B (ofTest 0 μ f)).val i =ᵐ[ν]
        fun p ↦ ∫ y, (∑' n, kernelJet (K n) i p y) * f.val (y.2, y.1) ∂μ := by
  obtain ⟨B, hnorm, hsum, hmem, hjet⟩ := exists_commonSupport_shell_extensions K μ ν
    s t hinput houtput (fun n ↦ P * dyadicShellWeight a q θ n)
    (fun n ↦ mul_nonneg hP (by unfold dyadicShellWeight; positivity))
    ((summable_dyadicShellWeight a q hθ hθ').mul_left P) hb
  refine ⟨B, hnorm.trans ?_, hsum, hmem, hjet⟩
  rw [tsum_mul_left]
  calc
    (P * ∑' n, dyadicShellWeight a q θ n) * compactSupportFactor μ ν s (Prod.swap ⁻¹' t)
        ≤ (P * (2 * θ ^ q)) * compactSupportFactor μ ν s (Prod.swap ⁻¹' t) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (tsum_dyadicShellWeight_le a q hθ hθ') hP)
        (compactSupportFactor_nonneg _ _ _ _)
    _ = _ := by ring

end JanetCartan.FiniteChain.Retarded.KernelSobolev
