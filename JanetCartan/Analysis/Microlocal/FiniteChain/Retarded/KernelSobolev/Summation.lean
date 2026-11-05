module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Extension
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelSobolev.Shells
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Countable sums of the actual supported kernels

For `app:ch_regular:eq:chain-tail`, summable bounds on output jets give convergence
in operator norm. Every component of the resulting completed Cartesian jet is
identified almost everywhere with the integral of the summed kernel jets. At the
zeroth index this is the literal summed kernel integral. Only the finitely many
requested derivative bounds are needed; no smoothness of the infinite sum is
assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open JanetCartan.RetardedSobolev.Spaces

namespace JanetCartan.FiniteChain.Retarded.KernelSobolev

variable {ι : Type*} [Countable ι] {d e m : ℕ}
  (K : ι → SupportedSmoothKernel d e)
  (μ : Measure ((Fin d → ℝ) × ℝ)) (ν : Measure ((Fin e → ℝ) × ℝ))
  [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]

/-- Termwise integration of a countable family of actual kernel jets. The
majorant differentiates only the kernel, never the datum
(`app:ch_regular:lem:finite-chain`, common kernel estimate). -/
theorem hasSum_kernelIntegral_jet (C : ι → ℝ) (hs : Summable C)
    (hb : ∀ j (i : JetIndex e m) p y, ‖kernelJet (K j) i p y‖ ≤ C j)
    (f : Test d) (i : JetIndex e m) (p : (Fin e → ℝ) × ℝ) :
    HasSum (fun j ↦ jet i (kernelIntegral (K j) μ f.val) p)
      (∫ y, (∑' j, kernelJet (K j) i p y) * f.val (y.2, y.1) ∂μ) := by
  have hf : Integrable (fun y : (Fin d → ℝ) × ℝ ↦ f.val (y.2, y.1)) μ :=
    (f.property.1.continuous.comp continuous_swap).integrable_of_hasCompactSupport
      (f.property.2.comp_homeomorph (Homeomorph.prodComm _ _))
  simp_rw [kernelIntegral_jet]
  apply hasSum_integral_of_dominated_convergence
    (fun j y ↦ C j * ‖f.val (y.2, y.1)‖)
  · exact fun j ↦ (kernelJet_aestronglyMeasurable (K j) μ i p).mul hf.aestronglyMeasurable
  · exact fun j ↦ Eventually.of_forall fun y ↦ by
      simpa only [norm_mul] using mul_le_mul_of_nonneg_right (hb j i p y) (norm_nonneg _)
  · exact Eventually.of_forall fun y ↦ hs.mul_right ‖f.val (y.2, y.1)‖
  · simpa only [tsum_mul_right] using hf.norm.const_mul (∑' j, C j)
  · exact Eventually.of_forall fun y ↦
      (hs.of_norm_bounded (hb · i p y)).hasSum.mul_right (f.val (y.2, y.1))

private theorem summed_extension_jet_ae
    (A : ι → Sobolev 0 μ →L[ℂ] Sobolev m ν)
    (hA : Summable (fun j ↦ ‖A j‖))
    (htest : ∀ j f, A j (ofTest 0 μ f) = ofTest m ν (kernelIntegralLinear (K j) μ f))
    (C : ι → ℝ) (hs : Summable C)
    (hb : ∀ j (i : JetIndex e m) p y, ‖kernelJet (K j) i p y‖ ≤ C j)
    (f : Test d) (i : JetIndex e m) :
    ((∑' j, A j) (ofTest 0 μ f)).val i =ᵐ[ν]
      fun p ↦ ∫ y, (∑' j, kernelJet (K j) i p y) * f.val (y.2, y.1) ∂μ := by
  let v := ofTest 0 μ f
  let B : ι → Lp ℂ 2 ν := fun j ↦ (A j v).val i
  have hB : Summable (fun j ↦ ‖B j‖) := by
    apply (hA.mul_right ‖v‖).of_nonneg_of_le (fun j ↦ norm_nonneg _)
    intro j
    exact (norm_le_pi_norm (A j v).val i).trans ((A j).le_opNorm v)
  let P : Sobolev m ν →L[ℂ] Lp ℂ 2 ν :=
    (ContinuousLinearMap.proj i).comp (sobolevSubmodule m ν).subtypeL
  have he : ((∑' j, A j) v).val i = ∑' j, B j :=
    (P.hasSum (hasSum_apply hA.of_norm.hasSum v)).tsum_eq.symm
  have hcoe := Lp.hasSum_coeFn_tsum (f := B)
    (ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hB))
  have hj : ∀ᵐ p ∂ν, ∀ j, B j p = jet i (kernelIntegral (K j) μ f.val) p := by
    apply ae_all_iff.mpr
    intro j
    change (A j (ofTest 0 μ f)).val i =ᵐ[ν] _
    rw [htest]
    exact (jet_memLp ν i (kernelIntegralLinear (K j) μ f)).coeFn_toLp
  change (fun p ↦ ((∑' j, A j) v).val i p) =ᵐ[ν] _
  rw [he]
  filter_upwards [hcoe, hj] with p hp hjp
  simp_rw [hjp] at hp
  exact hp.unique (hasSum_kernelIntegral_jet K μ C hs hb f i p)

/-- Extension, operator-norm convergence, and identification of every completed
jet with the integral of the summed kernel jets, all from pointwise derivative
bounds (`app:ch_regular:eq:chain-tail`). Supports may vary provided the displayed
support-weighted bounds are summable. For common supports this follows from
summability of `C` alone, as in `exists_commonSupport_shell_extensions`. -/
theorem exists_shell_kernel_extensions (C : ι → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hs : Summable C)
    (hb : ∀ j (i : JetIndex e m) p y, ‖kernelJet (K j) i p y‖ ≤ C j)
    (hw : Summable (fun j ↦ C j * compactSupportFactor μ ν
      (K j).inputSupport (Prod.swap ⁻¹' (K j).outputSupport))) :
    ∃ A : ι → Sobolev 0 μ →L[ℂ] Sobolev m ν,
      (∀ j, ‖A j‖ ≤ C j * compactSupportFactor μ ν
        (K j).inputSupport (Prod.swap ⁻¹' (K j).outputSupport)) ∧
      (∀ j f, A j (ofTest 0 μ f) = ofTest m ν (kernelIntegralLinear (K j) μ f)) ∧
      HasSum A (∑' j, A j) ∧
      ‖∑' j, A j‖ ≤ ∑' j, C j * compactSupportFactor μ ν
        (K j).inputSupport (Prod.swap ⁻¹' (K j).outputSupport) ∧
      ∀ f (i : JetIndex e m), ((∑' j, A j) (ofTest 0 μ f)).val i =ᵐ[ν]
        fun p ↦ ∫ y, (∑' j, kernelJet (K j) i p y) * f.val (y.2, y.1) ∂μ := by
  choose A hnorm htest _ using fun j ↦ exists_kernelSobolevExtension (K j) μ ν (hC j) (hb j)
  have hA : Summable (fun j ↦ ‖A j‖) := hw.of_norm_bounded (by simpa using hnorm)
  have hsum := operator_hasSum_of_summable_bounds A _ hw hnorm
  exact ⟨A, hnorm, htest, hsum.1, hsum.2,
    summed_extension_jet_ae K μ ν A hA htest C hs hb⟩

/-- With explicit common compact supports, summability of the derivative bounds
alone suffices. The completed outputs converge to the literal summed kernel,
and every summed derivative integral belongs to L²
(`app:ch_regular:eq:chain-tail`). -/
theorem exists_commonSupport_shell_extensions
    (s : Set ((Fin d → ℝ) × ℝ)) (t : Set (ℝ × (Fin e → ℝ)))
    (hinput : ∀ j, (K j).inputSupport = s) (houtput : ∀ j, (K j).outputSupport = t)
    (C : ι → ℝ) (hC : ∀ j, 0 ≤ C j) (hs : Summable C)
    (hb : ∀ j (i : JetIndex e m) p y, ‖kernelJet (K j) i p y‖ ≤ C j) :
    ∃ B : Sobolev 0 μ →L[ℂ] Sobolev m ν,
      ‖B‖ ≤ (∑' j, C j) * compactSupportFactor μ ν s (Prod.swap ⁻¹' t) ∧
      (∀ f, HasSum (fun j ↦ ofTest m ν (kernelIntegralLinear (K j) μ f))
        (B (ofTest 0 μ f))) ∧
      (∀ (f : Test d) (i : JetIndex e m), MemLp
        (fun p ↦ ∫ y, (∑' j, kernelJet (K j) i p y) * f.val (y.2, y.1) ∂μ) 2 ν) ∧
      ∀ f (i : JetIndex e m), (B (ofTest 0 μ f)).val i =ᵐ[ν]
        fun p ↦ ∫ y, (∑' j, kernelJet (K j) i p y) * f.val (y.2, y.1) ∂μ := by
  have hw : Summable (fun j ↦ C j * compactSupportFactor μ ν
      (K j).inputSupport (Prod.swap ⁻¹' (K j).outputSupport)) := by
    simpa only [hinput, houtput] using hs.mul_right (compactSupportFactor μ ν s (Prod.swap ⁻¹' t))
  obtain ⟨A, _, htest, hsum, hnorm, hjet⟩ := exists_shell_kernel_extensions K μ ν C hC hs hb hw
  refine ⟨∑' j, A j, ?_, ?_, ?_, hjet⟩
  · simpa only [hinput, houtput, tsum_mul_right] using hnorm
  · intro f
    simpa only [htest] using hasSum_apply hsum (ofTest 0 μ f)
  · intro f i
    exact MemLp.ae_eq (hjet f i) (Lp.memLp _)

omit [Countable ι] in
/-- The zeroth summed jet is the literal sum of the original kernels, in the
coordinate order of the existing L² space (`app:ch_regular:eq:chain-tail`). -/
@[simp] theorem summedKernel_zerothJet (p : (Fin e → ℝ) × ℝ) (y : (Fin d → ℝ) × ℝ) :
    (∑' j, kernelJet (K j) (zeroIndex e m) p y) = ∑' j, (K j).toFun (p.2, p.1) y := by
  simp only [kernelJet, jet_zeroIndex]

omit [Countable ι] in
/-- The summed extension is determined by the actual shell actions. In
particular changing the derivative majorants or the requested integration count
does not change the operator (`app:ch_regular:lem:finite-chain`). -/
theorem shell_extension_unique (A B : Sobolev 0 μ →L[ℂ] Sobolev m ν)
    (hA : ∀ f, HasSum (fun j ↦ ofTest m ν (kernelIntegralLinear (K j) μ f))
      (A (ofTest 0 μ f)))
    (hB : ∀ f, HasSum (fun j ↦ ofTest m ν (kernelIntegralLinear (K j) μ f))
      (B (ofTest 0 μ f))) : A = B := by
  apply DFunLike.coe_injective
  exact (denseRange_ofTest 0 μ).equalizer A.continuous B.continuous
    (funext fun f ↦ (hA f).unique (hB f))

end JanetCartan.FiniteChain.Retarded.KernelSobolev
