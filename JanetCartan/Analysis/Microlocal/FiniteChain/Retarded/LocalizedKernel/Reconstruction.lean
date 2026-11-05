module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Reconstruction.Coordinates
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Reconstruction.Schwartz

/-!
# Reconstruction of the complementary output operator

For `app:ch_regular:lem:finite-chain` and `app:ch_regular:eq:chain-tail`, the
frequency regularization of `1 - mo` converges pointwise to identity minus the
actual left output operator. Compact support and smoothness of the datum supply
Schwartz Fourier decay; the proof does not postulate inversion or integrability.
The identity contribution is recovered by inversion, not by treating `1 - mo`
as a compactly supported symbol.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
open scoped FourierTransform SchwartzMap RealInnerProductSpace Topology ContDiff
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Pointwise reconstruction of the full complementary output, including its
identity contribution (`app:ch_regular:lem:finite-chain`,
`app:ch_regular:eq:chain-tail`). All support, Fourier integrability, Fubini,
inversion and dominated convergence obligations follow from the stated smooth
compact support assumptions. -/
theorem tendsto_leftOperator_complementarySymbol
    (v : ℝ × E → ℂ) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (mo : (ℝ × E) → (ℝ × E) → ℂ) (hmo : ContDiff ℝ ∞ (Function.uncurry mo))
    (hmoc : HasCompactSupport (Function.uncurry mo))
    (χ : ℝ × E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : χ 0 = 1) (x : ℝ × E) :
    Tendsto (fun R : ℝ => leftOperator
      (complementarySymbol (fun ξ => (χ (R⁻¹ • ξ) : ℂ)) mo) v x) atTop
      (𝓝 (v x - leftOperator mo v x)) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E
  let u : 𝓢(WithLp 2 (ℝ × E), ℂ) :=
    (hvc.comp_homeomorph e.toHomeomorph).toSchwartzMap (hv.comp e.contDiff)
  let a : WithLp 2 (ℝ × E) → ℂ := fun ξ => mo x ((2 * Real.pi) • ξ.ofLp)
  let cutoff : WithLp 2 (ℝ × E) → ℝ := fun ξ => χ ((2 * Real.pi) • ξ.ofLp)
  have hp : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hms : Continuous (mo x) :=
    hmo.continuous.comp (continuous_const.prodMk continuous_id)
  have hmsc : HasCompactSupport (mo x) := by
    apply HasCompactSupport.of_support_subset_isCompact (hmoc.isCompact.image continuous_snd)
    intro ξ hξ
    exact ⟨(x, ξ), subset_tsupport (Function.uncurry mo) hξ, rfl⟩
  have ha : Continuous a := hms.comp ((WithLp.prod_continuous_ofLp 2 ℝ E).const_smul (2 * Real.pi))
  have hac : HasCompactSupport a :=
    (hmsc.comp_smul hp).comp_homeomorph e.toHomeomorph
  have hc : Continuous cutoff := hχ.continuous.comp ((WithLp.prod_continuous_ofLp 2 ℝ E).const_smul (2 * Real.pi))
  have hcc : HasCompactSupport cutoff :=
    (hχc.comp_smul hp).comp_homeomorph e.toHomeomorph
  have hc0 : cutoff 0 = 1 := by simpa [cutoff] using hχ0
  have h := tendsto_complementary_cyclesKernel a u (WithLp.toLp 2 x) ha hac
    cutoff hc hcc hc0
  have hout : (∫ y, u y • Pseudodifferential.amplitudeKernel
      (fun _x _y ξ => a ξ) (WithLp.toLp 2 x) y) = leftOperator mo v x := by
    rw [show x = (WithLp.toLp 2 x).ofLp from rfl, leftOperator_eq_cyclesKernel]
    rfl
  have hin (R : ℝ) : (∫ y, u y • Pseudodifferential.amplitudeKernel
      (fun _x _y ξ => cutoff (R⁻¹ • ξ) • (1 - a ξ)) (WithLp.toLp 2 x) y) =
      leftOperator (complementarySymbol (fun ξ => (χ (R⁻¹ • ξ) : ℂ)) mo) v x := by
    rw [show x = (WithLp.toLp 2 x).ofLp from rfl, leftOperator_eq_cyclesKernel]
    apply integral_congr_ae
    filter_upwards [] with y
    congr 1
    simp only [Pseudodifferential.amplitudeKernel, complementarySymbol, a, cutoff,
      WithLp.ofLp_smul, ← Complex.real_smul]
    simp_rw [smul_comm (2 * Real.pi) (R⁻¹)]
  simpa only [hout, hin, show u (WithLp.toLp 2 x) = v x from rfl] using h

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
