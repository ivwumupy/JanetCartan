module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalKernel.Limits.Pairing
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Tested distributional limits of the actual compact cross normals

This is a conditional limit theorem for
`app:ch_regular_base:eq:actual-normal-kernel` and the cross-product sentence
following `app:ch_regular_base:eq:actual-normal-amplitude`.

The supported tests are `conj (u x) * v y` in each matrix entry, where `u,v`
are continuous and compactly supported (hence all smooth compactly supported
tensor tests are supported). All integrals use Euclidean Lebesgue measure;
the frequency variable is the physical covector and the factor is `(2π)⁻ⁿ`.

The consuming fleet task `jc-deduce-fio-normal-kernel` retains final assembly
and must supply continuous compact regularizations,
strong L² convergence of their actual adjoints on these tests, almost-everywhere
convergence of the tested frequency integrands, and an integrable majorant.
The finite pairing identity and its absolute Fubini justification are proved
in `Limits.Pairing`, not hypothesized here. No unregularized operator existence
or production of these convergence hypotheses is asserted.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology ComplexInnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.FourierIntegral.NormalKernel

open NormalComparison

variable {n r : ℕ}
variable {S : Euclidean n → Euclidean n → ℝ}
variable {A B : ℕ → Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}

/-- Strong convergence of the actual adjoints on a tensor test and dominated
convergence of the literal tested frequency densities imply the tested
cross-normal identity. This is the limit step for the parent normal-kernel
construction (`app:ch_regular_base:eq:actual-normal-kernel`); the parent must
produce every convergence and domination hypothesis. The conclusion also
records absolute integrability of the limiting tested frequency density. -/
theorem compactGraph_cross_tested_limit
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ m i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A m p.1 p.2 i k))
    (hsA : ∀ m i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A m p.1 p.2 i k))
    (hB : ∀ m j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B m p.1 p.2 j k))
    (hsB : ∀ m j k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ B m p.1 p.2 j k))
    (T U : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r)
    {u v : Euclidean n → ℂ}
    (hu : Continuous u) (hsu : HasCompactSupport u)
    (hv : Continuous v) (hsv : HasCompactSupport v) (i j : Fin r)
    (hT : Tendsto (fun m ↦ (compactGraph hS (hA m) (hsA m)).adjoint
      (compactChannelTest hu hsu i)) atTop
        (𝓝 (T.adjoint (compactChannelTest hu hsu i))))
    (hU : Tendsto (fun m ↦ (compactGraph hS (hB m) (hsB m)).adjoint
      (compactChannelTest hv hsv j)) atTop
        (𝓝 (U.adjoint (compactChannelTest hv hsv j))))
    (F : Euclidean n → ℂ) (bound : Euclidean n → ℝ)
    (hbound : Integrable bound)
    (hdom : ∀ m, ∀ᵐ η ∂volume,
      ‖testedCrossFrequency S (A m) (B m) u v i j η‖ ≤ bound η)
    (hlim : ∀ᵐ η ∂volume, Tendsto
      (fun m ↦ testedCrossFrequency S (A m) (B m) u v i j η) atTop (𝓝 (F η))) :
    Integrable F ∧
      inner ℂ (compactChannelTest hu hsu i) (T (U.adjoint (compactChannelTest hv hsv j))) =
        ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η, F η := by
  have hmeas (m : ℕ) :=
    (integrable_testedCrossFrequency hS (hA m) (hsA m) (hB m) hu hv hsv i j).aestronglyMeasurable
  refine ⟨⟨aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim,
    hasFiniteIntegral_of_dominated_convergence hbound.hasFiniteIntegral hdom hlim⟩, ?_⟩
  have hint := (tendsto_integral_of_dominated_convergence bound hmeas hbound hdom hlim).const_mul
    (((2 * Real.pi) ^ n : ℂ)⁻¹)
  have hpair := hT.inner hU (𝕜 := ℂ)
  simp_rw [compactGraph_cross_tested hS (hA _) (hsA _) (hB _) (hsB _) hu hsu hv hsv i j]
    at hpair
  simpa only [ContinuousLinearMap.adjoint_inner_left] using tendsto_nhds_unique hpair hint

/-- Literal-amplitude specialization of `compactGraph_cross_tested_limit`:
when the tested frequency integrands converge to those of supplied amplitudes
`A₀,B₀`, the limiting cross normal has precisely their tested oscillatory
kernel. This is conditional on the parent's strong convergence and domination
proofs, and makes no unconditional existence claim
(`app:ch_regular_base:eq:actual-normal-kernel`, cross variant). -/
theorem compactGraph_cross_tested_limit_amplitudes
    (hS : Continuous (Function.uncurry S))
    (hA : ∀ m i k, Continuous (fun p : Euclidean n × Euclidean n ↦ A m p.1 p.2 i k))
    (hsA : ∀ m i k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A m p.1 p.2 i k))
    (hB : ∀ m j k, Continuous (fun p : Euclidean n × Euclidean n ↦ B m p.1 p.2 j k))
    (hsB : ∀ m j k, HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ B m p.1 p.2 j k))
    (T U : NormalOutputL2 n r →L[ℂ] NormalOutputL2 n r)
    (A₀ B₀ : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    {u v : Euclidean n → ℂ}
    (hu : Continuous u) (hsu : HasCompactSupport u)
    (hv : Continuous v) (hsv : HasCompactSupport v) (i j : Fin r)
    (hT : Tendsto (fun m ↦ (compactGraph hS (hA m) (hsA m)).adjoint
      (compactChannelTest hu hsu i)) atTop
        (𝓝 (T.adjoint (compactChannelTest hu hsu i))))
    (hU : Tendsto (fun m ↦ (compactGraph hS (hB m) (hsB m)).adjoint
      (compactChannelTest hv hsv j)) atTop
        (𝓝 (U.adjoint (compactChannelTest hv hsv j))))
    (bound : Euclidean n → ℝ) (hbound : Integrable bound)
    (hdom : ∀ m, ∀ᵐ η ∂volume,
      ‖testedCrossFrequency S (A m) (B m) u v i j η‖ ≤ bound η)
    (hlim : ∀ᵐ η ∂volume, Tendsto
      (fun m ↦ testedCrossFrequency S (A m) (B m) u v i j η) atTop
        (𝓝 (testedCrossFrequency S A₀ B₀ u v i j η))) :
    Integrable (testedCrossFrequency S A₀ B₀ u v i j) ∧
      inner ℂ (compactChannelTest hu hsu i) (T (U.adjoint (compactChannelTest hv hsv j))) =
        ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ η, ∫ x, ∫ y,
          Complex.exp (Complex.I * ((S x η - S y η : ℝ) : ℂ)) *
            (A₀ x η * (B₀ y η).conjTranspose) i j * star (u x) * v y :=
  compactGraph_cross_tested_limit hS hA hsA hB hsB T U hu hsu hv hsv i j hT hU
    (testedCrossFrequency S A₀ B₀ u v i j) bound hbound hdom hlim

end JanetCartan.FourierIntegral.NormalKernel
