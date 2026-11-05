module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.AveragedMixed.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The exact derivative of the phase increment

The fundamental theorem of calculus gives `D_x ΔS = B δ`, as used in
`app:ch_response:thm:response-literal-transfer`. All hypotheses concern the
primitive phase and its mixed derivatives along the actual covector segment.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer

local instance (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- The mixed matrix applied to a physical covector is the covector derivative
of the spatial partial derivative
(`app:ch_response:thm:response-literal-transfer`). -/
theorem mixedPhaseOperator_apply_eq_fderiv {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (x η v : Euclidean n) (i : Fin n) :
    mixedPhaseOperator S x η v i =
      fderiv ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i) η v := by
  have he := congrArg
    (fderiv ℝ (fun ξ ↦ partialDeriv (fun z ↦ S z ξ) x i) η)
    ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v)
  simpa only [mixedPhaseOperator, mixedMatrixOperatorEquiv_apply,
    FourierIntegral.mixedPhaseMatrix, partialDeriv,
    map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    smul_eq_mul, mul_comm] using he

/-- The coordinate form of the literal phase-increment identity. Smoothness
on a buffered chart supplies the displayed primitive differentiability and
continuity premises; no identity for the average is assumed
(`app:ch_response:thm:response-literal-transfer`). -/
theorem partialDeriv_phaseIncrement_eq_averagedMixedOperator {n : ℕ}
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (x δ : Euclidean n)
    (hx₀ : DifferentiableAt ℝ (fun z ↦ S z (ρ • ζ)) x)
    (hx₁ : DifferentiableAt ℝ (fun z ↦ S z (ρ • ζ + δ)) x)
    (hξ : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i : Fin n,
      DifferentiableAt ℝ (fun η ↦ partialDeriv (fun z ↦ S z η) x i)
        (ρ • ζ + t • δ))
    (hc : ContinuousOn
      (fun t : ℝ ↦ FourierIntegral.mixedPhaseMatrix S x (ρ • ζ + t • δ))
      (Icc 0 1)) (i : Fin n) :
    partialDeriv (fun z ↦ phaseIncrement S ζ ρ z δ) x i =
      averagedMixedOperator S ζ ρ x δ δ i := by
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
    (EuclideanSpace.proj i).comp
      (((ContinuousLinearMap.apply ℝ (Euclidean n)) δ).comp
        (mixedMatrixOperatorEquiv n).toContinuousLinearMap)
  have hi : IntervalIntegrable
      (fun t : ℝ ↦ FourierIntegral.mixedPhaseMatrix S x (ρ • ζ + t • δ)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hc
  have hLi : IntervalIntegrable
      (fun t : ℝ ↦ L (FourierIntegral.mixedPhaseMatrix S x (ρ • ζ + t • δ))) volume 0 1 :=
    ⟨L.integrable_comp hi.1, L.integrable_comp hi.2⟩
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ ↦ partialDeriv (fun z ↦ S z (ρ • ζ + s • δ)) x i)
        (L (FourierIntegral.mixedPhaseMatrix S x (ρ • ζ + t • δ))) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa using ht
    have hpath : HasDerivAt (fun s : ℝ ↦ ρ • ζ + s • δ) δ t := by
      simpa using ((hasDerivAt_id t).smul_const δ).const_add (ρ • ζ)
    have he : L (FourierIntegral.mixedPhaseMatrix S x (ρ • ζ + t • δ)) =
        fderiv ℝ (fun η ↦ partialDeriv (fun z ↦ S z η) x i) (ρ • ζ + t • δ) δ :=
      mixedPhaseOperator_apply_eq_fderiv S x (ρ • ζ + t • δ) δ i
    rw [he]
    exact (hξ t ht' i).hasFDerivAt.comp_hasDerivAt t hpath
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hLi
  have hcomm := L.intervalIntegral_comp_comm hi
  change (∫ t in (0 : ℝ)..1,
      L (FourierIntegral.mixedPhaseMatrix S x (ρ • ζ + t • δ))) =
    averagedMixedOperator S ζ ρ x δ δ i at hcomm
  rw [← hcomm, hFTC]
  simp only [one_smul, zero_smul, add_zero]
  change (fderiv ℝ (fun z ↦ S z (ρ • ζ + δ) - S z (ρ • ζ)) x)
    (EuclideanSpace.single i 1) = _
  exact congrArg (fun T : Euclidean n →L[ℝ] ℝ ↦ T (EuclideanSpace.single i 1))
    (hx₁.hasFDerivAt.sub hx₀.hasFDerivAt).fderiv

end JanetCartan.ResponseTransfer
