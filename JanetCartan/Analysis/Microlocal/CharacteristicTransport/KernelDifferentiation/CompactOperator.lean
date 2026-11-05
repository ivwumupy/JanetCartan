module

public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.KernelDifferentiation.RetardedCalculus
public import JanetCartan.Analysis.Microlocal.FourierIntegral.ConjugationIdentity.GraphDifferentiation.CompactIntegral

/-!
# Physical first-order calculus for a compact spectral integral

The derivative interchange and column sums used by the literal retarded kernel
in `app:ch_regular_base:eq:energy-complete-residual`. The compact-carrier API
constructs the integrable bounds from smoothness; no interchange is assumed.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
open WKB FourierIntegral.GraphDifferentiation
variable {n q : ℕ} {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] {μ : Measure Z} [IsFiniteMeasureOnCompacts μ]
local notation "FV" => Fin q → ℂ

/-- The full physical operator commutes with a common compact-carrier integral.
Consumer: frequency integration in the finite-cutoff residual identity
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem firstOrderApply_compactIntegral {f : Euclidean n × Z → FV} {K : Set Z}
    (hf : ContDiff ℝ ∞ f) (hK : IsCompact K) (hs : ∀ x z, z ∉ K → f (x,z) = 0)
    (C : Euclidean n → Fin n → FV →L[ℂ] FV) (D : Euclidean n → FV →L[ℂ] FV)
    (x : Euclidean n) :
    firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ ∫ z, f (y,z) ∂μ) x =
      ∫ z, firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
        (fun y ↦ f (y,z)) x ∂μ := by
  have hd := integrable_section (μ := μ) hK
    (contDiffOn_parameterFDeriv (U := univ) (V := univ)
      isOpen_univ isOpen_univ hf.contDiffOn).continuousOn
    (fun y _ z hz ↦ fderiv_section_eq_zero isOpen_univ (fun y _ z hz ↦ hs y z hz)
      (mem_univ y) hz) (mem_univ x)
  have hv := integrable_section (μ := μ) hK hf.continuous.continuousOn
    (fun y _ z hz ↦ hs y z hz) (mem_univ x)
  have hj (j : Fin n) : Integrable (fun z ↦ C x j
      (partialDeriv (fun y ↦ f (y,z)) x j)) μ :=
    (C x j).integrable_comp
      ((ContinuousLinearMap.apply ℝ FV (EuclideanSpace.single j 1)).integrable_comp hd)
  have hb : Integrable (fun z ↦ D x (f (x,z))) μ := (D x).integrable_comp hv
  have hdv := hasFDerivAt_integral (μ := μ) isOpen_univ hK hf.contDiffOn
    (fun y _ z hz ↦ hs y z hz) (mem_univ x)
  simp only [firstOrderApply, partialDeriv, hdv.fderiv,
    ContinuousLinearMap.integral_apply hd, ContinuousLinearMap.coe_coe]
  simp only [partialDeriv] at hj
  rw [integral_add (integrable_finsetSum Finset.univ fun j _ ↦ hj j) hb,
    integral_finsetSum Finset.univ fun j _ ↦ hj j]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    exact ((C x j).integral_comp_comm
      ((ContinuousLinearMap.apply ℝ FV (EuclideanSpace.single j 1)).integrable_comp hd)).symm
  · exact ((D x).integral_comp_comm hv).symm
end JanetCartan.CharacteristicTransport.KernelDifferentiation
namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
open WKB
variable {n q : ℕ}
local notation "FV" => Fin q → ℂ

/-- The fixed Fourier scalar commutes with the physical operator in
`app:ch_regular_base:eq:energy-complete-residual`. -/
theorem firstOrderApply_const_smul
    (C : Euclidean n → Fin n → FV →ₗ[ℂ] FV) (D : Euclidean n → FV →ₗ[ℂ] FV)
    {f : Euclidean n → FV} {x : Euclidean n} (hf : DifferentiableAt ℝ f x) (c : ℂ) :
    firstOrderApply C D (fun y ↦ c • f y) x = c • firstOrderApply C D f x := by
  rw [RegularSector.Characteristic.firstOrderApply_smul C D (differentiableAt_const c) hf]
  simp [partialDeriv]

/-- Columnwise identities pass through a finite matrix sum in
`app:ch_regular_base:eq:two-term-null-identity`. -/
theorem firstOrderApply_sum_columns
    (C : Euclidean n → Fin n → FV →ₗ[ℂ] FV) (D : Euclidean n → FV →ₗ[ℂ] FV)
    {f : Fin q → Euclidean n → FV} {x : Euclidean n}
    (hf : ∀ j, DifferentiableAt ℝ (f j) x) :
    firstOrderApply C D (fun y ↦ ∑ j, f j y) x = ∑ j, firstOrderApply C D (f j) x := by
  simp only [firstOrderApply, partialDeriv, fderiv_fun_sum (fun j _ ↦ hf j),
    sum_apply, map_sum, Finset.sum_add_distrib]
  rw [Finset.sum_comm]

end JanetCartan.CharacteristicTransport.KernelDifferentiation
