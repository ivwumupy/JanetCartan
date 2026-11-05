module

public import JanetCartan.Iteration.PhysicalMean.OriginalCanonicalInputTemplate
public import JanetCartan.Iteration.PhysicalMean.IndividualField

/-!
# Actual scalar An to the fixed-source Fourier-mass kernel

The exact representation supplied by93 identifies the original scalar-input
An with the one-column matrix operator in92's half-moment theorem. This is an
operator identity, not a Fourier-mass or inverse estimate. Its consumer is the
actual final unweighted native input at moment order n+1
(`app:ch_mean_pairs:eq:raw-adjoint-moments`, `main:eq:primary-fixed-scales`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalMean.OriginalCanonicalInput
open RawInputPartition PhysicalSamplingShells CurrentMean PeriodicLocalL2
open Pseudodifferential AmplitudeBound.PaperEstimates

local instance (J : ℕ) : MetricSpace (RefinedIndex J) :=
  TopologicalSpace.metrizableSpaceMetric (RefinedIndex J)

/-- Use the original scalar kernel representation, including its half-weight,
to identify the SAME native real adjoint with92's matrix moment input. -/
theorem scalarAnnularAdjoint_eq_matrixCoordinate {n J : ℕ}
    (φ : RefinedIndex J × Euclidean (n - 1) → Euclidean n → ℝ)
    (m : RefinedIndex J × Euclidean (n - 1) → ℝ)
    (a : Fin n → RefinedIndex J → Euclidean (n - 1) → Euclidean n → ℂ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (ha : ∀ i j, ContDiff ℝ ∞ (Function.uncurry (a i j)))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (has : ∀ i j η, tsupport (a i j η) ⊆ K)
    (A : Lp ℂ 2 (annularShellMeasure (n := n) (refinedRadius (J := J))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hA : ∀ f i, finiteL2CoordinateIsometry volume (A f) i =ᵐ[volume] fun x ↦ ∫ z,
      sampledMomentKernel φ (halfWeightedMomentMask m) (fun z y ↦ a i z.1 z.2 y) x z * f z
        ∂annularShellMeasure (n := n) (refinedRadius (J := J)))
    (w : ContinuumRow.OutputL2 n) :
    let μ := annularShellMeasure (n := n) (refinedRadius (J := J))
    let S := nativeMatrixRowOperator μ volume
      (sampledMomentMatrixEntry μ φ (halfWeightedMomentMask m) (fun i (_ : Unit) ↦ a i) hφ
        (continuous_halfWeightedMomentMask m hm) (hasCompactSupport_halfWeightedMomentMask m hms)
        (fun i _ j ↦ ha i j) hK (fun i _ j η ↦ has i j η))
    (transferOutputOperator (realQuadratureChannel A)).adjoint w =
      finiteL2CoordinateIsometry μ ((transferOutputOperator (realQuadratureChannel S)).adjoint w) () := by
  intro μ S
  let entries := sampledMomentMatrixEntry μ φ (halfWeightedMomentMask m) (fun i (_ : Unit) ↦ a i) hφ
    (continuous_halfWeightedMomentMask m hm) (hasCompactSupport_halfWeightedMomentMask m hms)
    (fun i _ j ↦ ha i j) hK (fun i _ j η ↦ has i j η)
  have he (f : Lp ℂ 2 μ) (i : Fin n) :
      finiteL2CoordinateIsometry volume (A f) i = entries i () f := by
    apply Lp.ext
    apply (hA f i).trans
    exact (sampledMomentOperator_ae_kernel μ φ (halfWeightedMomentMask m)
      (fun z ↦ a i z.1 z.2) hφ (continuous_halfWeightedMomentMask m hm)
      (continuous_originalSampledAmplitude (a i) (ha i))
      (hasCompactSupport_halfWeightedMomentMask m hms) hK (fun z ↦ has i z.1 z.2) f).symm
  exact nativeRealScalarRow_adjoint_eq_matrixCoordinate μ (fun i ↦ entries i ()) A he w

end JanetCartan.PhysicalMean.OriginalCanonicalInput
end
