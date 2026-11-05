module

public import JanetCartan.Iteration.PhysicalMean.CrossRow
public import JanetCartan.Iteration.PhysicalMean.ScalarInput
public import JanetCartan.Iteration.PhysicalMean.QuadraticRow
public import JanetCartan.Iteration.PhysicalSamplingShells.Samples

/-!
# The sharp full scalar cross rows in the original genuine real channel

The output-coordinate assembly costs only the fixed physical factor `√n`.
The actual channel is `2 Re`, with its genuine factor two; passage to periodic
outputs and the original sampled input isometry loses nothing. The final
consumer applies the SAME full `CrossRow` scalar estimates to
`two_mul_norm_fixedSourceQuadratic_le_aggregate`, cancelling that factor two.
No sample cardinality, shell count or frequency ceiling occurs
(`app:ch_mean_pairs:eq:mean-quadratic-low`, `app:ch_osc:cor:osc-real`).

The exact forward-coordinate and original-input identities are supplied by
the full-kernel realization. They are not operator-norm assumptions and do
not replace the full corrected amplitude by its principal term.
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8000
set_option maxHeartbeats 2000000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open Pseudodifferential PeriodicLocalL2 AmplitudeBound.PaperEstimates
open CurrentMean SmoothPeriodicFamily ContinuumRow CanonicalChange

section CoordinateBounds
variable {n : ℕ} {X : Type*} [MeasurableSpace X]

/-- The SAME scalar-input complex row costs only the square root of its fixed
output dimension, not the dimension or size of the input measure
(`app:ch_osc:prop:osc-normal`). -/
theorem norm_nativeScalarRow_le_of_coordinate_bounds
    (μ : Measure X)
    (B : Fin n → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (A : Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hcoord : ∀ f i, finiteL2CoordinateIsometry volume (A f) i = B i f)
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ i, ‖B i‖ ≤ c) :
    ‖A‖ ≤ Real.sqrt (n : ℝ) * c := by
  let S := (finiteL2CoordinateIsometry (I := Fin n) volume).toContinuousLinearEquiv.toContinuousLinearMap.comp A
  have hS (i : Fin n) :
      ‖(PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ Lp ℂ 2 (volume : Measure (Euclidean n))) i).comp S‖ ≤ c := by
    have he : (PiLp.proj (𝕜 := ℂ) 2
        (fun _ : Fin n ↦ Lp ℂ 2 (volume : Measure (Euclidean n))) i).comp S = B i := by
      ext1 f
      exact hcoord f i
    rw [he]
    exact hB i
  simpa only [S, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp, Fintype.card_fin] using
    norm_rowVectorOperator_le_of_coordinate_bounds μ volume S hc hS

/-- The genuine original scalar-input `2 Re` row and its periodic output cost
exactly the allowed factor `2√n`; the input Hilbert space is unchanged
(`app:ch_osc:cor:osc-real`, `app:ch_mean_pairs:eq:mean-quadratic-low`). -/
theorem norm_nativeRealScalarRow_le_of_coordinate_bounds
    (μ : Measure X)
    (B : Fin n → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (A : Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hcoord : ∀ f i, finiteL2CoordinateIsometry volume (A f) i = B i f)
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ i, ‖B i‖ ≤ c) :
    ‖transferOutputOperator (realQuadratureChannel A)‖ ≤ 2 * Real.sqrt (n : ℝ) * c := by
  calc
    ‖transferOutputOperator (realQuadratureChannel A)‖ ≤ ‖realQuadratureChannel A‖ :=
      norm_transferOutputOperator_le _
    _ ≤ 2 * ‖A‖ := realQuadratureChannel_norm_le A
    _ ≤ 2 * (Real.sqrt (n : ℝ) * c) :=
      mul_le_mul_of_nonneg_left (norm_nativeScalarRow_le_of_coordinate_bounds μ B A hcoord hc hB)
        (by norm_num)
    _ = 2 * Real.sqrt (n : ℝ) * c := by ring

/-- An exact original-input isometry transports the SAME genuine real row
without any input-coordinate count or frequency factor. The supplied equality
is the literal full-kernel realization, not a full-row bound
(`new:eq:amplitude-test`). -/
theorem norm_originalRealScalarRow_le_of_coordinate_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X)
    (B : Fin n → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (A : Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hcoord : ∀ f i, finiteL2CoordinateIsometry volume (A f) i = B i f)
    (e : Lp ℂ 2 μ ≃ₗᵢ[ℝ] E) (Rorig : E →L[ℝ] OutputL2 n)
    (he : Rorig.comp e.toContinuousLinearEquiv.toContinuousLinearMap =
      transferOutputOperator (realQuadratureChannel A))
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ i, ‖B i‖ ≤ c) :
    ‖Rorig‖ ≤ 2 * Real.sqrt (n : ℝ) * c := by
  rw [← ContinuousLinearMap.opNorm_comp_linearIsometryEquiv Rorig e, he]
  exact norm_nativeRealScalarRow_le_of_coordinate_bounds μ B A hcoord hc hB

end CoordinateBounds

/-- Task 27's ACTUAL sample/shell isometry, restricted to real scalars,
transports the unchanged nested original input. There is no flattening norm
loss and no replacement sampling measure (`new:eq:amplitude-test`). -/
theorem norm_sampledRealScalarRow_le_of_coordinate_bounds
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (n J : ℕ)
    (B : Fin n → Lp ℂ 2 (PhysicalSamplingShells.sampledShellMeasure (ι := ι) n J) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Euclidean n)))
    (A : Lp ℂ 2 (PhysicalSamplingShells.sampledShellMeasure (ι := ι) n J) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hcoord : ∀ f i, finiteL2CoordinateIsometry volume (A f) i = B i f)
    (Rorig : PiLp 2 (fun _ : ι ↦ PiLp 2 (fun i : RawInputPartition.RefinedIndex J ↦
      Lp ℂ 2 (RawInputRealization.annularMeasure n (RawInputPartition.refinedRadius i)))) →L[ℝ] OutputL2 n)
    (he : Rorig.comp
      ((PhysicalSamplingShells.sampledShellEquiv (V := ℂ) (ι := ι) n J).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) =
      transferOutputOperator (realQuadratureChannel A))
    {c : ℝ} (hc : 0 ≤ c) (hB : ∀ i, ‖B i‖ ≤ c) :
    ‖Rorig‖ ≤ 2 * Real.sqrt (n : ℝ) * c := by
  let e : Lp ℂ 2 (PhysicalSamplingShells.sampledShellMeasure (ι := ι) n J) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : ι ↦ PiLp 2 (fun i : RawInputPartition.RefinedIndex J ↦
        Lp ℂ 2 (RawInputRealization.annularMeasure n (RawInputPartition.refinedRadius i)))) :=
    { toLinearEquiv := (PhysicalSamplingShells.sampledShellEquiv (V := ℂ) (ι := ι) n J).toLinearEquiv.restrictScalars ℝ
      norm_map' := (PhysicalSamplingShells.sampledShellEquiv (V := ℂ) (ι := ι) n J).norm_map }
  exact norm_originalRealScalarRow_le_of_coordinate_bounds _ B A hcoord e Rorig he hc hB

section FullCrossRow
variable {n N : ℕ} {X : Type*}
  [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
  (φ : X → Euclidean n → ℝ) (m : X → ℝ)
  (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
  (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
  (B G : X → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
  (hC : ContDiff ℝ ∞ C) (hBc : Continuous (Function.uncurry B))
  (hGc : Continuous (Function.uncurry G))
  (hB : ∀ u, ContDiff ℝ ∞ (B u)) (hG : ∀ u, ContDiff ℝ ∞ (G u))
  {K : Set (Euclidean n)} (hK : IsCompact K) (hGK : ∀ u, tsupport (G u) ⊆ K)
  (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
  (hχK : ∀ x ∈ K, χ x = 1) (R : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ R)
  (CC CG Z : ℝ) (hCC : 0 ≤ CC) (hCG : 0 ≤ CG) (hZ : 0 ≤ Z)
  (hCb : cNorm K (n / 2 + 1) C ≤ CC)
  (hGb : ∀ u, m u ≠ 0 → cNorm K (n / 2 + 1) (G u) ≤ CG)
  (hBmem : ∀ u, m u ≠ 0 → ∀ j ≤ n / 2 + 1,
    MemLp (iteratedFDeriv ℝ j (B u)) 2 volume)
  (hBb : ∀ u, m u ≠ 0 →
    (∑ j ∈ Finset.range (n / 2 + 1 + 1), lpNorm (iteratedFDeriv ℝ j (B u)) 2 volume) ≤ Z)
  (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
  (hT : ∀ f : Lp ℂ 2 μ, T f =ᵐ[volume] fun x ↦ ∫ u,
    sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x u * f u ∂μ)

local notation "crossEntry" i => sampledMomentOperator μ φ m (modifiedCrossAdjointAmplitude C B G i) hφ hm
  (continuous_modifiedCrossAdjointAmplitude C B G hC.continuous hBc hGc i)
  hms hK (tsupport_modifiedCrossAdjointAmplitude_subset C B G hK.isClosed hGK i)

include hB hG hχ hχs hχK hbox hCC hCG hZ hCb hGb hBmem hBb hT

/-- ACTUAL application of the full corrected `CrossRow` scalar bounds to the
same complex row and genuine real periodic channel. The only new factor is
`2√n`; the original phase, complete mask, measure and scalar tester are literal
(`app:ch_mean_pairs:eq:mean-quadratic-low`). -/
theorem norm_modifiedCrossNativeRealRow_le
    (S : Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hcoord : ∀ f i, finiteL2CoordinateIsometry volume (S f) i = (crossEntry i) f) :
    ‖transferOutputOperator (realQuadratureChannel S)‖ ≤
      2 * Real.sqrt (n : ℝ) * modifiedCrossRowConstant n N R * ‖T‖ * CC * CG * Z := by
  have hbudget : 0 ≤ modifiedCrossRowConstant n N R * ‖T‖ * CC * CG * Z :=
    mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (modifiedCrossRowConstant_nonneg n N R) (norm_nonneg T)) hCC) hCG) hZ
  have hscalar (i : Fin n) : ‖crossEntry i‖ ≤
      modifiedCrossRowConstant n N R * ‖T‖ * CC * CG * Z :=
    norm_modifiedCrossNativeScalarRow_le μ φ m hφ hm hms C B G hC hBc hGc hB hG hK hGK
      χ hχ hχs hχK R hbox CC CG Z hCC hCG hZ hCb hGb hBmem hBb T hT i
  simpa only [mul_assoc] using
    norm_nativeRealScalarRow_le_of_coordinate_bounds μ (fun i ↦ crossEntry i) S hcoord hbudget hscalar

/-- The same full CrossRow bounds control the ORIGINAL weighted row via its
exact real input isometry. In particular one may use the actual task-27
real restriction of `sampledShellEquiv`; no weight or mask is changed
(`new:eq:amplitude-test`, `app:ch_mean_pairs:eq:mean-quadratic-low`). -/
theorem norm_modifiedCrossOriginalRow_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hcoord : ∀ f i, finiteL2CoordinateIsometry volume (S f) i = (crossEntry i) f)
    (e : Lp ℂ 2 μ ≃ₗᵢ[ℝ] E) (Rorig : E →L[ℝ] OutputL2 n)
    (he : Rorig.comp e.toContinuousLinearEquiv.toContinuousLinearMap =
      transferOutputOperator (realQuadratureChannel S)) :
    ‖Rorig‖ ≤
      2 * Real.sqrt (n : ℝ) * modifiedCrossRowConstant n N R * ‖T‖ * CC * CG * Z := by
  rw [← ContinuousLinearMap.opNorm_comp_linearIsometryEquiv Rorig e, he]
  exact norm_modifiedCrossNativeRealRow_le
    (μ := μ) (φ := φ) (m := m) (hφ := hφ) (hm := hm) (hms := hms)
    (C := C) (B := B) (G := G) (hC := hC) (hBc := hBc) (hGc := hGc) (hB := hB) (hG := hG)
    (hK := hK) (hGK := hGK) (χ := χ) (hχ := hχ) (hχs := hχs) (hχK := hχK)
    (R := R) (hbox := hbox) (CC := CC) (CG := CG) (Z := Z) (hCC := hCC) (hCG := hCG) (hZ := hZ)
    (hCb := hCb) (hGb := hGb) (hBmem := hBmem) (hBb := hBb) (T := T) (hT := hT) S hcoord

/-- The concrete quadratic consumer, with the full CrossRow scalar bounds
actually applied. Its factor two cancels precisely the genuine `2 Re` cost.
Only the fixed `√n` remains; no individual `CGraw`, sample count or shell count
enters the bound. The exact kernel identities connect the SAME source-dependent
`B = Dν v`, full corrected `Graw`, original measurement and current inverse
(`app:ch_mean_pairs:eq:mean-quadratic-low`). -/
theorem norm_fixedSourceQuadratic_le_modifiedCrossNativeRow
    {ι : Type*} [Fintype ι] {Raw : ι → Type*}
    [∀ i, NormedAddCommGroup (Raw i)] [∀ i, InnerProductSpace ℝ (Raw i)]
    [∀ i, CompleteSpace (Raw i)]
    (weight : ι → ℝ) (hweight : ∀ i, 0 ≤ weight i)
    (Cper : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hCper : IsSmoothPeriodic Cper)
    (Araw : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (Graw : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix (Fin N) (Fin n) ℂ))
    (CGraw : ι → ℝ)
    (hGraw : ∀ i v, periodicL2Norm (fun x ↦ (Graw i v).val x ()) ≤ CGraw i * ‖v‖)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u v : SmoothResidual n)
    (S : Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)))
    (hcoord : ∀ f i, finiteL2CoordinateIsometry volume (S f) i = (crossEntry i) f)
    (e : Lp ℂ 2 μ ≃ₗᵢ[ℝ] PiLp 2 Raw)
    (he : (modifiedCanonicalRow weight Cper hCper Araw Graw CGraw hGraw Q₀ v).comp
        e.toContinuousLinearEquiv.toContinuousLinearMap =
      transferOutputOperator (realQuadratureChannel S)) :
    ‖smoothResidualToL2 n (fixedSourceQuadratic weight Cper hCper Araw Graw Q₀ v u)‖ ≤
      Real.sqrt (n : ℝ) * modifiedCrossRowConstant n N R * ‖T‖ * CC * CG * Z *
        ‖CanonicalRow.weightedRow weight Araw‖ * ‖Q₀‖ * ‖smoothResidualToL2 n u‖ := by
  have hrow := norm_modifiedCrossOriginalRow_le
    (μ := μ) (φ := φ) (m := m) (hφ := hφ) (hm := hm) (hms := hms)
    (C := C) (B := B) (G := G) (hC := hC) (hBc := hBc) (hGc := hGc) (hB := hB) (hG := hG)
    (hK := hK) (hGK := hGK) (χ := χ) (hχ := hχ) (hχs := hχs) (hχK := hχK)
    (R := R) (hbox := hbox) (CC := CC) (CG := CG) (Z := Z) (hCC := hCC) (hCG := hCG) (hZ := hZ)
    (hCb := hCb) (hGb := hGb) (hBmem := hBmem) (hBb := hBb) (T := T) (hT := hT)
    S hcoord e (modifiedCanonicalRow weight Cper hCper Araw Graw CGraw hGraw Q₀ v) he
  have hquad := two_mul_norm_fixedSourceQuadratic_le_aggregate
    weight hweight Cper hCper Araw Graw CGraw hGraw Q₀ u v
  have hh := hquad.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrow
      (norm_nonneg (CanonicalRow.weightedRow weight Araw))) (norm_nonneg Q₀))
    (norm_nonneg (smoothResidualToL2 n u)))
  nlinarith only [hh]

end FullCrossRow
end JanetCartan.PhysicalMean
