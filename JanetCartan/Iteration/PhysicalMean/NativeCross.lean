module

public import JanetCartan.Iteration.PhysicalMean.ScalarNorm

/-!
# Construct the native full modified vector row

The scalar entries of the SAME modified full kernel assemble into an actual
complex vector-valued L² operator. The sharp scalar estimate and real-channel
norm estimate then apply without postulating a coordinate realization or a
successful row bound. Original-raw isometry and periodization identifications
remain literal integral identities for the parent producer
(`app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open Pseudodifferential PeriodicLocalL2 AmplitudeBound.PaperEstimates NormalComparison

/-- Assemble actual scalar L² coordinate rows in the fixed measured output
dimension. This construction does not count samples, bands, or input variables. -/
def nativeScalarRowsToVector {n : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (B : Fin n → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n))) :
    Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)) :=
  (finiteL2CoordinateIsometry volume).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n ↦ Lp ℂ 2 (volume : Measure (Euclidean n)))).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.pi B

/-- The constructed vector row has exactly its supplied scalar entries. -/
@[simp] theorem nativeScalarRowsToVector_coordinate {n : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (B : Fin n → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (f : Lp ℂ 2 μ) (i : Fin n) :
    finiteL2CoordinateIsometry volume (nativeScalarRowsToVector μ B f) i = B i f := by
  simp [nativeScalarRowsToVector]

section FullCross

variable {n N : ℕ} {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : X → Euclidean n → ℝ) (m : X → ℝ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B G : X → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hBc : Continuous (Function.uncurry B))
    (hGc : Continuous (Function.uncurry G))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hGK : ∀ u, tsupport (G u) ⊆ K)

/-- The actual native vector row of the FULL cross amplitude. Its scalar
entries use the original phase, complete mask and SAME input measure. -/
def nativeCrossRow :
    Lp ℂ 2 μ →L[ℂ] Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (Euclidean n)) :=
  nativeScalarRowsToVector μ (fun i ↦
    sampledMomentOperator μ φ m (modifiedCrossAdjointAmplitude C B G i) hφ hm
      (continuous_modifiedCrossAdjointAmplitude C B G hC.continuous hBc hGc i)
      hms hK (tsupport_modifiedCrossAdjointAmplitude_subset C B G hK.isClosed hGK i))

/-- The constructed vector row is literally the original scalar cross
integral in every physical coordinate, without any coordinate equality premise. -/
theorem nativeCrossRow_coordinate_ae (f : Lp ℂ 2 μ) (i : Fin n) :
    (fun x ↦ nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK f x i) =ᵐ[volume]
      fun x ↦ ∫ u, sampledMomentKernel φ m (modifiedCrossAdjointAmplitude C B G i) x u * f u ∂μ := by
  have hcoord := (finiteL2Coordinates_apply_ae volume
    (nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK f) i).symm
  change (fun x ↦ nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK f x i) =ᵐ[volume]
    (finiteL2CoordinateIsometry volume (nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK f) i) at hcoord
  rw [nativeCrossRow, nativeScalarRowsToVector_coordinate] at hcoord
  exact hcoord.trans (sampledMomentOperator_ae_kernel μ φ m (modifiedCrossAdjointAmplitude C B G i)
    hφ hm (continuous_modifiedCrossAdjointAmplitude C B G hC.continuous hBc hGc i)
    hms hK (tsupport_modifiedCrossAdjointAmplitude_subset C B G hK.isClosed hGK i) f)

/-- Literal FULL modified cross Bochner integral, on the SAME input measure
and original mask. The lower field is allowed to depend on the retained input
label; no pointwise supremum replaces its sharp Sobolev control. -/
def nativeCrossIntegral (f : Lp ℂ 2 μ) (x : Euclidean n) : EuclideanSpace ℂ (Fin n) :=
  ∫ u, ((m u : ℂ)*oscillatoryFactor 1 (φ u x)*f u) •
    CanonicalRowComparison.complexCrossMeasurement (C x) (B u x) (G u x) ∂μ

omit [SecondCountableTopology X] [SFinite μ] in
include hφ hm hms hC hBc hGc hK hGK in
/-- The literal vector integrand is integrable from the primitive original
compact kernel and input L² datum, rather than an extra integrability premise. -/
theorem nativeCrossIntegral_integrable (f : Lp ℂ 2 μ) (x : Euclidean n) :
    Integrable (fun u ↦ ((m u : ℂ)*oscillatoryFactor 1 (φ u x)*f u) •
      CanonicalRowComparison.complexCrossMeasurement (C x) (B u x) (G u x)) μ := by
  apply Integrable.of_eval_piLp
  intro i
  have hi := ContinuumAdjoint.DerivativeKernels.CompactCarrierKernel.integrable_compactKernel_mul_L2
    (continuous_sampledMomentKernel φ m (modifiedCrossAdjointAmplitude C B G i) hφ hm
      (continuous_modifiedCrossAdjointAmplitude C B G hC.continuous hBc hGc i))
    (hasCompactSupport_sampledMomentKernel φ m (modifiedCrossAdjointAmplitude C B G i)
      hms hK (tsupport_modifiedCrossAdjointAmplitude_subset C B G hK.isClosed hGK i)) f x
  convert hi using 1
  funext u
  simp only [PiLp.smul_apply, smul_eq_mul, sampledMomentKernel,
    modifiedCrossAdjointAmplitude, star_star]
  ring

/-- The constructed vector row is exactly the FULL modified cross integral
as an L² function, not just an operator satisfying the desired estimate. -/
theorem nativeCrossRow_ae_kernel (f : Lp ℂ 2 μ) :
    nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK f =ᵐ[volume]
      nativeCrossIntegral μ φ m C B G f := by
  have hi := nativeCrossIntegral_integrable μ φ m hφ hm hms C B G hC hBc hGc hK hGK f
  have hh : ∀ᵐ x ∂(volume : Measure (Euclidean n)), ∀ i : Fin n,
      nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK f x i =
        ∫ u, sampledMomentKernel φ m (modifiedCrossAdjointAmplitude C B G i) x u*f u ∂μ :=
    (ae_all_iff).mpr (fun i ↦ nativeCrossRow_coordinate_ae μ φ m hφ hm hms C B G hC hBc hGc hK hGK f i)
  filter_upwards [hh] with x hx
  ext i
  rw [hx i]
  dsimp only [nativeCrossIntegral]
  rw [eval_integral_piLp (fun j ↦ (hi x).eval_piLp j)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u ↦ by
    simp only [PiLp.smul_apply, smul_eq_mul, sampledMomentKernel,
      modifiedCrossAdjointAmplitude, star_star]
    ring

include hφ hm hms hC hBc hGc hK hGK in
/-- Genuine L² membership of the actual modified cross integral, including
arbitrary original sample weights and the complete native mask. -/
theorem nativeCrossIntegral_memLp (f : Lp ℂ 2 μ) :
    MemLp (nativeCrossIntegral μ φ m C B G f) 2 volume :=
  (memLp_congr_ae (nativeCrossRow_ae_kernel μ φ m hφ hm hms C B G hC hBc hGc hK hGK f)).mp
    (Lp.memLp (nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK f))

/-- Exact physical L² norm of the original cross integral. This equality
allows the balanced branch estimates to be applied directly to physical
coordinate derivatives before the same-order Sobolev transfer. -/
theorem nativeCrossIntegral_lpNorm (f : Lp ℂ 2 μ) :
    lpNorm (nativeCrossIntegral μ φ m C B G f) 2 volume =
      ‖nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK f‖ := by
  rw [← toReal_eLpNorm, eLpNorm_congr_ae
    (nativeCrossRow_ae_kernel μ φ m hφ hm hms C B G hC hBc hGc hK hGK f).symm]
  exact (Lp.norm_def _).symm

variable (hB : ∀ u, ContDiff ℝ ∞ (B u)) (hG : ∀ u, ContDiff ℝ ∞ (G u))
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (Rbox : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ Rbox)
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

include hB hG hχ hχs hχK hbox hCC hCG hZ hCb hGb hBmem hBb hT

/-- Actual sharp bound for the constructed FULL vector cross row. Neither
a successful vector-row norm nor its scalar coordinate realization is an
input. The fixed output dimension is the only coordinate loss. -/
theorem norm_nativeCrossRow_le :
    ‖nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK‖ ≤
      Real.sqrt (n : ℝ)*modifiedCrossRowConstant n N Rbox*‖T‖*CC*CG*Z := by
  have hb : 0 ≤ modifiedCrossRowConstant n N Rbox*‖T‖*CC*CG*Z := by
    have := modifiedCrossRowConstant_nonneg n N Rbox
    positivity
  have hn := norm_nativeScalarRow_le_of_coordinate_bounds μ
    (fun i ↦ sampledMomentOperator μ φ m (modifiedCrossAdjointAmplitude C B G i) hφ hm
      (continuous_modifiedCrossAdjointAmplitude C B G hC.continuous hBc hGc i)
      hms hK (tsupport_modifiedCrossAdjointAmplitude_subset C B G hK.isClosed hGK i))
    (nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK)
    (fun f i ↦ nativeScalarRowsToVector_coordinate μ _ f i) hb
    (fun i ↦ norm_modifiedCrossNativeScalarRow_le μ φ m hφ hm hms C B G hC hBc hGc hB hG
      hK hGK χ hχ hχs hχK Rbox hbox CC CG Z hCC hCG hZ hCb hGb hBmem hBb T hT i)
  simpa only [mul_assoc] using hn

/-- The SAME constructed native row with its genuine `2 Re` channel and
periodic output has precisely the sharp modified cross-row bound. -/
theorem norm_nativeRealCrossRow_le :
    ‖transferOutputOperator (realQuadratureChannel
      (nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK))‖ ≤
      2*Real.sqrt (n : ℝ)*modifiedCrossRowConstant n N Rbox*‖T‖*CC*CG*Z :=
  norm_modifiedCrossNativeRealRow_le (μ := μ) (φ := φ) (m := m)
    (hφ := hφ) (hm := hm) (hms := hms) (C := C) (B := B) (G := G)
    (hC := hC) (hBc := hBc) (hGc := hGc) (hB := hB) (hG := hG)
    (hK := hK) (hGK := hGK) (χ := χ) (hχ := hχ) (hχs := hχs) (hχK := hχK)
    (R := Rbox) (hbox := hbox) (CC := CC) (CG := CG) (Z := Z)
    (hCC := hCC) (hCG := hCG) (hZ := hZ) (hCb := hCb) (hGb := hGb)
    (hBmem := hBmem) (hBb := hBb) (T := T) (hT := hT)
    (nativeCrossRow μ φ m hφ hm hms C B G hC hBc hGc hK hGK)
    (fun f i ↦ nativeScalarRowsToVector_coordinate μ _ f i)

end FullCross
end JanetCartan.PhysicalMean
