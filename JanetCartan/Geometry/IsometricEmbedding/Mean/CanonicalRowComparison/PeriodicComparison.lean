module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalRowComparison.SampledRow
public import JanetCartan.Analysis.Fourier.Periodic.LocalL2.OutputTransfer
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalBandBounds

/-!
# The same sampled normal on the canonical output space

Transfer only the physical output to the auxiliary torus, leaving the raw
annular Hilbert spaces and their Lebesgue measures unchanged. Apply the
sampling producer's actual grouped-prefix event and colored comparison to
the finite weighted row, with the identical auxiliary/exterior summand on
both sides. This supplies the operator comparison format consumed by
`CanonicalChange.Comparison` and `CanonicalBandBounds`.

The transport endpoint still has to be identified with the original continuum
row, including the prepared-scalar change. No independently selected continuum
row or inverse is identified here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory

namespace JanetCartan.CanonicalRowComparison

open SeparatedSampling Sampling Sampling.Realization SamplingKernelBounds
open RawInputPartition PeriodicLocalL2

variable {J : Type*} [Fintype J] {n p : ℕ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- The sampled component on the canonical torus output, with the original
raw input Hilbert space (`app:ch_mean_pairs:defn:mean-canonical`). -/
def periodicSampledComponent (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : J → Lattice → Point)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n)
    (i : SampleIndex p B ψ w h U) : E →L[ℝ] PeriodicL2 n (Euclidean n) :=
  transferOutputOperator (sampledComponent B ψ w h U T i)

omit [CompleteSpace E] in
/-- The complete finite row transfers only its output. In particular, taking
its raw adjoint does not reinterpret initial variables as torus data
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem weightedRow_periodicSampledComponent
    (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : J → Lattice → Point)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n) :
    CanonicalRow.weightedRow (sampleWeight B ψ w h U)
        (periodicSampledComponent B ψ w h U T) =
      transferOutputOperator (CanonicalRow.weightedRow (sampleWeight B ψ w h U)
        (sampledComponent B ψ w h U T)) := by
  ext1 v
  simp [CanonicalRow.weightedRow_apply, transferOutputOperator, periodicSampledComponent]

/-- The normal of the SAME literal finite row transfers to the canonical
output with the exact factor four (`app:ch_waves:eq:real-normal`,
`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem periodic_sampled_weightedRow_normal
    (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : J → Lattice → Point)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n)
    (hμ : ∀ i : SampleIndex p B ψ w h U, 0 ≤ sampleWeight B ψ w h U i) :
    let A := CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (periodicSampledComponent B ψ w h U T)
    A.comp A.adjoint = transferOperator ((4 : ℝ) • realOutputCompression
      (∑ a, patchSampleNormal p B (ψ a) w h (T a) (U a))) := by
  dsimp only
  rw [weightedRow_periodicSampledComponent, transferOutputOperator_normal,
    sampled_weightedRow_normal B ψ w h U T hμ]

/-- The producer's common event and colored estimate give the complete
canonical normal comparison on the torus for every literal grouped prefix.
The unchanged auxiliary/exterior normal cancels exactly. Constants are those
of the SAME event and kernel family (`app:ch_mean_pairs:eq:mean-normal-comparison`,
`app:ch_waves:eq:sampling-all-prefixes`). The zero endpoint remains explicit
until its original-continuum identification is supplied. -/
theorem refined_complete_normal_sub_transport_le {bands : ℕ}
    (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (ξ : J → ShiftSpace p B h)
    (D : J → BandKernelData (Fin bands × ((Fin 3 → Fin (p + 1)) × Point)) n)
    (D₀ : J → BandKernelData (Fin bands × Point) n)
    (auxiliary : PeriodicL2 n (Euclidean n) →L[ℝ] PeriodicL2 n (Euclidean n))
    (L : ℕ)
    (hμ : ∀ i : SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a)),
      0 ≤ sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)) i)
    {samplingError transportError : ℝ}
    (hevent : ‖familyDeviation p B ψ w h
      (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)) ξ‖ ≤ samplingError)
    (htransport : ‖(∑ a, patchMeanNormal p B (ψ a) w h
      (fun c z ↦ refinedKernelPrefix (D a) L (c, z))) -
        (∑ a, ∫ z : Point, ψ a z • atomNormal (refinedKernelPrefix (D₀ a) L z))‖ ≤
          transportError) :
    let A := CanonicalRow.weightedRow
      (sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)))
      (periodicSampledComponent B ψ w h (fun a ↦ extendedShift (ξ a))
        (fun a c z ↦ refinedKernelPrefix (D a) L (c, z)))
    ‖(auxiliary + A.comp A.adjoint) - (auxiliary + transferOperator
      ((4 : ℝ) • realOutputCompression
        (∑ a, ∫ z : Point, ψ a z • atomNormal (refinedKernelPrefix (D₀ a) L z))))‖ ≤
      4 * (samplingError + transportError) := by
  dsimp only
  rw [add_sub_add_left_eq_sub, weightedRow_periodicSampledComponent,
    transferOutputOperator_normal]
  have hsub (X Y : EuclideanL2 n (Euclidean n) →L[ℝ] EuclideanL2 n (Euclidean n)) :
      transferOperator X - transferOperator Y = transferOperator (X - Y) := by
    simp only [transferOperator, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [hsub]
  exact (norm_transferOperator_le _).trans
    (sampled_weightedRow_normal_sub_transport_le B ψ w h ξ
      (fun a c z ↦ refinedKernelPrefix (D a) L (c, z))
      (fun a z ↦ refinedKernelPrefix (D₀ a) L z) hμ hevent htransport)

/-- Convert the sampling kernel's fixed Fourier scalar to the literal
`RawPrimary` integral convention. This factor depends only on dimension;
it is never an inverse sample weight, and both raw quadratures remain
unchanged (`app:ch_waves:eq:individual-representation`,
`app:ch_mean_pairs:defn:mean-canonical`). -/
def rawIntegralSampledComponent (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : J → Lattice → Point)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n)
    (i : SampleIndex p B ψ w h U) : E →L[ℝ] PeriodicL2 n (Euclidean n) :=
  ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ • periodicSampledComponent B ψ w h U T i

omit [CompleteSpace E] in
/-- The SAME nonnegative weights and literal sample labels form the raw
physical row. Only the sampling theorem's fixed Fourier convention is
converted (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem weightedRow_rawIntegralSampledComponent
    (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : J → Lattice → Point)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n) :
    CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (rawIntegralSampledComponent B ψ w h U T) =
        ((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹ •
          CanonicalRow.weightedRow (sampleWeight B ψ w h U)
            (periodicSampledComponent B ψ w h U T) := by
  ext1 v
  simp only [CanonicalRow.weightedRow_apply, rawIntegralSampledComponent,
    smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun _ _ ↦ smul_comm _ _ _)

/-- The fixed Fourier factor enters the raw normal squared. The original
raw adjoint is taken before any continuum inverse; no sampled operator is
inverted (`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem rawIntegral_sampled_weightedRow_normal
    (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (U : J → Lattice → Point)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n) :
    let A := CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (periodicSampledComponent B ψ w h U T)
    let Araw := CanonicalRow.weightedRow (sampleWeight B ψ w h U)
      (rawIntegralSampledComponent B ψ w h U T)
    Araw.comp Araw.adjoint = (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 •
      A.comp A.adjoint := by
  dsimp only
  rw [weightedRow_rawIntegralSampledComponent, map_smul,
    ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul, ← pow_two]

/-- Apply the supplied common event to literal raw-integral components,
including channels with the balanced label-count factor. Only the fixed Fourier
normalization is inverted. The SAME auxiliary normal, weights, shifts and raw
adjoints are retained (`app:ch_mean_pairs:eq:mean-normal-comparison`,
`app:ch_waves:eq:colored-normal-comparison`). -/
theorem rawIntegral_sampled_normal_sub_transport_le
    (B : ℝ) (ψ : J → Point → ℝ) (w : ℝ → ℝ) (h : ℝ)
    (ξ : J → ShiftSpace p B h)
    (T : J → (Fin 3 → Fin (p + 1)) → Point → E →L[ℂ] Output n)
    (T₀ : J → Point → E →L[ℂ] Output n)
    (hμ : ∀ i : SampleIndex p B ψ w h (fun a ↦ extendedShift (ξ a)),
      0 ≤ sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)) i)
    (auxiliary : PeriodicL2 n (Euclidean n) →L[ℝ] PeriodicL2 n (Euclidean n))
    {samplingError transportError : ℝ}
    (hevent : ‖familyDeviation p B ψ w h T ξ‖ ≤ samplingError)
    (htransport : ‖(∑ a, patchMeanNormal p B (ψ a) w h (T a)) -
      (∑ a, ∫ z : Point, ψ a z • atomNormal (T₀ a z))‖ ≤ transportError) :
    let Araw := CanonicalRow.weightedRow
      (sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)))
      (rawIntegralSampledComponent B ψ w h (fun a ↦ extendedShift (ξ a)) T)
    ‖(auxiliary + Araw.comp Araw.adjoint) -
      (auxiliary + (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 • transferOperator
        ((4 : ℝ) • realOutputCompression
          (∑ a, ∫ z : Point, ψ a z • atomNormal (T₀ a z))))‖ ≤
      (((2 * Real.pi) ^ (-(n : ℝ) / 2))⁻¹) ^ 2 * (4 * (samplingError + transportError)) := by
  dsimp only
  rw [add_sub_add_left_eq_sub, rawIntegral_sampled_weightedRow_normal]
  let c : ℝ := (2 * Real.pi) ^ (-(n : ℝ) / 2)
  let A := CanonicalRow.weightedRow (sampleWeight B ψ w h (fun a ↦ extendedShift (ξ a)))
    (periodicSampledComponent B ψ w h (fun a ↦ extendedShift (ξ a)) T)
  let R := transferOperator ((4 : ℝ) • realOutputCompression
    (∑ a, ∫ z : Point, ψ a z • atomNormal (T₀ a z)))
  change ‖(c⁻¹) ^ 2 • A.comp A.adjoint - (c⁻¹) ^ 2 • R‖ ≤
    (c⁻¹) ^ 2 * (4 * (samplingError + transportError))
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  dsimp only [A, R]
  rw [weightedRow_periodicSampledComponent, transferOutputOperator_normal]
  have hsub (X Y : EuclideanL2 n (Euclidean n) →L[ℝ] EuclideanL2 n (Euclidean n)) :
      transferOperator X - transferOperator Y = transferOperator (X - Y) := by
    simp only [transferOperator, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
  rw [hsub]
  exact (norm_transferOperator_le _).trans
    (sampled_weightedRow_normal_sub_transport_le B ψ w h ξ T T₀ hμ hevent htransport)

end JanetCartan.CanonicalRowComparison
