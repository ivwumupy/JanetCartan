module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Coordinates
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Bands
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Synthesis
public import JanetCartan.Analysis.Operator.RealQuadratures
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Literal sampling output and both physical quadratures

Coordinate and realification deductions for
`app:ch_waves:eq:colored-normal-comparison` and the real-normal assertion after
`app:ch_waves:eq:sampling-prefix-normal`. We use the existing
`Pseudodifferential.finiteL2CoordinateIsometry` with Lebesgue measure. Both
physical positions of the full normal kernel remain unchanged.

The consumer is the final assembly of the colored-to-transport comparison:
`Bands` produces the coordinate operator estimate; these results transport it
to `SamplingKernelBounds.Output` and then to the real output used by
`CurrentNormalComparison`. Actual wave-kernel identification, the transport
endpoint, and spectator integrability remain obligations of that assembly.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison

open NormalComparison SamplingKernelBounds Pseudodifferential

variable {n : ℕ}

/-- Conjugation by the existing coordinate isometry, for the full output in
`app:ch_waves:eq:colored-normal-comparison`. Only finite fiber coordinates
change; the underlying measure is still Lebesgue measure on `Euclidean n`. -/
def samplingOutputConjugation (n : ℕ) :
    (NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) ≃L[ℂ]
      (Output n →L[ℂ] Output n) :=
  let e := (finiteL2CoordinateIsometry (I := Fin n)
    (volume : Measure (Euclidean n))).symm.toContinuousLinearEquiv
  e.arrowCongr e

/-- The full two-sided action of the coordinate transfer
(`app:ch_waves:eq:colored-normal-comparison`). -/
@[simp] theorem samplingOutputConjugation_apply
    (A : NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) (f : Output n) :
    samplingOutputConjugation n A f =
      (finiteL2CoordinateIsometry volume).symm
        (A (finiteL2CoordinateIsometry volume f)) := rfl

/-- Output conjugation preserves the exact operator norm, with no dimension,
band-count, or sample-count loss (`app:ch_waves:eq:colored-normal-comparison`). -/
@[simp] theorem norm_samplingOutputConjugation
    (A : NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    ‖samplingOutputConjugation n A‖ = ‖A‖ := by
  let e := finiteL2CoordinateIsometry (I := Fin n) (volume : Measure (Euclidean n))
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    change ‖e.symm (A (e f))‖ ≤ _
    simpa only [e.symm.norm_map, e.norm_map] using A.le_opNorm (e f)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro f
    have h := (samplingOutputConjugation n A).le_opNorm (e.symm f)
    change ‖e.symm (A (e (e.symm f)))‖ ≤ _ at h
    simpa only [e.apply_symm_apply, e.symm.norm_map] using h

/-- Differences keep their exact norm on the literal sampling output
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem norm_samplingOutputConjugation_sub
    (A B : NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    ‖samplingOutputConjugation n A - samplingOutputConjugation n B‖ = ‖A - B‖ := by
  rw [← map_sub, norm_samplingOutputConjugation]

/-- Every finite color/band sum transfers exactly
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem samplingOutputConjugation_sum {ι : Type*} (s : Finset ι)
    (A : ι → NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    samplingOutputConjugation n (∑ i ∈ s, A i) =
      ∑ i ∈ s, samplingOutputConjugation n (A i) :=
  map_sum (samplingOutputConjugation n) A s

/-- Spectator integrability is equivalent in the two coordinate descriptions
(`app:ch_waves:eq:colored-normal-comparison`). The concrete integrability
proof is supplied by the parent from actual wave data. -/
theorem integrable_samplingOutputConjugation_iff
    {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    (A : Z → NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    Integrable (fun z ↦ samplingOutputConjugation n (A z)) ν ↔ Integrable A ν :=
  (samplingOutputConjugation n).integrable_comp_iff

/-- Transfer commutes with the fixed spectator Bochner integral, keeping its
original measure (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem samplingOutputConjugation_integral
    {Z : Type*} [MeasurableSpace Z] (ν : Measure Z)
    (A : Z → NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    samplingOutputConjugation n (∫ z, A z ∂ν) =
      ∫ z, samplingOutputConjugation n (A z) ∂ν :=
  ((samplingOutputConjugation n).integral_comp_comm A).symm

/-- A full two-position coordinate kernel is the same kernel on the literal
vector-valued output. Neither physical position nor Lebesgue measure changes
(`app:ch_osc:eq:osc-exact-normal-kernel`,
`app:ch_waves:eq:colored-normal-comparison`). -/
theorem samplingOutputConjugation_ae_kernel
    (A : NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n)
    (k : Euclidean n → Euclidean n → Fin n → Fin n → ℂ)
    (hA : ∀ (f : NormalOutputL2 n n) (i : Fin n),
      (A f) i =ᵐ[volume] fun x ↦ ∑ j, ∫ y, k x y i j * f j y)
    (f : Output n) :
    samplingOutputConjugation n A f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y, k x y i j * f y j) := by
  apply (finiteL2CoordinateIsometry_ae_iff volume _ _).mpr
  intro i
  have h := hA (finiteL2CoordinateIsometry volume f) i
  simp only [samplingOutputConjugation_apply,
    LinearIsometryEquiv.apply_symm_apply]
  refine h.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume f j] with y hy
  exact congrArg (k x y i j * ·) hy

/-- The actual uniform normal has its original two-position oscillatory
kernel on vector-valued Lebesgue L², with unchanged squared normalization
(`app:ch_osc:eq:osc-exact-normal-kernel`,
`app:ch_waves:eq:colored-normal-comparison`). -/
theorem uniformOscillatoryNormalOperator_sampling_ae_integral
    {G : UniformNormalGeometry n n} {C : ℕ → ℝ} (F : UniformNormalData G C)
    {K : ℝ} (hK : 0 ≤ K) {ε : ℝ} (hε : ε ∈ Set.Icc 0 G.ε₀)
    (g : Lp ℂ ∞ (volume.restrict G.D)) (f : Output n) :
    samplingOutputConjugation n (F.uniformOscillatoryNormalOperator K g ε) f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ j, ∫ y,
        (((K / (2 * Real.pi)) ^ n : ℝ) : ℂ) *
          (∫ u in G.D, oscillatoryFactor K (F.phase ε x u - F.phase ε y u) *
            (F.amplitude ε x u i * star (F.amplitude ε y u j)) * g u) * f y j) :=
  samplingOutputConjugation_ae_kernel _ _
    (F.uniformOscillatoryNormalOperator_ae_integral hK hε g) f

section Channels

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The original channel with output collected into vector-valued Lebesgue L²
(`app:ch_waves:eq:sampling-prefix-normal`). The input is unchanged. -/
def toSamplingOutput (T : E →L[ℂ] NormalOutputL2 n n) : E →L[ℂ] Output n :=
  (finiteL2CoordinateIsometry volume).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L T

/-- The actual conjugate Hilbert adjoint after coordinate collection
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem toSamplingOutput_adjoint (T : E →L[ℂ] NormalOutputL2 n n) :
    (toSamplingOutput T).adjoint =
      T.adjoint ∘L
        (finiteL2CoordinateIsometry volume).toContinuousLinearEquiv.toContinuousLinearMap := by
  simp only [toSamplingOutput, ContinuousLinearMap.adjoint_comp,
    LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.symm_symm]

/-- Full masked normal operators transfer by conjugation, using their actual
adjoints (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem toSamplingOutput_maskedNormal (T : E →L[ℂ] NormalOutputL2 n n)
    (M : E →L[ℂ] E) :
    toSamplingOutput T ∘L M ∘L (toSamplingOutput T).adjoint =
      samplingOutputConjugation n (T ∘L M ∘L T.adjoint) := by
  rw [toSamplingOutput_adjoint]
  rfl

/-- The unmasked normal transfer for the original rows
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem toSamplingOutput_normal (T : E →L[ℂ] NormalOutputL2 n n) :
    toSamplingOutput T ∘L (toSamplingOutput T).adjoint =
      samplingOutputConjugation n (T ∘L T.adjoint) := by
  rw [toSamplingOutput_adjoint]
  rfl

end Channels

/-- The physical normal transfer `4 Re`, as a bounded real-linear map on
coordinate operators. Its real part and inclusion are the existing
`RealQuadratures` maps on the full Lebesgue output
(`app:ch_waves:eq:real-normal`). -/
def samplingRealNormal (n : ℕ) :
    (NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) →L[ℝ]
      (Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (Euclidean n)) →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin n)) 2 (volume : Measure (Euclidean n))) :=
  LinearMap.mkContinuous
    { toFun := fun A ↦ (4 : ℝ) • realOutputCompression (samplingOutputConjugation n A)
      map_add' := by
        intro A B
        ext1 x
        simp [realOutputCompression, smul_add]
      map_smul' := by
        intro c A
        change (4 : ℝ) • realOutputCompression (samplingOutputConjugation n (c • A)) =
          c • ((4 : ℝ) • realOutputCompression (samplingOutputConjugation n A))
        rw [show samplingOutputConjugation n (c • A) = c • samplingOutputConjugation n A from
          ((samplingOutputConjugation n).toContinuousLinearMap.restrictScalars ℝ).map_smul c A]
        ext1 x
        simp [realOutputCompression, smul_smul, mul_comm] }
    4 (fun A ↦ by
      change ‖(4 : ℝ) • realOutputCompression (samplingOutputConjugation n A)‖ ≤ _
      rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
      exact mul_le_mul_of_nonneg_left
        ((realOutputCompression_norm_le _).trans_eq (norm_samplingOutputConjugation A))
        (by norm_num))

/-- Exact factor four in the physical normal transfer
(`app:ch_waves:eq:real-normal`). -/
@[simp] theorem samplingRealNormal_apply
    (A : NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    samplingRealNormal n A =
      (4 : ℝ) • realOutputCompression (samplingOutputConjugation n A) := rfl

/-- Realification costs only the fixed factor four
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem norm_samplingRealNormal_le
    (A : NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    ‖samplingRealNormal n A‖ ≤ 4 * ‖A‖ := by
  rw [samplingRealNormal_apply, norm_smul,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  exact mul_le_mul_of_nonneg_left
    ((realOutputCompression_norm_le _).trans_eq (norm_samplingOutputConjugation A))
    (by norm_num)

/-- The coordinate comparison transfers to both real input quadratures, with
no loss beyond the normal factor four
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem norm_samplingRealNormal_sub_le
    (A B : NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    ‖samplingRealNormal n A - samplingRealNormal n B‖ ≤ 4 * ‖A - B‖ := by
  rw [← map_sub]
  exact norm_samplingRealNormal_le _

/-- Both the literal complex output bound and its physical real counterpart
follow from a coordinate bound; its analytic producer is `Bands` followed by
the endpoint identification (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem sampling_normal_comparison_of_coordinate_bound
    (A B : NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) {b : ℝ}
    (h : ‖A - B‖ ≤ b) :
    ‖samplingOutputConjugation n A - samplingOutputConjugation n B‖ ≤ b ∧
      ‖samplingRealNormal n A - samplingRealNormal n B‖ ≤ 4 * b :=
  ⟨(norm_samplingOutputConjugation_sub A B).trans_le h,
    (norm_samplingRealNormal_sub_le A B).trans
      (mul_le_mul_of_nonneg_left h (by norm_num))⟩

/-- Real normals commute with finite color/band sums, including their original
real weights by real linearity (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem samplingRealNormal_sum {ι : Type*} (s : Finset ι)
    (A : ι → NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n) :
    samplingRealNormal n (∑ i ∈ s, A i) = ∑ i ∈ s, samplingRealNormal n (A i) :=
  map_sum (samplingRealNormal n) A s

/-- Integrable spectator families give integrable physical normals; the parent
must prove integrability from its actual wave data
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_samplingRealNormal
    {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    {A : Z → NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n} (hA : Integrable A ν) :
    Integrable (fun z ↦ samplingRealNormal n (A z)) ν :=
  (samplingRealNormal n).integrable_comp hA

/-- The exact factor-four real normal commutes with an integrable spectator
Bochner integral (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem samplingRealNormal_integral
    {Z : Type*} [MeasurableSpace Z] {ν : Measure Z}
    {A : Z → NormalOutputL2 n n →L[ℂ] NormalOutputL2 n n} (hA : Integrable A ν) :
    samplingRealNormal n (∫ z, A z ∂ν) = ∫ z, samplingRealNormal n (A z) ∂ν :=
  ((samplingRealNormal n).integral_comp_comm hA).symm

section RealChannels

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [InnerProductSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]

/-- This is the normal of the actual physical channel on the entire complex
input regarded as real, with exact factor four
(`app:ch_waves:eq:real-normal`). -/
theorem toSamplingOutput_real_maskedNormal (T : E →L[ℂ] NormalOutputL2 n n)
    (M : E →L[ℂ] E) :
    realQuadratureNormal (toSamplingOutput T) M =
      samplingRealNormal n (T ∘L M ∘L T.adjoint) := by
  rw [realQuadratureNormal_eq_four_realPart, toSamplingOutput_maskedNormal]
  rfl

/-- The unmasked physical row normal is exactly four times the real part of
the transferred full normal (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem toSamplingOutput_real_normal (T : E →L[ℂ] NormalOutputL2 n n) :
    realQuadratureChannel (toSamplingOutput T) ∘L
        (realQuadratureChannel (toSamplingOutput T)).adjoint =
      samplingRealNormal n (T ∘L T.adjoint) := by
  rw [realQuadratureChannel_normal_eq_four_realPart, toSamplingOutput_normal]
  rfl

omit [CompleteSpace E] in
/-- Both quadratures remain physical data after the coordinate change:
`2 Re(T f) - 2 Im(T g)` is evaluated at the same physical position
(`app:ch_osc:cor:osc-real`, `app:ch_waves:eq:sampling-prefix-normal`). -/
theorem toSamplingOutput_both_quadratures_ae
    (T : E →L[ℂ] NormalOutputL2 n n) (f g : E) :
    ∀ᵐ x ∂volume, ∀ i,
      realQuadratureChannel (toSamplingOutput T) (f + Complex.I • g) x i =
        2 * (((T f) i x).re - ((T g) i x).im) := by
  have hf := ae_all_iff.mpr (fun i ↦
    finiteL2Coordinates_apply_ae volume (toSamplingOutput T f) i)
  have hg := ae_all_iff.mpr (fun i ↦
    finiteL2Coordinates_apply_ae volume (toSamplingOutput T g) i)
  have he (v : E) : finiteL2CoordinateIsometry volume (toSamplingOutput T v) = T v :=
    (finiteL2CoordinateIsometry volume).apply_symm_apply (T v)
  change ∀ᵐ x ∂volume, ∀ i, (finiteL2CoordinateIsometry volume
    (toSamplingOutput T f)) i x = toSamplingOutput T f x i at hf
  change ∀ᵐ x ∂volume, ∀ i, (finiteL2CoordinateIsometry volume
    (toSamplingOutput T g)) i x = toSamplingOutput T g x i at hg
  rw [he] at hf hg
  filter_upwards [realQuadratureChannel_both_quadratures_ae (toSamplingOutput T) f g,
    hf, hg] with x hx hfx hgx
  intro i
  rw [hx i, ← hfx i, ← hgx i]

end RealChannels

/-- The checked `Bands` estimate on the literal complex sampling output and
on both physical real quadratures, with exactly the fixed factor four.
All hypotheses and the order of uniform quantifiers of
`exists_colored_prefix_homotopy_bound` are retained. This closes the coordinate
and realification steps of `app:ch_waves:eq:colored-normal-comparison`; the
parent must still identify the colored zero-parameter endpoint with transport
and perform the fixed spectator integration. -/
theorem exists_colored_prefix_output_homotopy_bound
    {Color : Type*} [Fintype Color] (G : UniformNormalGeometry n n)
    (C : ℕ → ℝ) {Rmin L : ℝ} (hRmin : 0 < Rmin) (hL : 0 ≤ L) :
    ∃ A > 0, ∀ (F : Color → ℕ → UniformNormalData G C)
      (R : Color → ℝ), (∀ c, Rmin ≤ R c) →
      ∀ (m : Color → Euclidean n → ℝ),
      (∀ c, ContDiffOn ℝ ∞ (m c) G.D) →
      ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∀ c u, u ∈ G.D → 0 ≤ m c u ∧ m c u ≤ 1) →
      (∀ c u, u ∈ G.D → ‖fderiv ℝ (m c) u‖ ≤ L / h) →
      ∀ g : Color → Lp ℂ ∞ (volume.restrict G.D),
      (∀ c, g c =ᵐ[volume.restrict G.D] fun u ↦ (m c u : ℂ)) →
      ∀ lam Λ : ℝ, 0 < lam → 1 ≤ Λ → Λ / (Rmin * lam) ≤ G.ε₀ →
      ∀ J ≤ RawInputPartition.cutoffCount Λ,
        let colored := ∑ c, ∑ j ∈ Finset.range J,
          (F c j).uniformOscillatoryNormalOperator (RawInputPartition.dyadicScale j) (g c)
            ((R c * lam)⁻¹ * RawInputPartition.dyadicScale j)
        let endpoint := ∑ c, ∑ j ∈ Finset.range J,
          (F c j).uniformOscillatoryNormalOperator (RawInputPartition.dyadicScale j) (g c) 0
        ‖samplingOutputConjugation n colored - samplingOutputConjugation n endpoint‖ ≤
            A * lam⁻¹ * Λ / h ∧
          ‖samplingRealNormal n colored - samplingRealNormal n endpoint‖ ≤
            4 * (A * lam⁻¹ * Λ / h) := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_colored_prefix_homotopy_bound (Color := Color) G C hRmin hL
  refine ⟨A, hA, ?_⟩
  intro F R hR m hm h hh hh₁ hmask hderiv g hg lam Λ hlam hΛ hbuffer J hJ
  exact sampling_normal_comparison_of_coordinate_bound _ _
    (hbound F R hR m hm h hh hh₁ hmask hderiv g hg lam Λ hlam hΛ hbuffer J hJ)

end JanetCartan.Sampling.ColoredNormalComparison
