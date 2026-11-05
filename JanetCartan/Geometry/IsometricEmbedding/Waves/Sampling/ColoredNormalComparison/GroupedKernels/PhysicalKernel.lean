module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.GroupedKernels.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.OutputTransfer
public import JanetCartan.Analysis.Microlocal.NormalComparison.KernelCalculus.FullKernel
public import Mathlib.Topology.UrysohnsLemma

/-!
# The full two-position kernel after band reassembly

The normal in `app:ch_waves:eq:sampling-prefix-normal` is represented on the
original vector-valued Lebesgue output. The frequency integral is over the
original wide band, and both positions use the unchanged `BandKernelData.kernel`.
Compactness supplies every Fubini integrability premise. An auxiliary continuous
frequency cutoff is used only to apply the existing compact-kernel theorem;
it equals one on the band and disappears from every exported formula.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped InnerProductSpace BigOperators ENNReal
set_option maxHeartbeats 800000

namespace JanetCartan.Sampling.ColoredNormalComparison
open RawInputRealization RawInputPartition SamplingKernelBounds
open NormalComparison Pseudodifferential AmplitudeBound

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {n : ℕ}

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
private theorem exists_compact_wideKernel (D : BandKernelData P n) (j : ℕ) (z : P) :
    ∃ t : Fin n → Euclidean n → Euclidean (n - 1) → ℂ,
      (∀ i, Continuous (Function.uncurry (t i))) ∧
      (∀ i, HasCompactSupport (Function.uncurry (t i))) ∧
      ∀ η ∈ wideBand n j, ∀ x i, t i x η = D.kernel z η x i := by
  obtain ⟨c, hc, _, hcs, _⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_samplingWideBand n j) isClosed_empty (Set.disjoint_empty _)
  let t := fun i x η ↦ (c η : ℂ) * D.kernel z η x i
  have hk : Continuous (fun q : Euclidean n × Euclidean (n - 1) ↦
      D.kernel z q.2 q.1) :=
    D.continuous_kernel.comp ((continuous_const.prodMk continuous_snd).prodMk continuous_fst)
  refine ⟨t, ?_, ?_, ?_⟩
  · intro i
    exact (Complex.continuous_ofReal.comp (c.continuous.comp continuous_snd)).mul
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i).continuous.comp hk)
  · intro i
    apply HasCompactSupport.intro (D.physicalSupport_compact.prod hcs)
    rintro ⟨x, η⟩ h
    by_cases hx : x ∈ D.physicalSupport
    · have hη : η ∉ tsupport c := fun hη ↦ h ⟨hx, hη⟩
      simp [t, image_eq_zero_of_notMem_tsupport hη]
    · simp [t, D.kernel_eq_zero z η x hx]
  · intro η hη x i
    have he : c η = 1 := hc hη
    simp [t, he]

private theorem wideKernelOperator_eq_compact (D : BandKernelData P n) (j : ℕ) (z : P)
    {t : Fin n → Euclidean n → Euclidean (n - 1) → ℂ}
    (hc : ∀ i, Continuous (Function.uncurry (t i)))
    (hs : ∀ i, HasCompactSupport (Function.uncurry (t i)))
    (he : ∀ η ∈ wideBand n j, ∀ x i, t i x η = D.kernel z η x i) :
    wideKernelOperator D j z =
      toSamplingOutput (compactVectorKernelOperator (wideBand n j) hc hs) := by
  apply ContinuousLinearMap.adjoint.injective
  rw [toSamplingOutput_adjoint]
  ext1 v
  apply Lp.ext
  filter_upwards [wideKernelOperator_hasAdjointKernel D j z v,
    compactVectorKernelOperator_adjoint_ae_integral (wideBand n j) hc hs
      (finiteL2CoordinateIsometry volume v),
    ae_restrict_mem (measurableSet_wideBand n j)] with η hη ht hmem
  change (wideKernelOperator D j z).adjoint v η =
    (compactVectorKernelOperator (wideBand n j) hc hs).adjoint
      (finiteL2CoordinateIsometry volume v) η
  rw [hη, ht, ← (finiteL2CoordinateIsometry volume).inner_map_map,
    PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [finiteL2Coordinates_apply_ae volume (D.column z η) i,
    D.column_coe z η] with x hx hk
  change (finiteL2CoordinateIsometry volume (D.column z η)) i x = _ at hx
  rw [RCLike.inner_apply, hx, hk, he η hmem x i]
  simp only [starRingEnd_apply, mul_comm]

private def wideKernelUnitWeight (n j : ℕ) :
    Lp ℂ ∞ (volume.restrict (wideBand n j)) :=
  (memLp_top_const (1 : ℂ)).toLp (fun _ ↦ 1)

private theorem wideKernelUnitWeight_coe (n j : ℕ) :
    wideKernelUnitWeight n j =ᵐ[volume.restrict (wideBand n j)] fun _ ↦ (1 : ℂ) :=
  MemLp.coeFn_toLp _

private theorem multiplication_wideKernelUnitWeight (n j : ℕ) :
    multiplicationOperator (wideKernelUnitWeight n j) = ContinuousLinearMap.id ℂ _ := by
  ext1 f
  apply Lp.ext
  filter_upwards [multiplicationOperator_coeFn (wideKernelUnitWeight n j) f,
    wideKernelUnitWeight_coe n j] with η hη h1
  change multiplicationOperator (wideKernelUnitWeight n j) f η = f η
  simpa only [h1, one_mul] using hη

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- Every inner frequency integral of the full matrix normal is absolutely
convergent, without assumptions beyond `BandKernelData`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_wideKernelNormal_entry (D : BandKernelData P n) (j : ℕ) (z : P)
    (x y : Euclidean n) (i k : Fin n) :
    Integrable (fun η ↦ D.kernel z η x i * star (D.kernel z η y k))
      (volume.restrict (wideBand n j)) := by
  have hc : Continuous (fun η ↦ D.kernel z η x i * star (D.kernel z η y k)) := by
    have hx := D.continuous_kernel.comp
      (((continuous_const (y := z)).prodMk continuous_id).prodMk (continuous_const (y := x)))
    have hy := D.continuous_kernel.comp
      (((continuous_const (y := z)).prodMk continuous_id).prodMk (continuous_const (y := y)))
    exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i).continuous.comp hx).mul
      (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) k).continuous.comp hy).star)
  exact hc.continuousOn.integrableOn_compact (isCompact_samplingWideBand n j)

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- Absolute convergence of the outer original Lebesgue integral for the full
matrix normal (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem integrable_wideKernelNormal_action (D : BandKernelData P n) (j : ℕ) (z : P)
    (f : SamplingKernelBounds.Output n) (x : Euclidean n) (i k : Fin n) :
    Integrable (fun y ↦ (∫ η in wideBand n j,
      D.kernel z η x i * star (D.kernel z η y k)) * f y k) volume := by
  obtain ⟨t, hc, hs, he⟩ := exists_compact_wideKernel D j z
  apply (integrable_compactCrossKernel_action (wideBand n j) (hc i) (hs i)
    (hc k) (hs k) (wideKernelUnitWeight n j)
    (finiteL2CoordinateIsometry volume f k) x).congr
  filter_upwards [finiteL2Coordinates_apply_ae volume f k] with y hy
  change (finiteL2CoordinateIsometry volume f) k y = _ at hy
  rw [hy]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_wideBand n j),
    wideKernelUnitWeight_coe n j] with η hη h1
  simp only [he η hη, h1, mul_one]

/-- The reassembled normal has the literal full two-position kernel on the
entire vector-valued Lebesgue output. Both physical positions use the original
kernel; the inner integral is over the original wide band
(`app:ch_waves:eq:sampling-prefix-normal`, `app:ch_waves:eq:colored-normal-comparison`). -/
theorem wideKernelOperator_normal_ae_integral (D : BandKernelData P n) (j : ℕ) (z : P)
    (f : SamplingKernelBounds.Output n) :
    atomNormal (wideKernelOperator D j z) f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun i ↦ ∑ k : Fin n, ∫ y,
        (∫ η in wideBand n j, D.kernel z η x i * star (D.kernel z η y k)) * f y k) := by
  obtain ⟨t, hc, hs, he⟩ := exists_compact_wideKernel D j z
  rw [wideKernelOperator_eq_compact D j z hc hs he]
  change (toSamplingOutput _ ∘L (toSamplingOutput _).adjoint) f =ᵐ[volume] _
  rw [toSamplingOutput_normal]
  apply samplingOutputConjugation_ae_kernel
  intro v i
  have h := compactVectorKernelOperator_cross_ae_integral (wideBand n j)
    hc hs hc hs (wideKernelUnitWeight n j) v i
  rw [multiplication_wideKernelUnitWeight] at h
  refine h.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  apply Finset.sum_congr rfl
  intro k _
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  dsimp only
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_wideBand n j),
    wideKernelUnitWeight_coe n j] with η hη h1
  simp only [he η hη, h1, mul_one]

end JanetCartan.Sampling.ColoredNormalComparison
