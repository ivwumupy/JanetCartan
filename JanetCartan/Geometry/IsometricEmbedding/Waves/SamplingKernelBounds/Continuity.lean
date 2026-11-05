module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Synthesis
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Continuity from squared kernels

Compactly supported continuous kernels vary continuously in the physical L²
space. Together with the squared-kernel estimate this gives operator norm
continuity in `app:ch_waves:eq:sampling-operator-bounds`. The compact integral
continuity theorem used below is proved by dominated convergence.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Topology
namespace JanetCartan.SamplingKernelBounds

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {d : ℕ}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

omit [FirstCountableTopology P] [LocallyCompactSpace P] [InnerProductSpace ℂ E] in
/-- Physical columns belong to L² by their actual compact support
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem memLp_compact_column {K : P → Euclidean d → E}
    (hK : Continuous K.uncurry) {S : Set (Euclidean d)} (hS : IsCompact S)
    (hs : ∀ p x, x ∉ S → K p x = 0) (p : P) : MemLp (K p) 2 volume :=
  (hK.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
    (HasCompactSupport.intro hS (hs p))

/-- Joint continuity and fixed compact physical support imply continuity into
literal Lebesgue L², by the squared-difference integral
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_compact_column {K : P → Euclidean d → E}
    (hK : Continuous K.uncurry) {S : Set (Euclidean d)} (hS : IsCompact S)
    (hs : ∀ p x, x ∉ S → K p x = 0) :
    Continuous (fun p ↦ (memLp_compact_column hK hS hs p).toLp (K p)) := by
  let F := fun p ↦ (memLp_compact_column hK hS hs p).toLp (K p)
  change Continuous F
  rw [continuous_iff_continuousAt]
  intro p
  have heq (q : P) : ‖F q - F p‖ ^ 2 = ∫ x in S, ‖K q x - K p x‖ ^ 2 := by
    rw [l2_vector_norm_sq_eq_integral (𝕜 := ℂ),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by simp [hs _ x hx])]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (F q) (F p),
      MemLp.coeFn_toLp (memLp_compact_column hK hS hs q),
      MemLp.coeFn_toLp (memLp_compact_column hK hS hs p)] with x hsub hq hp
    simp only [hsub, Pi.sub_apply, F, hq, hp]
  have hc : Continuous (fun q ↦ ‖F q - F p‖ ^ 2) := by
    simp_rw [heq]
    apply continuous_parametric_integral_of_continuous (s := S) _ hS
    exact (hK.sub (hK.comp (continuous_const.prodMk continuous_snd))).norm.pow 2
  have ht : Filter.Tendsto (fun q ↦ Real.sqrt (‖F q - F p‖ ^ 2)) (𝓝 p)
      (𝓝 (Real.sqrt (‖F p - F p‖ ^ 2))) := (Real.continuous_sqrt.comp hc).continuousAt.tendsto
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), Real.sqrt_zero] using ht

omit [FirstCountableTopology P] [LocallyCompactSpace P] [InnerProductSpace ℂ E] in
/-- Continuous columns are square integrable on a compact frequency set
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem memLp_restrict_compact_column {k : Euclidean d → E} (hk : Continuous k)
    {S : Set (Euclidean d)} (hS : IsCompact S) : MemLp k 2 (volume.restrict S) := by
  let : IsFiniteMeasure (volume.restrict S) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hS.measure_lt_top (μ := volume)⟩
  obtain ⟨C, hC⟩ := hS.bddAbove_image hk.norm.continuousOn
  apply MemLp.of_bound hk.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  exact hC (Set.mem_image_of_mem _ hx)

variable [CompleteSpace E]

/-- On a fixed compact frequency set, the bounded synthesis operator varies
continuously in operator norm. The proof squeezes its squared difference by
the dominated-convergence squared-kernel integral
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem continuous_kernelSynthesis_compact {k : P → Euclidean d → E}
    (hk : Continuous k.uncurry) {S : Set (Euclidean d)} (hS : IsCompact S) :
    Continuous (fun p ↦ kernelSynthesis (memLp_restrict_compact_column
      (hk.comp (continuous_const.prodMk continuous_id)) hS (k := k p))) := by
  let hmem := fun p ↦ memLp_restrict_compact_column
    (hk.comp (continuous_const.prodMk continuous_id)) hS (k := k p)
  let T := fun p ↦ kernelSynthesis (hmem p)
  change Continuous T
  rw [continuous_iff_continuousAt]
  intro p
  have hc : Continuous (fun q ↦ ∫ x in S, ‖k q x - k p x‖ ^ 2) :=
    continuous_parametric_integral_of_continuous
      ((hk.sub (hk.comp (continuous_const.prodMk continuous_snd))).norm.pow 2) hS
  have hz : Filter.Tendsto (fun q ↦ ‖T q - T p‖ ^ 2) (𝓝 p) (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ sq_nonneg _) (fun q ↦
      norm_kernelSynthesis_sub_sq_le (hmem q) (hmem p))
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero]
      using hc.continuousAt.tendsto (x := p)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hz
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

end JanetCartan.SamplingKernelBounds
