module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingKernelBounds.Continuity
public import JanetCartan.Analysis.Microlocal.NormalComparison.LocalOperators.Construction

/-!
# Compact Euclidean kernels with spectator parameters

Continuity in operator norm for the literal restricted-input kernels used in
`app:ch_waves:eq:colored-normal-comparison`. The consumer is spectator
integrability of the colored and transport prefix normals. All continuity
inputs below concern the primitive kernel; operator continuity is deduced.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
open SamplingKernelBounds NormalComparison

variable {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
  [LocallyCompactSpace P] {d : ℕ}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {μ : Measure (Euclidean d)} [IsLocallyFiniteMeasure μ]

omit [FirstCountableTopology P] [LocallyCompactSpace P] [InnerProductSpace ℂ E]
  [CompleteSpace E] in
/-- Fixed compact input support gives L² columns for the original restricted
Lebesgue measure (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem memLp_supported_column {k : P → Euclidean d → E}
    (hk : Continuous k.uncurry) {S : Set (Euclidean d)} (hS : IsCompact S)
    (hs : ∀ p u, u ∉ S → k p u = 0) (p : P) : MemLp (k p) 2 μ :=
  (hk.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
    (HasCompactSupport.intro hS (hs p))

/-- Joint continuity and fixed compact support imply operator-norm continuity
of synthesis, without changing the input restriction
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem continuous_supported_synthesis {k : P → Euclidean d → E}
    (hk : Continuous k.uncurry) {S : Set (Euclidean d)} (hS : IsCompact S)
    (hs : ∀ p u, u ∉ S → k p u = 0) :
    Continuous (fun p ↦ kernelSynthesis (memLp_supported_column (μ := μ) hk hS hs p)) := by
  let hmem := memLp_supported_column (μ := μ) hk hS hs
  let T := fun p ↦ kernelSynthesis (hmem p)
  change Continuous T
  rw [continuous_iff_continuousAt]
  intro p
  have hc : Continuous (fun q ↦ ∫ u, ‖k q u - k p u‖ ^ 2 ∂μ) := by
    have he (q : P) : (∫ u, ‖k q u - k p u‖ ^ 2 ∂μ) =
        ∫ u in S, ‖k q u - k p u‖ ^ 2 ∂μ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun u hu ↦ by simp [hs _ u hu])).symm
    simp_rw [he]
    exact continuous_parametric_integral_of_continuous
      ((hk.sub (hk.comp (continuous_const.prodMk continuous_snd))).norm.pow 2) hS
  have hz : Tendsto (fun q ↦ ‖T q - T p‖ ^ 2) (𝓝 p) (𝓝 0) := by
    apply squeeze_zero (fun _ ↦ sq_nonneg _) (fun q ↦
      norm_kernelSynthesis_sub_sq_le (hmem q) (hmem p))
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero]
      using hc.continuousAt.tendsto (x := p)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hz
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

variable {e : ℕ}

/-- Parameter continuity for the existing scalar compact-kernel operator.
Both the physical Lebesgue measure and the original input restriction are
retained (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem continuous_compactKernelOperator_family
    (D : Set (Euclidean d)) (t : P → Euclidean e → Euclidean d → ℂ)
    (ht : Continuous (fun q : P × (Euclidean e × Euclidean d) ↦ t q.1 q.2.1 q.2.2))
    {X : Set (Euclidean e)} {U : Set (Euclidean d)}
    (hX : IsCompact X) (hU : IsCompact U)
    (hs : ∀ p x u, (x, u) ∉ X ×ˢ U → t p x u = 0) :
    Continuous (fun p ↦ compactKernelOperator (μ := volume.restrict D) (ν := volume) (t := t p)
      (ht.comp (continuous_const.prodMk continuous_id))
      (HasCompactSupport.intro (hX.prod hU) (fun z hz ↦ hs p z.1 z.2 hz))) := by
  let K : (P × Euclidean d) → Euclidean e → ℂ := fun q x ↦ t q.1 x q.2
  have hK : Continuous K.uncurry :=
    ht.comp (continuous_fst.fst.prodMk (continuous_snd.prodMk continuous_fst.snd))
  have hKs : ∀ q x, x ∉ X → K q x = 0 := fun q x hx ↦ hs q.1 x q.2 (fun h ↦ hx h.1)
  let k : P → Euclidean d → Lp ℂ 2 (volume : Measure (Euclidean e)) :=
    fun p u ↦ (memLp_compact_column hK hX hKs (p, u)).toLp (K (p, u))
  have hk : Continuous k.uncurry := continuous_compact_column hK hX hKs
  have hks : ∀ p u, u ∉ U → k p u = 0 := by
    intro p u hu
    apply Lp.ext
    filter_upwards [(memLp_compact_column hK hX hKs (p, u)).coeFn_toLp,
      Lp.coeFn_zero ℂ 2 (volume : Measure (Euclidean e))] with x hx hz
    exact hx.trans ((hs p x u (fun h ↦ hu h.2)).trans hz.symm)
  have he (p : P) : compactKernelOperator (μ := volume.restrict D) (ν := volume) (t := t p)
      (ht.comp (continuous_const.prodMk continuous_id))
      (HasCompactSupport.intro (hX.prod hU) (fun z hz ↦ hs p z.1 z.2 hz)) =
      kernelSynthesis (memLp_supported_column (μ := volume.restrict D) hk hU hks p) := by
    apply ContinuousLinearMap.adjoint.injective
    ext1 f
    apply Lp.ext
    filter_upwards [compactKernelOperator_adjoint_ae_integral (μ := volume.restrict D) (t := t p)
      (ht.comp (continuous_const.prodMk continuous_id))
      (HasCompactSupport.intro (hX.prod hU) (fun z hz ↦ hs p z.1 z.2 hz)) f,
      kernelSynthesis_hasAdjointKernel
        (memLp_supported_column (μ := volume.restrict D) hk hU hks p) f] with u hu hv
    rw [hu, hv, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_compact_column hK hX hKs (p, u)).coeFn_toLp] with x hx
    simp only [k, K, hx, RCLike.inner_apply, starRingEnd_apply]
    exact mul_comm _ _
  simp_rw [he]
  exact continuous_supported_synthesis hk hU hks

/-- Finite vector output retains operator-norm continuity from the same compact
primitive kernels (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem continuous_compactVectorKernelOperator_family {r : ℕ}
    (D : Set (Euclidean d)) (t : Fin r → P → Euclidean e → Euclidean d → ℂ)
    (ht : ∀ i, Continuous (fun q : P × (Euclidean e × Euclidean d) ↦
      t i q.1 q.2.1 q.2.2))
    {X : Set (Euclidean e)} {U : Set (Euclidean d)}
    (hX : IsCompact X) (hU : IsCompact U)
    (hs : ∀ i p x u, (x, u) ∉ X ×ˢ U → t i p x u = 0) :
    Continuous (fun p ↦ compactVectorKernelOperator D (t := fun i ↦ t i p)
      (fun i ↦ (ht i).comp (continuous_const.prodMk continuous_id))
      (fun i ↦ HasCompactSupport.intro (hX.prod hU)
        (fun z hz ↦ hs i p z.1 z.2 hz))) := by
  let A := fun p i ↦ compactKernelOperator (μ := volume.restrict D) (ν := volume)
    (t := t i p) ((ht i).comp (continuous_const.prodMk continuous_id))
    (HasCompactSupport.intro (hX.prod hU) (fun z hz ↦ hs i p z.1 z.2 hz))
  have hA (i : Fin r) : Continuous (fun p ↦ A p i) :=
    continuous_compactKernelOperator_family D (t i) (ht i) hX hU (hs i)
  have he (p : P) : ContinuousLinearMap.pi (A p) =
      ∑ i, (ContinuousLinearMap.single ℂ (fun _ : Fin r ↦
        Lp ℂ 2 (volume : Measure (Euclidean e))) i).comp (A p i) := by
    ext f j
    simp
  have hc : Continuous (fun p ↦ ContinuousLinearMap.pi (A p)) := by
    simp_rw [he]
    exact continuous_finsetSum _ (fun i _ ↦ continuous_const.clm_comp (hA i))
  exact continuous_const.clm_comp hc

end JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
