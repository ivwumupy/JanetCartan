module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.KernelContinuity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.Integrated

/-!
# Spectator continuity of the original normal family

For `app:ch_waves:eq:colored-normal-comparison`, joint continuity of the original
phase and amplitude on the buffered boxes gives operator continuity. The fixed
compact supports come from `UniformNormalData`. A literal continuous mask is
inserted into one forward kernel, so no continuity of chosen L∞ representatives
is an input. These results feed the spectator integrability required by
`exists_integrated_colored_prefix_transport_bound`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
open NormalComparison AmplitudeBound

variable {P : Type*} [TopologicalSpace P] {n r : ℕ}
  {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- Continuity of the original normalized kernel needs primitive continuity
only on the buffered boxes; outside its fixed compact carrier it is locally
zero (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem continuous_uniformKernel_family (F : P → UniformNormalData G C)
    (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (hp : ContinuousOn (fun q : P × (Euclidean n × Euclidean n) ↦
      (F q.1).phase ε q.2.1 q.2.2) (univ ×ˢ (G.X ×ˢ G.D)))
    (ha : ContinuousOn (fun q : P × (Euclidean n × Euclidean n) ↦
      (F q.1).amplitude ε q.2.1 q.2.2) (univ ×ˢ (G.X ×ˢ G.D))) (i : Fin r) :
    Continuous (fun q : P × (Euclidean n × Euclidean n) ↦
      normalizedOscillatoryKernel (normalOperatorScale n K) K ((F q.1).phase ε)
        (fun x u ↦ (F q.1).amplitude ε x u i) q.2.1 q.2.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  by_cases hq : q.2 ∈ G.X₀ ×ˢ G.D₀
  · have hn : univ ×ˢ (G.X ×ˢ G.D) ∈ 𝓝 q :=
      (isOpen_univ.prod (G.isOpen_X.prod G.isOpen_D)).mem_nhds
        ⟨mem_univ _, G.X₀_subset hq.1, G.D₀_subset hq.2⟩
    have hp' := hp.continuousAt hn
    have ha' := (continuous_apply i).continuousAt.comp (ha.continuousAt hn)
    unfold normalizedOscillatoryKernel oscillatoryFactor
    fun_prop
  · apply (continuousAt_const (y := (0 : ℂ))).congr_of_eventuallyEq
    have hev := ((G.compact_X₀.isClosed.prod G.compact_D₀.isClosed).isOpen_compl.mem_nhds hq)
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds hev] with w hw
    simp [normalizedOscillatoryKernel, (F w.1).amplitude_eq_zero_off_carrier hε hw]

variable [FirstCountableTopology P] [LocallyCompactSpace P]

/-- The actual normalized forward operator is continuous in a spectator
parameter, from primitive joint phase/amplitude continuity and its original
compact cutoffs (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem continuous_uniformOscillatoryOperator_family (F : P → UniformNormalData G C)
    (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (hp : ContinuousOn (fun q : P × (Euclidean n × Euclidean n) ↦
      (F q.1).phase ε q.2.1 q.2.2) (univ ×ˢ (G.X ×ˢ G.D)))
    (ha : ContinuousOn (fun q : P × (Euclidean n × Euclidean n) ↦
      (F q.1).amplitude ε q.2.1 q.2.2) (univ ×ˢ (G.X ×ˢ G.D))) :
    Continuous (fun p ↦ (F p).uniformOscillatoryOperator K ε) := by
  have ht := continuous_uniformKernel_family F K hε hp ha
  have hs (i : Fin r) (p : P) (x u : Euclidean n) (hz : (x, u) ∉ G.X₀ ×ˢ G.D₀) :
      normalizedOscillatoryKernel (normalOperatorScale n K) K ((F p).phase ε)
        (fun x u ↦ (F p).amplitude ε x u i) x u = 0 := by
    simp [normalizedOscillatoryKernel, (F p).amplitude_eq_zero_off_carrier hε hz]
  have hc := continuous_compactVectorKernelOperator_family G.D
    (fun i p ↦ normalizedOscillatoryKernel (normalOperatorScale n K) K ((F p).phase ε)
      (fun x u ↦ (F p).amplitude ε x u i)) ht G.compact_X₀ G.compact_D₀ hs
  simpa only [UniformNormalData.uniformOscillatoryOperator, dite_eq_left hε] using hc

/-- Continuity of the masked forward operator from its literal mask. The
chosen L∞ representative may be arbitrary, provided it is exactly this
mask almost everywhere (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem continuous_uniformOscillatoryOperator_mul_family
    (F : P → UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (hp : ContinuousOn (fun q : P × (Euclidean n × Euclidean n) ↦
      (F q.1).phase ε q.2.1 q.2.2) (univ ×ˢ (G.X ×ˢ G.D)))
    (ha : ContinuousOn (fun q : P × (Euclidean n × Euclidean n) ↦
      (F q.1).amplitude ε q.2.1 q.2.2) (univ ×ˢ (G.X ×ˢ G.D)))
    (m : P → Euclidean n → ℂ) (hm : Continuous m.uncurry)
    (g : P → Lp ℂ ∞ (volume.restrict G.D)) (hg : ∀ p, g p =ᵐ[volume.restrict G.D] m p) :
    Continuous (fun p ↦ (F p).uniformOscillatoryOperator K ε ∘L multiplicationOperator (g p)) := by
  let t := fun i p x u ↦ normalizedOscillatoryKernel (normalOperatorScale n K) K
    ((F p).phase ε) (fun x u ↦ (F p).amplitude ε x u i) x u * m p u
  have ht (i : Fin r) : Continuous (fun q : P × (Euclidean n × Euclidean n) ↦
      t i q.1 q.2.1 q.2.2) :=
    (continuous_uniformKernel_family F K hε hp ha i).mul
      (hm.comp (continuous_fst.prodMk continuous_snd.snd))
  have hs (i : Fin r) (p : P) (x u : Euclidean n) (hz : (x, u) ∉ G.X₀ ×ˢ G.D₀) :
      t i p x u = 0 := by
    simp [t, normalizedOscillatoryKernel, (F p).amplitude_eq_zero_off_carrier hε hz]
  have he (p : P) : (F p).uniformOscillatoryOperator K ε ∘L multiplicationOperator (g p) =
      compactVectorKernelOperator G.D (t := fun i ↦ t i p)
        (fun i ↦ (ht i).comp (continuous_const.prodMk continuous_id))
        (fun i ↦ HasCompactSupport.intro (G.compact_X₀.prod G.compact_D₀)
          (fun z hz ↦ hs i p z.1 z.2 hz)) := by
    ext f i
    filter_upwards [(F p).uniformOscillatoryOperator_ae_integral K hε
      (multiplicationOperator (g p) f) i,
      compactVectorKernelOperator_ae_integral G.D (t := fun i ↦ t i p)
        (fun i ↦ (ht i).comp (continuous_const.prodMk continuous_id))
        (fun i ↦ HasCompactSupport.intro (G.compact_X₀.prod G.compact_D₀)
          (fun z hz ↦ hs i p z.1 z.2 hz)) f i] with x hx hy
    rw [ContinuousLinearMap.comp_apply, hx, hy]
    apply integral_congr_ae
    filter_upwards [multiplicationOperator_coeFn (g p) f, hg p] with u hu hgu
    simp only [hu, hgu, t, normalizedOscillatoryKernel]
    ring
  simp_rw [he]
  exact continuous_compactVectorKernelOperator_family G.D t ht G.compact_X₀ G.compact_D₀ hs

/-- Spectator continuity of the actual masked normal follows from two
forward kernels and the Hilbert adjoint, retaining both physical positions
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem continuous_uniformOscillatoryNormalOperator_family
    (F : P → UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (hp : ContinuousOn (fun q : P × (Euclidean n × Euclidean n) ↦
      (F q.1).phase ε q.2.1 q.2.2) (univ ×ˢ (G.X ×ˢ G.D)))
    (ha : ContinuousOn (fun q : P × (Euclidean n × Euclidean n) ↦
      (F q.1).amplitude ε q.2.1 q.2.2) (univ ×ˢ (G.X ×ˢ G.D)))
    (m : P → Euclidean n → ℂ) (hm : Continuous m.uncurry)
    (g : P → Lp ℂ ∞ (volume.restrict G.D)) (hg : ∀ p, g p =ᵐ[volume.restrict G.D] m p) :
    Continuous (fun p ↦ (F p).uniformOscillatoryNormalOperator K (g p) ε) := by
  simpa only [ContinuousLinearMap.comp_assoc, UniformNormalData.uniformOscillatoryNormalOperator,
    Function.comp_def]
    using (continuous_uniformOscillatoryOperator_mul_family F K hε hp ha m hm g hg).clm_comp
      (ContinuousLinearMap.adjoint.continuous.comp
        (continuous_uniformOscillatoryOperator_family F K hε hp ha))

end JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
