module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.KernelContinuity
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.KernelNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.OutputTransfer

/-!
# Literal Euclidean columns of the normalized oscillatory operator

The bridge from the original forward kernel to `kernelSynthesis`, retaining
`normalOperatorScale`, the input restriction, all compact cutoffs, and the
full Euclidean output in `app:ch_osc:eq:osc-exact-normal-kernel`.
The consumer is the common-kernel single-band disintegration.
-/

@[expose] public noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
open NormalComparison SamplingKernelBounds

variable {d e r : ℕ}
  (t : Fin r → Euclidean e → Euclidean d → ℂ)
  (ht : ∀ i, Continuous (Function.uncurry (t i)))
  {X : Set (Euclidean e)} {U : Set (Euclidean d)}
  (hX : IsCompact X) (hU : IsCompact U)
  (hs : ∀ i x u, (x, u) ∉ X ×ˢ U → t i x u = 0)

/-- The original physical column in finite L² coordinates; the underlying
physical measure is Euclidean volume (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
def compactCoordinateColumn (u : Euclidean d) : NormalOutputL2 e r :=
  WithLp.toLp 2 (fun i ↦ (memLp_compact_column (K := fun u x ↦ t i x u)
    ((ht i).comp continuous_swap) hX
    (fun u x hx ↦ hs i x u (fun h ↦ hx h.1)) u).toLp (fun x ↦ t i x u))

/-- Each coordinate retains its literal original kernel representative
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem compactCoordinateColumn_coe (u : Euclidean d) (i : Fin r) :
    (compactCoordinateColumn t ht hX hs u) i =ᵐ[volume] fun x ↦ t i x u :=
  (memLp_compact_column (K := fun u x ↦ t i x u)
    ((ht i).comp continuous_swap) hX
    (fun u x hx ↦ hs i x u (fun h ↦ hx h.1)) u).coeFn_toLp

/-- The columns are continuous in input coordinates by the original compact
physical cutoff (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem continuous_compactCoordinateColumn : Continuous (compactCoordinateColumn t ht hX hs) :=
  (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i ↦
    continuous_compact_column (K := fun u x ↦ t i x u) ((ht i).comp continuous_swap) hX
      (fun u x hx ↦ hs i x u (fun h ↦ hx h.1))))

/-- Compact input support is inherited without extending its restriction
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem compactCoordinateColumn_eq_zero (u : Euclidean d) (hu : u ∉ U) :
    compactCoordinateColumn t ht hX hs u = 0 := by
  ext i

  filter_upwards [compactCoordinateColumn_coe t ht hX hs u i,
    Lp.coeFn_zero ℂ 2 (volume : Measure (Euclidean e))] with x hx hz
  exact hx.trans ((hs i x u (fun h ↦ hu h.2)).trans hz.symm)

include hU in
/-- The original compact cutoffs supply L² integrability of the columns in
any retained input restriction (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem memLp_compactCoordinateColumn (D : Set (Euclidean d)) :
    MemLp (compactCoordinateColumn t ht hX hs) 2 (volume.restrict D) :=
  (continuous_compactCoordinateColumn t ht hX hs).memLp_of_hasCompactSupport
    (HasCompactSupport.intro hU (compactCoordinateColumn_eq_zero t ht hX hs))

/-- The existing normalized-operator construction is synthesis with its
literal Euclidean columns. Its original adjoint formula proves the equality;
no equality of normal operators is assumed
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem compactVectorKernelOperator_eq_synthesis (D : Set (Euclidean d)) :
    compactVectorKernelOperator D ht
      (fun i ↦ HasCompactSupport.intro (hX.prod hU) (fun z hz ↦ hs i z.1 z.2 hz)) =
      kernelSynthesis (memLp_compactCoordinateColumn t ht hX hU hs D) := by
  apply ContinuousLinearMap.adjoint.injective
  ext1 f
  apply Lp.ext
  filter_upwards [compactVectorKernelOperator_adjoint_ae_integral D ht
    (fun i ↦ HasCompactSupport.intro (hX.prod hU) (fun z hz ↦ hs i z.1 z.2 hz)) f,
    kernelSynthesis_hasAdjointKernel (memLp_compactCoordinateColumn t ht hX hU hs D) f]
    with u hu hv
  rw [hu, hv, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [compactCoordinateColumn_coe t ht hX hs u i] with x hx
  simp only [hx, RCLike.inner_apply, starRingEnd_apply]
  exact mul_comm _ _

variable {n : ℕ} {G : UniformNormalGeometry n n} {C : ℕ → ℝ}

/-- Literal normalized columns of the original single smooth band. Its input
scale is exactly `normalOperatorScale n K`, as in the manuscript
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
def uniformCoordinateColumn (F : UniformNormalData G C) (K : ℝ)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) : Euclidean n → NormalOutputL2 n n :=
  compactCoordinateColumn (U := G.D₀)
    (fun i ↦ normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε)
      (fun x u ↦ F.amplitude ε x u i))
    (fun i ↦ (F.normalizedKernel_contDiff hε (normalOperatorScale n K) K i).continuous)
    G.compact_X₀ (fun i x u hu ↦ by
      simp [normalizedOscillatoryKernel, F.amplitude_eq_zero_off_carrier hε hu])

/-- Pointwise physical kernel of the exact normalized columns
(`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem uniformCoordinateColumn_coe (F : UniformNormalData G C) (K : ℝ)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) (u : Euclidean n) (i : Fin n) :
    (uniformCoordinateColumn F K hε u) i =ᵐ[volume] fun x ↦
      normalizedOscillatoryKernel (normalOperatorScale n K) K (F.phase ε)
        (fun x u ↦ F.amplitude ε x u i) x u :=
  compactCoordinateColumn_coe _ _ _ _ u i

/-- Square integrability follows from the fixed cutoffs in `UniformNormalData`
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem memLp_uniformCoordinateColumn (F : UniformNormalData G C) (K : ℝ)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    MemLp (uniformCoordinateColumn F K hε) 2 (volume.restrict G.D) :=
  memLp_compactCoordinateColumn _ _ G.compact_X₀ G.compact_D₀ _ G.D

/-- The original normalized forward operator equals synthesis with the same
columns and input restriction (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem uniformOscillatoryOperator_eq_synthesis (F : UniformNormalData G C) (K : ℝ)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    F.uniformOscillatoryOperator K ε = kernelSynthesis (memLp_uniformCoordinateColumn F K hε) := by
  rw [F.uniformOscillatoryOperator_of_mem K hε]
  exact compactVectorKernelOperator_eq_synthesis _ _ G.compact_X₀ G.compact_D₀ _ G.D

/-- Full operator-valued integral of the exact normalized colored normal.
The mask is the original L∞ representative, and both physical positions
remain in the same Euclidean column (`app:ch_osc:eq:osc-exact-normal-kernel`). -/
theorem uniformOscillatoryNormalOperator_eq_integral_columns
    (F : UniformNormalData G C) (K : ℝ) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (g : Lp ℂ ∞ (volume.restrict G.D)) :
    F.uniformOscillatoryNormalOperator K g ε = ∫ u in G.D,
      g u • InnerProductSpace.rankOne ℂ (uniformCoordinateColumn F K hε u)
        (uniformCoordinateColumn F K hε u) := by
  rw [UniformNormalData.uniformOscillatoryNormalOperator,
    uniformOscillatoryOperator_eq_synthesis F K hε]
  exact kernelSynthesis_maskedNormal_eq_integral _ g

end JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
