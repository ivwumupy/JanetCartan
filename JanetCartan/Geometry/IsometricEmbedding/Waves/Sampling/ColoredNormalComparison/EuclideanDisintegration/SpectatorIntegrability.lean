module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.ColoredNormalComparison.EuclideanDisintegration.SpectatorContinuity

/-!
# The fixed compact spectator integral

These deductions discharge the two Bochner integrability premises of
`exists_integrated_colored_prefix_transport_bound` from primitive joint
continuity on the original spectator and buffered physical/input boxes.
The color masks are the literal convolved-box masks at `z₀(v) + Z u`.
No operator continuity, normal estimate, or integrability is assumed.
The actual phase/amplitude families remain inputs of the wave producers.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal ContDiff

namespace JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
open NormalComparison RawInputPartition SeparatedSampling LatticeQuadrature BackgroundQuadrature

variable {n r d : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

private theorem continuousOn_restrict_spectator {E : Type*} [TopologicalSpace E]
    {V : Set (Euclidean d)} {U : Set (Euclidean n × Euclidean n)}
    {f : Euclidean d × (Euclidean n × Euclidean n) → E}
    (hf : ContinuousOn f (V ×ˢ U)) :
    ContinuousOn (fun q : V × (Euclidean n × Euclidean n) ↦ f (q.1.val, q.2))
      (univ ×ˢ U) :=
  hf.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
    (fun q hq ↦ ⟨q.1.property, hq.2⟩)

/-- Single-band spectator integrability for the exact masked normal. This
local form only asks for primitive continuity on the fixed compact spectator
set and the original buffered boxes
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem integrable_uniformOscillatoryNormalOperator
    {V : Set (Euclidean d)} (hV : IsCompact V)
    (F : Euclidean d → UniformNormalData G C) (K : ℝ)
    {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (hp : ContinuousOn (fun q : Euclidean d × (Euclidean n × Euclidean n) ↦
      (F q.1).phase ε q.2.1 q.2.2) (V ×ˢ (G.X ×ˢ G.D)))
    (ha : ContinuousOn (fun q : Euclidean d × (Euclidean n × Euclidean n) ↦
      (F q.1).amplitude ε q.2.1 q.2.2) (V ×ˢ (G.X ×ˢ G.D)))
    (m : Euclidean d → Euclidean n → ℂ)
    (hm : ContinuousOn m.uncurry (V ×ˢ univ))
    (g : Euclidean d → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ v ∈ V, g v =ᵐ[volume.restrict G.D] m v) :
    Integrable (fun v ↦ (F v).uniformOscillatoryNormalOperator K (g v) ε)
      (volume.restrict V) := by
  let : LocallyCompactSpace V := hV.isClosed.locallyCompactSpace
  have hm' : Continuous (fun q : V × Euclidean n ↦ m q.1.val q.2) := by
    rw [← continuousOn_univ]
    exact hm.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun q _ ↦ ⟨q.1.property, mem_univ _⟩)
  apply ContinuousOn.integrableOn_compact hV
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_uniformOscillatoryNormalOperator_family (fun v : V ↦ F v) K hε
    (continuousOn_restrict_spectator hp) (continuousOn_restrict_spectator ha)
    (fun v : V ↦ m v) hm' (fun v : V ↦ g v) (fun v ↦ hg v v.property)

/-- Single-band integrability of the uncolored transport normal on literal
Euclidean output, before finite-prefix summation
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem integrable_uniformTransportNormal
    {V : Set (Euclidean d)} (hV : IsCompact V)
    (F : Euclidean d → UniformNormalData G C) (K : ℝ)
    (hp : ContinuousOn (fun q : Euclidean d × (Euclidean n × Euclidean n) ↦
      (F q.1).phase 0 q.2.1 q.2.2) (V ×ˢ (G.X ×ˢ G.D)))
    (ha : ContinuousOn (fun q : Euclidean d × (Euclidean n × Euclidean n) ↦
      (F q.1).amplitude 0 q.2.1 q.2.2) (V ×ˢ (G.X ×ˢ G.D))) :
    Integrable (fun v ↦ (F v).uniformOscillatoryOperator K 0 ∘L
      ((F v).uniformOscillatoryOperator K 0).adjoint) (volume.restrict V) := by
  let : LocallyCompactSpace V := hV.isClosed.locallyCompactSpace
  apply ContinuousOn.integrableOn_compact hV
  rw [continuousOn_iff_continuous_domRestrict]
  have hc := continuous_uniformOscillatoryOperator_family (fun v : V ↦ F v) K
    (show (0 : ℝ) ∈ Icc 0 G.ε₀ from ⟨le_rfl, G.ε₀_pos.le⟩)
    (continuousOn_restrict_spectator hp) (continuousOn_restrict_spectator ha)
  exact hc.clm_comp (ContinuousLinearMap.adjoint.continuous.comp hc)

/-- The literal colored prefix is Bochner integrable over the fixed compact
spectator domain. This supplies the first integrability premise of
`exists_integrated_colored_prefix_transport_bound`. Only the original phase
and amplitude need joint continuity; arbitrary exact L∞ realizations of the
actual finite masks give the same result
(`app:ch_waves:eq:colored-normal-comparison`). -/
theorem integrable_coloredPrefixNormal
    {V : Set (Euclidean d)} (hV : IsCompact V)
    {κ : ℝ → ℝ} (hc : HasCompactSupport κ) (hs : ContDiff ℝ ∞ κ)
    (p : ℕ) (B h : ℝ) (z₀ : Euclidean d → Point) (hz₀ : ContinuousOn z₀ V)
    (Z : Euclidean n →L[ℝ] Point)
    (F : Euclidean d → (Fin 3 → Fin (p + 1)) → ℕ → UniformNormalData G C)
    (R : (Fin 3 → Fin (p + 1)) → ℝ) (lam : ℝ) (J : ℕ)
    (hε : ∀ c j, j ∈ Finset.range J → (R c * lam)⁻¹ * dyadicScale j ∈ Icc 0 G.ε₀)
    (hp : ∀ c j, j ∈ Finset.range J →
      ContinuousOn (fun q : Euclidean d × (Euclidean n × Euclidean n) ↦
        (F q.1 c j).phase ((R c * lam)⁻¹ * dyadicScale j) q.2.1 q.2.2)
        (V ×ˢ (G.X ×ˢ G.D)))
    (ha : ∀ c j, j ∈ Finset.range J →
      ContinuousOn (fun q : Euclidean d × (Euclidean n × Euclidean n) ↦
        (F q.1 c j).amplitude ((R c * lam)⁻¹ * dyadicScale j) q.2.1 q.2.2)
        (V ×ˢ (G.X ×ˢ G.D)))
    (g : Euclidean d → (Fin 3 → Fin (p + 1)) → Lp ℂ ∞ (volume.restrict G.D))
    (hg : ∀ v ∈ V, ∀ c, g v c =ᵐ[volume.restrict G.D] fun u ↦
      (coloredBlockMask p (integerCube (blockCutoff p B h)) (convolvedBoxWindow κ p)
        h c (z₀ v + Z u) : ℂ)) :
    Integrable (fun v ↦ coloredPrefixNormal (F v) R (g v) lam J) (volume.restrict V) := by
  unfold coloredPrefixNormal
  refine integrable_finsetSum (μ := volume.restrict V)
    (f := fun c v ↦ ∑ j ∈ Finset.range J,
      (F v c j).uniformOscillatoryNormalOperator (dyadicScale j) (g v c)
        ((R c * lam)⁻¹ * dyadicScale j)) Finset.univ (fun c _ ↦ ?_)
  refine integrable_finsetSum (μ := volume.restrict V)
    (f := fun j v ↦ (F v c j).uniformOscillatoryNormalOperator (dyadicScale j) (g v c)
      ((R c * lam)⁻¹ * dyadicScale j)) (Finset.range J) (fun j hj ↦ ?_)
  apply integrable_uniformOscillatoryNormalOperator hV (fun v ↦ F v c j)
    (dyadicScale j) (hε c j hj) (hp c j hj) (ha c j hj)
    (fun v u ↦ (coloredBlockMask p (integerCube (blockCutoff p B h))
      (convolvedBoxWindow κ p) h c (z₀ v + Z u) : ℂ)) ?_ (fun v ↦ g v c)
    (fun v hv ↦ hg v hv c)
  exact Complex.continuous_ofReal.continuousOn.comp
    ((contDiff_coloredBlockMask hc hs p _ h c).continuous.continuousOn.comp
      ((hz₀.comp continuous_fst.continuousOn (fun _ hq ↦ hq.1)).add
        (Z.continuous.comp continuous_snd).continuousOn) (fun _ _ ↦ mem_univ _))
    (fun _ _ ↦ mem_univ _)

/-- The transport prefix has its actual compact-spectator Bochner integral.
This discharges the second integrability premise of
`exists_integrated_colored_prefix_transport_bound`, without assuming an
operator bound or continuity (`app:ch_waves:eq:colored-normal-comparison`). -/
theorem integrable_transportPrefixNormal
    {V : Set (Euclidean d)} (hV : IsCompact V)
    (F₀ : Euclidean d → ℕ → UniformNormalData G C) (J : ℕ)
    (hp : ∀ j, j ∈ Finset.range J →
      ContinuousOn (fun q : Euclidean d × (Euclidean n × Euclidean n) ↦
        (F₀ q.1 j).phase 0 q.2.1 q.2.2) (V ×ˢ (G.X ×ˢ G.D)))
    (ha : ∀ j, j ∈ Finset.range J →
      ContinuousOn (fun q : Euclidean d × (Euclidean n × Euclidean n) ↦
        (F₀ q.1 j).amplitude 0 q.2.1 q.2.2) (V ×ˢ (G.X ×ˢ G.D))) :
    Integrable (fun v ↦ transportPrefixNormal (F₀ v) J) (volume.restrict V) := by
  unfold transportPrefixNormal
  refine integrable_finsetSum (μ := volume.restrict V)
    (f := fun j v ↦ (F₀ v j).uniformOscillatoryOperator (dyadicScale j) 0 ∘L
      ((F₀ v j).uniformOscillatoryOperator (dyadicScale j) 0).adjoint)
    (Finset.range J) (fun j hj ↦ ?_)
  exact integrable_uniformTransportNormal hV (fun v ↦ F₀ v j) (dyadicScale j)
    (hp j hj) (ha j hj)

end JanetCartan.Sampling.ColoredNormalComparison.EuclideanDisintegration
