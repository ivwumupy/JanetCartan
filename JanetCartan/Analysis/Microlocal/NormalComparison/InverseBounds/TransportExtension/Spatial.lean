module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.Support

/-!
# Buffered spatial zero extension

The global smooth transport amplitudes of `app:ch_osc:prop:osc-normal`, Step 2.
Their full spatial jet constants are chosen before the input family.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

local instance transportSpatialMatrixTopology (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Actual zero extension from the buffered original boxes, for the matrix
transport channels of `app:ch_osc:prop:osc-normal`. -/
def UniformNormalData.extendedTransportCoefficient (F : UniformNormalData G C)
    (ε : ℝ) (c : Option (Fin n))
    (q : Euclidean n × (Euclidean n × Euclidean n)) : Matrix (Fin r) (Fin r) ℂ :=
  (G.X ×ˢ (G.X ×ˢ G.D)).indicator
    (fun z ↦ F.normalTransportCoefficient ε c z.1 z.2.1 z.2.2) q

/-- The zero extension agrees with the original coefficient on its original
boxes (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.extendedTransportCoefficient_eq_on
    (F : UniformNormalData G C) (ε : ℝ) (c : Option (Fin n))
    {q : Euclidean n × (Euclidean n × Euclidean n)}
    (hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D)) :
    F.extendedTransportCoefficient ε c q =
      F.normalTransportCoefficient ε c q.1 q.2.1 q.2.2 :=
  indicator_of_mem hq _

/-- At admissible parameters the literal totalized coefficient already vanishes
outside the boxes. Thus its buffered extension agrees everywhere, a useful
identity for `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.extendedTransportCoefficient_eq
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (c : Option (Fin n)) :
    F.extendedTransportCoefficient ε c =
      fun q ↦ F.normalTransportCoefficient ε c q.1 q.2.1 q.2.2 := by
  apply Set.indicator_eq_self.mpr
  exact (F.normalTransportCoefficient_support hε c).trans
    (Set.prod_mono G.X₀_subset (Set.prod_mono G.X₀_subset G.D₀_subset))

/-- Compact support of the actual buffered extension in
`app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.extendedTransportCoefficient_support
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (c : Option (Fin n)) :
    Function.support (F.extendedTransportCoefficient ε c) ⊆
      G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀) := by
  rw [F.extendedTransportCoefficient_eq hε]
  exact F.normalTransportCoefficient_support hε c

/-- Off the compact support, the extension is identically zero on a spatial
neighborhood; this discharges smoothness across the box boundaries in
`app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.extendedTransportCoefficient_eventuallyEq_zero
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (c : Option (Fin n)) {q : Euclidean n × (Euclidean n × Euclidean n)}
    (hq : q ∉ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀)) :
    F.extendedTransportCoefficient ε c =ᶠ[𝓝 q] 0 := by
  have hclosed := G.compact_X₀.isClosed.prod (G.compact_X₀.isClosed.prod G.compact_D₀.isClosed)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hq] with z hz
  by_contra h
  exact hz (F.extendedTransportCoefficient_support hε c h)

/-- Global spatial smoothness of the buffered extension in
`app:ch_osc:prop:osc-normal`, without a hypothesis on coefficient regularity. -/
theorem UniformNormalData.extendedTransportCoefficient_contDiff
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (c : Option (Fin n)) : ContDiff ℝ ∞ (F.extendedTransportCoefficient ε c) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  by_cases hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D)
  · rw [F.extendedTransportCoefficient_eq hε]
    exact (F.normalTransportCoefficient_contDiffAt c (q := (ε, q)) ⟨hε, hq⟩).comp q
      (contDiffAt_const.prodMk contDiffAt_id)
  · have hk : q ∉ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀) :=
      fun hk ↦ hq ⟨G.X₀_subset hk.1, G.X₀_subset hk.2.1, G.D₀_subset hk.2.2⟩
    exact contDiffAt_const.congr_of_eventuallyEq
      (F.extendedTransportCoefficient_eventuallyEq_zero hε c hk)

/-- Joint measurability in all three spatial variables, as required by the
matrix channel estimate of `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.extendedTransportCoefficient_stronglyMeasurable
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (c : Option (Fin n)) : StronglyMeasurable (F.extendedTransportCoefficient ε c) :=
  (F.extendedTransportCoefficient_contDiff hε c).continuous.stronglyMeasurable

/-- Global full spatial Frobenius jets of the actual extension. The constant
is fixed using only `G,C` before choosing the family, as required in
`app:ch_osc:prop:osc-normal`, Step 2. -/
theorem UniformNormalGeometry.exists_extendedTransportCoefficient_jet_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (N : ℕ)
    (hN : N + 3 ≤ 20 * (n + 1)) :
    ∃ K > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀, ∀ c : Option (Fin n), ∀ q, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (F.extendedTransportCoefficient ε c) q‖ ≤ K := by
  obtain ⟨K, hK, hb⟩ := G.exists_normalTransportCoefficient_jet_bound C N hN
  refine ⟨K, hK, ?_⟩
  intro F ε hε c q k hk
  by_cases hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D)
  · rw [F.extendedTransportCoefficient_eq hε]
    exact hb F ε hε c q hq k hk
  · have hs : q ∉ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀) :=
      fun hs ↦ hq ⟨G.X₀_subset hs.1, G.X₀_subset hs.2.1, G.D₀_subset hs.2.2⟩
    rw [((F.extendedTransportCoefficient_eventuallyEq_zero hε c hs).iteratedFDeriv ℝ k).eq_of_nhds]
    simpa using hK.le

end JanetCartan.NormalComparison
