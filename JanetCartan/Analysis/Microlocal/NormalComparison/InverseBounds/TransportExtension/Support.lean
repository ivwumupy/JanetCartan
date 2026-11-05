module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportJets

/-!
# Support of the literal transport coefficients

The compact support assertion in `app:ch_osc:prop:osc-normal`, Step 2,
including the parameter derivative at both endpoints of the closed interval.
-/

@[expose] public noncomputable section

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison

variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

local instance transportSupportMatrixTopology (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- The full normal amplitude has both physical supports and the input support
of `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.normalAmplitude_eq_zero_off_support
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {q : Euclidean n × (Euclidean n × Euclidean n)}
    (hq : q ∉ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀)) :
    normalAmplitude (F.amplitude ε) q.1 q.2.1 q.2.2 = 0 := by
  have ha (x : Euclidean n) (hx : (x, q.2.2) ∉ G.X₀ ×ˢ G.D₀) :
      F.amplitude ε x q.2.2 = 0 := by
    by_contra h
    exact hx (F.amplitude_support ε hε h)
  by_cases hx : (q.1, q.2.2) ∈ G.X₀ ×ˢ G.D₀
  · have hy : (q.2.1, q.2.2) ∉ G.X₀ ×ˢ G.D₀ := fun hy ↦ hq ⟨hx.1, hy⟩
    ext i j
    simp [normalAmplitude, ha q.2.1 hy]
  · ext i j
    simp [normalAmplitude, ha q.1 hx]

/-- One-sided uniqueness on the nondegenerate parameter interval proves the
support of `∂ε A` even at its endpoints. No support condition beyond that interval
is used in `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.normalAmplitude_parameterDeriv_eq_zero_off_support
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    {q : Euclidean n × (Euclidean n × Euclidean n)}
    (hq : q ∉ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀)) :
    deriv (fun t ↦ normalAmplitude (F.amplitude t) q.1 q.2.1 q.2.2) ε = 0 := by
  have hd : HasDerivWithinAt
      (fun t ↦ normalAmplitude (F.amplitude t) q.1 q.2.1 q.2.2) 0 (Icc 0 G.ε₀) ε :=
    (hasDerivWithinAt_const ε (Icc 0 G.ε₀) (0 : Matrix (Fin r) (Fin r) ℂ)).congr
      (fun t ht ↦ F.normalAmplitude_eq_zero_off_support ht hq)
      (F.normalAmplitude_eq_zero_off_support hε hq)
  exact hd.deriv_eq_zero (uniqueDiffOn_Icc G.ε₀_pos ε hε)

/-- The flux vanishes on a full spatial neighborhood off the fixed compact
support. This is the support argument for its divergence in
`app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.normalTransportFlux_eventuallyEq_zero
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (j : Fin n) {q : Euclidean n × (Euclidean n × Euclidean n)}
    (hq : q ∉ G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀)) :
    (fun z : Euclidean n × (Euclidean n × Euclidean n) ↦
      F.normalTransportFlux ε j z.1 z.2.1 z.2.2) =ᶠ[𝓝 q] 0 := by
  have hclosed := G.compact_X₀.isClosed.prod (G.compact_X₀.isClosed.prod G.compact_D₀.isClosed)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hq] with z hz
  simp [normalTransportFlux, F.normalAmplitude_eq_zero_off_support hε hz]

/-- All literal coefficients, including the divergence term, have the compact
support claimed in `app:ch_osc:prop:osc-normal`, Step 2. -/
theorem UniformNormalData.normalTransportCoefficient_support
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀)
    (c : Option (Fin n)) :
    Function.support (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      F.normalTransportCoefficient ε c q.1 q.2.1 q.2.2) ⊆
        G.X₀ ×ˢ (G.X₀ ×ˢ G.D₀) := by
  intro q hq
  by_contra hz
  apply hq
  cases c with
  | some j =>
    change -(F.normalTransportFlux ε j q.1 q.2.1 q.2.2) = 0
    rw [(F.normalTransportFlux_eventuallyEq_zero hε j hz).eq_of_nhds]
    exact neg_zero
  | none =>
    have hd (j : Fin n) : partialDeriv (F.normalTransportFlux ε j q.1 q.2.1) q.2.2 j = 0 := by
      have heq := (F.normalTransportFlux_eventuallyEq_zero hε j hz).comp_tendsto
        (show Tendsto (fun u : Euclidean n ↦ (q.1, (q.2.1, u))) (𝓝 q.2.2) (𝓝 q) from
          (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousAt)
      change fderiv ℝ (F.normalTransportFlux ε j q.1 q.2.1) q.2.2
        (EuclideanSpace.single j 1) = 0
      change F.normalTransportFlux ε j q.1 q.2.1 =ᶠ[𝓝 q.2.2]
        (fun _ ↦ (0 : Matrix (Fin r) (Fin r) ℂ)) at heq
      rw [heq.fderiv_eq]
      simp
    change deriv (fun t ↦ normalAmplitude (F.amplitude t) q.1 q.2.1 q.2.2) ε -
      ∑ j, partialDeriv (F.normalTransportFlux ε j q.1 q.2.1) q.2.2 j = 0
    rw [F.normalAmplitude_parameterDeriv_eq_zero_off_support hε hz]
    simp [hd]

end JanetCartan.NormalComparison
