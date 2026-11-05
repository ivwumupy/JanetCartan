module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.Regularity
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InputJacobian
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InverseJetInduction.Bounds
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InverseJetInduction.Differential

/-!
# Uniform finite jets of the actual inverse chart

Conditional implicit differentiation for `app:ch_osc:setup:osc-normal` and
Step 1 of `app:ch_osc:prop:osc-normal`. Forward jets and inverse input Jacobian
jets control every finite spatial inverse jet. The bound is selected before
the phase family, with no compactness assertion about that family.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff
namespace JanetCartan.NormalComparison
open InverseChartJet
variable {n r : ℕ}

set_option maxHeartbeats 800000 in
/-- Uniform spatial inverse jets from forward jets and inverse input Jacobian
jets (`app:ch_osc:prop:osc-normal`, Step 1). The constant depends only on the
fixed geometry, order and two supplied bounds, and precedes `C` and `F`.
The inverse-Jacobian premise can be discharged separately using
`exists_inverseInputJacobian_jet_bound`. -/
theorem UniformNormalGeometry.exists_inverseChart_jet_bound_of_inverseInputJacobian
    (G : UniformNormalGeometry n r) (N : ℕ) (B J : ℝ) :
    ∃ K > 0, ∀ {C : ℕ → ℝ} (F : UniformNormalData G C),
      (∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N + 1,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          averagedGradient (F.phase ε) q.1 q.2.1 q.2.2) z‖ ≤ B) →
      (∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          (fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).inverse) z‖ ≤ J) →
      ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.V), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.inverseChart ε q.1 q.2.1 q.2.2) z‖ ≤ K := by
  let E := Euclidean n
  let S := E × (E × E)
  let U := G.X ×ˢ (G.X ×ˢ G.V)
  let W := G.X ×ˢ (G.X ×ˢ G.D)
  let Q := chartBaseMap E
  let L := chartInputMap E
  let P := chartOutputMap E
  let M := (2 : ℝ)^N * max 0 J * (‖P‖ + ‖Q‖ * max 0 B)
  obtain ⟨A, _hA, hA⟩ := G.exists_inverseChart_norm_bound
  obtain ⟨K, hK, hbound⟩ := exists_jet_bound_of_fderiv_eq_comp Q L N A M
  refine ⟨K, hK, ?_⟩
  intro C F hfjet hajet ε hε
  let g : S → E := fun q ↦ F.inverseChart ε q.1 q.2.1 q.2.2
  let f : S → E := fun q ↦ averagedGradient (F.phase ε) q.1 q.2.1 q.2.2
  let a : S → E →L[ℝ] E := fun q ↦
    (fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).inverse
  let H : S → S →L[ℝ] E := fun q ↦ a q ∘L (P - fderiv ℝ f q ∘L Q)
  have hU : IsOpen U := G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_V)
  have hW : IsOpen W := G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)
  have hf : ContDiffOn ℝ ∞ f W := F.averagedGradient_spatial_contDiffOn (F.parameter_subset hε)
  have ha : ContDiffOn ℝ ∞ a W := F.inverseInputJacobian_contDiffOn.comp
    (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz ↦ ⟨hε, hz⟩)
  have hH : ContDiffOn ℝ ∞ H W := ha.clm_comp
    (contDiffOn_const.sub ((hf.fderiv_of_isOpen hW (m := ∞) (by simp)).clm_comp contDiffOn_const))
  have hgraph (z : S) : Q z + L (g z) = (z.1, (z.2.1, g z)) := by
    simp [Q, L, chartBaseMap, chartInputMap]
  apply hbound g H U W hU hW (F.inverseChart_spatial_contDiffOn hε) hH
  · intro z hz
    change Q z + L (g z) ∈ W
    rw [hgraph]
    exact ⟨hz.1, hz.2.1, F.inverseChart_mem hε hz.1 hz.2.1 hz.2.2⟩
  · intro z hz
    rw [hgraph]
    exact F.inverseChart_fderiv_eq hε hz
  · intro z hz
    exact hA F ε hε z.1 hz.1 z.2.1 hz.2.1 z.2.2 hz.2.2
  · intro z hz k hk
    exact norm_iteratedFDeriv_implicitCoefficient_le P Q hW hf ha
      (hfjet ε hε) (hajet ε hε) hz hk

end JanetCartan.NormalComparison
