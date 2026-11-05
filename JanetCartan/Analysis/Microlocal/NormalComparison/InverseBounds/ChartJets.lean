module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.Regularity
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InputJacobian
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.InverseJetInduction

/-!
# Normal inverse chart regularity and quantitative jets

Prerequisites for `app:ch_osc:setup:osc-normal` and
`app:ch_osc:prop:osc-normal` in `paper.tex`. Local implicit functions identify
smooth extensions of the actual inverse on the admissible interval. The
inverse chart and inverse input Jacobian have finite spatial jet bounds with
constants chosen before the phase family, using only forward jets and the
determinant gap. The forward-jet premise is supplied by `InputJets` in the
downstream normal-amplitude and transport-coefficient assembly.
-/

@[expose] public noncomputable section

open Set

namespace JanetCartan.NormalComparison

variable {n r : ℕ}

/-- Uniform spatial jets of the actual inverse chart from forward jets
through one additional order (`app:ch_osc:prop:osc-normal`, Step 1).
The constant depends only on the fixed geometry, order and forward bound,
and is quantified before the family. The inverse differential estimate is
derived from the determinant gap; no inverse-jet premise remains. -/
theorem UniformNormalGeometry.exists_inverseChart_jet_bound
    (G : UniformNormalGeometry n r) (N : ℕ) (B : ℝ) :
    ∃ K > 0, ∀ {C : ℕ → ℝ} (F : UniformNormalData G C),
      (∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N + 1,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          averagedGradient (F.phase ε) q.1 q.2.1 q.2.2) z‖ ≤ B) →
      ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.V), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.inverseChart ε q.1 q.2.1 q.2.2) z‖ ≤ K := by
  obtain ⟨J, _hJ, hJacobian⟩ := G.exists_inverseInputJacobian_jet_bound N B
  obtain ⟨K, hK, hChart⟩ :=
    G.exists_inverseChart_jet_bound_of_inverseInputJacobian N B J
  exact ⟨K, hK, fun F hForward ↦ hChart F hForward (hJacobian F hForward)⟩

/-- The inverse-chart jet order used for the normal amplitude in
`app:ch_osc:prop:osc-normal`, Step 1. The parent amplitude construction
supplies forward jets through `2 * (n + 1) + 3` from the input phase bounds. -/
theorem UniformNormalGeometry.exists_inverseChart_amplitude_jet_bound
    (G : UniformNormalGeometry n r) (B : ℝ) :
    ∃ K > 0, ∀ {C : ℕ → ℝ} (F : UniformNormalData G C),
      (∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ 2 * (n + 1) + 3,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          averagedGradient (F.phase ε) q.1 q.2.1 q.2.2) z‖ ≤ B) →
      ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.V), ∀ k ≤ 2 * (n + 1) + 2,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.inverseChart ε q.1 q.2.1 q.2.2) z‖ ≤ K :=
  G.exists_inverseChart_jet_bound (2 * (n + 1) + 2) B

end JanetCartan.NormalComparison
