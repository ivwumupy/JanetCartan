module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InputJets
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets

/-!
# Inverse and velocity bounds from the original input jets

This discharges the forward-jet premises in `ChartJets` using the original
input data of `app:ch_osc:setup:osc-normal`. Constants precede the family;
no inverse bounds or transport bounds are assumed.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000

open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- A single bound for the finite forward jets needed in
`app:ch_osc:prop:osc-normal`, depending only on the given input sequence. -/
def normalForwardJetBound (C : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), averagedGradientJetBound C k

/-- Each forward jet is bounded by the fixed finite sum used by the inverse
estimates in `app:ch_osc:prop:osc-normal`. -/
theorem averagedGradientJetBound_le_normalForwardJetBound {k N : ℕ} (hk : k ≤ N) :
    averagedGradientJetBound C k ≤ normalForwardJetBound C N :=
  Finset.single_le_sum (fun i _ ↦ averagedGradientJetBound_nonneg C i)
    (Finset.mem_range.mpr (by omega))

/-- The input-only setup implies uniform inverse-chart jets, with all
forward-jet premises discharged (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalGeometry.exists_inverseChart_jet_bound_of_input
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (N : ℕ)
    (hN : N + 2 ≤ 20 * (n + 1)) :
    ∃ K > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.V), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.inverseChart ε q.1 q.2.1 q.2.2) z‖ ≤ K := by
  obtain ⟨K, hK, hbound⟩ := G.exists_inverseChart_jet_bound N (normalForwardJetBound C (N + 1))
  refine ⟨K, hK, fun F ↦ hbound F ?_⟩
  intro ε hε z hz k hk
  exact (F.averagedGradient_spatial_jet_bound hε (by omega) hz).trans
    (averagedGradientJetBound_le_normalForwardJetBound hk)

/-- The input-only setup implies uniform inverse input-Jacobian jets for
`transportVelocity` (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalGeometry.exists_inverseInputJacobian_jet_bound_of_input
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (N : ℕ)
    (hN : N + 2 ≤ 20 * (n + 1)) :
    ∃ K > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          (fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).inverse) z‖ ≤ K := by
  obtain ⟨K, hK, hbound⟩ :=
    G.exists_inverseInputJacobian_jet_bound N (normalForwardJetBound C (N + 1))
  refine ⟨K, hK, fun F ↦ hbound F ?_⟩
  intro ε hε z hz k hk
  exact (F.averagedGradient_spatial_jet_bound hε (by omega) hz).trans
    (averagedGradientJetBound_le_normalForwardJetBound hk)

/-- The actual transport velocity is ambient smooth at each admissible point,
including both parameter endpoints (`app:ch_osc:prop:osc-normal`, Step 2). -/
theorem UniformNormalData.transportVelocity_contDiffAt (F : UniformNormalData G C)
    {q : ℝ × (Euclidean n × (Euclidean n × Euclidean n))}
    (hq : q ∈ Icc 0 G.ε₀ ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      F.transportVelocity p.1 p.2.1 p.2.2.1 p.2.2.2) q := by
  have hf := F.averagedGradient_contDiffOn.contDiffAt
    ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
      ⟨F.parameter_subset hq.1, hq.2⟩)
  exact (F.inverseInputJacobian_contDiffAt hq).clm_apply (contDiffAt_parameter_deriv hf)

/-- Spatial smoothness of the velocity on the original boxes, used to take
its divergence in `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalData.transportVelocity_contDiffOn_spatial
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      F.transportVelocity ε q.1 q.2.1 q.2.2) (G.X ×ˢ (G.X ×ˢ G.D)) := by
  intro q hq
  exact ((F.transportVelocity_contDiffAt ⟨hε, hq⟩).comp q
    (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt

/-- Uniform full spatial jets of `w = (DᵤΨ)⁻¹ ∂εΨ`, derived from the original
input jets and the determinant gap (`app:ch_osc:prop:osc-normal`, Step 2).
Both positions are independent, and no mask occurs. -/
theorem UniformNormalGeometry.exists_transportVelocity_jet_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (N : ℕ)
    (hN : N + 2 ≤ 20 * (n + 1)) :
    ∃ K > 0, ∀ F : UniformNormalData G C,
      ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.transportVelocity ε q.1 q.2.1 q.2.2) z‖ ≤ K := by
  obtain ⟨J, hJ, hbound⟩ := G.exists_inverseInputJacobian_jet_bound_of_input C N hN
  let B := normalForwardJetBound C N
  let K := (2 : ℝ)^N * J * B
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro F ε hε z hz k hk
  have hInv : ContDiffOn ℝ ∞ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      (fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).inverse)
      (G.X ×ˢ (G.X ×ˢ G.D)) :=
    F.inverseInputJacobian_contDiffOn.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hq ↦ ⟨hε, hq⟩)
  have hb := InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
    (ContinuousLinearMap.id ℝ (Euclidean n →L[ℝ] Euclidean n))
    (ContinuousLinearMap.norm_id_le) (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))
    hInv (F.averagedGradient_parameterDeriv_contDiffOn (F.parameter_subset hε))
    hJ.le hz k (fun i hi ↦ hbound F ε hε z hz i (hi.trans hk))
    (fun i hi ↦ (F.averagedGradient_parameter_jet_bound hε (by omega) hz).trans
      (averagedGradientJetBound_le_normalForwardJetBound (hi.trans hk)))
  apply hb.trans
  apply le_trans _ (le_max_right 1 K)
  have hB : 0 ≤ normalForwardJetBound C N :=
    Finset.sum_nonneg (fun i _ ↦ averagedGradientJetBound_nonneg C i)
  dsimp [K, B]
  gcongr
  norm_num

end JanetCartan.NormalComparison
