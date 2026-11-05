module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.InverseAmplitude.Regularity

/-!
# Uniform jets of the inverse normal amplitude

Quantitative composition and product estimates for Step 1 of
`app:ch_osc:prop:osc-normal`. Constants are chosen before the input family.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

namespace InverseAmplitudeJet
/-- The finite composition estimate on open sets used twice in Step 1 of
`app:ch_osc:prop:osc-normal`: for the reciprocal Jacobian and the inverse chart. -/
theorem norm_iteratedFDeriv_comp_on_open_le
    {E H W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E → H} {g : H → W} {U : Set E} {V : Set H}
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g V) (hmap : MapsTo f U V)
    {z : E} (hz : z ∈ U) (k : ℕ) {A B : ℝ}
    (hgjet : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (f z)‖ ≤ A)
    (hfjet : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f z‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (g ∘ f) z‖ ≤ (k.factorial : ℝ) * A * (max 1 B)^k := by
  have h := norm_iteratedFDerivWithin_comp_le hg hf (n := k) (by simp)
    hV.uniqueDiffOn hU.uniqueDiffOn hmap hz
    (fun i hi ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ hV (hmap hz)]
      exact hgjet i hi)
    (fun i hi hik ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ hU hz]
      exact ((hfjet i hi hik).trans (le_max_right 1 B)).trans
        (le_self_pow₀ (le_max_left 1 B) (by omega)))
  rwa [iteratedFDerivWithin_of_isOpen _ hU hz] at h
end InverseAmplitudeJet

/-- Spatial jets of the actual reciprocal absolute input Jacobian follow
from the original input bounds (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalGeometry.exists_reciprocalAbsJacobian_jet_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (N : ℕ)
    (hN : N + 2 ≤ 20 * (n + 1)) :
    ∃ K > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀,
      ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          |(fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).det|⁻¹) z‖ ≤ K := by
  let B := normalForwardJetBound C (N + 1)
  obtain ⟨A, hA, hbound⟩ := exists_reciprocalAbsNormalJacobian_jet_bound (n := n) N B G.gap_pos
  let K := (N.factorial : ℝ) * A * (max 1 B)^N
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro F ε hε z hz k hk
  let J := fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
    fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2
  let V : Set (Euclidean n →L[ℝ] Euclidean n) := {L | L.det ≠ 0}
  have hV : IsOpen V := isOpen_ne.preimage ContinuousLinearMap.continuous_det
  have hJ : ContDiffOn ℝ ∞ J (G.X ×ˢ (G.X ×ˢ G.D)) :=
    F.inputJacobian_contDiffOn.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hq ↦ ⟨F.parameter_subset hε, hq⟩)
  have hj (q) (hq : q ∈ G.X ×ˢ (G.X ×ˢ G.D)) (i) (hi : i ≤ N) :
      ‖iteratedFDeriv ℝ i J q‖ ≤ B :=
    (F.norm_iteratedFDeriv_inputJacobian_le (F.parameter_subset hε) hq i).trans
      ((F.averagedGradient_spatial_jet_bound hε (by omega) hq).trans
        (averagedGradientJetBound_le_normalForwardJetBound (by omega)))
  have hmap : MapsTo J (G.X ×ˢ (G.X ×ˢ G.D)) V := fun q hq ↦
    abs_pos.mp (G.gap_pos.trans_le (F.jacobian_gap ε hε q.1 hq.1 q.2.1 hq.2.1 q.2.2 hq.2.2))
  have hb := InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le
    (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)) hV hJ
    (show ContDiffOn ℝ ∞ (fun L : Euclidean n →L[ℝ] Euclidean n ↦ |L.det|⁻¹) V from
      fun L hL ↦ (contDiffAt_reciprocalAbsNormalJacobian hL).contDiffWithinAt)
    hmap hz k
    (fun i hi ↦ hbound (J z) (by simpa using hj z hz 0 (Nat.zero_le N))
      (F.jacobian_gap ε hε z.1 hz.1 z.2.1 hz.2.1 z.2.2 hz.2.2) i (hi.trans hk))
    (fun i _ hi ↦ hj z hz i (hi.trans hk))
  apply hb.trans
  apply le_trans _ (le_max_right 1 K)
  have hf : (k.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hk
  dsimp [K]
  gcongr
  exact le_max_left _ _

/-- Smoothness of the input amplitude multiplied by the reciprocal absolute
Jacobian, before composing with the inverse (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.jacobianWeightedAmplitude_contDiffOn
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ Icc 0 G.ε₀) :
    ContDiffOn ℝ ∞ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      |(fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).det|⁻¹ •
        normalAmplitude (F.amplitude ε) q.1 q.2.1 q.2.2) (G.X ×ˢ (G.X ×ˢ G.D)) := by
  have hs : ContDiffOn ℝ ∞ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      |(fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).det|⁻¹)
      (G.X ×ˢ (G.X ×ˢ G.D)) := fun q hq ↦
    ((F.reciprocalAbsJacobian_contDiffAt ⟨hε, hq⟩).comp q
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  exact hs.smul (F.normalAmplitude_contDiffOn_spatial (F.parameter_subset hε))

/-- Frobenius jets of the full input amplitude divided by the absolute
Jacobian (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalGeometry.exists_jacobianWeightedAmplitude_jet_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (N : ℕ)
    (hN : N + 2 ≤ 20 * (n + 1)) :
    ∃ K > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀,
      ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          |(fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).det|⁻¹ •
            normalAmplitude (F.amplitude ε) q.1 q.2.1 q.2.2) z‖ ≤ K := by
  obtain ⟨A, hA, hbound⟩ := G.exists_reciprocalAbsJacobian_jet_bound C N hN
  let B := ∑ i ∈ Finset.range (N + 1), normalAmplitudeJetBound r C i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ ↦ normalAmplitudeJetBound_nonneg r C i)
  let K := (2 : ℝ)^N * A * B
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro F ε hε z hz k hk
  have hs : ContDiffOn ℝ ∞ (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      |(fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).det|⁻¹)
      (G.X ×ˢ (G.X ×ˢ G.D)) := fun q hq ↦
    ((F.reciprocalAbsJacobian_contDiffAt ⟨hε, hq⟩).comp q
      (contDiffAt_const.prodMk contDiffAt_id)).contDiffWithinAt
  have hb := InverseChartJet.norm_iteratedFDeriv_bilinear_on_open_le
    (ContinuousLinearMap.lsmul ℝ ℝ) (ContinuousLinearMap.opNorm_lsmul_le)
    (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)) hs
    (F.normalAmplitude_contDiffOn_spatial (F.parameter_subset hε)) hA.le hz k (B := B)
    (fun i hi ↦ hbound F ε hε z hz i (hi.trans hk))
    (fun i hi ↦ (F.norm_iteratedFDeriv_normalAmplitude_le hε hz (k := i) (by omega)).trans
      (Finset.single_le_sum (fun j _ ↦ normalAmplitudeJetBound_nonneg r C j)
        (Finset.mem_range.mpr (by omega))))
  apply hb.trans
  apply le_trans _ (le_max_right 1 K)
  dsimp [K]
  gcongr
  norm_num

/-- Full spatial Frobenius jets of the actual inverse amplitude on the open
chart, derived solely from input bounds (`app:ch_osc:prop:osc-normal`, Step 1). -/
theorem UniformNormalGeometry.exists_maskFreeInverseAmplitude_chart_jet_bound
    (G : UniformNormalGeometry n r) (C : ℕ → ℝ) (N : ℕ)
    (hN : N + 2 ≤ 20 * (n + 1)) :
    ∃ K > 0, ∀ F : UniformNormalData G C, ∀ ε ∈ Icc 0 G.ε₀,
      ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.V), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          F.maskFreeInverseAmplitude ε q.1 q.2.1 q.2.2) z‖ ≤ K := by
  obtain ⟨A, hA, hAmp⟩ := G.exists_jacobianWeightedAmplitude_jet_bound C N hN
  obtain ⟨J, hJ, hInv⟩ := G.exists_inverseChart_jet_bound_of_input C N hN
  let Q := InverseChartJet.chartBaseMap (Euclidean n)
  let L := InverseChartJet.chartInputMap (Euclidean n)
  let B := ‖Q‖ + ‖L‖ * J
  let K := (N.factorial : ℝ) * A * (max 1 B)^N
  refine ⟨max 1 K, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro F ε hε z hz k hk
  let U := G.X ×ˢ (G.X ×ˢ G.V)
  let W := G.X ×ˢ (G.X ×ˢ G.D)
  let g := fun q : Euclidean n × (Euclidean n × Euclidean n) ↦ F.inverseChart ε q.1 q.2.1 q.2.2
  let T := fun q ↦ Q q + L (g q)
  let H := fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
    |(fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).det|⁻¹ •
      normalAmplitude (F.amplitude ε) q.1 q.2.1 q.2.2
  have hU : IsOpen U := G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_V)
  have hW : IsOpen W := G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)
  have hg : ContDiffOn ℝ ∞ g U := F.inverseChart_spatial_contDiffOn hε
  have hT : ContDiffOn ℝ ∞ T U := Q.contDiff.contDiffOn.add (L.contDiff.comp_contDiffOn hg)
  have hTe (q) : T q = (q.1, (q.2.1, g q)) := by
    simp [T, Q, L, InverseChartJet.chartBaseMap, InverseChartJet.chartInputMap]
  have hmap : MapsTo T U W := by
    intro q hq
    rw [hTe]
    exact ⟨hq.1, hq.2.1, F.inverseChart_mem hε hq.1 hq.2.1 hq.2.2⟩
  have hTjet (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) : ‖iteratedFDeriv ℝ i T z‖ ≤ B := by
    have hgz := hg.contDiffAt (hU.mem_nhds hz)
    rw [show T = fun q ↦ Q q + (L ∘ g) q from rfl,
      fun_iteratedFDeriv_add_apply ((Q.contDiff (n := i)).contDiffAt)
        (((L.contDiff (n := i)).contDiffAt.comp z (hgz.of_le (by simp))))]
    exact (norm_add_le _ _).trans
      (add_le_add (InverseChartJet.norm_iteratedFDeriv_linear_pos_le Q z hi)
        ((L.norm_iteratedFDeriv_comp_left hgz (by simp)).trans
          (mul_le_mul_of_nonneg_left (hInv F ε hε z hz i (hik.trans hk)) (norm_nonneg L))))
  have hb := InverseAmplitudeJet.norm_iteratedFDeriv_comp_on_open_le hU hW hT
    (F.jacobianWeightedAmplitude_contDiffOn hε) hmap hz k
    (fun i hi ↦ hAmp F ε hε (T z) (hmap hz) i (hi.trans hk)) hTjet
  have heq : EqOn (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      F.maskFreeInverseAmplitude ε q.1 q.2.1 q.2.2) (H ∘ T) U := by
    intro q hq
    simp [hTe, H, g, UniformNormalData.maskFreeInverseAmplitude,
      hq.2.2, inverseJacobianAmplitude]
  have heqjet := iteratedFDerivWithin_congr (𝕜 := ℝ) heq hz k
  rw [iteratedFDerivWithin_of_isOpen _ hU hz,
    iteratedFDerivWithin_of_isOpen _ hU hz] at heqjet
  rw [heqjet]
  apply hb.trans
  apply le_trans _ (le_max_right 1 K)
  have hf : (k.factorial : ℝ) ≤ N.factorial := by exact_mod_cast Nat.factorial_le hk
  dsimp [K]
  gcongr
  exact le_max_left _ _

end JanetCartan.NormalComparison
