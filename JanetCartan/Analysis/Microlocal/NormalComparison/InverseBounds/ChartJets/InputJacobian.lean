module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.Regularity
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.ChartJets.DeterminantGap

/-!
# Finite spatial jets of the inverse input Jacobian

The coefficient used by `transportVelocity` in `app:ch_osc:prop:osc-normal`
is bounded using forward spatial jets and the determinant gap alone.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.NormalComparison
variable {n r : ℕ} {G : UniformNormalGeometry n r} {C : ℕ → ℝ}

/-- Spatial smoothness of the exact averaged gradient on the open input
boxes (`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.averagedGradient_spatial_contDiffOn (F : UniformNormalData G C)
    {ε : ℝ} (hε : ε ∈ F.parameterDomain) :
    ContDiffOn ℝ ∞ (fun z : Euclidean n × (Euclidean n × Euclidean n) ↦
      averagedGradient (F.phase ε) z.1 z.2.1 z.2.2) (G.X ×ˢ (G.X ×ˢ G.D)) :=
  F.averagedGradient_contDiffOn.comp (contDiffOn_const.prodMk contDiffOn_id)
    (fun _ hz ↦ ⟨hε, hz⟩)

/-- Differentiation in the input variable costs exactly one forward spatial
jet, with no norm loss (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.norm_iteratedFDeriv_inputJacobian_le
    (F : UniformNormalData G C) {ε : ℝ} (hε : ε ∈ F.parameterDomain)
    {z : Euclidean n × (Euclidean n × Euclidean n)} (hz : z ∈ G.X ×ˢ (G.X ×ˢ G.D))
    (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2) z‖ ≤
    ‖iteratedFDeriv ℝ (k + 1) (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
      averagedGradient (F.phase ε) q.1 q.2.1 q.2.2) z‖ := by
  let E := Euclidean n
  let S := E × (E × E)
  let U := G.X ×ˢ (G.X ×ˢ G.D)
  let f : S → E := fun q ↦ averagedGradient (F.phase ε) q.1 q.2.1 q.2.2
  let L : E →L[ℝ] S := (ContinuousLinearMap.inr ℝ E (E × E)).comp
    (ContinuousLinearMap.inr ℝ E E)
  let R : (S →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ E S E).flip L
  have hU : IsOpen U := G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D)
  have hf (q) (hq : q ∈ U) : ContDiffAt ℝ ∞ f q :=
    (F.averagedGradient_spatial_contDiffOn hε).contDiffAt (hU.mem_nhds hq)
  have hL : ‖L‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by
      simpa using mul_le_mul (ContinuousLinearMap.norm_inr_le_one ℝ E (E × E))
        (ContinuousLinearMap.norm_inr_le_one ℝ E E) (norm_nonneg _) zero_le_one)
  have hR : ‖R‖ ≤ 1 := by
    apply R.opNorm_le_bound zero_le_one
    intro A
    change ‖A.comp L‖ ≤ 1 * ‖A‖
    exact (ContinuousLinearMap.opNorm_comp_le A L).trans
      (by simpa using mul_le_mul_of_nonneg_left hL (norm_nonneg A))
  have heq : EqOn (fun q : S ↦ fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2)
      (R ∘ fderiv ℝ f) U := by
    intro q hq
    have hd : HasFDerivAt (fun u : E ↦ (q.1, (q.2.1, u))) L q.2.2 :=
      (hasFDerivAt_prodMk_right q.1 q.2).comp q.2.2
        (hasFDerivAt_prodMk_right q.2.1 q.2.2)
    exact ((hf q hq).differentiableAt (by simp) |>.hasFDerivAt.comp q.2.2 hd).fderiv
  have heqjet := iteratedFDerivWithin_congr (𝕜 := ℝ) heq hz k
  rw [iteratedFDerivWithin_of_isOpen k hU hz,
    iteratedFDerivWithin_of_isOpen k hU hz] at heqjet
  rw [heqjet]
  calc
    _ ≤ ‖R‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ f) z‖ :=
      R.norm_iteratedFDeriv_comp_left ((hf z hz).fderiv_right (m := ∞) (by simp)) (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ f) z‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ = _ := by rw [one_mul, norm_iteratedFDeriv_fderiv]

/-- Joint smoothness of the input Jacobian, before inversion
(`app:ch_osc:setup:osc-normal`). -/
theorem UniformNormalData.inputJacobian_contDiffOn (F : UniformNormalData G C) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      fderiv ℝ (averagedGradient (F.phase q.1) q.2.1 q.2.2.1) q.2.2.2)
      (F.parameterDomain ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) := by
  intro q hq
  have hf := F.averagedGradient_contDiffOn.contDiffAt (x := q)
    ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds hq)
  have haux := hf.comp (q, q.2.2.2)
    (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.fst.prodMk
      (contDiffAt_fst.snd.snd.fst.prodMk contDiffAt_snd)))
  exact (haux.fderiv contDiffAt_snd.snd.snd (by simp)).contDiffWithinAt

/-- The actual inverse input Jacobian is ambient smooth even at an admissible
parameter endpoint (`app:ch_osc:prop:osc-normal`). This inverse is a canonical
linear-map operation and has no arbitrary choices outside the interval. -/
theorem UniformNormalData.inverseInputJacobian_contDiffAt (F : UniformNormalData G C)
    {q : ℝ × (Euclidean n × (Euclidean n × Euclidean n))}
    (hq : q ∈ Icc 0 G.ε₀ ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) :
    ContDiffAt ℝ ∞ (fun p : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      (fderiv ℝ (averagedGradient (F.phase p.1) p.2.1 p.2.2.1) p.2.2.2).inverse) q :=
  by
    have hi : ContDiffAt ℝ ∞
        (ContinuousLinearMap.inverse : (Euclidean n →L[ℝ] Euclidean n) →
          Euclidean n →L[ℝ] Euclidean n)
        (fderiv ℝ (averagedGradient (F.phase q.1) q.2.1 q.2.2.1) q.2.2.2) :=
      (F.jacobian_isInvertible hq.1 hq.2.1 hq.2.2.1 hq.2.2.2).contDiffAt_map_inverse
    exact hi.comp q (F.inputJacobian_contDiffOn.contDiffAt
      ((F.isOpen_parameterDomain.prod (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))).mem_nhds
        ⟨F.parameter_subset hq.1, hq.2⟩))

/-- Joint smoothness of the actual inverse input Jacobian on the admissible
parameter interval (`app:ch_osc:prop:osc-normal`). -/
theorem UniformNormalData.inverseInputJacobian_contDiffOn (F : UniformNormalData G C) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (Euclidean n × (Euclidean n × Euclidean n)) ↦
      (fderiv ℝ (averagedGradient (F.phase q.1) q.2.1 q.2.2.1) q.2.2.2).inverse)
      (Icc 0 G.ε₀ ×ˢ (G.X ×ˢ (G.X ×ˢ G.D))) := by
  intro q hq
  exact (F.inverseInputJacobian_contDiffAt hq).contDiffWithinAt

/-- The inverse input Jacobian has uniform spatial jets through `N` from
forward jets through `N+1` and the determinant gap. The constant is chosen
before the family, as required by `app:ch_osc:prop:osc-normal`. -/
theorem UniformNormalGeometry.exists_inverseInputJacobian_jet_bound
    (G : UniformNormalGeometry n r) (N : ℕ) (B : ℝ) :
    ∃ K > 0, ∀ {C : ℕ → ℝ} (F : UniformNormalData G C),
      (∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N + 1,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          averagedGradient (F.phase ε) q.1 q.2.1 q.2.2) z‖ ≤ B) →
      ∀ ε ∈ Icc 0 G.ε₀, ∀ z ∈ G.X ×ˢ (G.X ×ˢ G.D), ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (fun q : Euclidean n × (Euclidean n × Euclidean n) ↦
          (fderiv ℝ (averagedGradient (F.phase ε) q.1 q.2.1) q.2.2).inverse) z‖ ≤ K := by
  obtain ⟨K, hK, hbound⟩ := exists_inverse_field_jet_bound_of_det_gap
    (E := Euclidean n) N B G.gap_pos
  refine ⟨K, hK, ?_⟩
  intro C F hj ε hε
  apply hbound _ _ (G.isOpen_X.prod (G.isOpen_X.prod G.isOpen_D))
  · exact (F.inputJacobian_contDiffOn.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hz ↦ ⟨F.parameter_subset hε, hz⟩)).of_le (by simp)
  · intro z hz
    exact F.jacobian_gap ε hε z.1 hz.1 z.2.1 hz.2.1 z.2.2 hz.2.2
  · intro z hz k hk
    exact (F.norm_iteratedFDeriv_inputJacobian_le (F.parameter_subset hε) hz k).trans
      (hj ε hε z hz (k + 1) (by omega))

end JanetCartan.NormalComparison
