module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedFlowProfiles.HamiltonInverse
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Endpoint

/-!
# Global phase estimates for the actual source-dilated reference

Use the normalized frame and Hamilton bounds for the supplied flat reference
inside the same retained quantitative family. A fixed affine extension keeps
the canonical transported position on its entire supported chart. Its global
transverse gap and derivative-trade profiles are uniform before the source
scale varies. No unnormalized normal-pairing gap is required.

Consumer: the phase, graph and trade-field inputs of
`UniformEndpoint.exists_uniform_scalarTransportCarrierAdjoint_periodic_raw_bound`,
`app:ch_background:prop:bg-adjoint` and `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow CanonicalCarrier NormalizedFlowProfiles PhaseExtension DerivativeKernels
open ProjectedStressFrame

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Uniform mixed jets of the literal retained Hamilton footpoint for every
admitted witness of the SAME source frame. The normalized frame producer
discharges the high budgets, and the original phase pullback loses one
derivative. This supplies the cutoff-support bounds in
`exists_source_supported_phase_inputs` (`app:ch_background:prop:bg-normalized`). -/
theorem exists_source_transportPosition_bounds (H : FlatReference n)
    {c C : ℝ} (hP : P.IsValid c C) (hbounded : Bornology.IsBounded U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hLO : L ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius))) :
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Q.1 = projectedStress (sourceDilation H.map σ) →
      ∀ m, cNorm L m (transportPosition T Q) ≤ B m := by
  obtain ⟨σ₀, hσ₀, hσ₁, B, hB, hb⟩ :=
    exists_source_hamilton_inverse_profiles H T hbounded hphysical
  obtain ⟨D, hD, hd⟩ := exists_transportPosition_le_phase T hP hL hLO
  refine ⟨σ₀, hσ₀, hσ₁, fun m ↦ D m * B (m + 1),
    fun m ↦ mul_pos (hD m) (hB _), ?_⟩
  intro σ hσ Q hQ m
  apply (hd Q m).trans
  apply mul_le_mul_of_nonneg_left _ (hD m).le
  exact (le_add_of_nonneg_right (cNorm_nonneg _ _ _)).trans (hb σ hσ Q hQ (m + 1))

private theorem norm_iteratedFDeriv_linear_pos_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (i : ℕ) (hi : 1 ≤ i) (p : E) :
    ‖iteratedFDeriv ℝ i L p‖ ≤ ‖L‖ := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ ↦ L := funext fun _ ↦ L.fderiv
  rw [he]
  cases j with
  | zero => simp
  | succ j => simp [iteratedFDeriv_succ_const]

/-- Construct the actual source-family global phase inputs, with one cutoff
and one positive source cap for ALL derivative orders. The graph and branch
profiles are chosen before `σ` and any admitted frame witness. Every derivative
is in the original physical/carrier or symbol variables, and the extension
agrees near the entire supported chart. The initial and carrier fields are
the existing literal Gram formulas and satisfy both exact trades.

The normalized frame, phase and inverse-chart producers discharge all
varying analytic premises. This supplies `hY`, `hΦ`, `hL`, `hV`, `hphaseL`,
`hphaseV`, `hYB` and `hcoeff` of the scalar-transport raw endpoint, with high
budget `H = 1` (`app:ch_background:prop:bg-adjoint`,
`app:ch_background:eq:bg-derivative-trade`). Supported conic geometry and
amplitude profiles remain separate inputs for the SAME row. -/
theorem exists_source_supported_phase_inputs (H : FlatReference n)
    {c C : ℝ} (hP : P.IsValid c C) (hbounded : Bornology.IsBounded U)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (z₀ : Euclidean 3) {r cap : ℝ} (hr : 0 < r) (hcap : 0 < cap)
    (hcarrier : closedBall (ActualComparison.spectatorCenter z₀) (3 * r) ×ˢ
        closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2)) :
    ∃ (a : ℝ) (χ : Euclidean n × CarrierParameter → ℝ),
      0 < a ∧ a ≤ r ∧ a < cap ∧ 4 * a < T.physicalRadius ∧
      ContDiff ℝ ∞ χ ∧ (∀ p, χ p ∈ Icc (0 : ℝ) 1) ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ extensionDomain T ∧
      supportedChart z₀ a ⊆ interior {p | χ p = 1} ∧
    ∃ σ₀ > (0 : ℝ), σ₀ ≤ 1 ∧
    ∃ (B : ℕ → ℝ) (D : List (InitialCarrierDerivative n) → ℕ → ℝ),
      (∀ i, 0 ≤ B i) ∧ (∀ ds i, 0 ≤ D ds i) ∧
      (∀ σ ∈ Ioc (0 : ℝ) σ₀,
        ∃ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
          cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (Q - fun _ ↦ cubeStress n) < T.family.threshold},
          Q.1 = projectedStress (sourceDilation H.map σ)) ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
      ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Q.1 = projectedStress (sourceDilation H.map σ) →
      let A := frozenSpatialReference T (z₀ 0, ActualComparison.spectatorCenter z₀)
      let Y := affineExtension A χ (transportPosition T Q)
      ContDiff ℝ ∞ Y ∧ HasCompactSupport (fun p ↦ Y p - A p.1) ∧
      (∀ p ∈ supportedChart z₀ a, Y =ᶠ[𝓝 p] transportPosition T Q) ∧
      (∀ x z, TransverseGap (1 / 4) (spatialMatrix Y z x)) ∧
      ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n × Euclidean (n - 1) ↦
        phase Y p.1 p.2.1 p.2.2) ∧
      ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ (p.1, Y (p.2, p.1))) ∧
      (∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ initialField Y p.1 p.2 h)) ∧
      (∀ h, ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ carrierField Y p.1 p.2 h)) ∧
      (∀ z x η h, inner ℝ h η =
        fderiv ℝ (fun y ↦ phase Y z y η) x (initialField Y z x h)) ∧
      (∀ z x η h, fderiv ℝ (fun w ↦ phase Y w x η) z h =
        fderiv ℝ (fun y ↦ phase Y z y η) x (carrierField Y z x h)) ∧
      (∀ p : CarrierParameter × Euclidean n, ∀ i, 1 ≤ i →
        ‖iteratedFDeriv ℝ i (fun p : CarrierParameter × Euclidean n ↦
          (p.1, Y (p.2, p.1))) p‖ ≤ B i) ∧
      (∀ ds : List (InitialCarrierDerivative n), ∀ p : AdjointSymbolPoint n,
        ∀ e ∈ ds, ∀ j i,
          ‖iteratedFDeriv ℝ i (fun p : AdjointSymbolPoint n ↦
            branchField (initialField Y) (carrierField Y) e j p.1) p‖ ≤ D ds i) := by
  classical
  obtain ⟨a, χ, δ, ha, har, hacap, hphys, hχ, hχrange, hc, hs, hp, hδ, hactual⟩ :=
    exists_supported_affine_extensions_transverseGap T hP z₀ hr hcap hcarrier
  let A := frozenSpatialReference T (z₀ 0, ActualComparison.spectatorCenter z₀)
  have hs' : tsupport χ ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hps
    exact ⟨(hs hps).1, fun i ↦ ((hs hps).2 i).trans (by linarith [hP.1])⟩
  obtain ⟨s₁, hs₁, hs₁1, Bpos, hBpos, hpos⟩ :=
    exists_source_transportPosition_bounds T H hP hbounded hphysical hc hs'
  obtain ⟨s₂, hs₂, _, _, _, Qs, hQs, hsource, hreg, _⟩ :=
    exists_admitted_source_frame_profiles T H hbounded hphysical hδ
  let σ₀ := min s₁ s₂
  have hσ₀ : 0 < σ₀ := lt_min hs₁ hs₂
  have hcap₁ {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) s₁ :=
    ⟨hσ.1, hσ.2.trans (min_le_left _ _)⟩
  have hcap₂ {σ : ℝ} (hσ : σ ∈ Ioc (0 : ℝ) σ₀) : σ ∈ Ioc (0 : ℝ) s₂ :=
    ⟨hσ.1, hσ.2.trans (min_le_right _ _)⟩
  have hsmall (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀)
      (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
      (hQ : Q.1 = projectedStress (sourceDilation H.map σ)) :
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ := by
    have he : Q = Qs σ (hcap₂ hσ) := Subtype.ext (hQ.trans (hQs σ (hcap₂ hσ)).symm)
    subst Q
    apply (cNorm_mono_set_of_contDiffAt (hphysical.trans subset_closure)
      hbounded.isCompact_closure ?_).trans_lt (hsource σ (hcap₂ hσ)).2.2
    intro x hx
    exact ((hreg σ (hcap₂ hσ) x hx).sub contDiffAt_const).of_le (by simp)
  obtain ⟨R, hR, hsupport⟩ := hc.isBounded.subset_closedBall_lt
    0 (0 : Euclidean n × CarrierParameter)
  let J := closedBall (0 : Euclidean n × CarrierParameter) R
  let Jg := closedBall (0 : CarrierParameter × Euclidean n) R
  obtain ⟨E₀, hE₀, hext⟩ := exists_cNorm_affineExtension_le A
    (extensionDomain_open T) (isCompact_closedBall _ _) hχ hc hs (L := J)
  obtain ⟨G₀, hG₀, hgraph⟩ := exists_cNorm_affineGraph_le A
    (extensionDomain_open T) (isCompact_closedBall _ _) hχ hc hs (L := Jg)
  let E := fun m ↦ E₀ m * (1 + Bpos m)
  let G := fun m ↦ G₀ m * (1 + Bpos m)
  have hE m : 0 < E m := mul_pos (hE₀ m) (by linarith [hBpos m])
  have hG m : 0 < G m := mul_pos (hG₀ m) (by linarith [hBpos m])
  have hquarter : (0 : ℝ) < 1 / 4 := by norm_num
  choose Cfield hCfield hfield using fun e j m ↦ exists_cNorm_branchField_le_firstJet
    (0 : Euclidean n × CarrierParameter) hR (E 1) hquarter e j m
  let Aref := A.comp (ContinuousLinearMap.fst ℝ (Euclidean n) CarrierParameter)
  let Bfield := fun e j i ↦ Cfield e j i * (1 + E (i + 1)) + ‖firstJetBranch e j Aref‖
  have hBfield e j i : 0 ≤ Bfield e j i := by
    have := hCfield e j i
    have := hE (i + 1)
    dsimp [Bfield]
    positivity
  let D := fun (ds : List (InitialCarrierDerivative n)) i ↦ ∑ e ∈ ds.toFinset, ∑ j, Bfield e j i
  let Lref : (CarrierParameter × Euclidean n) →L[ℝ] CarrierParameter × Euclidean (n - 1) :=
    (ContinuousLinearMap.fst ℝ CarrierParameter (Euclidean n)).prod
      (A.comp (ContinuousLinearMap.snd ℝ CarrierParameter (Euclidean n)))
  refine ⟨a, χ, ha, har, hacap, hphys, hχ, hχrange, hc, hs, hp, σ₀, hσ₀,
    (min_le_left _ _).trans hs₁1, (fun i ↦ G i + ‖Lref‖), D,
    (fun i ↦ add_nonneg (hG i).le (norm_nonneg _)),
    (fun ds i ↦ Finset.sum_nonneg fun e _ ↦ Finset.sum_nonneg fun j _ ↦ hBfield e j i),
    (fun σ hσ ↦ ⟨Qs σ (hcap₂ hσ), hQs σ (hcap₂ hσ)⟩), ?_⟩
  intro σ hσ Q hQ
  dsimp only
  let Y := affineExtension A χ (transportPosition T Q)
  obtain ⟨hY, hcompact, hagree, hgap⟩ := hactual Q (hsmall σ hσ Q hQ)
  have hgap' : ∀ z x, TransverseGap (1 / 4) (spatialMatrix Y z x) := fun z x ↦ hgap x z
  have htransport := transportPosition_contDiffOn_extensionDomain T hP Q
  have hYbound (m) : cNorm J m Y ≤ E m :=
    (hext _ htransport m).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hpos σ (hcap₁ hσ) Q hQ m)) (hE₀ m).le)
  have hgraphBound (m) : cNorm Jg m
      (fun p : CarrierParameter × Euclidean n ↦ (p.1, Y (p.2,p.1))) ≤ G m :=
    (hgraph _ htransport m).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) (hpos σ (hcap₁ hσ) Q hQ m)) (hG₀ m).le)
  refine ⟨hY, hcompact, hagree, hgap, phase_contDiff hY, graph_contDiff hY,
    initialField_contDiff hY hquarter hgap', carrierField_contDiff hY hquarter hgap',
    initialField_trade hY hquarter hgap', carrierField_trade hY hquarter hgap', ?_, ?_⟩
  · intro p i hi
    by_cases hpJ : p ∈ Jg
    · exact (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
        ((graph_contDiff hY).of_le (by simp)) hpJ (le_refl i)).trans
          ((hgraphBound i).trans (le_add_of_nonneg_right (norm_nonneg _)))
    · have hnot : (p.2,p.1) ∉ tsupport χ := by
        intro hps
        apply hpJ
        simpa only [Jg, J, mem_closedBall_zero_iff, Prod.norm_def, max_comm] using hsupport hps
      have he : (fun p : CarrierParameter × Euclidean n ↦ (p.1, Y (p.2,p.1))) =ᶠ[𝓝 p] Lref := by
        have hh := (affineExtension_eventuallyEq_reference A (transportPosition T Q) hnot).comp_tendsto
          continuous_swap.continuousAt
        filter_upwards [hh] with q hq
        exact congrArg (Prod.mk q.1) hq
      rw [(he.iteratedFDeriv ℝ i).eq_of_nhds]
      exact (norm_iteratedFDeriv_linear_pos_le Lref i hi p).trans
        (le_add_of_nonneg_left (hG i).le)
  · have hjet (p) (hpJ : p ∈ J) :
        ‖fderiv ℝ Y p‖ ≤ E 1 ∧ TransverseGap (1 / 4) (spatialMatrix Y p.2 p.1) := by
      refine ⟨?_, hgap p.1 p.2⟩
      have hh := norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
        (hY.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) hpJ (le_refl 1)
      rw [norm_iteratedFDeriv_one] at hh
      exact hh.trans (hYbound 1)
    let f := fun e j (p : Euclidean n × CarrierParameter) ↦
      branchField (initialField Y) (carrierField Y) e j (p.2,p.1)
    have hf e j : ContDiff ℝ ∞ (f e j) :=
      (branchField_contDiff_of_gap hY hquarter (fun p ↦ hgap p.1 p.2) e j).comp
        (contDiff_snd.prodMk contDiff_fst)
    have hglobal e j i (p : Euclidean n × CarrierParameter) :
        ‖iteratedFDeriv ℝ i (f e j) p‖ ≤ Bfield e j i := by
      by_cases hpJ : p ∈ J
      · apply (norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
          ((hf e j).of_le (by simp)) hpJ (le_refl i)).trans
        apply (hfield e j i Y hY hjet).trans
        exact (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) (hYbound (i + 1)))
          (hCfield e j i).le).trans (le_add_of_nonneg_right (norm_nonneg _))
      · have hd := (affineExtension_eventuallyEq_reference A (transportPosition T Q)
          (fun hh ↦ hpJ (hsupport hh))).fderiv (𝕜 := ℝ)
        have he : f e j =ᶠ[𝓝 p] (fun _ ↦ firstJetBranch e j Aref) := by
          filter_upwards [hd] with q hq
          change branchField (initialField Y) (carrierField Y) e j (q.2,q.1) = _
          rw [← firstJetBranch_fderiv (hY.differentiable (by simp)).differentiableAt e j]
          exact congrArg (firstJetBranch e j) (hq.trans Aref.fderiv)
        rw [(he.iteratedFDeriv ℝ i).eq_of_nhds]
        have hconst : ‖iteratedFDeriv ℝ i (fun _ : Euclidean n × CarrierParameter ↦
            firstJetBranch e j Aref) p‖ ≤ ‖firstJetBranch e j Aref‖ := by
          cases i with
          | zero => simp
          | succ i => simp [iteratedFDeriv_succ_const]
        exact hconst.trans (le_add_of_nonneg_left
          (mul_nonneg (hCfield e j i).le (by linarith [hE (i + 1)])))
    intro ds p e heds j i
    have hswap := (LinearIsometryEquiv.prodComm ℝ CarrierParameter (Euclidean n)).norm_iteratedFDeriv_comp_right
      (f e j) p.1 i
    change ‖iteratedFDeriv ℝ i (branchField (initialField Y) (carrierField Y) e j) p.1‖ =
      ‖iteratedFDeriv ℝ i (f e j) (p.1.2,p.1.1)‖ at hswap
    have htotal : Bfield e j i ≤ D ds i := by
      apply (Finset.single_le_sum (fun k _ ↦ hBfield e k i) (Finset.mem_univ j)).trans
      exact Finset.single_le_sum
        (fun e _ ↦ Finset.sum_nonneg fun j _ ↦ hBfield e j i) (List.mem_toFinset.mpr heds)
    apply (adjoint_spatial_jet_lift_bound _
      (branchField_contDiff_of_gap hY hquarter (fun p ↦ hgap p.1 p.2) e j) i p).trans
    rw [hswap]
    exact (hglobal e j i (p.1.2,p.1.1)).trans htotal

end JanetCartan.ContinuumAdjoint.Canonical.NormalizedFamily
