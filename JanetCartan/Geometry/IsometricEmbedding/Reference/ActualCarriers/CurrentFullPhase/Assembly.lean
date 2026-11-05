module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# Full-phase production from the paper's primitive frame neighborhood

This is the assembled construction consumed by the actual-carrier parent.
There are no analytic input hypotheses besides smoothness and componentwise
frame closeness to the fixed cube frame. The finite detecting menu and all
reference/current chart choices precede requested accuracy and high orders
(`app:ch_seed:prop:seed-actual-menu`, Step 1).
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase
open HamiltonPhase FrozenMenu FrozenPhaseReference

/-- Construct actual full-phase inputs for the literal normalized determinant
from smoothness and primitive componentwise `C⁶` frame closeness. The finite
menu retains its full validity (including centered incidence sections and the
detector), and each reference retains doubled closed patch characteristicity,
annular and transverse bounds in `T.data`. Every analytic field of each input
is proved. The chart identities ensure that the same phase enjoys
`current_phase_continuity` at every finite order, especially phase `C⁵` from
frame `C⁶`, and `current_phase_bound` at frame order `m+1`. The parent supplies
the independently constructed projected frame to get immersion order `m+3`
(`app:ch_seed:prop:seed-actual-menu`, Step 1;
`app:ch_seed:eq:seed-phase-tame`; `app:lem:common-hamilton-phase`). -/
theorem exists_finite_current_fullPhaseInputs {n : ℕ} (hn : 5 ≤ n)
    {U : Set (Euclidean n)} (hU : IsOpen U) {b : ℝ} (hb : 0 < b)
    (hBU : ball (0 : Euclidean n) b ⊆ U) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) U hU,
        (∀ i, ∀ q ∈ (T i).data.localReference.stateDomain,
          q.1 ∈ ball (0 : Euclidean n) b) ∧
        ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ),
          ∀ (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U),
            (∀ i j, cNorm (closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius) 6
              (fun x ↦ Q x j - cubeStress n j) < δ) →
            ∀ i, ∃ hlow : cNorm (closedBall (0 : Euclidean n)
                (T i).data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) <
                  (T i).family.threshold,
              ∃ I : CarrierFullPhaseInput (T i).reference
                  (normalizedHomogeneousSymbol hU Q hQ) ε,
                I.flow = (T i).family.flow ⟨Q, hQ, hlow⟩ ∧
                  HEq I.chart ((T i).currentChart ⟨Q, hQ, hlow⟩) := by
  obtain ⟨D, c, C, hD, T, hphysical⟩ :=
    exists_quantitative_frozenReference_coverData hn hU hb hBU
  refine ⟨D, c, C, hD, T, hphysical, ?_⟩
  intro ε hε
  obtain ⟨d, hd, hc⟩ := exists_common_fullPhaseInput_threshold D T hε
  refine ⟨d / 14, by positivity, fun Q hQ hcomp ↦ ?_⟩
  apply hc Q hQ
  intro i
  have hKU := frameBall_subset_of_stateDomain (T i).data.localReference
    (fun q hq ↦ hBU (hphysical i q hq))
  apply frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _)
    (fun x hx ↦ ((hQ.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le
      (by simp : (6 : ℕ∞ω) ≤ ∞)) hd
  convert hcomp i using 1
  norm_num

/-- Componentwise `C^(m+1)` frame continuity for the very same selected current
phase. The domain premise is discharged by the physical containment in
`exists_finite_current_fullPhaseInputs`; the phase comparison is derived from
the constructed family, not assumed (`app:lem:common-hamilton-phase`). -/
theorem PatchQuantitativeFamily.current_phase_continuity_componentwise {n : ℕ}
    {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (hdomain : ∀ q ∈ T.data.localReference.stateDomain, q.1 ∈ U)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ Q,
      (∀ j, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m + 1)
        (fun x ↦ Q.1 x j - cubeStress n j) < δ) →
      cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
        T.data.adapted.baseData.2) T.family.radius) m
        (phase (T.currentChart Q).coordinates - phase T.reference.chart.coordinates) < ε := by
  obtain ⟨d, hd, hc⟩ := T.current_phase_continuity m hε
  refine ⟨d / (2 * ((m + 1 : ℕ) + 1)), by positivity, fun Q hcomp ↦ ?_⟩
  apply hc Q
  apply frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _)
    (fun x hx ↦ ((Q.2.1.contDiffAt (hU.mem_nhds
      (frameBall_subset_of_stateDomain T.data.localReference hdomain hx))).sub contDiffAt_const).of_le
        (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞)) hd
  exact hcomp

end JanetCartan.ActualCarriers.CurrentFullPhase
