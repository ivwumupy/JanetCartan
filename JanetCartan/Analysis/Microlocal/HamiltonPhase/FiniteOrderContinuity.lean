module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FamilyConstruction
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.SymbolJets
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.RootValueBounds
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.PhaseBounds
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.BufferedFamily
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.InverseStability

/-!
# Components of finite-order Hamilton-phase continuity

For `app:lem:common-hamilton-phase`, the symbol seminorm is the existing `cNorm`
on the fixed compact state domain (in particular the closed state ball in
`exists_commonBufferedHamiltonPhases`). The Hamilton field uses symbol order
`m + 1`; the section energy uses order `m`. The fixed `C³` neighborhood used to
obtain common charts is separate from these finite-order perturbation bounds.

The constructed roots, flows, buffered inverse coordinates and explicit phases
are compared on fixed compact inner domains. The final theorem constructs one
family of actual charts, chosen before the order and tolerance, and proves
symbol-to-phase continuity for that family. The separate low neighborhood
supplies common-domain existence; all higher comparisons are derived.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff InnerProductSpace

namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- The epsilon-delta final step of `app:lem:common-hamilton-phase` on a fixed
compact inner target. The tolerance is uniform over both inverse-coordinate
maps and their open targets. The parent construction must derive its input
seminorm bound from the differentiated root, ODE, and inverse equations. -/
theorem exists_phase_finiteOrder_tolerance {K : Set (E × (ℝ × U))}
    (hK : IsCompact K) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (V : Set (E × (ℝ × U)))
      (C C₀ : E × (ℝ × U) → ℝ × U),
      IsOpen V → K ⊆ V → ContDiffOn ℝ m C V → ContDiffOn ℝ m C₀ V →
      cNorm K m (fun z ↦ C z - C₀ z) ≤ δ →
        cNorm K m (fun z ↦ phase C z - phase C₀ z) < ε := by
  obtain ⟨B, hB, hbound⟩ := exists_phase_finiteOrder_bound hK m
  refine ⟨(ε / 2) / B, div_pos (half_pos hε) hB, ?_⟩
  intro V C C₀ hV hKV hC hC₀ hclose
  calc
    _ ≤ B * cNorm K m (fun z ↦ C z - C₀ z) := hbound V C C₀ hV hKV hC hC₀
    _ ≤ B * ((ε / 2) / B) := mul_le_mul_of_nonneg_left hclose hB.le
    _ = ε / 2 := mul_div_cancel₀ _ hB.ne'
    _ < ε := half_lt_self hε

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]

/-- Finite-order continuity in `app:lem:common-hamilton-phase`. One family of
actual compatible charts is constructed in a fixed scalar `C³` neighborhood.
On every fixed compact inner target, a scalar `C^(m+1)` tolerance yields `C^m`
closeness of the inverse coordinates and the explicit phase. The tolerance
precedes the perturbed symbol, and the charts precede both `m` and the tolerance.

The normalized state domain is the explicit closed ball in `D`, which may be
chosen inside the paper's normalized nonzero covector patch. The root, ODE,
composition and inverse estimates are all instantiated, with no stability
premise. State containment and source admissibility are retained for identifying
these charts with the tame construction. This is the finite-order continuity assertion on the buffered local
charts; conic extension and one-high coefficient bounds are separate results. -/
theorem exists_commonBufferedHamiltonPhases_finiteOrder
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) (horth : ∀ v : U, ⟪ν, j v⟫_ℝ = 0)
    (hspan : ∀ x : E, ⟪ν, x⟫_ℝ = 0 → ∃ u : U, j u = x)
    {s₀ : InitialData U} {τ₀ R : ℝ} (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (r b δ : ℝ) (Φ₀ : HamiltonFlow H₀ U) (C₀ : ProjectionChart Φ₀)
      (A : (ℝ × InitialData U) ≃L[ℝ] (E × (ℝ × U))) (V : Set (E × (ℝ × U))),
      0 < r ∧ 0 < b ∧ 0 < δ ∧ IsOpen V ∧ IsCompact (closure V) ∧
      (j s₀.1, s₀.2) ∈ V ∧ C₀.target = V ∧
      ContDiffOn ℝ ∞ C₀.coordinates V ∧ ContDiffOn ℝ ∞ (phase C₀.coordinates) V ∧
      ∃ (F : (H : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}) → HamiltonFlow H.1 U) (C : (H : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}) → ProjectionChart (F H)),
        (∀ H : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ},
          (F H).time = Φ₀.time ∧ (F H).parameters = Φ₀.parameters ∧
          (F H).sectionMap = j.toContinuousLinearMap ∧ (C H).target = V ∧
          (C H).source = ball ((0 : ℝ), s₀) (3 * r) ∩ (F H).augmentedProjection ⁻¹' V ∧
          (C H).source ⊆ ball ((0 : ℝ), s₀) (2 * r) ∧
          ContDiffOn ℝ ∞ (C H).coordinates V ∧ ContDiffOn ℝ ∞ (phase (C H).coordinates) V ∧
          cthickening b ((F H).augmentedProjection '' closure (ball ((0 : ℝ), s₀) r)) ⊆ V ∧
          cthickening b (closure V) ⊆ (F H).augmentedProjection '' ball ((0 : ℝ), s₀) (2 * r) ∧
          (∀ q ∈ ball ((0 : ℝ), s₀) (3 * r),
            ‖(A.symm : (E × (ℝ × U)) →L[ℝ] (ℝ × InitialData U)).comp
              (fderiv ℝ (F H).augmentedProjection q) - ContinuousLinearMap.id ℝ (ℝ × InitialData U)‖ ≤ 1 / 2) ∧
          ball ((0 : ℝ), s₀) (3 * r) ⊆ (F H).time ×ˢ (F H).parameters ∧
          (∀ q ∈ (F H).time ×ˢ (F H).parameters,
            ((F H).position q, (F H).momentum q) ∈ closedBall z₀ R)) ∧
        (∀ K : Set (E × (ℝ × U)), IsCompact K → K ⊆ V →
          ∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ), ∀ H : {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ},
            cNorm (closedBall z₀ R) (m + 1) (fun z ↦ H.1.h z - H₀.h z) < d →
            cNorm K m ((C H).coordinates - C₀.coordinates) +
              cNorm K m (fun z ↦ phase (C H).coordinates z - phase C₀.coordinates z) < ε) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨r, b, δ, d, Φ₀, C₀, A, V, hr, hb, hδ, hd, hV, hVc, hzV,
      hC₀t, hC₀buffer, hC₀, hΦ₀, hfamily⟩ :=
    exists_common_finiteOrder_bufferedCharts H₀ hD hDH₀ hH₀ j ν horth hspan hR hRD henergy htrans
  let S := {H : HomogeneousSymbol E // D ⊆ H.domain ∧ ContDiffOn ℝ ∞ H.h D ∧
    cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ}
  have hex (H : S) := hfamily H.1 H.2.1 H.2.2.1 H.2.2.2
  let F (H : S) : HamiltonFlow H.1 U := (hex H).choose
  let C (H : S) : ProjectionChart (F H) := (hex H).choose_spec.choose
  refine ⟨r, b, δ, Φ₀, C₀, A, V, hr, hb, hδ, hV, hVc, hzV, hC₀t, hC₀,
    hC₀t ▸ C₀.contDiffOn_phase (hC₀t.symm ▸ hC₀), F, C, ?_, ?_⟩
  · intro H
    obtain ⟨ht, hp, hj, hCt, hCs, hbuffer, hC, _hΦ, hinner, houter, hgap, _hcompare, hadm, hrange⟩ :=
      (hex H).choose_spec.choose_spec
    exact ⟨ht, hp, hj, hCt, hCs, hbuffer, hC,
      hCt ▸ (C H).contDiffOn_phase (hCt.symm ▸ hC), hinner, houter, hgap, hadm, hrange⟩
  · intro K hK hKV m ε hε
    obtain ⟨B, hB, hphase⟩ := exists_phase_finiteOrder_bound hK m
    have he : 0 < ε / (1 + B) := div_pos hε (by linarith)
    obtain ⟨di, hdi, hinverse⟩ := C₀.exists_coordinates_finiteOrder_continuity
      ((0 : ℝ), s₀) hr hK hV hKV (by rw [hC₀t]) hΦ₀ (hC₀t.symm ▸ hC₀) A
      (fun z hz ↦ hC₀buffer (C₀.maps_to_source z (hC₀t.symm ▸ hKV hz))) m he
    refine ⟨d m di hdi, hd m di hdi, ?_⟩
    intro H hsmall
    obtain ⟨_ht, _hp, _hj, hCt, _hCs, hbuffer, hC, hΦ, _hinner, _houter, hgap, hcompare, _hadm, _hrange⟩ :=
      (hex H).choose_spec.choose_spec
    have hi := hinverse H.1 (F H) (C H) (by rw [hCt]) hΦ
      (hCt.symm ▸ hC)
      (fun z hz ↦ hbuffer ((C H).maps_to_source z (hCt.symm ▸ hKV hz)))
      hgap (hcompare m di hdi hsmall)
    have hc : cNorm K m ((C H).coordinates - C₀.coordinates) < ε / (1 + B) := by
      linarith [cNorm_nonneg K m (chartLift (C H).coordinates - chartLift C₀.coordinates)]
    have hs := hphase V (C H).coordinates C₀.coordinates hV hKV
      (hC.of_le (by simp)) (hC₀.of_le (by simp))
    have hs' : cNorm K m (fun z ↦ phase (C H).coordinates z - phase C₀.coordinates z) ≤
        B * cNorm K m ((C H).coordinates - C₀.coordinates) := by
      convert! hs using 1
    have hm := (lt_div_iff₀ (show 0 < 1 + B by linarith)).mp hc
    change cNorm K m ((C H).coordinates - C₀.coordinates) +
      cNorm K m (fun z ↦ phase (C H).coordinates z - phase C₀.coordinates z) < ε
    nlinarith only [hm, hs']

end JanetCartan.HamiltonPhase
