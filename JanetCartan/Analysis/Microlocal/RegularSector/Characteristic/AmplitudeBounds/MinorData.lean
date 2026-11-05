module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.PrimitiveBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition
public import JanetCartan.Analysis.Microlocal.FullPhaseCharts.InverseEstimates.QuotientJets.LocalNorms

/-!
# Original-gap estimates for the literal normalized minor data

The nullvectors and signed datum of `paper-v2.tex`,
`app:ch_regular_base:lem:characteristic-kernel`, are fixed rational functions
of the original matrix pair. Compact-range composition gives one additive
high norm, with constants chosen before that pair and the signed mask.
The complement estimate instantiates the existing primitive inverse producer;
localization preserves every jet on the working ball.

Consumers are `pencilChartRight`, `pencilChartLeft`, `pencilSignedDatum` and
`pencilChartComplement` in the amplitude construction. Bounds for their
primitive matrix pair must still be derived from `Q`, the root and the flow.
No norm bound on a nullvector, signed datum or inverse is assumed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.AmplitudeBounds

open FullPhaseCharts.InverseEstimates

variable {ι E : Type} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The ambient rational domain for the nullvectors in
`app:ch_regular_base:lem:characteristic-kernel`. Its conditions are the two
original denominators, with no characteristic equation required nearby. -/
def minorNullvectorDomain (r c : ι) : Set (Matrix ι ι ℝ × Matrix ι ι ℝ) :=
  {p | p.1.adjugate r c ≠ 0 ∧ minorTransportCoefficient p.1 p.2 r c ≠ 0}

/-- Smoothness near the original-gap compact class, used for the actual
normalized nullvector estimates (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem minorNullvectorDomain_regular (r c : ι) {m : ℕ∞ω} :
    IsOpen (minorNullvectorDomain r c) ∧
      ContDiffOn ℝ m (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦
        minorRightNullvector p.1 r c) (minorNullvectorDomain r c) ∧
      ContDiffOn ℝ m (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦
        minorLeftNullvector p.1 p.2 r c) (minorNullvectorDomain r c) := by
  have hH (i j : ι) : ContDiff ℝ m
      (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ p.1 i j) :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp contDiff_fst
  have hA (i j : ι) : ContDiff ℝ m
      (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ p.2 i j) :=
    (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp contDiff_snd
  have hm : Continuous (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ p.1.adjugate r c) :=
    (continuous_apply c).comp ((continuous_apply r).comp continuous_fst.matrix_adjugate)
  have ht := (contDiff_minorTransportCoefficient_pair r c (m := ∞)).continuous
  exact ⟨(isClosed_eq hm continuous_const).isOpen_compl.inter
      (isClosed_eq ht continuous_const).isOpen_compl,
    contDiffOn_minorRightNullvector r c (fun i j ↦ (hH i j).contDiffOn)
      (fun _ hp ↦ hp.1),
    contDiffOn_minorLeftNullvector r c (fun i j ↦ (hH i j).contDiffOn)
      (fun i j ↦ (hA i j).contDiffOn) (fun _ hp ↦ hp.2)⟩

/-- Joint single-high estimates, without derivative loss, for the actual
normalized nullvectors. The original selected minor and transport gaps and
the primitive matrix value bound determine every constant before the array
(`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem exists_minorNullvectors_cNorm_bounds (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    (r c : ι) (M : ℝ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (V : Set E), IsOpen V → closedBall x ρ ⊆ V →
      ∀ U : E → Matrix ι ι ℝ × Matrix ι ι ℝ,
        ContDiffOn ℝ ∞ U V → MapsTo U (closedBall x ρ) (minorCoefficientClass r c M μ ν) →
        ∀ m,
          cNorm (closedBall x ρ) m (fun y ↦ minorRightNullvector (U y).1 r c) ≤
            C m * (1 + cNorm (closedBall x ρ) m U) ∧
          cNorm (closedBall x ρ) m (fun y ↦ minorLeftNullvector (U y).1 (U y).2 r c) ≤
            C m * (1 + cNorm (closedBall x ρ) m U) := by
  have hs : minorCoefficientClass r c M μ ν ⊆ minorNullvectorDomain r c :=
    fun _ hp ↦ ⟨abs_pos.mp (hμ.trans_le hp.2.2.2.1),
      abs_pos.mp (hν.trans_le hp.2.2.2.2)⟩
  have hk (m : ℕ) := ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
    x hρ (isCompact_minorCoefficientClass r c M μ ν) (le_refl m)
    (fun p hp ↦ (minorNullvectorDomain_regular r c).2.1.contDiffAt
      ((minorNullvectorDomain_regular r c (m := m)).1.mem_nhds (hs hp)))
  have hl (m : ℕ) := ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
    x hρ (isCompact_minorCoefficientClass r c M μ ν) (le_refl m)
    (fun p hp ↦ (minorNullvectorDomain_regular r c).2.2.contDiffAt
      ((minorNullvectorDomain_regular r c (m := m)).1.mem_nhds (hs hp)))
  choose A hA hka using hk
  choose B hB hlb using hl
  refine ⟨fun m ↦ A m + B m, fun m ↦ add_pos (hA m) (hB m), ?_⟩
  intro V hV hball U hU hmap m
  have hn : 0 ≤ 1 + cNorm (closedBall x ρ) m U :=
    add_nonneg zero_le_one (cNorm_nonneg _ _ _)
  exact ⟨(hka m V hV hball U hU hmap).trans
      (mul_le_mul_of_nonneg_right (by linarith [hB m]) hn),
    (hlb m V hV hball U hU hmap).trans
      (mul_le_mul_of_nonneg_right (by linarith [hA m]) hn)⟩

/-- A signed scalar mask times the literal normalized left row has one
additive high contribution from each primitive. Only the mask's value norm
is bounded in advance; no sign or lower bound is imposed on it
(`app:ch_regular_base:lem:characteristic-kernel`, the datum `lᵀσ`). -/
theorem exists_minorSignedDatum_cNorm_bounds (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    (r c : ι) (M S : ℝ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (V : Set E), IsOpen V → closedBall x ρ ⊆ V →
      ∀ (U : E → Matrix ι ι ℝ × Matrix ι ι ℝ) (σ : E → ℝ),
        ContDiffOn ℝ ∞ U V → ContDiffOn ℝ ∞ σ V →
        MapsTo U (closedBall x ρ) (minorCoefficientClass r c M μ ν) →
        cNorm (closedBall x ρ) 0 σ ≤ S →
        ∀ m, cNorm (closedBall x ρ) m
          (fun y ↦ σ y • minorLeftNullvector (U y).1 (U y).2 r c) ≤
            C m * (1 + cNorm (closedBall x ρ) m U + cNorm (closedBall x ρ) m σ) := by
  let K := minorCoefficientClass r c M μ ν ×ˢ closedBall (0 : ℝ) S
  have hK : IsCompact K := (isCompact_minorCoefficientClass r c M μ ν).prod
    (isCompact_closedBall _ _)
  have houter (m : ℕ) (p) (hp : p ∈ K) : ContDiffAt ℝ m
      (fun q : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
        q.2 • minorLeftNullvector q.1.1 q.1.2 r c) p := by
    have hdom : p.1 ∈ minorNullvectorDomain r c :=
      ⟨abs_pos.mp (hμ.trans_le hp.1.2.2.2.1), abs_pos.mp (hν.trans_le hp.1.2.2.2.2)⟩
    exact contDiffAt_snd.smul (((minorNullvectorDomain_regular r c).2.2.contDiffAt
      ((minorNullvectorDomain_regular r c (m := m)).1.mem_nhds hdom)).comp p contDiffAt_fst)
  choose C hC hb using fun m ↦
    ProjectedStressFrame.exists_cNorm_comp_le_tame_closedBall_contDiffOn
      x hρ hK (le_refl m) (houter m)
  refine ⟨C, hC, ?_⟩
  intro V hV hball U σ hU hσ hmap hlow m
  have hlocal (j : ℕ) : ∀ y ∈ closedBall x ρ, ContDiffAt ℝ j σ y :=
    fun y hy ↦ (hσ.contDiffAt (hV.mem_nhds (hball hy))).of_le (by simp)
  have hm : MapsTo (fun y ↦ (U y, σ y)) (closedBall x ρ) K := by
    intro y hy
    refine ⟨hmap hy, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    have hs0 : ‖σ y‖ ≤ cNorm (closedBall x ρ) 0 σ := by
      simpa only [norm_iteratedFDeriv_zero] using
        norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall x ρ)
          (hlocal 0) hy (le_refl 0)
    exact hs0.trans hlow
  have hn := cNorm_prodMk_le_on (closedBall x ρ) (isCompact_closedBall _ _) m
    (fun y hy ↦ (hU.contDiffAt (hV.mem_nhds (hball hy))).of_le (by simp)) (hlocal m)
  exact (hb m V hV hball (fun y ↦ (U y, σ y)) (hU.prodMk hσ) hm).trans
    (mul_le_mul_of_nonneg_left (by linarith) (hC m).le)

/-- The zero-displacement complement needed by the correction column obeys
the original primitive inverse estimate on any open enlargement of the
working ball. This explicitly instantiates
`exists_minorComplementInverse_primitive_tame`; the inverse is not an input
(`app:ch_regular_base:eq:two-term-null-identity`). -/
theorem exists_minorComplement_cNorm_bounds (x : E) {ρ : ℝ} (hρ : 0 < ρ)
    (r c : ι) (M : ℝ) {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧
      ∀ (V : Set E), IsOpen V → closedBall x ρ ⊆ V →
      ∀ U : E → Matrix ι ι ℝ × Matrix ι ι ℝ,
        ContDiffOn ℝ ∞ U V → MapsTo U (closedBall x ρ) (minorCoefficientClass r c M μ ν) →
        ∀ m, cNorm (closedBall x ρ) m
          (fun y ↦ minorComplementInverse (U y).1 (U y).2 r c 0) ≤
            C m * (1 + cNorm (closedBall x ρ) m U) := by
  obtain ⟨ε, hε, _, _, C, hC, _, _, hb⟩ :=
    exists_minorComplementInverse_primitive_tame x hρ r c M hμ hν
  refine ⟨C, hC, ?_⟩
  intro V hV hball U hU hmap m
  obtain ⟨U', hU', _, _, he⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall x hρ hV hball hU
  have hmap' : MapsTo (fun y ↦ (U' y, (0 : ℝ))) (closedBall x ρ)
      (minorCoefficientClass r c M μ ν ×ˢ closedBall (0 : ℝ) ε) := by
    intro y hy
    refine ⟨?_, mem_closedBall_self hε.le⟩
    change U' y ∈ minorCoefficientClass r c M μ ν
    rw [(he y hy).eq_of_nhds]
    exact hmap hy
  have hn : cNorm (closedBall x ρ) m (fun y ↦ (U' y, (0 : ℝ))) ≤
      cNorm (closedBall x ρ) m U' := by
    simpa only [show (fun _ : E ↦ (0 : ℝ)) = (0 : E → ℝ) from rfl,
      cNorm_zero, add_zero] using
      cNorm_prodMk_le_on (closedBall x ρ) (isCompact_closedBall _ _) m
      (fun _ _ ↦ hU'.contDiffAt.of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
      (fun _ _ ↦ contDiffAt_const (c := (0 : ℝ)))
  have hnorm := GeometricProfile.cNorm_eq_of_eventuallyEq he m
  have hout := GeometricProfile.cNorm_eq_of_eventuallyEq
    (fun y hy ↦ (he y hy).fun_comp
      (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ minorComplementInverse p.1 p.2 r c 0)) m
  change cNorm (closedBall x ρ) m (fun y ↦ minorComplementInverse (U' y).1 (U' y).2 r c 0) =
    cNorm (closedBall x ρ) m (fun y ↦ minorComplementInverse (U y).1 (U y).2 r c 0) at hout
  have hh := (hb m (fun y ↦ (U' y, (0 : ℝ))) (hU'.prodMk contDiff_const) hmap').trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl hn) (hC m).le)
  simpa only [hout, hnorm] using hh

end JanetCartan.RegularSector.Characteristic.AmplitudeBounds
