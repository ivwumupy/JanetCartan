module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.SectionRoots
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.FlowStability
public import JanetCartan.Analysis.Microlocal.HamiltonPhase.FiniteOrderContinuity.Composition

/-!
# Constructed root-initialized flows with finite-order continuity

For `app:lem:common-hamilton-phase`, construct roots and phase-space flows on
common domains, retaining the root cylinder. Their finite-order comparison
and the composition estimate yield continuity of the actual section flow.
The consumer is the buffered projection-chart and phase assembly.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff InnerProductSpace
namespace JanetCartan.HamiltonPhase

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]

/-- `app:lem:common-hamilton-phase`: actual common roots and Hamilton flows,
with continuity of the root, joint flow and root-initialized section flow.
All compact sets and the `C³` existence neighborhood precede the perturbation.
For every `m` and accuracy, a scalar-symbol `C^(m+1)` tolerance controls all
three differences. The differentiated root and ODE estimates are instantiated;
no finite-order closeness is supplied as a premise. The comparison applies to
any smooth root in the retained interval and any actual common ODE flow. -/
theorem exists_common_finiteOrder_rootedFlows
    (H₀ : HomogeneousSymbol E) {D : Set (E × E)} (hD : IsOpen D)
    (hDH₀ : D ⊆ H₀.domain) (hH₀ : ContDiffOn ℝ ∞ H₀.h D)
    (j : U →ₗᵢ[ℝ] E) (ν : E) {s₀ : InitialData U} {τ₀ R : ℝ}
    (hR : 0 < R)
    (hRD : closedBall (transverseSectionState j ν (s₀, τ₀)) R ⊆ D)
    (henergy : H₀.h (transverseSectionState j ν (s₀, τ₀)) = s₀.2.1)
    (htrans : ⟪H₀.hp (transverseSectionState j ν (s₀, τ₀)), ν⟫_ℝ ≠ 0) :
    let z₀ := transverseSectionState j ν (s₀, τ₀)
    ∃ (r a ρ T δ : ℝ) (g₀ : InitialData U → ℝ) (Ψ₀ : (E × E) × ℝ → E × E),
      0 < r ∧ 0 < a ∧ 0 < ρ ∧ 0 < T ∧ 0 < δ ∧
      g₀ s₀ = τ₀ ∧ ODE.IsSmoothFlowOn H₀.vectorField z₀ R ρ T Ψ₀ ∧
      MapsTo (transverseSectionState j ν)
        (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) (ball z₀ (ρ / 2)) ∧
      ContDiffOn ℝ ∞ g₀ (ball s₀ (2 * r)) ∧
      (∀ s ∈ ball s₀ (2 * r), g₀ s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
        H₀.h (transverseSectionState j ν (s, g₀ s)) = s.2.1) ∧
      (∀ m : ℕ, ∀ ε > (0 : ℝ), ∃ d > (0 : ℝ),
        ∀ (H : HomogeneousSymbol E) (g : InitialData U → ℝ) (Ψ : (E × E) × ℝ → E × E),
          D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
          ODE.IsSmoothFlowOn H.vectorField z₀ R ρ T Ψ →
          ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) →
          (∀ s ∈ ball s₀ (2 * r), g s ∈ Icc (τ₀ - a) (τ₀ + a) ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1) →
          cNorm (closedBall z₀ R) (m + 1) (fun z ↦ H.h z - H₀.h z) < d →
          cNorm (closedBall s₀ r) m (g - g₀) +
            cNorm (closedBall z₀ (ρ / 2) ×ˢ Icc (-(T / 2)) (T / 2)) m (Ψ - Ψ₀) +
            cNorm (Icc (-(T / 2)) (T / 2) ×ˢ closedBall s₀ r) m
              (sectionFlowState j ν g Ψ - sectionFlowState j ν g₀ Ψ₀) < ε) ∧
      ∀ H : HomogeneousSymbol E, D ⊆ H.domain → ContDiffOn ℝ ∞ H.h D →
        cNorm (closedBall z₀ R) 3 (fun z ↦ H.h z - H₀.h z) ≤ δ →
        ∃ (g : InitialData U → ℝ) (Ψ : (E × E) × ℝ → E × E),
          ODE.IsSmoothFlowOn H.vectorField z₀ R ρ T Ψ ∧
          ContDiffOn ℝ ∞ g (ball s₀ (2 * r)) ∧
          (∀ s ∈ ball s₀ (2 * r), g s ∈ Ioo (τ₀ - a) (τ₀ + a) ∧
            H.h (transverseSectionState j ν (s, g s)) = s.2.1) ∧
          ContDiffOn ℝ ∞ (sectionFlowState j ν g Ψ) (Ioo (-T) T ×ˢ ball s₀ (2 * r)) := by
  let z₀ := transverseSectionState j ν (s₀, τ₀)
  obtain ⟨ρ, hρ, T, hT, Cf, _hCf, δf, hδf, Ψ₀, hΨ₀, hflows⟩ :=
    exists_common_symbol_flows H₀ hD hDH₀ hR hRD hH₀
  let D' := D ∩ ball z₀ (min R (ρ / 2))
  have hD' : IsOpen D' := hD.inter isOpen_ball
  have hbase : z₀ ∈ D' :=
    ⟨hRD (mem_closedBall_self hR.le), mem_ball_self (lt_min hR (half_pos hρ))⟩
  have hD'R : D' ⊆ closedBall z₀ R := fun _ hz ↦
    ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hz.2)
  obtain ⟨r, a, δr, g₀, hr, ha, hδr, hgbase, hmap, hg₀, hroot₀, hrootclose, hroots⟩ :=
    exists_common_finiteOrder_sectionRoots H₀ hD hD' inter_subset_left hD'R
      (isCompact_closedBall _ _) hRD hDH₀ hH₀ j ν hbase henergy htrans
  have hmapρ : MapsTo (transverseSectionState j ν)
      (closedBall s₀ (2 * r) ×ˢ Icc (τ₀ - a) (τ₀ + a)) (ball z₀ (ρ / 2)) :=
    fun _ hz ↦ ball_subset_ball (min_le_right _ _) (hmap hz).2
  let P := closedBall s₀ r
  let Q := Icc (-(T / 2)) (T / 2) ×ˢ P
  let L := closedBall z₀ (ρ / 2) ×ˢ Icc (-(T / 2)) (T / 2)
  have hP : IsCompact P := isCompact_closedBall _ _
  have hQ : IsCompact Q := isCompact_Icc.prod hP
  have hL : IsCompact L := (isCompact_closedBall _ _).prod isCompact_Icc
  have hPsub : P ⊆ ball s₀ (2 * r) := closedBall_subset_ball (by linarith)
  have hLsub : L ⊆ ball z₀ ρ ×ˢ Ioo (-T) T := by
    intro z hz
    exact ⟨closedBall_subset_ball (by linarith) hz.1,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hinput (g : InitialData U → ℝ)
      (hg : ∀ s ∈ ball s₀ (2 * r), g s ∈ Icc (τ₀ - a) (τ₀ + a)) :
      MapsTo (sectionFlowInput j ν g) Q L := by
    intro q hq
    exact ⟨ball_subset_closedBall (hmapρ
      ⟨ball_subset_closedBall (hPsub hq.2), hg _ (hPsub hq.2)⟩), hq.1⟩
  refine ⟨r, a, ρ, T, min δf δr, g₀, Ψ₀, hr, ha, hρ, hT,
    lt_min hδf hδr, hgbase, hΨ₀, hmapρ, hg₀, hroot₀, ?_, ?_⟩
  · intro m ε hε
    have hε3 : 0 < ε / 3 := by positivity
    obtain ⟨dc, hdc, hcomp⟩ := SectionEnergy.exists_cNorm_sectionFlowState_sub_lt j ν
      hQ hP hL (fun _ hq ↦ hq.2)
      (fun s hs ↦ (hg₀.contDiffAt (isOpen_ball.mem_nhds (hPsub hs))).of_le (by simp))
      (fun z hz ↦ (hΨ₀.smooth.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
        (hLsub hz))).of_le (by simp))
      (hinput g₀ (fun s hs ↦ Ioo_subset_Icc_self (hroot₀ s hs).1)) (m := m) hε3
    have hac : 0 < min dc (ε / 3) := lt_min hdc hε3
    obtain ⟨dr, hdr, hrclose⟩ := hrootclose m (min dc (ε / 3)) hac
    obtain ⟨df, hdf, hfclose⟩ := exists_cNorm_hamiltonFlow_sub_lt H₀ hD hRD hDH₀ hH₀
      hΨ₀ (half_pos hρ) (by linarith : ρ / 2 < ρ)
      (half_pos hT) (by linarith : T / 2 < T) m hac
    refine ⟨min dr df, lt_min hdr hdf, ?_⟩
    intro H g Ψ hDH hH hΨ hg hroot hsmall
    have hgr := hrclose H g hH hg hroot (hsmall.trans_le (min_le_left _ _))
    have hfr := hfclose H Ψ hDH hH hΨ (hsmall.trans_le (min_le_right _ _))
    have hsc := hcomp g Ψ
      (fun s hs ↦ (hg.contDiffAt (isOpen_ball.mem_nhds (hPsub hs))).of_le (by simp))
      (fun z hz ↦ (hΨ.smooth.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
        (hLsub hz))).of_le (by simp))
      (hinput g (fun s hs ↦ (hroot s hs).1))
      (hgr.trans_le (min_le_left _ _)) (hfr.trans_le (min_le_left _ _))
    have hgr' := hgr.trans_le (min_le_right _ _)
    have hfr' := hfr.trans_le (min_le_right _ _)
    change cNorm P m (g - g₀) + cNorm L m (Ψ - Ψ₀) +
      cNorm Q m (sectionFlowState j ν g Ψ - sectionFlowState j ν g₀ Ψ₀) < ε
    linarith
  · intro H hDH hH hsmall
    obtain ⟨g, hg, hroot, _huniq⟩ := hroots H hH (hsmall.trans (min_le_right _ _))
    obtain ⟨Ψ, hΨ, _hclose⟩ := hflows H hDH hH (hsmall.trans (min_le_left _ _))
    refine ⟨g, Ψ, hΨ, hg, hroot, ?_⟩
    exact (sectionFlowState_properties H j ν hΨ hg (fun s hs ↦
      ball_subset_ball (by linarith : ρ / 2 ≤ ρ)
        (hmapρ ⟨ball_subset_closedBall hs, Ioo_subset_Icc_self (hroot s hs).1⟩))).1

end JanetCartan.HamiltonPhase
