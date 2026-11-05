module

public import JanetCartan.Analysis.Microlocal.FullSourceStationary.SourceDomain
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.FixedPullback

/-!
# Actual full-source phase profiles

The original full Hamilton phase, pulled back by the fixed physical coordinate
permutation, retains coefficient shift one and history reserve `Rstar + 3`.
Every derivative includes the independent full source parameters. Consumers:
the full-source stationary and Hessian constructions, and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ConstructedCarrierJets
open ResponseTransfer.RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles
open LeadingWave.FullModulation

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)
local notation "Param" => Euclidean 3 × Euclidean d

/-- Smoothness of the original source phase on any open coordinate domain
mapping to its literal full phase domain. The source label and covector remain
independent (`app:ch_response:eq:response-exact-phase`). -/
theorem fullSourcePhaseInCoordinates_smooth (i : Fin (d + 1)) (Q : _)
    {Ω : Set (E × Param)}
    (hΩ : ∀ q ∈ Ω, ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T) :
    ContDiffOn ℝ ∞ (fun q ↦ T.fullSourcePhaseInCoordinates i Q q.1 q.2) Ω :=
  (phase_smooth T Q).comp
    (((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk
      contDiff_snd.snd).contDiffOn
    (fun q hq ↦ ball_subset_ball (by linarith [T.family.radius_pos] :
      T.family.radius ≤ 2 * T.family.radius) (hΩ q hq))

/-- The literal full source has coefficient order `m+1` on every supplied
compact carrier. The fixed pullback drops only the spectator label, leaving
the covector independent; the bound is the actual current Hamilton phase bound
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_fullSourcePhaseInCoordinates_frame_bound (i : Fin (d + 1))
    {K : Set (E × Param)} (hK : IsCompact K)
    (hKD : ∀ q ∈ K, ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧ ∀ Q m,
      cNorm K m (fun q ↦ T.fullSourcePhaseInCoordinates i Q q.1 q.2) ≤ A m *
        (1 + cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (m + 1) Q.1) := by
  let ψ : E × Param → E × (ℝ × Euclidean d) :=
    fun q ↦ ((primaryCoordinateChange i).symm q.1, (0, q.2.2))
  let J := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  have hψ : ContDiff ℝ ∞ ψ :=
    ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk
      (contDiff_const.prodMk contDiff_snd.snd)
  have hψJ : MapsTo ψ K J := by
    intro q hq
    apply ball_subset_closedBall
    exact (LeadingWave.FullModulation.inclusion_mem_ball T
      (w := ((primaryCoordinateChange i).symm q.1, q.2.2))).mpr (hKD q hq)
  obtain ⟨B, hB, hb⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK
    (isCompact_closedBall _ _) (fun _ _ ↦ hψ.contDiffAt) hψJ
  refine ⟨fun m ↦ B m * T.family.coefficient m,
    fun m ↦ mul_pos (hB m) (T.family.coefficient_pos m), ?_⟩
  intro Q m
  let F := HamiltonPhase.phase (T.currentChart Q).coordinates
  have hF : ∀ q ∈ J, ContDiffAt ℝ ∞ F q := fun q hq ↦
    (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius < 2 * T.family.radius) hq))
  change cNorm K m (F ∘ ψ) ≤ _
  exact (hb F hF m).trans ((mul_le_mul_of_nonneg_left
    (T.current_phase_bound Q m) (hB m).le).trans_eq (by ring))

/-- The SAME admissible history supplies all-order full-source profiles with
the original reserve `Rstar+3`. Constants precede the history, its length, and
the derivative order; no covector is identified with a carrier-graph value
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_full_source_phase_profiles (i : Fin (d + 1))
    {K : Set (E × Param)} (hK : IsCompact K)
    (hKD : ∀ q ∈ K, ((primaryCoordinateChange i).symm q.1, q.2.2) ∈ phaseDomain T)
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar Rstar kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : Rstar + 3 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (n : ℕ) (u : Fin n → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin n → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
      ∀ m, cNorm K m (fun q ↦ T.fullSourcePhaseInCoordinates i Q q.1 q.2) ≤
        A m * currentCoefficientScale R₀ n ^ (m - Rstar) := by
  obtain ⟨S, hS, AQ, _AB, hAQ, _, hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles G hr hrR hR ext
      hextcenter hextradius hStar (reserve := Rstar + 1) (by omega) horder
  obtain ⟨B, hB, hb⟩ := T.exists_fullSourcePhaseInCoordinates_frame_bound i hK hKD
  refine ⟨S, hS, fun m ↦ B m * (1 + AQ (m + 1)),
    fun m ↦ mul_nonneg (hB m).le (by linarith [hAQ (m + 1)]), ?_⟩
  intro R₀ hR₀ n u ell hu Q hQ m
  have hL : 1 ≤ currentCoefficientScale R₀ n :=
    one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) n
  have h1 := one_le_pow₀ hL (n := m - Rstar)
  have hc := ((hcoeff R₀ hR₀ n u ell hu).2.2
    (closedBall (0 : E) T.data.localReference.stateRadius) (isCompact_closedBall _ _)).1 (m + 1)
  have hframe : cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (m + 1) Q.1 ≤
      AQ (m + 1) * currentCoefficientScale R₀ n ^ (m - Rstar) := by
    rw [hQ]
    simpa only [show m + 1 - (Rstar + 1) = m - Rstar by omega] using hc
  apply (hb Q m).trans
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 hframe) (hB m).le]

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
