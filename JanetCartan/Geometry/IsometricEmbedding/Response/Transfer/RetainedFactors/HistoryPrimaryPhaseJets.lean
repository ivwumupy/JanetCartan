module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Response.Compatible.PrimaryCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.Restriction

/-!
# Original history grades for the same primary phase

The literal primary phase in the retained time-first coordinates is a fixed
smooth pullback of the original full-energy phase. Its order `m` therefore
uses coefficient order `m+1`, with no further loss. The actual admissible
history supplies that coefficient profile with map reserve `Rstar+3`.

Consumer: the primary terms in the primitive modulated-phase grade for
`app:ch_response:eq:direct-envelope-profile`. This does not choose the common
supported carrier or prove that a history lies in the primary family's fixed
low neighborhood; it preserves that original subtype and its literal field.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu CompatibleResponse ConstructedCarrierJets
open ResponseTransfer.RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles

variable {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
local notation "E" => Euclidean (d + 1)

/-- The ORIGINAL primary phase in the retained coordinate order has frame
shift one on every compact primary carrier. Constants precede the current
frame; all parameter derivatives are joint derivatives of the same phase.
The proof applies the fixed pullback bound to `current_phase_bound`, rather
than assuming a primary-phase profile
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_primaryPhaseInCoordinates_frame_bound
    {c C : ℝ} (hP : P.IsValid c C) (i : Fin (d + 1))
    {K : Set (E × Euclidean 3)} (hK : IsCompact K)
    (hKU : ∀ q ∈ K, (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
      q.2 ∈ parameterInterior (2 * P.radius)) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧ ∀ Q m,
      cNorm K m (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2) ≤ A m *
        (1 + cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (m + 1) Q.1) := by
  let F : E × Euclidean 3 → E × Euclidean 3 := fun q ↦ ((primaryCoordinateChange i).symm q.1, q.2)
  let ψ := T.carrierRestriction ∘ F
  let J := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  have hF : ContDiff ℝ ∞ F :=
    ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd
  have hψ : ∀ q ∈ K, ContDiffAt ℝ ∞ ψ q := by
    intro q hq
    have hFq : F q ∈ ball (0 : E) T.physicalRadius ×ˢ parameterInterior (2 * P.radius) := hKU q hq
    have houter : ContDiffAt ℝ ∞ T.carrierRestriction (F q) :=
      (T.carrierRestriction_smooth hP).contDiffAt
        ((isOpen_ball.prod (isOpen_parameterInterior (2 * P.radius))).mem_nhds hFq)
    exact houter.comp q hF.contDiffAt
  have hψJ : MapsTo ψ K J := by
    intro q hq
    exact ball_subset_closedBall (T.reference.target_contains _ (hKU q hq).1 _ (hKU q hq).2)
  obtain ⟨B, hB, hb⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK
    (isCompact_closedBall _ _) hψ hψJ
  refine ⟨fun m ↦ B m * T.family.coefficient m,
    fun m ↦ mul_pos (hB m) (T.family.coefficient_pos m), ?_⟩
  intro Q m
  let S := phase (T.currentChart Q).coordinates
  have hS : ∀ q ∈ J, ContDiffAt ℝ ∞ S q := fun q hq ↦
    (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius < 2 * T.family.radius) hq))
  change cNorm K m (S ∘ ψ) ≤ _
  exact (hb S hS m).trans ((mul_le_mul_of_nonneg_left
    (T.current_phase_bound Q m) (hB m).le).trans_eq (by ring))

/-- Admissible histories supply the actual joint primary-phase grade
`L^(m-Rstar)` with fixed map reserve `Rstar+3`. The phase is the original
`T.currentChart` carrier at the SAME extended projected-stress field, identified
by `hQ`. All constants precede histories, orders, samples and frequencies.
No power of the envelope scale `K` is spent, so this retains the original
`1 ≤ L ≤ K ≤ λ^(1-ν)` contract
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_admissible_history_primary_phase_profiles
    {c C : ℝ} (hP : P.IsValid c C) (i : Fin (d + 1))
    {K : Set (E × Euclidean 3)} (hK : IsCompact K)
    (hKU : ∀ q ∈ K, (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
      q.2 ∈ parameterInterior (2 * P.radius))
    (G : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters E) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar Rstar kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : Rstar + 3 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap G.map u) →
      ∀ m, cNorm K m (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2) ≤
        A m * currentCoefficientScale R₀ s ^ (m - Rstar) := by
  obtain ⟨S, hS, AQ, AB, hAQ, _, hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles G hr hrR hR ext
      hextcenter hextradius hStar (reserve := Rstar + 1) (by omega) horder
  obtain ⟨B, hB, hb⟩ := T.exists_primaryPhaseInCoordinates_frame_bound hP i hK hKU
  refine ⟨S, hS, fun m ↦ B m * (1 + AQ (m + 1)),
    fun m ↦ mul_nonneg (hB m).le (by linarith [hAQ (m + 1)]), ?_⟩
  intro R₀ hR₀ s u ell hu Q hQ m
  have hL : 1 ≤ currentCoefficientScale R₀ s :=
    one_le_currentCoefficientScale (by linarith : 1 ≤ R₀) s
  have h1 := one_le_pow₀ hL (n := m - Rstar)
  have hc := ((hcoeff R₀ hR₀ s u ell hu).2.2
    (closedBall (0 : E) T.data.localReference.stateRadius) (isCompact_closedBall _ _)).1 (m + 1)
  have hframe : cNorm (closedBall (0 : E) T.data.localReference.stateRadius) (m + 1) Q.1 ≤
      AQ (m + 1) * currentCoefficientScale R₀ s ^ (m - Rstar) := by
    rw [hQ]
    simpa only [show m + 1 - (Rstar + 1) = m - Rstar by omega] using hc
  apply (hb Q m).trans
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add h1 hframe) (hB m).le]

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
