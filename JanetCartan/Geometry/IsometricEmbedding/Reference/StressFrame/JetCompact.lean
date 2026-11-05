module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.Jet

/-!
# A compact admissible range for the stress second jet

The low jet bound and the two separate gaps from
`app:ch_seed:setup:seed-current` give a compact range on which both inverse
arguments in the projected stress coefficient are units. This supplies the
compact range needed for `app:ch_seed:eq:seed-frame-tame`.

The ambient operator is continuous on the closed metric-gap locus. Its
quantitative lower-bound condition is closed relative to that locus, so the
admissible range is a closed subset of a finite-dimensional closed ball.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius JanetCartan.StressFrame

namespace JanetCartan.ProjectedStressFrame

/-- The quantitative metric gap makes the jet metric invertible
(`app:ch_seed:setup:seed-current`). -/
theorem isUnit_jetMetric_of_lower_bound {n N : ℕ} {J : StressJet n N}
    {κmet : ℝ} (hκmet : 0 < κmet)
    (hgap : ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖J.1 v‖ ^ 2) : IsUnit (jetMetric J) := by
  refine (isUnit_and_norm_inverse_le_of_energy (jetMetric J)
    (inv_nonneg.mpr hκmet.le) ?_).1
  intro v
  rw [jetMetric, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
  exact (le_inv_mul_iff₀ hκmet).mpr (hgap v)

/-- The quantitative ambient lower bound forces a trivial kernel and hence
invertibility in finite dimension (`app:ch_seed:setup:seed-current`). -/
theorem isUnit_jetAmbient_of_lower_bound {n N : ℕ} {J : StressJet n N}
    {L : ℝ} (hbound : ∀ w, ‖w‖ ≤ L * ‖jetAmbient J w‖) :
    IsUnit (jetAmbient J) := by
  have hinj : Function.Injective (jetAmbient J) := by
    apply (injective_iff_map_eq_zero (jetAmbient J)).mpr
    intro w hw
    have h := hbound w
    rw [hw, norm_zero, mul_zero] at h
    exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- Jets satisfying the low norm bound and the separate metric and ambient
lower bounds for `app:ch_seed:eq:seed-frame-tame`. The definition imposes only
quantitative inequalities, with no compactness or invertibility assumptions. -/
def admissibleStressJets (n N : ℕ) (M κmet L : ℝ) : Set (StressJet n N) :=
  {J | ‖J‖ ≤ M ∧ (∀ v, κmet * ‖v‖ ^ 2 ≤ ‖J.1 v‖ ^ 2) ∧
    ∀ w, ‖w‖ ≤ L * ‖jetAmbient J w‖}

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in
/-- A positive metric gap makes the bounded admissible jet range compact
(`app:ch_seed:eq:seed-frame-tame`). Nonnegativity of `M` and `L` is not needed
for this compactness statement. -/
theorem isCompact_admissibleStressJets {n N : ℕ} (M : ℝ) {κmet : ℝ}
    (hκmet : 0 < κmet) (L : ℝ) : IsCompact (admissibleStressJets n N M κmet L) := by
  let : ProperSpace (StressJet n N) := FiniteDimensional.proper ℝ (StressJet n N)
  let s : Set (StressJet n N) := {J | ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖J.1 v‖ ^ 2}
  have hs : IsClosed s := by
    simp only [s, Set.ofPred_forall]
    exact isClosed_iInter fun v ↦ isClosed_le continuous_const
      ((continuous_fst.clm_apply continuous_const).norm.pow 2)
  have hA : ContinuousOn (@jetAmbient n N) s := by
    intro J hJ
    exact (contDiffAt_jetAmbient
      (isUnit_jetMetric_of_lower_bound hκmet hJ)).continuousAt.continuousWithinAt
  have hc (w : Euclidean N) : IsClosed {J ∈ s | ‖w‖ ≤ L * ‖jetAmbient J w‖} :=
    hs.isClosed_le continuousOn_const
      (continuousOn_const.mul ((hA.clm_apply continuousOn_const).norm))
  have hall : IsClosed {J : StressJet n N | J ∈ s ∧ ∀ w, ‖w‖ ≤ L * ‖jetAmbient J w‖} := by
    have h := isClosed_iInter hc
    simpa only [Set.iInter_ofPred, forall_and, forall_const] using h
  have hball : IsCompact (Metric.closedBall (0 : StressJet n N) M) :=
    isCompact_closedBall _ _
  have hcompact := hball.inter_right hall
  convert hcompact using 1
  ext J
  simp only [admissibleStressJets, Set.mem_ofPred_eq, Set.mem_inter_iff,
    Metric.mem_closedBall, s]
  rw [show dist J 0 = ‖J‖ from dist_zero_right J]

/-- The low bound and the separate quantitative gaps supply a compact range
containing every admissible jet, with both inverse arguments units throughout
the range (`app:ch_seed:setup:seed-current`, `app:ch_seed:eq:seed-frame-tame`). -/
theorem exists_compact_stressJet_range {n N : ℕ} {M κmet L : ℝ}
    (_hM : 0 ≤ M) (hκmet : 0 < κmet) (_hL : 0 ≤ L) :
    ∃ t : Set (StressJet n N), IsCompact t ∧
      (∀ J : StressJet n N, ‖J‖ ≤ M →
        (∀ v, κmet * ‖v‖ ^ 2 ≤ ‖J.1 v‖ ^ 2) →
        (∀ w, ‖w‖ ≤ L * ‖jetAmbient J w‖) → J ∈ t) ∧
      (∀ J ∈ t, IsUnit (jetMetric J)) ∧
      (∀ J ∈ t, IsUnit (jetAmbient J)) := by
  refine ⟨admissibleStressJets n N M κmet L,
    isCompact_admissibleStressJets M hκmet L, ?_, ?_, ?_⟩
  · intro J hJ hgap hbound
    exact ⟨hJ, hgap, hbound⟩
  · intro J hJ
    exact isUnit_jetMetric_of_lower_bound hκmet hJ.2.1
  · intro J hJ
    exact isUnit_jetAmbient_of_lower_bound hJ.2.2

end JanetCartan.ProjectedStressFrame
