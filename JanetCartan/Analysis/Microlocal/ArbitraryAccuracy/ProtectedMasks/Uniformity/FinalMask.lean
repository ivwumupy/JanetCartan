module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ProtectedMasks.Uniformity.CanonicalBounds

/-!
# A common final physical proof mask

The common angular margin from `ProtectedFlow.exists_initialized_signed_no_return`
and the annular bounds from `exists_uniform_physicalDirectRelation_bounds_of_section`
give a compact envelope in finite-dimensional physical phase space. A single
smooth mask covers this envelope, with a positive shoulder and all derivative
constants fixed before the current coefficient field. No compactness of the
coefficient class is used.

Consumer: the final physical mask in `app:ch_regular:lem:finite-chain`.
The uniform intermediate relation buffers are a separate obligation.
-/

@[expose] public noncomputable section

open Set Metric Filter
open scoped ContDiff Topology

namespace JanetCartan.ArbitraryAccuracy.ProtectedMasks

open ProtectedFlow FiniteChain.Graph

variable {d : ℕ}

/-- The common endpoint envelope, formed from physical base, annular and
angular bounds chosen before the current field
(`app:ch_regular:lem:finite-chain`, protected finite-chain paragraph). -/
def protectedAnnularCarrier (B : Set (Euclidean (d + 1))) (a b ε : ℝ)
    (Γ : Set (Euclidean (d + 1))) : Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
  {p | p ∈ B ×ˢ PhysicalShells.frequencyAnnulus a b ∧
    closedBall (normalizedCovector p.2) ε ⊆ Γ}

/-- The endpoint envelope is compact in physical phase space, independently
of whether the varying coefficient class is compact
(`app:ch_regular:lem:finite-chain`). -/
theorem isCompact_protectedAnnularCarrier
    {B Γ : Set (Euclidean (d + 1))} (hB : IsCompact B) (hΓ : IsClosed Γ)
    {a b ε : ℝ} (ha : 0 < a) (hε : 0 ≤ ε) :
    IsCompact (protectedAnnularCarrier B a b ε Γ) := by
  let D : Set (Euclidean (d + 1) × Euclidean (d + 1)) :=
    B ×ˢ PhysicalShells.frequencyAnnulus a b
  have hD : IsCompact D := hB.prod (PhysicalShells.isCompact_frequencyAnnulus a b)
  have hn : ContinuousOn (fun p : Euclidean (d + 1) × Euclidean (d + 1) ↦
      normalizedCovector p.2) D := by
    apply (continuous_snd.norm.continuousOn.inv₀ ?_).smul continuous_snd.continuousOn
    intro p hp
    exact ne_of_gt (ha.trans_le hp.2.1)
  have hclosed : IsClosed (⋂ v ∈ closedBall (0 : Euclidean (d + 1)) ε,
      D ∩ {p | normalizedCovector p.2 + v ∈ Γ}) := by
    apply isClosed_biInter
    intro v _
    exact (hn.add continuousOn_const).preimage_isClosed_of_isClosed hD.isClosed hΓ
  have heq : protectedAnnularCarrier B a b ε Γ =
      ⋂ v ∈ closedBall (0 : Euclidean (d + 1)) ε,
        D ∩ {p | normalizedCovector p.2 + v ∈ Γ} := by
    ext p
    simp only [protectedAnnularCarrier, mem_ofPred_eq, mem_iInter, mem_inter_iff]
    constructor
    · intro hp v hv
      refine ⟨hp.1, hp.2 ?_⟩
      simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hv
    · intro hp
      refine ⟨(hp 0 (by simpa only [mem_closedBall, dist_self] using hε)).1, ?_⟩
      intro w hw
      have hv : w - normalizedCovector p.2 ∈ closedBall (0 : Euclidean (d + 1)) ε := by
        simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hw
      simpa only [add_sub_cancel] using (hp _ hv).2
  apply hD.of_isClosed_subset (heq ▸ hclosed)
  exact fun _ hp ↦ hp.1

/-- The retained positive angular margin puts the entire common envelope
strictly inside the final physical cone (`app:ch_regular:thm:no-return`). -/
theorem protectedAnnularCarrier_subset_protectedRegion
    {B Γ : Set (Euclidean (d + 1))} {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    protectedAnnularCarrier B a b ε Γ ⊆ physicalProtectedRegion Γ := by
  intro p hp
  refine ⟨norm_pos_iff.mp (ha.trans_le hp.1.2.1), ?_⟩
  exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (closedBall_mem_nhds _ hε) hp.2)

/-- A single final physical mask, its positive closed shoulder, its annulus,
and ALL derivative constants are chosen from the fixed primitive envelopes.
Every subset of the common endpoint envelope is covered with the same width.
This constructs the final-mask part of `app:ch_regular:lem:finite-chain`;
it does not assert uniform nesting of the intermediate masks. -/
theorem exists_common_protectedAnnularLocalizer
    {B Γ : Set (Euclidean (d + 1))} (hB : IsCompact B) (hΓ : IsClosed Γ)
    {a b ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ (m : LocalizerSymbol (d + 1)) (δ c C R : ℝ) (H : ℕ → ℝ),
      IsBufferedLocalizer m (protectedAnnularCarrier B a b ε Γ)
        (physicalProtectedRegion Γ) ∧
      0 < δ ∧ 0 < c ∧ c < C ∧ 0 < R ∧
      tsupport m ⊆ closedBall 0 R ×ˢ PhysicalShells.frequencyAnnulus c C ∧
      (∀ k, 0 ≤ H k) ∧ (∀ k p, ‖iteratedFDeriv ℝ k m p‖ ≤ H k) ∧
      ∀ S ⊆ protectedAnnularCarrier B a b ε Γ,
        cthickening δ S ⊆ interior {p | m p = 1} := by
  have hK := isCompact_protectedAnnularCarrier (b := b) hB hΓ ha hε.le
  obtain ⟨m, hm, hr, hc, hs, hp⟩ := CompatibleResponse.exists_compact_family_cutoff hK
    (isOpen_physicalProtectedRegion Γ) (protectedAnnularCarrier_subset_protectedRegion ha hε)
  have hm' : IsBufferedLocalizer m (protectedAnnularCarrier B a b ε Γ)
      (physicalProtectedRegion Γ) := ⟨hm, hr, hc, hs, hp⟩
  obtain ⟨δ, hδ, hδplateau⟩ := hK.exists_cthickening_subset_open isOpen_interior hp
  obtain ⟨B', c, C, _, hcc, hcC, hsupport⟩ :=
    EvolutionLocalization.exists_elapsed_localizer_annular_carrier hm' (fun _ hp ↦ hp.1)
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuousOn
    (continuous_fst.continuousOn : ContinuousOn (Prod.fst :
      Euclidean (d + 1) × Euclidean (d + 1) → Euclidean (d + 1)) (tsupport m))
  choose H hH hbound using fun k ↦ hc.exists_bound_iteratedFDeriv hm k
  refine ⟨m, δ, c, C, max R 0 + 1, H, hm', hδ, hcc, hcC,
    by positivity, ?_, hH, fun k p ↦ hbound k k le_rfl p, ?_⟩
  · intro p hp
    refine ⟨?_, (hsupport hp).2⟩
    rw [mem_closedBall, dist_zero_right]
    exact (hR p hp).trans ((le_max_left R 0).trans (le_add_of_nonneg_right zero_le_one))
  · intro S hS
    exact (cthickening_subset_of_subset δ hS).trans hδplateau

end JanetCartan.ArbitraryAccuracy.ProtectedMasks
