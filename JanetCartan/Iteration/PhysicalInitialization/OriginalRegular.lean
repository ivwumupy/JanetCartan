module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalProtected
public import JanetCartan.Iteration.PhysicalInitialization.SourceInterval
public import JanetCartan.Iteration.PhysicalPrimary.CharacteristicAdjointMomentum
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.IncidenceProfiles
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalRegularTemplate

/-!
# Normalized smooth fixed inverse on the original protected sectors

The projected no-return product, independent full source domains, terminal
plateaus, physical extension and normalized complete solver are applied on the
same original selected geometry. All regularity, frame margins, fixed inverse
operators and current coefficient bounds come from the original physical
construction. The regular family retains one common time chosen over BOTH
source signs and every original source patch, before its masks. A single
physical phase cutoff per original patch covers the entire original source
and every signed incidence box; all sector phases are literal pullbacks.
The source reference is exactly `sourceDilation H.map σ`. A positive `γ`,
chosen after the regular family but before `σ`, gives one smaller interval
and one common prehistory threshold for both the globally extended current
C6 margin and the exact original-aperture graph momentum bound. The native
normalized inverse and its `R/Kloc/Inv/Corr` lets are not reselected.
Consumers: the complete primary and signed-product responses, including both
source signs independently of both adjoints and both signed terminal plateaus
(`app:ch_regular:eq:exact-physical`,
`app:ch_regular:thm:no-return`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 24000000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalInitialization.OriginalRegular
open PhysicalSeed OriginalProtected ActualCarriers ActualCarriers.CurrentFullPhase

variable {n : ℕ}

/-- Every label in the full original frozen cube, with its actual spatial
covector, belongs to one of the original doubled cells. The cells themselves
also allow independent variation of the covector (`app:ch_response:eq:fixed-factor-transfer`). -/
theorem original_source_parameter_cell (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (z : Euclidean 3) (hz : z ∈ FrozenMenu.parameterCube ((OriginalBoundary.D hn).patches a.1 a.2).radius) :
    ∃ j : OriginalBoundary.centers hn a, (z, (OriginalBoundary.T hn a).reference.spatialPatch z) ∈
      closedBall (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val) (OriginalBoundary.σcover hn a j) := by
  let T := OriginalBoundary.T hn a
  have hc := OriginalBoundary.parameter_cover hn a
  have h₀ : (0 : Euclidean n) ∈ ball 0 (OriginalBoundary.εlead hn a) :=
    mem_ball_self (OriginalBoundary.leadTolerance_pos hn a)
  let point : Euclidean n × (Euclidean 3 × Euclidean (n-1)) :=
    (0, z, T.reference.spatialPatch z)
  have hinner : point ∈ ball 0 (OriginalBoundary.εlead hn a) ×ˢ OriginalBoundary.V hn a := ⟨h₀, hc.2.1 z hz⟩
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hc.2.2 hinner)
  have hd : dist (z, T.reference.spatialPatch z) (j.val.val, T.reference.spatialPatch j.val.val) ≤
      OriginalBoundary.σcover hn a j := (le_max_right (dist (0 : Euclidean n) 0) _).trans hj
  exact ⟨j, hd⟩

theorem original_source_parameter_covered (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (z : Euclidean 3) (hz : z ∈ FrozenMenu.parameterCube ((OriginalBoundary.D hn).patches a.1 a.2).radius) :
    (z, (OriginalBoundary.T hn a).reference.spatialPatch z) ∈ Csrc hn a := by
  obtain ⟨j, hj⟩ := original_source_parameter_cell hn a z hz
  have hσ := (OriginalBoundary.comparison_pos hn a j).2.2.2.2.2.2.2.2
  exact Csrc_cell hn a j (closedBall_subset_closedBall (by linarith only [hσ]) hj)

/-- Actual nonvacuity on every original patch: the original zero parameter
and its actual covector already belong to the unchanged full source. -/
theorem original_source_nonempty (hn : 5 ≤ n) (a : OriginalPatchIndex hn) :
    ((Xsrc hn a) ×ˢ (Csrc hn a)).Nonempty := by
  have hp := ((OriginalBoundary.hD hn).2.2.2.2.1 a.1 a.2).1.1
  exact ⟨(0, 0, (OriginalBoundary.T hn a).reference.spatialPatch 0),
    mem_closedBall_self (sourceRadius_pos hn).le,
    original_source_parameter_covered hn a 0 (FrozenMenu.zero_mem_parameterCube hp.le)⟩

/-- The physical selector lies inside the original compact modulation domain
and the signed protection region. No source parameter is shrunk. -/
def coreRadius (hn : 5 ≤ n) (r : ℝ) : ℝ := min (OriginalProtected.sourceRadius hn) r / 2

theorem core_spec (hn : 5 ≤ n) {r : ℝ} (hr : 0 < r) :
    0 < coreRadius hn r ∧ coreRadius hn r < r ∧
    closedBall (0 : Euclidean n) (coreRadius hn r) ⊆ ball 0 (OriginalBoundary.b hn) ∧
    ∀ a : OriginalPatchIndex hn,
      closedBall (0 : Euclidean n) (coreRadius hn r) ⊆ OriginalProtected.Xsrc hn a ∧
      closedBall (0 : Euclidean n) (coreRadius hn r) ⊆ ball 0 (OriginalBoundary.T hn a).physicalRadius := by
  have hm : 0 < min (OriginalProtected.sourceRadius hn) r := lt_min (OriginalProtected.sourceRadius_pos hn) hr
  have hs : coreRadius hn r < OriginalProtected.sourceRadius hn := (half_lt_self hm).trans_le (min_le_left _ _)
  refine ⟨half_pos hm, (half_lt_self hm).trans_le (min_le_right _ _),
    closedBall_subset_ball (hs.trans (OriginalProtected.sourceRadius_lt_b hn)), ?_⟩
  intro a
  have h : closedBall (0 : Euclidean n) (coreRadius hn r) ⊆ OriginalProtected.Xsrc hn a := closedBall_subset_closedBall hs.le
  exact ⟨h, h.trans (OriginalProtected.source_domains hn a).2.2.2.2⟩

theorem exists_cell_radius (hn : 5 ≤ n) :
    ∃ u > (0 : ℝ), ∀ (a : OriginalPatchIndex hn) (j : OriginalBoundary.centers hn a),
      u < OriginalBoundary.σcover hn a j := by
  let Cell := (a : OriginalPatchIndex hn) × OriginalBoundary.centers hn a
  have hp (p : Cell) : 0 < OriginalBoundary.σcover hn p.1 p.2 :=
    (OriginalBoundary.comparison_pos hn p.1 p.2).2.2.2.2.2.2.2.2
  obtain ⟨u, hu, hall⟩ := Pi.exists_forall_pos_add_lt
    (x := fun _ : Cell ↦ (0 : ℝ)) (y := fun p : Cell ↦ OriginalBoundary.σcover hn p.1 p.2) hp
  exact ⟨u, hu, fun a j ↦ by simpa only [zero_add] using hall ⟨a, j⟩⟩

def cellRadius (hn : 5 ≤ n) : ℝ := (exists_cell_radius hn).choose

def screenedRadius (hn : 5 ≤ n) (r μ : ℝ) : ℝ := min r (min μ (cellRadius hn))

theorem screened_pos (hn : 5 ≤ n) {r μ : ℝ} (hr : 0 < r) (hμ : 0 < μ) :
    0 < screenedRadius hn r μ := lt_min hr (lt_min hμ (exists_cell_radius hn).choose_spec.1)

/-- This is the required direction: the actual envelope product `χsrc * χ₂`
remains inside the narrower χ₂ support and hence inside the original measured
source plateau. The broad χsrc itself is neither recut nor required to fit
inside the subsequently selected inverse family. -/
theorem core_inside_native_cutoffs (hn : 5 ≤ n) {r μ : ℝ} (hr : 0 < r) (hμ : 0 < μ) :
    coreRadius hn (screenedRadius hn r μ) < r ∧ coreRadius hn (screenedRadius hn r μ) < μ ∧
    ∀ (a : OriginalPatchIndex hn) (j : OriginalBoundary.centers hn a),
      coreRadius hn (screenedRadius hn r μ) < OriginalBoundary.σcover hn a j := by
  have h := (core_spec hn (screened_pos hn hr hμ)).2.1
  exact ⟨h.trans_le (min_le_left _ _), h.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
    fun a j ↦ (h.trans_le ((min_le_right _ _).trans (min_le_right _ _))).trans
      ((exists_cell_radius hn).choose_spec.2 a j)⟩

theorem radius_lt_same_chart {H G : FlatReference n} {r : ℝ} (heq : H.domain = G.domain)
    (hr : r < G.domain.chartRadius) : r < H.domain.chartRadius := by rwa [heq]

open CompatibleResponse LeadingWave.FullModulation Filter
open scoped Topology

/-- The full open parameter window for a complete characteristic letter. This
is the union of the original doubled cells, not a new source selection. -/
def wholeWindow (hn : 5 ≤ n) (a : OriginalPatchIndex hn) : Set (Euclidean 3 × Euclidean (n-1)) :=
  ⋃ j : OriginalBoundary.centers hn a, ball
    (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val) (2 * OriginalBoundary.σcover hn a j)

theorem wholeWindow_spec (hn : 5 ≤ n) (a : OriginalPatchIndex hn) :
    IsOpen (wholeWindow hn a) ∧ IsCompact (closure (wholeWindow hn a)) ∧
    closure (wholeWindow hn a) ⊆ Csrc hn a ∧ ∀ j : OriginalBoundary.centers hn a,
      closedBall (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val)
        (OriginalBoundary.σcover hn a j) ⊆ wholeWindow hn a := by
  have hK := (source_domains hn a).2.1
  have hcl : closure (wholeWindow hn a) ⊆ Csrc hn a := closure_minimal
    (iUnion_subset fun j ↦ ball_subset_closedBall.trans (Csrc_cell hn a j)) hK.isClosed
  refine ⟨isOpen_iUnion fun _ ↦ isOpen_ball, hK.of_isClosed_subset isClosed_closure hcl, hcl, ?_⟩
  intro j
  have hσ := (OriginalBoundary.comparison_pos hn a j).2.2.2.2.2.2.2.2
  exact (closedBall_subset_ball (by linarith only [hσ] : OriginalBoundary.σcover hn a j < 2*OriginalBoundary.σcover hn a j)).trans
    (subset_iUnion (fun j : OriginalBoundary.centers hn a ↦ ball
      (j.val.val, (OriginalBoundary.T hn a).reference.spatialPatch j.val.val) (2*OriginalBoundary.σcover hn a j)) j)

theorem original_source_in_wholeWindow (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (z : Euclidean 3) (hz : z ∈ FrozenMenu.parameterCube ((OriginalBoundary.D hn).patches a.1 a.2).radius) :
    (z, (OriginalBoundary.T hn a).reference.spatialPatch z) ∈ wholeWindow hn a := by
  obtain ⟨j, hj⟩ := original_source_parameter_cell hn a z hz
  exact (wholeWindow_spec hn a).2.2.2 j hj

theorem wholeWindow_source_germ {n : ℕ} (hn : 5 ≤ n) (a : OriginalPatchIndex hn)
    (χ : Euclidean n × (Euclidean 3 × Euclidean (n-1)) → ℝ)
    (h : ∀ q ∈ Xsrc hn a ×ˢ Csrc hn a, χ =ᶠ[𝓝 q] fun _ ↦ 1) :
    ∀ q ∈ Xsrc hn a ×ˢ closure (wholeWindow hn a), χ =ᶠ[𝓝 q] fun _ ↦ 1 :=
  fun q hq ↦ h q ⟨hq.1, (wholeWindow_spec hn a).2.2.1 hq.2⟩

/-- Pull a sector carrier back to the original physical coordinates without
changing either its source label or its independent covector. -/
def sectorToPhysical {d : ℕ} (i : Fin (d+1))
    (q : Euclidean (d+1) × (Euclidean 3 × Euclidean d)) :=
  ((primaryCoordinateChange i).symm q.1, q.2)

theorem sectorToPhysical_smooth {d : ℕ} (i : Fin (d+1)) : ContDiff ℝ ∞ (sectorToPhysical i) :=
  ((primaryCoordinateChange i).symm.contDiff.comp contDiff_fst).prodMk contDiff_snd

theorem compact_sector_phase {d : ℕ} (i : Fin (d+1))
    {χ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ} (hc : HasCompactSupport χ) :
    HasCompactSupport (χ ∘ sectorToPhysical i) :=
  hc.comp_homeomorph ((primaryCoordinateChange i).symm.toHomeomorph.prodCongr (Homeomorph.refl _))

/-- One physical phase representative for all letters in any finite word.
The same cutoff covers the full original source and the physical pullbacks
of every protected characteristic incidence box. Its chart restrictions are
literal compositions, not independent phase choices. -/
theorem exists_shared_physical_phase {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn)
    {I : Type*} [Finite I] (idx : I → Fin (d+1))
    (Kp : I → Bool → Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d)))
    (hK : ∀ p neg, IsCompact (Kp p neg))
    (hD : ∀ p neg q, q ∈ Kp p neg → ((sectorToPhysical (idx p) q).1, q.2.2) ∈ phaseDomain (OriginalBoundary.T hn a)) :
    ∃ χ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ q ∈ tsupport χ, (q.1, q.2.2) ∈ phaseDomain (OriginalBoundary.T hn a)) ∧
      (∀ q ∈ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a, χ =ᶠ[𝓝 q] fun _ ↦ 1) ∧
      (∀ Q, ContDiff ℝ ∞ (fun q ↦ χ q * phase (OriginalBoundary.T hn a) Q q.1 q.2.2)) ∧
      ∀ p, ContDiff ℝ ∞ (χ ∘ sectorToPhysical (idx p)) ∧
        (∀ q ∈ tsupport (χ ∘ sectorToPhysical (idx p)),
          ((sectorToPhysical (idx p) q).1, q.2.2) ∈ phaseDomain (OriginalBoundary.T hn a)) ∧
        (∀ neg q, q ∈ Kp p neg → χ ∘ sectorToPhysical (idx p) =ᶠ[𝓝 q] fun _ ↦ 1) ∧
        ∀ Q, ((fun q ↦ (χ ∘ sectorToPhysical (idx p)) q *
                  (OriginalBoundary.T hn a).fullSourcePhaseInCoordinates (idx p) Q q.1 q.2) =
          (fun q ↦ χ q * phase (OriginalBoundary.T hn a) Q q.1 q.2.2) ∘ sectorToPhysical (idx p)) ∧
          (fun q ↦ (χ ∘ sectorToPhysical (idx p)) q *
                  (OriginalBoundary.T hn a).negativeFullSourcePhaseInCoordinates (idx p) Q q.1 q.2) =
            (fun q ↦ -(χ q * phase (OriginalBoundary.T hn a) Q q.1 q.2.2)) ∘ sectorToPhysical (idx p) := by
  let T := OriginalBoundary.T hn a
  let A := OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a
  let K := A ∪ ⋃ p, ⋃ n : Bool, sectorToPhysical (idx p) '' Kp p n
  let Ω := (fun q : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦ (q.1, q.2.2)) ⁻¹' phaseDomain T
  have hΩ : IsOpen Ω := isOpen_ball.preimage (continuous_fst.prodMk continuous_snd.snd)
  have hb := OriginalProtected.source_domains hn a
  have hcompact : IsCompact K := (hb.1.prod hb.2.1).union
    (isCompact_iUnion fun p ↦ isCompact_iUnion fun n ↦ (hK p n).image (sectorToPhysical_smooth (idx p)).continuous)
  have hdom : K ⊆ Ω := by
    intro q hq
    rcases hq with h | h
    · exact hb.2.2.2.1 h
    · obtain ⟨p, hp⟩ := mem_iUnion.mp h
      obtain ⟨neg, u, hu, rfl⟩ := mem_iUnion.mp hp
      exact hD p neg u hu
  obtain ⟨χ, hχ, hc, hs, _, he⟩ := NormalComparison.exists_contDiff_localization hΩ hcompact hdom
    (contDiff_const (c := (1 : ℝ))).contDiffOn
  refine ⟨χ, hχ, hc, hs, fun q hq ↦ he q (Or.inl hq), ?_, ?_⟩
  · intro Q
    have hraw : ContDiffOn ℝ ∞ (fun q : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
        phase T Q q.1 q.2.2) Ω :=
      (phase_smooth T Q).comp (contDiff_fst.prodMk contDiff_snd.snd).contDiffOn
        (fun _ hy ↦ ball_subset_ball (by linarith only [T.family.radius_pos] : T.family.radius ≤ 2*T.family.radius) hy)
    apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hq : q ∈ tsupport χ
    · exact hχ.contDiffAt.mul (hraw.contDiffAt (hΩ.mem_nhds (hs hq)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with u hu
      exact mul_eq_zero_of_left hu _
  · intro p
    refine ⟨hχ.comp (sectorToPhysical_smooth _), fun _ h ↦ hs
      (tsupport_comp_subset_preimage χ (sectorToPhysical_smooth _).continuous h), ?_, ?_⟩
    · intro neg q hq
      exact (he _ (Or.inr (mem_iUnion.mpr ⟨p, mem_iUnion.mpr ⟨neg, mem_image_of_mem _ hq⟩⟩))).comp_tendsto
        (sectorToPhysical_smooth _).continuous.continuousAt
    · intro Q
      refine ⟨rfl, ?_⟩
      funext q
      exact mul_neg _ _

open RegularSector.Characteristic ResponseTransfer.RetainedFactors

def primarySet {d : ℕ} (z : RootState (Euclidean d)) (ε : ℝ) (V : Set (Euclidean 3 × Euclidean d)) :=
  closure (elapsedPhysicalBox z ε) ×ˢ closure V

theorem primarySet_compact {d : ℕ} (z : RootState (Euclidean d)) (ε : ℝ) {V : Set (Euclidean 3 × Euclidean d)}
    (hV : IsCompact (closure V)) : IsCompact (primarySet z ε V) := by
  have hx := isCompact_closure_retained_physicalBox z (2 * ε)
  simp only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at hx
  exact hx.prod hV

/- Native regular construction with the actual original doubled parameter cells,
not an existence assumption for an inverse or a coefficient margin. -/
proof_from regular_on_fixed_sectors {d : ℕ} (hn : 5 ≤ d+1) (r : ℝ) (hr : 0 < r) (μ : ℝ) (hμ : 0 < μ)
    (Γin Γout : Set (Euclidean (d+1))) (hin : IsCompact Γin) (hout : IsCompact Γout)
    (hnest : Γin ⊆ interior Γout) (hsym : ∀ ξ ∈ Γout, -ξ ∈ Γout)
    (hbad : Γout ⊆ (cubeBadSubspaceUnion (d+1))ᶜ)
    (gap : ℝ) (hgap : 0 < gap) (δ : ℝ) (hδ : 0 < δ)
    (qext : BallExtension.Parameters (Euclidean (d+1))) (hcenter : qext.center = 0)
    (hradius : qext.radius = OriginalBoundary.b hn) (H : FlatReference (d+1))
    (hR : OriginalBoundary.R hn < H.domain.chartRadius) (m : ℕ) (hm : 6 ≤ m) :=
  FixedDomainInverse.exists_terminal_physical_inverse_on_source_interval
    (fun a : OriginalPatchIndex hn ↦ (OriginalBoundary.D hn).patches a.1 a.2)
    (OriginalBoundary.T hn)
    (fun a ↦ (original_frameBall_subset hn a).trans (closedBall_subset_ball (OriginalBoundary.b_lt_R hn)))
    (OriginalProtected.Csrc hn) (fun a ↦ (OriginalProtected.source_domains hn a).2.1)
    (fun a ↦ (OriginalProtected.source_domains hn a).2.2.1)
    (OriginalProtected.Xsrc hn) (fun a ↦ (OriginalProtected.source_domains hn a).1)
    (fun a ↦ (OriginalProtected.source_domains hn a).2.2.2.1)
    (Ω := ball 0 (OriginalBoundary.b hn)) isOpen_ball (0 : Euclidean (d+1))
    (core_spec hn (screened_pos hn hr hμ)).1 (core_spec hn (screened_pos hn hr hμ)).2.2.1
    (fun a ↦ ((core_spec hn (screened_pos hn hr hμ)).2.2.2 a).2)
    hn hin hout hnest hsym hbad hgap (radius := r)
    qext hcenter hradius.le (OriginalBoundary.b_lt_R hn) m hm (half_pos hδ)
    (κ := 1/2) (by norm_num) (by norm_num) H hR (sourceCap := 1) zero_lt_one

/-- The reserved half-margin at the source gives the actual current maps all
rank and frame properties on the original (wide) coefficient domain. -/
theorem actual_history_frames (hn : 5 ≤ n) (G : FlatReference n)
    (hR : OriginalBoundary.R hn < G.domain.chartRadius) (m : ℕ) (hm : 6 ≤ m) {δ : ℝ} (hδ : 0 < δ)
    (hframe : ∀ i, cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) m
      (fun y ↦ ProjectedStressFrame.projectedStress G.map y i - cubeStress n i) < δ / 2)
    {Cband : ℝ} (hband : 1 ≤ Cband) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ)/2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ContDiffOn ℝ ∞ F (ball 0 (OriginalBoundary.R hn)) ∧
      IsImmersionOn F (ball 0 (OriginalBoundary.R hn)) ∧ HasFullNormalRankOn F (ball 0 (OriginalBoundary.R hn)) ∧
      ∀ i, cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) 6
        (fun y ↦ ProjectedStressFrame.projectedStress F y i - cubeStress n i) < δ := by
  obtain ⟨S, hS, C, _, k, _, h⟩ := PhysicalGeometry.exists_cube_frame_neighborhood G
    (OriginalBoundary.b_pos hn) (OriginalBoundary.b_lt_R hn) hR hband hStar horder hδ
    (fun i ↦ (cNorm_mono_order hm).trans_lt (hframe i))
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ j u ell hu
  have hc := h R₀ hR₀ j u ell hu
  exact ⟨RevisedGlobal.contDiffOn_finiteMap G.contDiff.contDiffOn u,
    hc.1, hc.2.1, hc.2.2.2.2.2.2⟩

def original_projected_map (hn : 5 ≤ n) (δ : ℝ) (F : Euclidean n → Euclidean (embeddingDimension n))
    (h : ContDiffOn ℝ ∞ F (ball 0 (OriginalBoundary.R hn)) ∧ IsImmersionOn F (ball 0 (OriginalBoundary.R hn)) ∧
      HasFullNormalRankOn F (ball 0 (OriginalBoundary.R hn)) ∧ ∀ i, cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) 6
        (fun y ↦ ProjectedStressFrame.projectedStress F y i - cubeStress n i) < δ) :
    ProtectedFlow.ProjectedImmersionNeighborhood (n := n) (embeddingDimension n) (ball 0 (OriginalBoundary.R hn))
      (closedBall 0 (OriginalBoundary.b hn)) δ := ⟨F, h⟩

open RegularSector.FiniteMasks.ActualFamily

def measuredSourceCutoff {n : ℕ} {μ : ℝ} (hμ : 0 < μ) : Euclidean n → ℝ :=
  ContinuumRow.FixedCutoffs.physical hμ 2

theorem small_source_product {d : ℕ} (hn : 5 ≤ d+1) {r μ : ℝ} (hr : 0 < r) (hμ : 0 < μ)
    {Ω K : Set (Euclidean (d+1))} {M : ℝ}
    (f : ActualMaskFamily Ω 0 (coreRadius hn (screenedRadius hn r μ)) (cubeStress (d+1)) K M)
    (χ₂ : ContDiffBump (0 : Euclidean (d+1))) (t : ℝ)
    (hs : tsupport (χ₂ : Euclidean (d+1) → ℝ) ⊆ ball 0 (min t f.physicalRadius)) :
    (∀ y ∈ tsupport (χ₂ : Euclidean (d+1) → ℝ), measuredSourceCutoff hμ =ᶠ[𝓝 y] (fun _ ↦ 1)) ∧
    (fun y ↦ measuredSourceCutoff hμ y * χ₂ y) = (χ₂ : Euclidean (d+1) → ℝ) ∧
    (∀ y ∈ tsupport (χ₂ : Euclidean (d+1) → ℝ), f.inputMask =ᶠ[𝓝 y] (fun _ ↦ 1)) ∧
    ∀ (a : OriginalPatchIndex hn) (j : OriginalBoundary.centers hn a),
      tsupport (fun y ↦ measuredSourceCutoff hμ y * χ₂ y) ⊆
        OriginalProtected.Xsrc hn a ∩ ball 0 (OriginalBoundary.σcover hn a j) := by
  have hρ := f.physicalRadius_pos
  have hsmall := core_inside_native_cutoffs hn hr hμ
  have hx : tsupport (χ₂ : Euclidean (d+1) → ℝ) ⊆ closedBall 0 f.physicalRadius :=
    hs.trans ((ball_subset_ball (min_le_right _ _)).trans ball_subset_closedBall)
  have hcore := hx.trans ((closedBall_subset_closedBall (by linarith only [hρ] : f.physicalRadius ≤ 4*f.physicalRadius)).trans f.physicalBall_coefficientDomain)
  have hμsrc : tsupport (χ₂ : Euclidean (d+1) → ℝ) ⊆
      interior {y | measuredSourceCutoff hμ y = 1} := by
    apply hcore.trans
    apply (closedBall_subset_closedBall _).trans (ContinuumRow.FixedCutoffs.physical_plateau hμ (2 : Fin 3))
    change coreRadius hn (screenedRadius hn r μ) ≤ (2+1)*μ
    linarith only [hsmall.2.1, hμ]
  have hsrc : (fun y ↦ measuredSourceCutoff hμ y * χ₂ y) = (χ₂ : Euclidean (d+1) → ℝ) := by
    funext y
    by_cases hy : y ∈ tsupport (χ₂ : Euclidean (d+1) → ℝ)
    · rw [show measuredSourceCutoff hμ y = 1 from interior_subset (s := {z | measuredSourceCutoff hμ z = 1}) (hμsrc hy), one_mul]
    · have hz := (notMem_tsupport_iff_eventuallyEq.mp hy).eq_of_nhds
      change χ₂ y = 0 at hz
      rw [hz, mul_zero]
  refine ⟨fun y hy ↦ ?_, hsrc, fun y hy ↦ ?_, fun a j ↦ ?_⟩
  · filter_upwards [isOpen_interior.mem_nhds (hμsrc hy)] with z hz
    exact interior_subset (s := {z | measuredSourceCutoff hμ z = 1}) hz
  · have hp := f.inputMask_plateau (closedBall_subset_closedBall (by linarith only [hρ] : f.physicalRadius ≤ 2*f.physicalRadius) (hx hy))
    filter_upwards [isOpen_interior.mem_nhds hp] with z hz
    exact interior_subset (s := {z | f.inputMask z = 1}) hz
  · rw [hsrc]
    exact subset_inter (hcore.trans (((core_spec hn (screened_pos hn hr hμ)).2.2.2 a).1))
      (hcore.trans (closedBall_subset_ball (hsmall.2.2 a j)))

/-- The physical graph-momentum windows are selected before the final
contraction of H, inside the regular source interval already chosen. -/
theorem source_interval_for_graph_and_frame_margins {n : ℕ} (hn : 5 ≤ n) (H : FlatReference n)
    {cap : ℝ} (hcap : 0 < cap) {I : Type*} [Finite I] {η : I → ℝ} (hη : ∀ p, 0 < η p)
    {ηframe : ℝ} (hframePos : 0 < ηframe) :
    ∃ cap40 : ℝ, 0 < cap40 ∧ cap40 < cap ∧ cap40 ≤ 1 ∧
      ∀ σ ∈ Ioc (0 : ℝ) cap40,
        (∀ p i, cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) 6
          (fun x ↦ ProjectedStressFrame.projectedStress (sourceDilation H.map σ) x i - cubeStress n i) < η p) ∧
        ∀ i, cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) 6
          (fun x ↦ ProjectedStressFrame.projectedStress (sourceDilation H.map σ) x i - cubeStress n i) < ηframe := by
  obtain ⟨e, he, hsmall⟩ := Pi.exists_forall_pos_add_lt (x := fun _ : I ↦ (0 : ℝ)) (y := η) hη
  have htol : 0 < min e ηframe := lt_min he hframePos
  obtain ⟨_, _, _, cap40, hpos, hlt, hone, _, hframe, _⟩ :=
    ReferenceInitialization.FullCoefficientDilation.exists_fullReducedCoefficients_finite_margin_interval H
      (isCompact_closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) (Finset.univ : Finset Unit)
      (fun _ ↦ 6) (fun _ ↦ min e ηframe) (fun _ _ ↦ htol) htol hcap
  refine ⟨cap40, hpos, hlt, hone, ?_⟩
  intro σ hσ
  have hh := (hframe σ hσ).2.2.2.2.2
  exact ⟨fun p i ↦ ((hh i).trans_le (min_le_left _ _)).trans (by simpa only [zero_add] using hsmall p),
    fun i ↦ (hh i).trans_le (min_le_right _ _)⟩

theorem regular_scale_of_graph_scale {σ a b : ℝ} (h : σ ∈ Ioc (0 : ℝ) a) (hab : a < b) : σ ∈ Ioc (0 : ℝ) b :=
  ⟨h.1, h.2.trans hab.le⟩

theorem common_graph_threshold {I : Type*} [Finite I] (S : ℝ) (L : I → ℝ) : ∃ M : ℝ, S ≤ M ∧ ∀ p, L p ≤ M := by
  classical
  let := Fintype.ofFinite I
  let s := insert S (Finset.univ.image L)
  have hs : s.Nonempty := Finset.insert_nonempty _ _
  exact ⟨s.max' hs, s.le_max' S (Finset.mem_insert_self _ _),
    fun p ↦ s.le_max' (L p) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩))⟩

theorem common_graph_frame_threshold {I : Type*} [Finite I] (S Sframe : ℝ) (L : I → ℝ) :
    ∃ M : ℝ, S ≤ M ∧ Sframe ≤ M ∧ ∀ p, L p ≤ M := by
  obtain ⟨M, hM, hL⟩ := common_graph_threshold (max S Sframe) L
  exact ⟨M, (le_max_left _ _).trans hM, (le_max_right _ _).trans hM, hL⟩

theorem stationary_current_grades {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn) (r : ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1)) (B : Euclidean (d+1) → MetricTensor (d+1))
    (M γ : ℝ)
    (hg : ∀ K : Set (Euclidean (d+1)), IsCompact K →
      cNorm K (RegularSector.FiniteEvolution.sectorLowOrder d) Q ≤ M ∧
      cNorm K (RegularSector.FiniteEvolution.sectorLowOrder d) B ≤ M ∧ cNorm K 4 Q ≤ M)
    (hnorm : ∀ K : Set (Euclidean (d+1)), cNorm K 6 (Q - fun _ ↦ cubeStress (d+1)) < γ) :
    let A := closedBall 0 (OriginalBoundary.T hn a).data.localReference.stateRadius
    cNorm A 4 Q ≤ M ∧ cNorm (closedBall 0 r) 4 Q ≤ M ∧ cNorm A 6 (Q - fun _ ↦ cubeStress (d+1)) < γ :=
  ⟨(hg _ (isCompact_closedBall _ _)).2.2, (hg _ (isCompact_closedBall _ _)).2.2, hnorm _⟩

theorem stationary_regular_grade_three {d : ℕ} (r : ℝ)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1)) (B : Euclidean (d+1) → MetricTensor (d+1))
    (M : ℝ) (hg : ∀ K : Set (Euclidean (d+1)), IsCompact K →
      cNorm K (RegularSector.FiniteEvolution.sectorLowOrder d) Q ≤ M ∧
      cNorm K (RegularSector.FiniteEvolution.sectorLowOrder d) B ≤ M ∧ cNorm K 4 Q ≤ M) :
    cNorm (closedBall 0 r) 3 Q ≤ M :=
  (cNorm_mono_order (by decide : 3 ≤ 4)).trans ((hg _ (isCompact_closedBall _ _)).2.2)

theorem stationary_initial_clock {d : ℕ} {z : RootState (Euclidean d)} {r a t : ℝ}
    {W : RootState (Euclidean d) → RootState (Euclidean d)} {Φ : RootState (Euclidean d) × ℝ → RootState (Euclidean d)}
    (hr : 0 < r) (ha : 2*a ≤ r/4) (hΦ : ODE.IsSmoothFlowOn W z r (r/2) t Φ) :
    a ≤ r ∧ ∀ v ∈ ball z a, Φ (v,0) = v := by
  refine ⟨by linarith only [hr, ha], fun v hv ↦ hΦ.initial v ?_⟩
  exact ball_subset_closedBall (ball_subset_ball (by linarith only [hr, ha] : a ≤ r/2) hv)

def frameInOriginalPatch {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn)
    (Q : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1)) (hQ : ContDiff ℝ ∞ Q)
    {ρ : ℝ} (hnear : ∀ K : Set (Euclidean (d+1)), cNorm K 6 (Q - fun _ ↦ cubeStress (d+1)) < ρ)
    (hρ : ρ ≤ (OriginalBoundary.T hn a).family.threshold) :
    {A : Euclidean (d+1) → Fin (d+1) → MetricTensor (d+1) //
      ContDiffOn ℝ ∞ A (ball 0 (OriginalBoundary.R hn)) ∧
      cNorm (closedBall 0 (OriginalBoundary.T hn a).data.localReference.stateRadius) 6
        (A - fun _ ↦ cubeStress (d+1)) < (OriginalBoundary.T hn a).family.threshold} :=
  ⟨Q, hQ.contDiffOn, (hnear _).trans_le hρ⟩

apply_regular_inverse_to_original_protected_sectors
retain_original_regular_source_interval
construct_original_regular_current_solver
retain_original_small_source_product
construct_original_regular_phase_and_incidence
realize_original_regular_current_phase
apply_original_signed_stationary_branches
apply_actual_graph_momentum_cap

end JanetCartan.PhysicalInitialization.OriginalRegular
