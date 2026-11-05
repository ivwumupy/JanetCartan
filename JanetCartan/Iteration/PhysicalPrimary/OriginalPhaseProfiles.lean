module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalRegular
public import JanetCartan.Iteration.PhysicalEllipticWords.Phase
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalPhaseProfilesTemplate

/-!
# Actual original whole physical phase profiles

The original25 source-dilated reference, its prescribed extension and ONE
already selected physical cutoff supply the full joint phase jets. The
compact set is the unchanged Xsrc × Csrc, containing the later closed3f-radius
word box and the whole independent source-parameter window. The actual current
sourceFrame is used; neither a frame margin nor a phase profile is assumed.

Consumers: the endpoint/algebraic/elliptic measured residual alphabet and the
actual whole-source retarded construction (`app:ch_response:eq:direct-envelope-profile`,
`app:ch_regular:lem:finite-chain`). The gradient annulus remains the separate
original incidence producer; no gradient band or phase is chosen here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16000
@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPrimary.OriginalPhaseProfiles
open PhysicalSeed PhysicalInitialization ActualCarriers FrozenMenu
open ActualCarriers.CurrentFullPhase CompatibleResponse HamiltonPhase
open LeadingWave.FullModulation ProtectedFlow ProjectedStressFrame
open RegularSector.FiniteMasks.ActualFamily

/-- The already known zero-coordinate identity is kept private here to avoid
building the unrelated, uncached retained-source application leaf. -/
private theorem original_zero_coordinates {d : ℕ} (y : Euclidean (d+1)) :
    (primaryCoordinateChange (0 : Fin (d+1))).symm y = y := by
  have hzero : primaryCoordinateChange (0 : Fin (d+1)) y = y :=
    (RegularSector.Characteristic.coordinateSplit 0).symm_apply_apply y
  calc
    _ = (primaryCoordinateChange (0 : Fin (d+1))).symm
        (primaryCoordinateChange (0 : Fin (d+1)) y) := congrArg _ hzero.symm
    _ = y := ContinuousLinearEquiv.symm_apply_apply _ y

private theorem original_zero_phase {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn)
    (Q : _) (y : Euclidean (d+1)) (c : Euclidean 3 × Euclidean d) :
    (OriginalBoundary.T hn a).fullSourcePhaseInCoordinates 0 Q y c =
      phase (OriginalBoundary.T hn a) Q y c.2 := by
  change phase (OriginalBoundary.T hn a) Q ((primaryCoordinateChange 0).symm y) c.2 = _
  rw [original_zero_coordinates]

/-- Apply the actual physical-history phase producer at physical index zero,
on the complete original source set and the prescribed original cutoff germ.
The public original-data specializer below closes every cutoff/reference input;
only exact numerical reserve and admissible-history conditions remain
(`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_prescribed_cutoff_phase_profiles {d : ℕ} (hn : 5 ≤ d+1)
    (a : OriginalPatchIndex hn)
    (χp : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ)
    (hχp : ContDiff ℝ ∞ χp)
    (hχdomain : ∀ q ∈ tsupport χp, (q.1,q.2.2) ∈ phaseDomain (OriginalBoundary.T hn a))
    (hχone : ∀ q ∈ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a,
      χp =ᶠ[𝓝 q] fun _ ↦ 1)
    (G : FlatReference (d+1)) (hR : OriginalBoundary.R hn < G.domain.chartRadius)
    (ext : BallExtension.Parameters (Euclidean (d+1))) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = OriginalBoundary.b hn)
    {Cband : ℝ} (hband : 1 ≤ Cband) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : reserve+3 ≤ rStar) (hreserve2 : 2 ≤ reserve)
    (horder : RevisedScales.displacementLoss (d+1) +
      bandExponent * ((rStar : ℝ) + ((d+1 : ℕ) : ℝ)/2) + 2 < (kMin : ℝ)) :
    let T := OriginalBoundary.T hn a
    let KP : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d)) :=
      OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a
    ∃ S : ℝ, 2 ≤ S ∧ ∃ Aphase : ℕ → ℝ, (∀ k, 0 ≤ Aphase k) ∧ ∀ Q,
      let φ := fun q : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
        χp q * phase T Q q.1 q.2.2
      ContDiff ℝ ∞ φ ∧
        (∀ q ∈ KP, φ =ᶠ[𝓝 q] fun b ↦ phase T Q b.1 b.2.2) ∧
        ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1))))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
          Q.1 = extendedProjectedStress ext (RevisedGlobal.finiteMap G.map u) →
          cNorm KP 2 φ ≤ Aphase 2 ∧
            (∀ k, cNorm KP k φ ≤ Aphase k * currentCoefficientScale R₀ j ^ (k-reserve)) ∧
            ∀ k q, q ∈ KP → ‖iteratedFDeriv ℝ k φ q‖ ≤
              Aphase k * currentCoefficientScale R₀ j ^ (k-reserve) := by
  intro T KP
  have hd := OriginalProtected.source_domains hn a
  have hdomain q (hq : q ∈ tsupport χp) :
      ((primaryCoordinateChange (0 : Fin (d+1))).symm q.1,q.2.2) ∈ phaseDomain T := by
    simpa only [original_zero_coordinates] using hχdomain q hq
  have hsource : KP ⊆ domain T := hd.2.2.2.1
  have hKD q (hq : q ∈ KP) :
      ((primaryCoordinateChange (0 : Fin (d+1))).symm q.1,q.2.2) ∈ phaseDomain T := by
    have hfull : q ∈ domain T := hsource hq
    have hp : (q.1,q.2.2) ∈ phaseDomain T := hfull
    simpa only [original_zero_coordinates] using hp
  obtain ⟨S,hS,Aphase,hA,hprofiles⟩ := PhysicalEllipticWords.exists_history_elliptic_phase_profiles
    T 0 χp hχp hdomain (hd.1.prod hd.2.1) hKD hχone G
    (OriginalBoundary.b_pos hn) (OriginalBoundary.b_lt_R hn) hR ext hextcenter hextradius
    hband hStar hreserve hreserve2 horder
  refine ⟨S,hS,Aphase,hA,?_⟩
  intro Q
  dsimp only [T] at hprofiles ⊢
  have hzero : Function.uncurry ((OriginalBoundary.T hn a).fullSourcePhaseInCoordinates 0 Q) =
      (fun q : Euclidean (d+1) × (Euclidean 3 × Euclidean d) ↦
        phase (OriginalBoundary.T hn a) Q q.1 q.2.2) := by
    funext q
    exact original_zero_phase hn a Q q.1 q.2
  have hp := hprofiles Q
  refine ⟨?_,?_,?_⟩
  · simpa only [original_zero_phase] using hp.1
  · intro q hq
    have hg := hp.2.1 q hq
    simpa only [original_zero_phase,hzero] using hg
  · intro R₀ hR₀ j u ell hu hQ
    simpa only [original_zero_phase] using hp.2.2 R₀ hR₀ j u ell hu hQ

/-- The actual word box is a subset of the original whole source set. Only
set restriction is performed; the radius and all full source parameters remain
unchanged (`app:ch_regular:lem:finite-chain`). -/
theorem original_word_phase_box_subset {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn)
    {Ω : Set (Euclidean (d+1))} {R M : ℝ}
    {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
    (f : ActualMaskFamily Ω (0 : Euclidean (d+1)) R A₀ K M)
    (hcore : closedBall (0 : Euclidean (d+1)) R ⊆ OriginalProtected.Xsrc hn a) :
    closedBall (0 : Euclidean (d+1)) (3*f.physicalRadius) ×ˢ
      closure (OriginalRegular.wholeWindow hn a) ⊆
        OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a := by
  apply Set.prod_mono _ (OriginalRegular.wholeWindow_spec hn a).2.2.1
  exact (closedBall_subset_closedBall (by linarith only [f.physicalRadius_pos] :
    3*f.physicalRadius ≤ 4*f.physicalRadius)).trans
      (f.physicalBall_coefficientDomain.trans hcore)

/-- Restrict a proved native whole-source profile to its exact original word
box, with the identical constant, current scale and natural reserve. This
helper is applied to the actual phase producer below, not left as an input of
its original-current specialization (`app:ch_response:eq:direct-envelope-profile`). -/
theorem restrict_original_joint_profiles {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn)
    {K : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d))}
    (hK : K ⊆ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a)
    {φ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ}
    {Aphase : ℕ → ℝ} {L : ℝ} {reserve : ℕ} (hφ : ContDiff ℝ ∞ φ)
    (hb : cNorm (OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a) 2 φ ≤ Aphase 2 ∧
      (∀ k, cNorm (OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a) k φ ≤
        Aphase k * L ^ (k-reserve)) ∧
      ∀ k q, q ∈ OriginalProtected.Xsrc hn a ×ˢ OriginalProtected.Csrc hn a →
        ‖iteratedFDeriv ℝ k φ q‖ ≤ Aphase k * L ^ (k-reserve)) :
    cNorm K 2 φ ≤ Aphase 2 ∧
      (∀ k, cNorm K k φ ≤ Aphase k * L ^ (k-reserve)) ∧
      ∀ k q, q ∈ K → ‖iteratedFDeriv ℝ k φ q‖ ≤ Aphase k * L ^ (k-reserve) := by
  have hc := (OriginalProtected.source_domains hn a).1.prod
    (OriginalProtected.source_domains hn a).2.1
  refine ⟨(cNorm_mono_set hK hc (hφ.of_le (by simp))).trans hb.1, ?_, ?_⟩
  · intro k
    exact (cNorm_mono_set hK hc (hφ.of_le (by simp))).trans (hb.2.1 k)
  · intro k q hq
    exact hb.2.2 k q (hK hq)

open RegularSector.Characteristic.ResidualCoordinates

private def jointPhysicalCoordinateIsometry {d : ℕ} (index : Fin (d+1)) :
    (Euclidean (d+1) × (Euclidean 3 × Euclidean d)) ≃ₗᵢ[ℝ]
      (Euclidean (d+1) × (Euclidean 3 × Euclidean d)) where
  toLinearEquiv := (physicalCoordinates index).toLinearEquiv.prodCongr
    (LinearEquiv.refl ℝ (Euclidean 3 × Euclidean d))
  norm_map' q := by
    change max ‖physicalCoordinates index q.1‖ ‖q.2‖ = max ‖q.1‖ ‖q.2‖
    rw [norm_physicalCoordinates]

private theorem cNorm_jointPhysicalCoordinateIsometry {d : ℕ} (index : Fin (d+1))
    (K : Set (Euclidean (d+1) × (Euclidean 3 × Euclidean d)))
    (φ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ) (k : ℕ) :
    cNorm K k (φ ∘ jointPhysicalCoordinateIsometry index) =
      cNorm (jointPhysicalCoordinateIsometry index '' K) k φ := by
  unfold cNorm
  apply Finset.sum_congr rfl
  intro j _hj
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨q,hq,rfl⟩
    refine ⟨jointPhysicalCoordinateIsometry index q,⟨q,hq,rfl⟩,?_⟩
    exact ((jointPhysicalCoordinateIsometry index).norm_iteratedFDeriv_comp_right φ q j).symm
  · rintro ⟨q,⟨p,hp,rfl⟩,rfl⟩
    exact ⟨p,hp,(jointPhysicalCoordinateIsometry index).norm_iteratedFDeriv_comp_right φ p j⟩

/-- The actual chart pullback preserves every joint phase derivative with
constant one. Its native coordinate word box uses the SAME physical radius,
window, profile and natural reserve (`app:ch_response:eq:direct-envelope-profile`). -/
theorem original_coordinate_joint_profiles {d : ℕ} (hn : 5 ≤ d+1) (a : OriginalPatchIndex hn)
    (index : Fin (d+1)) (r : ℝ)
    {φ : Euclidean (d+1) × (Euclidean 3 × Euclidean d) → ℝ}
    {Aphase : ℕ → ℝ} {L : ℝ} {reserve : ℕ} (hφ : ContDiff ℝ ∞ φ)
    (hb : cNorm (closedBall (0 : Euclidean (d+1)) r ×ˢ closure (OriginalRegular.wholeWindow hn a)) 2 φ ≤ Aphase 2 ∧
      (∀ k, cNorm (closedBall (0 : Euclidean (d+1)) r ×ˢ closure (OriginalRegular.wholeWindow hn a)) k φ ≤
        Aphase k * L ^ (k-reserve)) ∧
      ∀ k q, q ∈ closedBall (0 : Euclidean (d+1)) r ×ˢ closure (OriginalRegular.wholeWindow hn a) →
        ‖iteratedFDeriv ℝ k φ q‖ ≤ Aphase k * L ^ (k-reserve)) :
    let K := closedBall ((physicalCoordinates index).symm (0 : Euclidean (d+1))) r ×ˢ
      closure (OriginalRegular.wholeWindow hn a)
    let ψ := Function.uncurry (fun y b ↦ φ (physicalCoordinates index y,b))
    cNorm K 2 ψ ≤ Aphase 2 ∧
      (∀ k, cNorm K k ψ ≤ Aphase k * L ^ (k-reserve)) ∧
      ∀ k q, q ∈ K → ‖iteratedFDeriv ℝ k ψ q‖ ≤ Aphase k * L ^ (k-reserve) := by
  intro K ψ
  let e := jointPhysicalCoordinateIsometry index
  have hmap q (hq : q ∈ K) :
      e q ∈ closedBall (0 : Euclidean (d+1)) r ×ˢ closure (OriginalRegular.wholeWindow hn a) := by
    refine ⟨?_,hq.2⟩
    change physicalCoordinates index q.1 ∈ closedBall 0 r
    simpa only [map_zero,mem_closedBall_zero_iff,norm_physicalCoordinates] using hq.1
  have hc := (isCompact_closedBall (0 : Euclidean (d+1)) r).prod
    (OriginalRegular.wholeWindow_spec hn a).2.1
  have hnorm k : cNorm K k ψ ≤
      cNorm (closedBall (0 : Euclidean (d+1)) r ×ˢ closure (OriginalRegular.wholeWindow hn a)) k φ := by
    change cNorm K k (φ ∘ e) ≤ _
    rw [cNorm_jointPhysicalCoordinateIsometry]
    exact cNorm_mono_set (image_subset_iff.mpr hmap) hc (hφ.of_le (by simp))
  refine ⟨(hnorm 2).trans hb.1,fun k ↦ (hnorm k).trans (hb.2.1 k),?_⟩
  intro k q hq
  change ‖iteratedFDeriv ℝ k (φ ∘ e) q‖ ≤ _
  rw [e.norm_iteratedFDeriv_comp_right]
  exact hb.2.2 k (e q) (hmap q hq)

end JanetCartan.PhysicalPrimary.OriginalPhaseProfiles

retain_original_whole_phase_profiles
retain_original_word_phase_box
apply_original_current_whole_phase_profiles
