module

public import JanetCartan.Iteration.PhysicalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryAdmission

/-!
# Admit physical current frames to the original retained coefficient range

The positive tolerance precedes the reference and the fixed regular mask family
application. The SAME affine extension of the current projected stress lies in
the supplied coefficient radius and satisfies all physical C6 phase margins.
Current coefficient smallness is produced from actual physical admissibility,
not assumed. This is the range input of `app:ch_regular:thm:exact-correction`
and `app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalInitialization
open ProtectedFlow GeometricProfile CurrentCoefficientProfiles
open ActualCarriers.CurrentFullPhase ProjectedStressFrame

/-- `app:ch_seed:setup:seed-current`: the prescribed reference tolerance and
actual physical displacement give the SAME globally extended current Q its
range and every local phase bound. No constant is chosen after the history. -/
theorem exists_reference_tolerance_for_physical_frame_admission {n : ℕ}
    (ext : BallExtension.Parameters (Euclidean n)) {r : ℝ}
    (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference n, ∀ R : ℝ,
      0 < r → r < R → R < G.domain.chartRadius →
      (∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
        (fun x ↦ projectedStress G.map x i - cubeStress n i) < η) →
      ∀ {Cband : ℝ}, 1 ≤ Cband →
      ∀ rStar kMin : ℕ, 8 ≤ rStar →
      RevisedScales.displacementLoss n +
        bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ) →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let Q := extendedProjectedStress ext (RevisedGlobal.finiteMap G.map u)
      ContDiff ℝ ∞ Q ∧ MapsTo Q univ (closedBall (cubeStress n) ε) ∧
      ∀ K : Set (Euclidean n), cNorm K 6 (Q - fun _ ↦ cubeStress n) < δ := by
  obtain ⟨C, hC, hbound⟩ := exists_affineFrameExtension_bound ext 6
  let a := min ε δ / (C + 1)
  have ha : 0 < a := div_pos (lt_min hε hδ) (by linarith)
  refine ⟨(a / (2 * (6 + 1))) / 2, by positivity, ?_⟩
  intro G R hr hrR hR hreference Cband hband rStar kMin hStar horder
  obtain ⟨S, hS, _, _, _, _, hgeometry⟩ :=
    PhysicalGeometry.exists_cube_frame_neighborhood G hr hrR hR hband hStar horder
      (by positivity : 0 < a / (2 * (6 + 1))) hreference
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ s u ell hu Q
  obtain ⟨_, _, _, _, _, hframe, hclose⟩ := hgeometry R₀ hR₀ s u ell hu
  let F := RevisedGlobal.finiteMap G.map u
  have hraw : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) :=
    contDiffOn_pi.mpr hframe
  have hball : closedBall ext.center ext.radius ⊆ ball (0 : Euclidean n) R := by
    simpa only [hextcenter, hextradius] using closedBall_subset_ball hrR
  have hrawAt : ∀ x ∈ closedBall ext.center ext.radius,
      ContDiffAt ℝ ∞ (projectedStress F) x :=
    fun x hx ↦ hraw.contDiffAt (isOpen_ball.mem_nhds (hball hx))
  have hsmall : cNorm (closedBall ext.center ext.radius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < a := by
    apply frame_cNorm_lt_of_componentwise (isCompact_closedBall _ _)
      (fun x hx ↦ ((hrawAt x hx).sub contDiffAt_const).of_le (by simp)) ha
    simpa only [hextcenter, hextradius, Pi.sub_apply, F, Nat.cast_ofNat] using hclose
  have hQ : ContDiff ℝ ∞ Q :=
    contDiff_affineFrameExtension ext (fun x hx ↦ (hrawAt x hx).contDiffWithinAt)
  have hglobal : cNorm univ 6 (Q - fun _ ↦ cubeStress n) < min ε δ := by
    have hh := (hbound (projectedStress F) hrawAt).trans_lt
      (mul_lt_mul_of_pos_left hsmall hC)
    have hCa : C * a < min ε δ := by
      dsimp [a]
      rw [← mul_div_assoc]
      apply (div_lt_iff₀ (by linarith : 0 < C + 1)).mpr
      nlinarith [lt_min hε hδ]
    exact hh.trans hCa
  have hc : HasCompactSupport (Q - fun _ ↦ cubeStress n) :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall ext.center (ext.radius + ext.width / 2))
      ((subset_tsupport _).trans (tsupport_affineFrameExtension_sub ext (projectedStress F)))
  obtain ⟨bound, _, hjet⟩ := hc.exists_bound_iteratedFDeriv (hQ.sub contDiff_const) 6
  have hbounded j (hj : j ≤ 6) :
      BddAbove ((fun x ↦ ‖iteratedFDeriv ℝ j (Q - fun _ ↦ cubeStress n) x‖) '' univ) :=
    ⟨bound, by rintro _ ⟨x, _, rfl⟩; exact hjet j hj x⟩
  refine ⟨hQ, ?_, fun K ↦
    ((cNorm_mono_set_of_bddAbove (subset_univ K) hbounded).trans_lt hglobal).trans_le
      (min_le_right _ _)⟩
  intro x _
  have hx := norm_iteratedFDeriv_le_cNorm_of_bddAbove (hbounded 0 (by omega))
    (mem_univ x) (by omega : 0 ≤ 6)
  have hx' : ‖Q x - cubeStress n‖ < ε := by
    simpa using (hx.trans_lt hglobal).trans_le (min_le_left ε δ)
  simpa only [mem_closedBall, dist_eq_norm] using hx'.le

end JanetCartan.PhysicalInitialization
