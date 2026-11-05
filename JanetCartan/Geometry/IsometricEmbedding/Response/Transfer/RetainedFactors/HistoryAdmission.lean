module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.CurrentFullPhase.FrameComponents

/-!
# Admit the actual history coefficients to the retained constructor

The finite low norm is chosen before the root chart, and the coefficient
neighborhood is supplied by the initialized reference's cube-frame tolerance.
The SAME prescribed affine extension is used for the principal frame and the
complete zeroth coefficient. These are inputs to `CappedConstruction` and to
`UniformEvolution.exists_retained_signed_retarded_operators`, not assumptions
about a successful response. Sources: `main:prop:current-scale`,
`app:ch_regular:eq:coefficient-extension`, and
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.RetainedFactors
open ProtectedFlow GeometricProfile CurrentCoefficientProfiles
open ActualCarriers.CurrentFullPhase ProjectedStressFrame

/-- A single finite low coefficient bound, including the full connection
matrix, holds on every compact measurement set for every admissible history.
Use `order = retardedCoefficientOrder d` before selecting the retained chart;
the constructor's orders ten and nine then follow by monotonicity. Neither a
coefficient bound nor a current mean is assumed (`main:prop:current-scale`). -/
theorem exists_admissible_history_retained_low_coefficients {n : ℕ}
    (G : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (ext : BallExtension.Parameters (Euclidean n)) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar order kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + order ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ M > (0 : ℝ),
      ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      let Q := extendedProjectedStress ext F
      let B := reducedZerothProjection n ∘ extendedReducedCoefficients ext (fun _ _ ↦ 0) F
      ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ B ∧
      ∀ K : Set (Euclidean n), IsCompact K →
        cNorm K order Q ≤ M ∧ cNorm K order B ≤ M := by
  obtain ⟨S, hS, AQ, AB, hAQ, hAB, hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles G hr hrR hR ext
      hextcenter hextradius hStar hreserve horder
  refine ⟨S, hS, 1 + AQ order + AB order, by linarith [hAQ order, hAB order], ?_⟩
  intro R₀ hR₀ s u ell hu F Q B
  obtain ⟨hQ, hB, hprofiles⟩ := hcoeff R₀ hR₀ s u ell hu
  refine ⟨hQ, hB, ?_⟩
  intro K hK
  obtain ⟨hq, hb⟩ := hprofiles K hK
  have hq' : cNorm K order Q ≤ AQ order := by simpa using hq order
  have hb' : cNorm K order B ≤ AB order := by simpa using hb order
  constructor <;> linarith [hAQ order, hAB order]

/-- The initialized reference's componentwise tolerance supplies the actual
global coefficient range and every local C6 primary-phase admission condition.
The positive tolerance precedes the reference and history; its producer is the
scaled-reference initializer at that tolerance. This theorem uses the original
Seeley extension and does not assume smallness of the extended current frame
(`app:ch_seed:setup:seed-current`, `app:ch_regular:eq:coefficient-extension`). -/
theorem exists_reference_tolerance_for_retained_history_admission {n : ℕ}
    (ext : BallExtension.Parameters (Euclidean n)) {r : ℝ}
    (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference n, ∀ R : ℝ,
      0 < r → r < R → R < G.domain.chartRadius →
      (∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
        (fun x ↦ projectedStress G.map x i - cubeStress n i) < η) →
      ∀ kMin : ℕ,
      displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let Q := extendedProjectedStress ext (finiteHistoryMap G.map u)
      ContDiff ℝ ∞ Q ∧ MapsTo Q univ (closedBall (cubeStress n) ε) ∧
      ∀ K : Set (Euclidean n), cNorm K 6 (Q - fun _ ↦ cubeStress n) < δ := by
  obtain ⟨C, hC, hbound⟩ := exists_affineFrameExtension_bound ext 6
  let a := min ε δ / (C + 1)
  have ha : 0 < a := div_pos (lt_min hε hδ) (by linarith)
  refine ⟨(a / (2 * (6 + 1))) / 2, by positivity, ?_⟩
  intro G R hr hrR hR hreference kMin horder
  obtain ⟨S, hS, _, _, _, _, hgeometry⟩ :=
    HistoryGeometry.exists_cube_frame_neighborhood G hr hrR hR horder
      (by positivity : 0 < a / (2 * (6 + 1))) hreference
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ s u ell hu Q
  obtain ⟨_, _, _, _, _, hframe, hclose⟩ := hgeometry R₀ hR₀ s u ell hu
  let F := finiteHistoryMap G.map u
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

end JanetCartan.ResponseTransfer.RetainedFactors
