module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SeedTransport
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.MatchedFlows

/-!
# The same smooth seed scalar and its positive contractions

For `paper.tex`, `app:ch_background:eq:bg-Nsigma` and
`app:ch_background:prop:bg-normalized`. The null coefficient producer selects
a minor and a ball for the admitted seed. One actual common-flow construction
then supplies its smooth unit scalar and every positive contraction, with
inverse identities and a common compact footpoint range retained.
Consumer: `MatchedSeedCoefficients` and the finite same-seed assembly.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open NullTransport ActualFlow FlowAmplitude HamiltonPhase NormalizedBackground.SourceGeometry

/-- Construct the seed scalar and its actual positive contractions from the
primitive projected frame margin. The scalar's smoothness, positivity and null
transport equations are proved on the SAME seed witnesses used by ODE
uniqueness. Every contraction has a common inner cylinder and ODE-footpoint
range, independent of the initial density. Flatness and transversality come
from `exists_finite_retained_source_scale_interval`.
Source: `app:ch_background:eq:bg-Nsigma`, `app:ch_background:prop:bg-normalized`. -/
theorem exists_retained_seed_matched_unit_transport {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c₀ C₀ : ℝ} (hP : P.IsValid c₀ C₀)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U) :
    ∃ δ > (0 : ℝ), ∀ (F : Euclidean n → Euclidean N) (_hF : ContDiff ℝ ∞ F)
      (_hi : IsImmersionOn F U) (_hrank : HasFullNormalRankOn F U),
      ∀ Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold},
      Q.1 = projectedStress F →
      (∀ x ∈ U, inducedMetric F x = 1) →
      (∀ v ∈ closedBall (0, T.data.center) T.data.localReference.stateRadius,
        ⟪(normalizedHomogeneousSymbol hU Q.1 Q.2.1).hp v, T.data.adapted.normal⟫_ℝ ≠ 0) →
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
      ∀ z ∈ parameterCube P.radius,
        ∃ row col : Fin n, ∃ τ R : ℝ, 0 < τ ∧ 0 < R ∧
        ∃ D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
        ∃ Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
          IsOpen D ∧
          Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 32) ⊆ D ∧
          C ⁻¹' D ⊆ U ×ˢ parameterInterior (3 * P.radius / 2) ∧
          D ⊆ Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 4) ∧
          ContDiffOn ℝ ∞ Φ (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
          ContDiffOn ℝ ∞ Y D ∧
          MapsTo (fun q ↦ (q.1, Φ q))
            (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) D ∧
          MapsTo (fun q ↦ (q.1, Y q)) D
            (Ioo (-τ) τ ×ˢ ball ((0 : Euclidean (n - 1)), z) (R / 8)) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), Φ (0, p) = p) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
            Y (t, Φ (t, p)) = p) ∧
          (∀ q ∈ D, Φ (q.1, Y q) = q.2) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
            (Φ (t, p)).2 = p.2) ∧
          (∀ q ∈ D, (Y q).2 = q.2.2) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8), ∀ t ∈ Ioo (-τ) τ,
            HasDerivAt (fun s ↦ Φ (s, p))
              ((adaptedCoordinates T.data.adapted
                (carrierTransportDirection T Q row col (C.symm (t, Φ (t, p))))).2, 0) t) ∧
          let α := carrierScalarAmplitude T Q F row col Φ Y (fun _ ↦ 1)
          ContDiffOn ℝ ∞ α (C ⁻¹' D) ∧
          ContDiffOn ℝ ∞ (fun w ↦ α w • carrierNullvector T Q col w) (C ⁻¹' D) ∧
          (∀ p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8),
            α (T.data.adapted.embedding p.1, p.2) = 1) ∧
          (∀ w ∈ C ⁻¹' D, 0 < α w ∧ α w • carrierNullvector T Q col w ≠ 0) ∧
          (∀ w ∈ C ⁻¹' D,
            fderiv ℝ (fun x ↦ α (x, w.2)) w.1 (carrierTransportDirection T Q row col w) +
              carrierTransportPotential T Q F row col w * α w = 0) ∧
          (∀ w ∈ C ⁻¹' D,
            reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
              (fun j ↦ (α w • carrierNullvector T Q col w) j) = 0) ∧
          (∀ w ∈ C ⁻¹' D, carrierConullvector T Q row w ⬝ᵥ reducedOperator F Q.1
            (fun x ↦ α (x, w.2) • carrierNullvector T Q col (x, w.2)) w.1 = 0) ∧
          ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
          ∀ σ : ℝ, 0 < σ → σ ≤ 1 →
          ∀ Qσ : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
            cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
              (Q - fun _ ↦ cubeStress n) < T.family.threshold},
            Qσ.1 = projectedStress (sourceDilation F σ) →
          ∃ Dσ : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)),
          ∃ Φσ Yσ : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3,
            IsOpen Dσ ∧ Ioo (-τ) τ ×ˢ ball (0, z) (R / 32) ⊆ Dσ ∧
            ContDiffOn ℝ ∞ Yσ Dσ ∧
            ContDiffOn ℝ ∞ Yσ
              (Ioo (-(2 * τ)) (2 * τ) ×ˢ ball (0, z) (R / 4)) ∧
            (∀ m, cNorm (Icc (-τ) τ ×ˢ closedBall (0, z) (R / 8)) m Φσ +
              cNorm (Icc (-τ) τ ×ˢ closedBall (0, z) (R / 8)) m Yσ ≤ B m) ∧
            MapsTo (fun q ↦ (q.1, Yσ q)) Dσ
              (Ioo (-τ) τ ×ˢ ball (0, z) (R / 8)) ∧
            (∀ q ∈ Dσ, (Yσ q).2 = q.2.2) ∧
            (∀ p ∈ ball (0, z) (R / 8), Φσ (0, p) = p) ∧
            (∀ p ∈ ball (0, z) (R / 8), ∀ t ∈ Ioo (-τ) τ, Yσ (t, Φσ (t, p)) = p) ∧
            (∀ q ∈ Dσ, Φσ (q.1, Yσ q) = q.2) ∧
            EqOn Φσ (sourceTransportFlow Φ σ)
              (Ioo (-τ) τ ×ˢ ball (0, z) (R / 8)) ∧
            EqOn Yσ (sourceTransportFlow Y σ) Dσ ∧
            EqOn (carrierScalarAmplitude T Qσ (sourceDilation F σ) row col Φσ Yσ (fun _ ↦ σ))
              (sourceAmplitude α σ) (C ⁻¹' Dσ) ∧
            EqOn (fun w ↦ carrierScalarAmplitude T Qσ (sourceDilation F σ)
                row col Φσ Yσ (fun _ ↦ σ) w • carrierNullvector T Qσ col w)
              (sourceAmplitude (fun w ↦ α w • carrierNullvector T Q col w) σ)
              (C ⁻¹' Dσ) := by
  let K := closedBall (0 : Euclidean n) T.data.localReference.stateRadius
  have hK : IsCompact K := isCompact_closedBall _ _
  have hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K := Subset.rfl
  have hKU : K ⊆ U := hphysical
  obtain ⟨δ, μ, κ, hδ, _, _, V, hV, hcover, hcoeff⟩ :=
    exists_projected_null_coefficients (N := N) hn hP T hK hKU hball
  refine ⟨δ, hδ, ?_⟩
  intro F hF hi hrank Q₀ hseed hflat htrans hclose
  obtain ⟨hlow, hc⟩ := hcoeff F hF.contDiffOn hi hrank (by simpa only [hseed] using hclose)
  let Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold} :=
    ⟨projectedStress F, contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF.contDiffOn hi hrank), hlow⟩
  have hQQ : Q = Q₀ := Subtype.ext hseed.symm
  rw [← hQQ] at htrans ⊢
  let C := coordinates (Z := Euclidean 3) (adaptedCoordinates T.data.adapted)
  dsimp only
  intro z hz
  obtain ⟨row, hr⟩ := mem_iUnion.mp (hcover hz)
  obtain ⟨col, hzV⟩ := mem_iUnion.mp hr
  let Ω := (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
    (parameterInterior (3 * P.radius / 2) ∩ V row col)
  have hΩ : IsOpen Ω := (isOpen_ball.inter isOpen_interior).prod
    ((isOpen_parameterInterior _).inter (hV row col))
  have h0K : (0 : Euclidean n) ∈ interior K :=
    mem_interior.mpr ⟨ball 0 T.data.localReference.stateRadius,
      ball_subset_closedBall.trans hball, isOpen_ball,
      mem_ball_self T.data.localReference.stateRadius_pos⟩
  have hzΩ : ((0 : Euclidean n), z) ∈ Ω :=
    ⟨⟨mem_ball_self T.physicalRadius_pos, h0K⟩,
      ⟨fun i ↦ (hz i).trans_lt (by linarith [hP.1]), hzV⟩⟩
  obtain ⟨r, hr, hballΩ⟩ := Metric.isOpen_iff.mp hΩ (0, z) hzΩ
  obtain ⟨hk, _, hd, hp, hnull⟩ := hc row col
  have hpatch : ball ((0 : Euclidean n), z) r ⊆
      ball 0 T.physicalRadius ×ˢ parameterCube (2 * P.radius) := by
    intro w hw
    have hh := hballΩ hw
    exact ⟨hh.1.1, fun i ↦ (hh.2.1 i).le.trans (by linarith [hP.1])⟩
  obtain ⟨R, τ, hR, hτ, _, B, hB, D, Φ, Y, hD, hsmallD, hdomain, hbigD, hΦ, hY,
    hΦD, hYU, hΦ₀, hYΦ, hΦY, hYz, hvelocity, hcurrent⟩ :=
    exists_retained_source_matched_null_flows T Q hF hrank hphysical rfl htrans hflat
      row col hr hpatch (hd.mono hballΩ) (hk.mono hballΩ)
  have hphys : C ⁻¹' D ⊆ Ω := hdomain.trans hballΩ
  have hΦz (p) (hp : p ∈ ball ((0 : Euclidean (n - 1)), z) (R / 8))
      (t) (ht : t ∈ Ioo (-τ) τ) : (Φ (t, p)).2 = p.2 := by
    have hh := hYz _ (hΦD (show (t, p) ∈ Ioo (-τ) τ ×ˢ
      ball ((0 : Euclidean (n - 1)), z) (R / 8) from ⟨ht, hp⟩))
    rw [hYΦ p hp t ht] at hh
    exact hh.symm
  have hsym (w) (hw : w ∈ C ⁻¹' D) (i) : (Q.1 w.1 i).IsSymm :=
    (projectedStress_mem_stressSpace (hF.contDiffAt.of_le (by simp))
      (hrank w.1 (hKU (interior_subset (hphys hw).1.2))) i).1
  obtain ⟨hα, hb, hinit, hpos, _, hscalar, hsymbol, hreduce⟩ :=
    carrierScalarAmplitude_spec T Q F row col isOpen_Ioo ordConnected_Ioo
      isOpen_ball hD ⟨neg_neg_of_pos hτ, hτ⟩ (hk.mono hphys) (hp.mono hphys) hsym
      (fun w hw ↦ (hnull w (hphys hw)).2.2.2.2.2.1)
      (fun w hw ↦ (hnull w (hphys hw)).2.2.1)
      (r := fun _ ↦ 1) contDiffOn_const (fun _ _ ↦ zero_lt_one)
      hΦ hΦD hΦ₀ hY hYU hYΦ hΦY hvelocity
  refine ⟨row, col, τ, R, hτ, hR, D, Φ, Y, hD, hsmallD, ?_, hbigD, hΦ,
    hY, hΦD, hYU, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hα, hb, hinit, ?_, hscalar, hsymbol, hreduce, B, hB, ?_⟩
  · intro w hw
    exact ⟨hKU (interior_subset (hphys hw).1.2), (hphys hw).2.1⟩
  · intro w hw
    exact ⟨hpos w hw, smul_ne_zero (hpos w hw).ne' (hnull w (hphys hw)).1⟩
  · intro σ hσ hσ1 Qσ hQσ
    obtain ⟨Dσ, Φσ, Yσ, hDσ, hsmallσ, _, _, hYσ, hYbufferσ, hnormσ, _, hYzσ, hYUσ,
      hinitσ, hYΦσ, hΦYσ, _, hΦmatch, hYmatch, hαmatch, hbmatch, _⟩ :=
      hcurrent σ hσ hσ1 Qσ hQσ
    exact ⟨Dσ, Φσ, Yσ, hDσ, hsmallσ, hYσ, hYbufferσ, hnormσ, hYUσ, hYzσ, hinitσ,
      hYΦσ, hΦYσ, hΦmatch, hYmatch, hαmatch, hbmatch⟩

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs
