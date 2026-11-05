module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.TransportProfiles.LocalBounds

/-!
# A fixed finite refinement for the transport coefficient profiles

For `main:prop:current-scale`, the compact carrier cube is covered before the
source scale and the geometric gaps are chosen. The same fixed balls support
all six literal transport coefficients and every derivative order.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.CurrentCoefficientProfiles
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame NullTransport

/-- The six actual joint transport coefficients in
`app:eq:uniform-high-coeff`, including the reciprocal denominator and the
zeroth-order potential with all Christoffel terms. -/
def currentTransportCoefficientNorm {n N : ℕ} {P : Patch n}
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (J : Set (Euclidean n × Euclidean 3)) (m : ℕ) : ℝ :=
  cNorm J m (carrierNullvector T Q col) +
    cNorm J m (carrierConullvector T Q row) +
    cNorm J m (carrierAdaptedDenominator T Q row col) +
    cNorm J m (fun w ↦ (carrierAdaptedDenominator T Q row col w)⁻¹) +
    cNorm J m (carrierTransportDirection T Q row col) +
    cNorm J m (carrierTransportPotential T Q F row col)

/-- `main:prop:current-scale`: one finite minor refinement and frame threshold
precede the source scale, immersion budget and normal gap. The same compact
balls cover a fixed physical neighborhood times the original closed carrier
cube. The sole analytic inputs to the high constants are primitive geometry;
the six coefficient estimates themselves are proved from their formulas. -/
theorem exists_transport_refinement_before_geometry {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ ε g : ℝ, 0 < δ ∧ 0 < ε ∧ 0 < g ∧
    ∃ centers : Finset (parameterCube P.radius),
    ∃ row col : centers → Fin n, ∃ ρ L : centers → ℝ,
    ∃ Ω : centers → Set (Euclidean n × Euclidean 3),
      (∀ j, 0 < ρ j ∧ 0 < L j ∧ IsOpen (Ω j) ∧
        closedBall ((0 : Euclidean n), j.1.1) (ρ j) ⊆ Ω j ∧
        Ω j ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
          parameterInterior (3 * P.radius / 2)) ∧
      (closedBall (0 : Euclidean n) ε ×ˢ parameterCube P.radius ⊆
        ⋃ j, closedBall ((0 : Euclidean n), j.1.1) (ρ j)) ∧
      ∀ (C₀ κmet κnormal : ℝ), 0 < κmet → 0 < κnormal →
      ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κnormal * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < δ →
        ∃ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ j : centers,
          ContDiffOn ℝ ∞ (carrierNullvector T Q (col j)) (Ω j) ∧
          ContDiffOn ℝ ∞ (carrierConullvector T Q (row j)) (Ω j) ∧
          ContDiffOn ℝ ∞ (carrierTransportDirection T Q (row j) (col j)) (Ω j) ∧
          ContDiffOn ℝ ∞ (carrierTransportPotential T Q F (row j) (col j)) (Ω j) ∧
          (∀ w ∈ Ω j,
            carrierNullvector T Q (col j) w ≠ 0 ∧ carrierConullvector T Q (row j) w ≠ 0 ∧
            reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) *ᵥ
              (fun k ↦ carrierNullvector T Q (col j) w k) = 0 ∧
            carrierConullvector T Q (row j) w ᵥ*
              reducedSymbol (Q.1 w.1) (T.carrierGradient Q w.1 w.2) = 0 ∧
            g ≤ |carrierAdaptedDenominator T Q (row j) (col j) w| ∧
            carrierAdaptedDenominator T Q (row j) (col j) w ≠ 0 ∧
            |(carrierAdaptedDenominator T Q (row j) (col j) w)⁻¹| ≤ g⁻¹) ∧
          cNorm (closedBall ((0 : Euclidean n), j.1.1) (ρ j)) 1
            (carrierTransportDirection T Q (row j) (col j)) ≤ L j ∧
          ∀ m, currentTransportCoefficientNorm T Q F (row j) (col j)
            (closedBall ((0 : Euclidean n), j.1.1) (ρ j)) m ≤
              B m * (1 + cNorm K (m + 5) F) := by
  classical
  obtain ⟨δ₀, μ, κ, hδ₀, hμ, hκ, V, hV, hcover, hcoeff⟩ :=
    exists_transport_coefficient_bounds_before_geometry (N := N) hn hP T hK hKU hball
  have hchoose (z : parameterCube P.radius) : ∃ row col, z.1 ∈ V row col := by
    obtain ⟨row, hrow⟩ := mem_iUnion.mp (hcover z.2)
    obtain ⟨col, hcol⟩ := mem_iUnion.mp hrow
    exact ⟨row, col, hcol⟩
  choose row col hminor using hchoose
  let Ω := fun z : parameterCube P.radius ↦
    (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
      (parameterInterior (3 * P.radius / 2) ∩ V (row z) (col z))
  have hΩ (z) : IsOpen (Ω z) :=
    (isOpen_ball.inter isOpen_interior).prod
      ((isOpen_parameterInterior _).inter (hV (row z) (col z)))
  have h0K : (0 : Euclidean n) ∈ interior K :=
    mem_interior.mpr ⟨ball 0 T.data.localReference.stateRadius,
      ball_subset_closedBall.trans hball, isOpen_ball,
      mem_ball_self T.data.localReference.stateRadius_pos⟩
  have hzΩ (z : parameterCube P.radius) : ((0 : Euclidean n), z.1) ∈ Ω z :=
    ⟨⟨mem_ball_self T.physicalRadius_pos, h0K⟩,
      ⟨fun i ↦ (z.2 i).trans_lt (by linarith [hP.1]), hminor z⟩⟩
  choose ρ R hρ _hR hwork hx _hbuffer using fun z ↦
    exists_adapted_coefficient_ball T (hΩ z) z.1 (hzΩ z)
  choose η L hη _hηδ hL hhigh using fun z ↦
    hcoeff (row z) (col z) (0, z.1) (ρ z) (hρ z) (hx z) (hwork z)
  have hc : parameterCube P.radius ⊆
      ⋃ z : parameterCube P.radius, ball z.1 (ρ z / 2) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (half_pos (hρ _))⟩
  obtain ⟨centers, hcenters⟩ := (isCompact_parameterCube P.radius).elim_finite_subcover
    (fun z : parameterCube P.radius ↦ ball z.1 (ρ z / 2)) (fun _ ↦ isOpen_ball) hc
  obtain ⟨ε, δ, _, hε, _, hδ, _, hcommon⟩ := exists_common_phase_buffers
    (fun j : centers ↦ ρ j.1 / 2) (fun j : centers ↦ η j.1) (fun _ ↦ (1 : ℝ))
    (fun j ↦ half_pos (hρ j.1)) (fun j ↦ hη j.1)
  refine ⟨min δ T.family.threshold, ε, μ * κ, lt_min hδ T.family.threshold_pos,
    hε, mul_pos hμ hκ, centers, (fun j ↦ row j.1), (fun j ↦ col j.1),
    (fun j ↦ ρ j.1), (fun j ↦ L j.1), (fun j ↦ Ω j.1), ?_, ?_, ?_⟩
  · intro j
    exact ⟨hρ j.1, hL j.1, hΩ j.1, hwork j.1, fun _ hw ↦ ⟨hw.1, hw.2.1⟩⟩
  · rintro ⟨x, z⟩ ⟨hx, hz⟩
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcenters hz)
    obtain ⟨hq', hzq⟩ := mem_iUnion.mp hq
    let j : centers := ⟨q, hq'⟩
    refine mem_iUnion.mpr ⟨j, ?_⟩
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    have hh := (hcommon j).1
    exact ⟨(mem_closedBall.mp hx).trans (by linarith [hρ q]),
      (mem_ball.mp hzq).le.trans (by linarith [hρ q])⟩
  intro C₀ κmet κnormal hκmet hκnormal
  choose B hB hbound using fun j : centers ↦ hhigh j.1 C₀ κmet κnormal hκmet hκnormal
  let Bmax := fun m ↦ 1 + ∑ j : centers, B j m
  have hBmax (m) : 0 < Bmax m := by
    have hh := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦ (hB j m).le)
    change 0 < 1 + ∑ j : centers, B j m
    linarith
  refine ⟨Bmax, hBmax, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hclose
  have hframe := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold := by
    apply (cNorm_mono_set_of_contDiffAt hball hK _).trans_lt
      (hclose.trans_le (min_le_right _ _))
    intro x hx
    exact ((hframe.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp)
  refine ⟨hlow, ?_⟩
  dsimp only
  intro j
  obtain ⟨hlowj, hk, hl, hd, hp, hnull, hdir, hhighj⟩ :=
    hbound j F hF hi hrank hlowF hmet hnormal
      (hclose.trans_le ((min_le_left _ _).trans (hcommon j).2.1))
  refine ⟨hk, hl, hd, hp, hnull, hdir, ?_⟩
  intro m
  apply (hhighj m).trans
  apply mul_le_mul_of_nonneg_right _ (by linarith [cNorm_nonneg K (m + 5) F])
  have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j : centers ↦ B j m)
    (fun j _ ↦ (hB j m).le) (Finset.mem_univ j)
  change B j m ≤ 1 + ∑ j : centers, B j m
  linarith

end JanetCartan.CurrentCoefficientProfiles
