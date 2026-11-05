module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.JointExtensions.Transport.Coefficients

/-!
# Fixed extensions of the actual null-transport coefficients

For `main:prop:current-scale` and `app:eq:uniform-high-coeff`, the finite minor
cover is chosen using the SMALLER agreement balls of the fixed Seeley
operators. The larger original product balls supply all coefficient bounds.
The frame threshold, common physical radius, operators and supports precede
geometric budgets, metric/normal gaps, current immersions and all orders.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.CurrentCoefficientProfiles.JointExtensions
open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame NullTransport
open NullTransport.CoefficientBounds

/-- `main:prop:current-scale`, `app:eq:uniform-high-coeff`: a finite buffered
minor cover of the ORIGINAL closed parameter cube, with one positive physical
radius. All six literal coefficients of the canonical current chart have
fixed smooth compactly supported extensions agreeing on this cover. Their
summed global seminorm is first bounded by the literal larger-ball norm at
the same order, then by primitive immersion data with reserve FIVE.

The threshold `δ` precedes every geometric budget and gap, so the parent
common-reference construction may use it as `CommonProfiles`' additional
frame margin. No transport profile or extension estimate is assumed. -/
theorem exists_transport_extensions_before_geometry {n N : ℕ} (hn : 2 ≤ n)
    {P : Patch n} {c C : ℝ} (hP : P.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : PatchQuantitativeFamily P U hU)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K) :
    ∃ δ ε g : ℝ, 0 < δ ∧ 0 < ε ∧ 0 < g ∧
    ∃ centers : Finset (parameterCube P.radius),
    ∃ row col : centers → Fin n, ∃ ρ L : centers → ℝ,
    ∃ hρ : ∀ j, 0 < ρ j,
    ∃ Ω : centers → Set (Euclidean n × Euclidean 3),
      (∀ j, 0 < L j ∧ IsOpen (Ω j) ∧
        closedBall ((0 : Euclidean n), j.1.1) (ρ j) ⊆ Ω j ∧
        Ω j ⊆ (ball (0 : Euclidean n) T.physicalRadius ∩ interior K) ×ˢ
          parameterInterior (3 * P.radius / 2) ∧
        MapsTo Prod.fst (closedBall ((0 : Euclidean n), j.1.1) (ρ j))
          (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)) ∧
      (closedBall (0 : Euclidean n) ε ×ˢ parameterCube P.radius ⊆
        ⋃ j, closedBall ((0 : Euclidean n), j.1.1)
          (transportExtensionRadius ((0 : Euclidean n), j.1.1) (hρ j))) ∧
      ∃ E : ℕ → ℝ, (∀ m, 0 < E m) ∧
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
          ContDiffOn ℝ ∞ (carrierAdaptedDenominator T Q (row j) (col j)) (Ω j) ∧
          ContDiffOn ℝ ∞ (fun w ↦ (carrierAdaptedDenominator T Q (row j) (col j) w)⁻¹)
            (Ω j) ∧
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
          TransportExtensionProperties ((0 : Euclidean n), j.1.1) (hρ j)
            (carrierNullvector T Q (col j)) ∧
          TransportExtensionProperties ((0 : Euclidean n), j.1.1) (hρ j)
            (carrierConullvector T Q (row j)) ∧
          TransportExtensionProperties ((0 : Euclidean n), j.1.1) (hρ j)
            (carrierAdaptedDenominator T Q (row j) (col j)) ∧
          TransportExtensionProperties ((0 : Euclidean n), j.1.1) (hρ j)
            (fun w ↦ (carrierAdaptedDenominator T Q (row j) (col j) w)⁻¹) ∧
          TransportExtensionProperties ((0 : Euclidean n), j.1.1) (hρ j)
            (carrierTransportDirection T Q (row j) (col j)) ∧
          TransportExtensionProperties ((0 : Euclidean n), j.1.1) (hρ j)
            (carrierTransportPotential T Q F (row j) (col j)) ∧
          ∀ m,
            extendedTransportCoefficientNorm T Q F (row j) (col j)
                ((0 : Euclidean n), j.1.1) (hρ j) m ≤
              E m * currentTransportCoefficientNorm T Q F (row j) (col j)
                (closedBall ((0 : Euclidean n), j.1.1) (ρ j)) m ∧
            extendedTransportCoefficientNorm T Q F (row j) (col j)
                ((0 : Euclidean n), j.1.1) (hρ j) m ≤
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
  let r := fun z : parameterCube P.radius ↦
    transportExtensionRadius ((0 : Euclidean n), z.1) (hρ z)
  have hr (z) : 0 < r z := transportExtensionRadius_pos _ _
  have hc : parameterCube P.radius ⊆
      ⋃ z : parameterCube P.radius, ball z.1 (r z / 2) := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, mem_ball_self (half_pos (hr _))⟩
  obtain ⟨centers, hcenters⟩ := (isCompact_parameterCube P.radius).elim_finite_subcover
    (fun z : parameterCube P.radius ↦ ball z.1 (r z / 2)) (fun _ ↦ isOpen_ball) hc
  obtain ⟨ε, δ, _, hε, _, hδ, _, hcommon⟩ := exists_common_phase_buffers
    (fun j : centers ↦ r j.1 / 2) (fun j : centers ↦ η j.1) (fun _ ↦ (1 : ℝ))
    (fun j ↦ half_pos (hr j.1)) (fun j ↦ hη j.1)
  refine ⟨min δ T.family.threshold, ε, μ * κ, lt_min hδ T.family.threshold_pos,
    hε, mul_pos hμ hκ, centers, (fun j ↦ row j.1), (fun j ↦ col j.1),
    (fun j ↦ ρ j.1), (fun j ↦ L j.1), (fun j ↦ hρ j.1), (fun j ↦ Ω j.1), ?_, ?_, ?_⟩
  · intro j
    exact ⟨hL j.1, hΩ j.1, hwork j.1, (fun _ hw ↦ ⟨hw.1, hw.2.1⟩), hx j.1⟩
  · rintro ⟨x, z⟩ ⟨hx, hz⟩
    obtain ⟨q, hq⟩ := mem_iUnion.mp (hcenters hz)
    obtain ⟨hq', hzq⟩ := mem_iUnion.mp hq
    let j : centers := ⟨q, hq'⟩
    refine mem_iUnion.mpr ⟨j, ?_⟩
    rw [mem_closedBall, Prod.dist_eq, max_le_iff]
    have hh := (hcommon j).1
    exact ⟨(mem_closedBall.mp hx).trans (by change ε ≤ r q; linarith [hr q]),
      (mem_ball.mp hzq).le.trans (by change r q / 2 ≤ r q; linarith [hr q])⟩
  choose E hE hext using fun (j : centers) (m : ℕ) ↦
    exists_extendedTransportCoefficientNorm_le (N := N) T
      ((0 : Euclidean n), j.1.1) (hρ j.1) m
  let Emax := fun m ↦ 1 + ∑ j : centers, E j m
  have hEmax (m) : 0 < Emax m := by
    have hh := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦ (hE j m).le)
    change 0 < 1 + ∑ j : centers, E j m
    linarith
  have hEE (j : centers) (m) : E j m ≤ Emax m := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j : centers ↦ E j m)
      (fun j _ ↦ (hE j m).le) (Finset.mem_univ j)
    change E j m ≤ 1 + ∑ j : centers, E j m
    linarith
  refine ⟨Emax, hEmax, ?_⟩
  intro C₀ κmet κnormal hκmet hκnormal
  choose B hB hbound using fun j : centers ↦ hhigh j.1 C₀ κmet κnormal hκmet hκnormal
  let Bmax := fun m ↦ 1 + ∑ j : centers, B j m
  have hBmax (m) : 0 < Bmax m := by
    have hh := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) ↦ (hB j m).le)
    change 0 < 1 + ∑ j : centers, B j m
    linarith
  have hBB (j : centers) (m) : B j m ≤ Bmax m := by
    have hh := Finset.single_le_sum (s := Finset.univ) (f := fun j : centers ↦ B j m)
      (fun j _ ↦ (hB j m).le) (Finset.mem_univ j)
    change B j m ≤ 1 + ∑ j : centers, B j m
    linarith
  refine ⟨fun m ↦ Emax m * Bmax m, fun m ↦ mul_pos (hEmax m) (hBmax m), ?_⟩
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
  let Q := (⟨projectedStress F, hframe, hlow⟩ :
    {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  intro j
  obtain ⟨hlowj, hk, hl, hd, hp, hnull, hdir, hhighj⟩ :=
    hbound j F hF hi hrank hlowF hmet hnormal
      (hclose.trans_le ((min_le_left _ _).trans (hcommon j).2.1))
  have hinput : Ω j.1 ⊆ inputDomain T := by
    intro w hw
    exact ⟨⟨hKU (interior_subset hw.1.2), hw.1.1⟩,
      fun i ↦ (hw.2.1 i).trans (by linarith [hP.1])⟩
  have hden := contDiffOn_carrierAdaptedDenominator T Q hP (row j.1) (col j.1) hinput
  have hinv := contDiffOn_carrierReciprocalDenominator T Q hP (row j.1) (col j.1)
    hinput (fun w hw ↦ (hnull w hw).2.2.2.2.2.1)
  have hkAt := fun x (hx : x ∈ closedBall ((0 : Euclidean n), j.1.1) (ρ j.1)) ↦
    hk.contDiffAt ((hΩ j.1).mem_nhds (hwork j.1 hx))
  have hlAt := fun x (hx : x ∈ closedBall ((0 : Euclidean n), j.1.1) (ρ j.1)) ↦
    hl.contDiffAt ((hΩ j.1).mem_nhds (hwork j.1 hx))
  have hdenAt := fun x (hx : x ∈ closedBall ((0 : Euclidean n), j.1.1) (ρ j.1)) ↦
    hden.contDiffAt ((hΩ j.1).mem_nhds (hwork j.1 hx))
  have hinvAt := fun x (hx : x ∈ closedBall ((0 : Euclidean n), j.1.1) (ρ j.1)) ↦
    hinv.contDiffAt ((hΩ j.1).mem_nhds (hwork j.1 hx))
  have hdAt := fun x (hx : x ∈ closedBall ((0 : Euclidean n), j.1.1) (ρ j.1)) ↦
    hd.contDiffAt ((hΩ j.1).mem_nhds (hwork j.1 hx))
  have hpAt := fun x (hx : x ∈ closedBall ((0 : Euclidean n), j.1.1) (ρ j.1)) ↦
    hp.contDiffAt ((hΩ j.1).mem_nhds (hwork j.1 hx))
  refine ⟨hk, hl, hden, hinv, hd, hp, hnull, hdir,
    transportExtensionProperties_of_contDiffAt _ _ hkAt,
    transportExtensionProperties_of_contDiffAt _ _ hlAt,
    transportExtensionProperties_of_contDiffAt _ _ hdenAt,
    transportExtensionProperties_of_contDiffAt _ _ hinvAt,
    transportExtensionProperties_of_contDiffAt _ _ hdAt,
    transportExtensionProperties_of_contDiffAt _ _ hpAt, ?_⟩
  intro m
  have hnorm : 0 ≤ currentTransportCoefficientNorm T Q F (row j.1) (col j.1)
      (closedBall ((0 : Euclidean n), j.1.1) (ρ j.1)) m := by
    unfold currentTransportCoefficientNorm
    exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg
      (cNorm_nonneg _ _ _) (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _))
        (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)) (cNorm_nonneg _ _ _)
  have hcompare := (hext j m Q F (row j.1) (col j.1)
    hkAt hlAt hdenAt hinvAt hdAt hpAt).trans
      (mul_le_mul_of_nonneg_right (hEE j m) hnorm)
  refine ⟨hcompare, ?_⟩
  have hlocal : currentTransportCoefficientNorm T Q F (row j.1) (col j.1)
      (closedBall ((0 : Euclidean n), j.1.1) (ρ j.1)) m ≤
        Bmax m * (1 + cNorm K (m + 5) F) :=
    (hhighj m).trans (mul_le_mul_of_nonneg_right (hBB j m)
      (by linarith [cNorm_nonneg K (m + 5) F]))
  exact hcompare.trans ((mul_le_mul_of_nonneg_left hlocal (hEmax m).le).trans_eq
    (mul_assoc _ _ _).symm)

end JanetCartan.CurrentCoefficientProfiles.JointExtensions
