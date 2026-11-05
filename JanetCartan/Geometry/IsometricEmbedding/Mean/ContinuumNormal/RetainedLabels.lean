module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.CarrierGraph
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.KernelCoefficients
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.InitialMultiplier.Realization

/-!
# Frozen initial multipliers on the retained leading cell

The incidence center and the selected flow center need not agree. The retained
full-modulation graph buffer places the original labels in the scalar's `L / 8`
ball. The inverse-flow identities then give the exact time-zero label. Neither
step chooses another flow, another minor or another angular mask.

`exists_sqrt_initial_realization_of_retained_cell` constructs the bounded input
multiplier and identifies its composition with the same supplied unit carrier.
It retains the original density interval, literal test and adjoint actions,
Lebesgue input space, both real quadratures, and the normal's factor four.

The geometric inputs are the outputs of
`CurrentCoefficientProfiles.exists_full_joint_leading_wave_before_geometry_with_carrier_data_and_working_balls`
and `ContinuumRow.LeadingCarrier.exists_leading_carrier_buffers`, retained by
`ReferenceInitialization.NormalizedHistory.exists_common_normalized_history_reference_with_chart_centers_and_carrier_data`. In
particular that stronger initializer retains `Vcomp ⊆ Dc`; the projection in
`ContinuumRow.InitializedLeading` does not retain this inclusion. The final
normal assembly must use the stronger SAME witnesses before projecting them.
The unit test/adjoint input still requires the frozen realization on the selected
row masks; no unit gap or current normal comparison is assumed or proved here.

Sources: `app:ch_background:prop:bg-frame`, `app:ch_background:eq:bg-T`,
`app:ch_background:eq:bg-realification`, and v2 `new:lem:scaling`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedLabels
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow CanonicalCarrier CanonicalConic LeadingPrimitive
open FrozenModel.InitialMultiplier FullPhaseCharts ActualComparison

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The retained full graph buffer puts its time-zero carrier labels in the
ORIGINAL scalar ball, even when the flow center differs from the incidence
center. The `L / 64` buffer is a conclusion of the leading construction,
not a new label-cap assumption (`app:ch_waves:eq:joint-tame`,
`app:ch_background:prop:bg-frame`). -/
theorem initialLabel_mem_of_retained_graph (zc : Euclidean 3) {L τ σ : ℝ} (hL : 0 < L) (hσ : 0 < σ)
    (hworking : closedBall ((0 : Euclidean n), (zc, T.reference.spatialPatch zc)) (2 * σ) ⊆
      (coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τ / 2) (τ / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), (zc, T.reference.spatialPatch zc)) (L / 64)))
    {z : CarrierParameter}
    (hz : carrierGraph T (0, z) ∈
      closedBall ((0 : Euclidean n), (zc, T.reference.spatialPatch zc)) σ) :
    ((0 : Euclidean (n - 1)), parameter z) ∈
      ball ((0 : Euclidean (n - 1)), zc) (L / 8) := by
  obtain ⟨q, hq, he⟩ := hworking (closedBall_subset_closedBall (by linarith) hz)
  have hcoord := congrArg (coordinates (adaptedCoordinates T.data.adapted)) he
  simp only [ContinuousLinearEquiv.apply_symm_apply, carrierGraph, coordinates_apply,
    map_zero, Prod.fst_zero, Prod.snd_zero] at hcoord
  rw [hcoord] at hq
  have hlabel : dist (parameter z) zc ≤ L / 64 := by
    have hp := hq.2
    simp only [mem_closedBall, Prod.dist_eq, dist_self, max_le_iff] at hp
    exact hp.2.1
  simp only [mem_ball, Prod.dist_eq, dist_self, max_lt_iff]
  exact ⟨by positivity, hlabel.trans_lt (by linarith)⟩

/-- The retained compatibility inclusion and the actual inverse-flow equations
compute the time-zero footpoint on the selected cell. The flow range, initial
identity and right inverse all come from the SAME full-modulation producer
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`). -/
theorem inverseLabel_zero_of_retained_cell {E : Set (Euclidean n × CarrierParameter)}
    {Vcomp Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hcoords : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) E Vcomp)
    (hcompat : Vcomp ⊆ Dc)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {I : Set ℝ} {L : Set (Euclidean (n - 1) × Euclidean 3)}
    (hrange : MapsTo (fun q ↦ (q.1, y q)) Dc (I ×ˢ L))
    (hφ0 : ∀ p ∈ L, φ (0, p) = p)
    (hφy : ∀ q ∈ Dc, φ (q.1, y q) = q.2)
    {z : CarrierParameter} (hz : ((0 : Euclidean n), z) ∈ E) :
    y (0, (0, parameter z)) = (0, parameter z) := by
  have hDc := hcompat (hcoords hz)
  simp only [coordinates_apply, map_zero,
    Prod.fst_zero, Prod.snd_zero] at hDc
  have he := hφy _ hDc
  rw [hφ0 _ (hrange hDc).2] at he
  exact he



/-- Construct the smooth bounded label representative on the original retained
cell, using only the row's `aMask ≤ r` and `aMask ≤ a` mask inequalities.
The auxiliary representative cutoff has plateau on the ENTIRE original carrier
support; it does not change that support or the angular width. The graph buffer
and inverse-flow identities prove the literal weight `1 + v (0, parameter z)`.
The scalar's original `L / 4` smoothness and `L / 8` density interval suffice
(`app:ch_background:prop:bg-frame`). Consumer:
`exists_sqrt_initial_realization_of_retained_cell`. -/
theorem exists_retained_sqrt_labelWeight
    (zc z₀ : Euclidean 3) {L τ σ r a aMask : ℝ}
    (hL : 0 < L) (hσ : 0 < σ) (haMask : 0 < aMask)
    (hmaskr : aMask ≤ r) (hmaska : aMask ≤ a)
    {E : Set (Euclidean n × CarrierParameter)}
    (houter : coefficientDomain z₀ r (6 * a) ⊆ E)
    (hgraph : MapsTo (carrierGraph T) E
      (closedBall ((0 : Euclidean n), (zc, T.reference.spatialPatch zc)) σ))
    (hworking : closedBall ((0 : Euclidean n), (zc, T.reference.spatialPatch zc)) (2 * σ) ⊆
      (coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τ / 2) (τ / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), (zc, T.reference.spatialPatch zc)) (L / 64)))
    {Vcomp Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hcoords : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) E Vcomp)
    (hcompat : Vcomp ⊆ Dc)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {I : Set ℝ} {Dinitial : Set (Euclidean (n - 1) × Euclidean 3)}
    (hrange : MapsTo (fun q ↦ (q.1, y q)) Dc (I ×ˢ Dinitial))
    (hφ0 : ∀ p ∈ Dinitial, φ (0, p) = p)
    (hφy : ∀ q ∈ Dc, φ (q.1, y q) = q.2)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hv : ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zc) (L / 4)))
    (hden : ∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zc) (L / 8),
      1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
    let initial := fun q ↦ Real.sqrt (1 + v q)
    ∃ b : CarrierParameter → ℝ,
      ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ (∀ z, 0 ≤ b z) ∧
      (∀ z, ‖b z‖ ≤ 4) ∧
      EqOn b (labelWeight y initial) (carrierSupport z₀ (r := aMask)) ∧
      (∀ z ∈ carrierSupport z₀ (r := aMask),
        labelWeight y initial z = 1 + v (0, parameter z)) ∧
      (∀ z ∈ carrierSupport z₀ (r := aMask), (1 / 2 : ℝ) ≤ initial (y (0, (0, parameter z)))) := by
  let Z := ball (z₀ 0) aMask ×ˢ ball (spectatorCenter z₀) aMask
  have hZE (z) (hz : z ∈ Z) : ((0 : Euclidean n), z) ∈ E := by
    apply houter
    refine ⟨mem_ball_self (by linarith), ?_, ?_⟩
    · exact ball_subset_ball hmaskr hz.1
    · exact ball_subset_ball (by linarith) hz.2
  have hlabel (z) (hz : z ∈ Z) : ((0 : Euclidean (n - 1)), parameter z) ∈
      ball ((0 : Euclidean (n - 1)), zc) (L / 8) :=
    initialLabel_mem_of_retained_graph T zc hL hσ hworking (hgraph (hZE z hz))
  have hyzero (z) (hz : z ∈ Z) : y (0, (0, parameter z)) = (0, parameter z) :=
    inverseLabel_zero_of_retained_cell T hcoords hcompat φ y hrange hφ0 hφy (hZE z hz)
  let χ : ContDiffBump (z₀ 0, spectatorCenter z₀) :=
    { rIn := aMask / 2
      rOut := 3 * aMask / 4
      rIn_pos := half_pos haMask
      rIn_lt_rOut := by linarith }
  have hZopen : IsOpen Z := isOpen_ball.prod isOpen_ball
  have hχZ : tsupport χ ⊆ Z := by
    rw [χ.tsupport_eq]
    intro z hz
    have hz' : z ∈ ball (z₀ 0, spectatorCenter z₀) aMask :=
      closedBall_subset_ball (by change 3 * aMask / 4 < aMask; linarith) hz
    simpa only [Z, ← ball_prod_same] using hz'
  have hweightsmooth : ContDiffOn ℝ ∞ (fun z : CarrierParameter ↦ 1 + v (0, parameter z)) Z :=
    contDiffOn_const.add (hv.comp
      (contDiffOn_const.prodMk parameter.contDiff.contDiffOn)
      (fun z hz ↦ ball_subset_ball (by linarith) (hlabel z hz)))
  let b := fun z : CarrierParameter ↦ χ z * (1 + v (0, parameter z))
  have hb : ContDiff ℝ ∞ b := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact χ.contDiffAt.mul (hweightsmooth.contDiffAt (hZopen.mem_nhds (hχZ hz)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with q hq
      simp only [b, hq, Pi.zero_apply, zero_mul]
  have hdenZ z (hz : z ∈ Z) := hden _ (ball_subset_closedBall (hlabel z hz))
  have hs z (hz : z ∈ carrierSupport z₀ (r := aMask)) : z ∈ Z :=
    ⟨closedBall_subset_ball (by linarith) hz.1,
      closedBall_subset_ball (by linarith) hz.2⟩
  have hweight z (hz : z ∈ carrierSupport z₀ (r := aMask)) :
      labelWeight y (fun q ↦ Real.sqrt (1 + v q)) z = 1 + v (0, parameter z) := by
    rw [labelWeight, hyzero z (hs z hz), Real.sq_sqrt (by linarith [(hdenZ z (hs z hz)).1])]
  refine ⟨b, hb, χ.hasCompactSupport.mul_right, ?_, ?_, ?_, hweight, ?_⟩
  · intro z
    by_cases hz : z ∈ tsupport χ
    · exact mul_nonneg χ.nonneg (by linarith [(hdenZ z (hχZ hz)).1])
    · simp only [b, image_eq_zero_of_notMem_tsupport hz, zero_mul, le_refl]
  · intro z
    by_cases hz : z ∈ tsupport χ
    · have hnorm : ‖1 + v (0, parameter z)‖ ≤ (3 / 2 : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hdenZ z (hχZ hz)).1])]
        exact (hdenZ z (hχZ hz)).2
      calc
        ‖b z‖ = χ z * ‖1 + v (0, parameter z)‖ := by
          change ‖χ z * (1 + v (0, parameter z))‖ = _
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
        _ ≤ 1 * (3 / 2 : ℝ) := mul_le_mul χ.le_one hnorm (norm_nonneg _) zero_le_one
        _ ≤ 4 := by norm_num
    · simp only [b, image_eq_zero_of_notMem_tsupport hz, zero_mul, norm_zero]
      norm_num
  · intro z hz
    rw [hweight z hz]
    change χ z * (1 + v (0, parameter z)) = 1 + v (0, parameter z)
    rw [χ.one_of_mem_closedBall (by simpa only [carrierSupport, closedBall_prod_same] using hz), one_mul]
  · intro z hz
    rw [hyzero z (hs z hz)]
    apply Real.le_sqrt_of_sq_le
    linarith [(hdenZ z (hs z hz)).1]

/-- Realize the nonconstant frozen carrier on the supplied retained cell and
unit operator, with the SAME selected minor, flows, measurement, angular mask
and high cutoff. The representative and all its bounds are constructed above
from the actual leading geometry. Literal realization and uniqueness reuse
`InitialMultiplier.Realization`; no independent carrier is identified by fiat.
The unit realization remains an explicit input of this relative construction,
with producer the common-mask frozen construction. The finite gap and current
normal comparison remain with the parent (`app:ch_background:eq:bg-T`,
`app:ch_background:eq:bg-realification`, `app:ch_background:prop:bg-frame`). -/
theorem exists_sqrt_initial_realization_of_retained_cell
    (zc z₀ : Euclidean 3) {L τ σ r a aMask : ℝ}
    (hL : 0 < L) (hσ : 0 < σ) (haMask : 0 < aMask)
    (hmaskr : aMask ≤ r) (hmaska : aMask ≤ a)
    {E : Set (Euclidean n × CarrierParameter)}
    (houter : coefficientDomain z₀ r (6 * a) ⊆ E)
    (hgraph : MapsTo (carrierGraph T) E
      (closedBall ((0 : Euclidean n), (zc, T.reference.spatialPatch zc)) σ))
    (hworking : closedBall ((0 : Euclidean n), (zc, T.reference.spatialPatch zc)) (2 * σ) ⊆
      (coordinates (adaptedCoordinates T.data.adapted)).symm ''
        (Icc (-τ / 2) (τ / 2) ×ˢ
          closedBall ((0 : Euclidean (n - 1)), (zc, T.reference.spatialPatch zc)) (L / 64)))
    {Vcomp Dc : Set (ℝ × (Euclidean (n - 1) × Euclidean 3))}
    (hcoords : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      coordinates (adaptedCoordinates T.data.adapted) (p.1, parameter p.2)) E Vcomp)
    (hcompat : Vcomp ⊆ Dc)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    {I : Set ℝ} {Dinitial : Set (Euclidean (n - 1) × Euclidean 3)}
    (hrange : MapsTo (fun q ↦ (q.1, y q)) Dc (I ×ˢ Dinitial))
    (hφ0 : ∀ p ∈ Dinitial, φ (0, p) = p)
    (hφy : ∀ q ∈ Dc, φ (q.1, y q) = q.2)
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hv : ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zc) (L / 4)))
    (hden : ∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zc) (L / 8),
      1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2))
    {N : ℕ}
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    {μ δ : ℝ} (hμ : 0 < μ) (hμcell : 4 * μ < 1 / 2)
    (θ : Euclidean (n - 1)) (hδ : 0 < δ) (high : ℝ → ℝ)
    (V : CarrierL2 n →L[ℂ] ComplexOutputL2 n)
    (hVtest : ∀ f : carrierInitialTestSpace n,
      V (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral
        (FrozenModel.normalizedCarrierData T Q F row col φ y (fun _ ↦ 1) hμ hμcell
          (angularMask z₀ θ haMask hδ) high 0) f.val)
    (hVadj : ∀ w : ComplexOutputL2 n,
      V.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral
        (FrozenModel.normalizedCarrierData T Q F row col φ y (fun _ ↦ 1) hμ hμcell
          (angularMask z₀ θ haMask hδ) high 0) w) :
    let initial := fun q ↦ Real.sqrt (1 + v q)
    let e := FrozenModel.normalizedCarrierData T Q F row col φ y initial hμ hμcell
      (angularMask z₀ θ haMask hδ) high 0
    ∃ (b : CarrierParameter → ℝ) (hb : ContDiff ℝ ∞ b) (hbb : ∀ z, ‖b z‖ ≤ 4),
      HasCompactSupport b ∧ (∀ z, 0 ≤ b z) ∧
      EqOn b (labelWeight y initial) (carrierSupport z₀ (r := aMask)) ∧
      (∀ z ∈ carrierSupport z₀ (r := aMask),
        labelWeight y initial z = 1 + v (0, parameter z)) ∧
      let M := labelMultiplier (n := n) b hb.continuous hbb
      let W := V ∘L M
      ‖M‖ ≤ 4 ∧ M.adjoint = M ∧ ‖W‖ ≤ ‖V‖ * 4 ∧
      (∀ f : carrierInitialTestSpace n,
        W (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) ∧
      (∀ f : CarrierL2 n, ∀ᵐ x ∂volume, x ∉ e.outputChart → W f x = 0) ∧
      (∀ Z : CarrierL2 n →L[ℂ] ComplexOutputL2 n,
        (∀ f : carrierInitialTestSpace n,
          Z (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val) → Z = W) ∧
      (∀ w : ComplexOutputL2 n,
        MemLp (carrierAdjointIntegral e w) 2 (carrierMeasure n) ∧
        W.adjoint w =ᵐ[carrierMeasure n] carrierAdjointIntegral e w) ∧
      (∀ w : OutputL2 n, (1 / 16 : ℝ) * ‖(realQuadratureChannel V).adjoint w‖ ^ 2 ≤
        ‖(realQuadratureChannel W).adjoint w‖ ^ 2) ∧
      W ∘L W.adjoint = V ∘L (M ∘L M) ∘L V.adjoint ∧
      realQuadratureChannel W ∘L (realQuadratureChannel W).adjoint =
        (4 : ℝ) • realOutputCompression (V ∘L (M ∘L M) ∘L V.adjoint) := by
  obtain ⟨b, hb, hc, hn, hbb, heq, hlabel, hlower⟩ :=
    exists_retained_sqrt_labelWeight T zc z₀ hL hσ haMask hmaskr hmaska houter
      hgraph hworking hcoords hcompat φ y hrange hφ0 hφy v hv hden
  let initial := fun q ↦ Real.sqrt (1 + v q)
  let angular := angularMask z₀ θ haMask hδ
  let e := FrozenModel.normalizedCarrierData T Q F row col φ y initial hμ hμcell angular high 0
  let M := labelMultiplier (n := n) b hb.continuous hbb
  let W := V ∘L M
  have hang : ∀ z ∉ carrierSupport z₀ (r := aMask), ∀ η, angular z η = 0 :=
    fun z hz η ↦ angularMask_zero_outside z₀ θ haMask hδ hz η
  have hM : ‖M‖ ≤ 4 := labelMultiplier_norm_le b hb.continuous (by norm_num) hbb
  have htest : ∀ f : carrierInitialTestSpace n,
      W (carrierInitialTestToLp f) =ᵐ[volume] carrierTestIntegral e f.val :=
    labelMultiplier_test_action T Q F row col φ y initial hμ hμcell angular high
      hang b hb hbb heq V hVtest
  refine ⟨b, hb, hbb, hc, hn, heq, hlabel, hM, labelMultiplier_adjoint b hb.continuous hbb,
    (ContinuousLinearMap.opNorm_comp_le V M).trans
      (mul_le_mul_of_nonneg_left hM (norm_nonneg V)), htest,
    carrierRealization_eq_zero_outside e W htest, ?_, ?_, ?_,
    labelMultiplier_complex_normal b hb.continuous hbb V,
    labelMultiplier_real_normal b hb.continuous hbb V⟩
  · exact fun Z hZ ↦ FrozenModel.carrierExtensions_eq_of_initialTests e W Z htest hZ
  · intro w
    exact ⟨labelMultiplier_adjoint_memLp T Q F row col φ y initial hμ hμcell angular high
      hang b hb.continuous hbb heq V hVadj w,
      labelMultiplier_adjoint_action T Q F row col φ y initial hμ hμcell angular high
        hang b hb.continuous hbb heq V hVadj w⟩
  · exact labelMultiplier_real_adjoint_comparison T Q F row col φ y initial hμ hμcell
      angular high hang b hb.continuous hbb heq hlower V hVadj

end JanetCartan.ContinuumNormal.RetainedLabels
