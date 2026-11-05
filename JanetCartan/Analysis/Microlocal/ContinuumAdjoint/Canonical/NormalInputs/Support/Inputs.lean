module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Geometry
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DerivativeKernels.ExpansionSupport.Conic

/-!
# Original support inside the phase-restricted canonical chart

These are the compact supports, `hdom`, `hJ`, and the input containment used by
`exists_scalarTransportCarrierAdjoint_periodic_raw_bound` and the normalized-jet
construction. All radii and supports are fixed before the current immersion.
Source: `app:ch_background:prop:bg-adjoint`, `bg-full-complex-amplitude`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
open ContinuumRow DerivativeKernels ModifiedNormalSymbol PhaseExtension
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open CanonicalConic ContinuumNormalReduction.TransportSymbol
open ContinuumRow.TransportKernel

variable {n : ℕ}

/-- Strictly smaller closed masks lie in the interior of the phase-agreement
chart, including the physical and BOTH carrier coordinates (`bg-Psi`). -/
theorem supportedChart_subset_interior_supportedChart {z₀ : Euclidean 3}
    {aMask aPhase : ℝ} (ha : aMask < aPhase) :
    supportedChart (n := n) z₀ aMask ⊆ interior (supportedChart z₀ aPhase) := by
  rw [supportedChart, supportedChart, carrierSupport, carrierSupport,
    interior_prod_eq, interior_prod_eq]
  rintro p ⟨hx, hs, hv⟩
  exact ⟨ball_subset_interior_closedBall (closedBall_subset_ball (by linarith) hx),
    ball_subset_interior_closedBall (closedBall_subset_ball (by linarith) hs),
    ball_subset_interior_closedBall (closedBall_subset_ball (by linarith) hv)⟩

/-- Select positive mask radii strictly below the outer radii and the phase
radius, while retaining the input-ball refinement of `exists_refined_mask_radii`.
There is no current immersion in this choice (`bg-full-complex-amplitude`). -/
theorem exists_normalSupport_radii {r a aPhase d : ℝ} (hr : 0 < r) (ha : 0 < a)
    (hphase : 0 < aPhase) (hd : 0 < d) :
    ∃ rMask > (0 : ℝ), rMask < r ∧ rMask ≤ d ∧
      ∃ aMask > (0 : ℝ), aMask < a ∧ aMask < aPhase ∧
        aMask ≤ rMask ∧ 4 * aMask < d := by
  obtain ⟨rMask, hrMask, hrr, hrd, aMask, haMask, haa, har, had⟩ :=
    exists_refined_mask_radii (half_pos hr) (half_pos (lt_min ha hphase)) hd
  exact ⟨rMask, hrMask, hrr.trans_lt (half_lt_self hr), hrd,
    aMask, haMask,
    haa.trans_lt ((half_lt_self (lt_min ha hphase)).trans_le (min_le_left _ _)),
    haa.trans_lt ((half_lt_self (lt_min ha hphase)).trans_le (min_le_right _ _)), har, had⟩

/-- The three fixed compact supports required by the raw adjoint endpoint
(`app:ch_background:prop:bg-adjoint`). -/
theorem normalSupport_compact_parameters (z₀ : Euclidean 3)
    (ηb : Euclidean (n - 1)) (rMask aMask : ℝ) :
    IsCompact (closedBall (0 : Euclidean n) (4 * aMask)) ∧
      IsCompact (carrierSupport z₀ (r := aMask)) ∧
      IsCompact (closedDirections ηb rMask) :=
  ⟨isCompact_closedBall _ _, carrierSupport_compact z₀,
    closedDirections_compact ηb rMask⟩

/-- The fixed angular support consists of unit covectors
(`app:ch_background:prop:bg-adjoint`). -/
theorem normalSupport_directions_unit (ηb : Euclidean (n - 1)) (rMask : ℝ) :
    closedDirections ηb rMask ⊆ {η | ‖η‖ = 1} :=
  fun _ hp ↦ mem_sphere_zero_iff_norm.mp hp.1

/-- Both physical positions in the original conic mask satisfy phase agreement
on a neighborhood (`app:ch_background:eq:bg-Psi`). -/
theorem conicMaskSupport_subset_phaseAgreementDomain {z₀ : Euclidean 3}
    {ηb : Euclidean (n - 1)} {rMask aMask aPhase : ℝ} (ha : aMask < aPhase) :
    conicMaskSupport z₀ ηb rMask aMask ⊆ phaseAgreementDomain z₀ aPhase := by
  intro p hp
  exact ⟨supportedChart_subset_interior_supportedChart ha ⟨hp.1.1, hp.2.1⟩,
    supportedChart_subset_interior_supportedChart ha ⟨hp.1.2, hp.2.1⟩⟩

variable {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {rMask aMask : ℝ}

/-- The original support is exactly the intersection of the endpoint's two
conic buffers, at the SAME carrier and covector (`bg-full-complex-amplitude`). -/
theorem normalSupport_mem_iff_conicBuffers (p : JointVariables n) :
    p ∈ normalSupport T z₀ ηb rMask aMask ↔
      ((jointInputCoordinates T p).2.1, p.1.1, (jointInputCoordinates T p).2.2) ∈
        adjointConicBuffer (closedBall 0 (4 * aMask)) (carrierSupport z₀ (r := aMask))
          (closedDirections ηb rMask) 1 ∧
      ((jointInputCoordinates T p).2.1, p.1.2.1, (jointInputCoordinates T p).2.2) ∈
        adjointConicBuffer (closedBall 0 (4 * aMask)) (carrierSupport z₀ (r := aMask))
          (closedDirections ηb rMask) 1 := by
  constructor
  · intro hp
    exact ⟨⟨hp.1.2.1, hp.1.1.1, hp.1.2.2.2, hp.2⟩,
      ⟨hp.1.2.1, hp.1.1.2, hp.1.2.2.2, hp.2⟩⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨⟨hx.2.1, hy.2.1⟩, hx.1,
      norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hx.2.2.2), hx.2.2.1⟩, hx.2.2.2⟩

/-- The positive original frequency threshold closes the unbounded input
support. This is an input statement, before applying the canonical map
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalSupport_isClosed : IsClosed (normalSupport T z₀ ηb rMask aMask) := by
  have hc := isClosed_adjointConicBuffer (n := n)
    (X := closedBall 0 (4 * aMask)) isClosed_closedBall
    (carrierSupport_compact z₀ (r := aMask)).isClosed
    (closedDirections_compact ηb rMask).isClosed (by norm_num : (0 : ℝ) < 1)
  have he : normalSupport T z₀ ηb rMask aMask =
      (fun p : JointVariables n ↦
        ((jointInputCoordinates T p).2.1, p.1.1, (jointInputCoordinates T p).2.2)) ⁻¹'
        adjointConicBuffer (closedBall 0 (4 * aMask)) (carrierSupport z₀ (r := aMask))
          (closedDirections ηb rMask) 1 ∩
      (fun p : JointVariables n ↦
        ((jointInputCoordinates T p).2.1, p.1.2.1, (jointInputCoordinates T p).2.2)) ⁻¹'
        adjointConicBuffer (closedBall 0 (4 * aMask)) (carrierSupport z₀ (r := aMask))
          (closedDirections ηb rMask) 1 :=
    Set.ext (normalSupport_mem_iff_conicBuffers T)
  rw [he]
  exact (hc.preimage ((jointInputCoordinates T).continuous.snd.fst.prodMk
    (continuous_fst.fst.prodMk (jointInputCoordinates T).continuous.snd.snd))).inter
      (hc.preimage ((jointInputCoordinates T).continuous.snd.fst.prodMk
        (continuous_fst.snd.fst.prodMk (jointInputCoordinates T).continuous.snd.snd)))

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    {r a aPhase : ℝ}

/-- The exact input-containment premise for the independent normalized-jet
helper. The outer physical parameter is `6 * a`; the masks can be any smaller
refinement, strictly inside the phase chart (`bg-Psi`). -/
theorem normalSupport_subset_inputDomain (hηb : ηb ≠ 0) (hr : 0 < r)
    (ha : 0 < a) (har : a ≤ r) (hrr : rMask ≤ r) (haa : aMask ≤ a)
    (hphase : aMask < aPhase) :
    normalSupport T z₀ ηb rMask aMask ⊆
      (normalChart T Q z₀ ηb r (6 * a) aPhase).inputDomain := by
  intro p hp
  exact ⟨conicMaskSupport_subset hηb hr ha har
    (conicMaskSupport_mono z₀ ηb hrr haa hp.1),
    conicMaskSupport_subset_phaseAgreementDomain hphase hp.1⟩

/-- The raw endpoint's `hdom`, with its literal carrier coordinates and both
original amplitude supports (`app:ch_background:prop:bg-adjoint`). -/
theorem normalChart_domain_of_conicBuffers (hηb : ηb ≠ 0) (hr : 0 < r)
    (ha : 0 < a) (har : a ≤ r) (hrr : rMask ≤ r) (haa : aMask ≤ a)
    (hphase : aMask < aPhase) (x y : Euclidean n) (v : Euclidean 2) (w : Euclidean n)
    (hx : ((chartCarrierVariable (normalChart T Q z₀ ηb r (6 * a) aPhase).coordinates v w).1,
      x, (chartCarrierVariable (normalChart T Q z₀ ηb r (6 * a) aPhase).coordinates v w).2) ∈
        adjointConicBuffer (closedBall 0 (4 * aMask)) (carrierSupport z₀ (r := aMask))
          (closedDirections ηb rMask) 1)
    (hy : ((chartCarrierVariable (normalChart T Q z₀ ηb r (6 * a) aPhase).coordinates v w).1,
      y, (chartCarrierVariable (normalChart T Q z₀ ηb r (6 * a) aPhase).coordinates v w).2) ∈
        adjointConicBuffer (closedBall 0 (4 * aMask)) (carrierSupport z₀ (r := aMask))
          (closedDirections ηb rMask) 1) :
    w ∈ (normalChart T Q z₀ ηb r (6 * a) aPhase).domain x y v := by
  change ((x, y, w), v) ∈ (normalChart T Q z₀ ηb r (6 * a) aPhase).inputDomain
  apply normalSupport_subset_inputDomain T Q hηb hr ha har hrr haa hphase
  exact (normalSupport_mem_iff_conicBuffers T ((x, y, w), v)).mpr ⟨hx, hy⟩

/-- The raw endpoint's `hJ`, proved directly from the original supports;
input-domain membership is not needed (`bg-full-complex-amplitude`). -/
theorem normalSupport_of_conicBuffers {aOuter : ℝ} (p : JointVariables n)
    (hx : (((normalChart T Q z₀ ηb r aOuter aPhase).carrier p).1, p.1.1,
      ((normalChart T Q z₀ ηb r aOuter aPhase).carrier p).2) ∈
        adjointConicBuffer (closedBall 0 (4 * aMask)) (carrierSupport z₀ (r := aMask))
          (closedDirections ηb rMask) 1)
    (hy : (((normalChart T Q z₀ ηb r aOuter aPhase).carrier p).1, p.1.2.1,
      ((normalChart T Q z₀ ηb r aOuter aPhase).carrier p).2) ∈
        adjointConicBuffer (closedBall 0 (4 * aMask)) (carrierSupport z₀ (r := aMask))
          (closedDirections ηb rMask) 1) :
    p ∈ normalSupport T z₀ ηb rMask aMask :=
  (normalSupport_mem_iff_conicBuffers T p).mpr ⟨hx, hy⟩

end JanetCartan.ContinuumAdjoint.Canonical.NormalInputs
