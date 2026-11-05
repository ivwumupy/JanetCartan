module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.RetainedLeading.InitialBuffer
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.NormalInputs.Support.Inputs
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.FlowConstruction.Chart

/-!
# The original retained initial scalar on a different carrier tube

The full leading scalar is controlled on its original `R / 8` ball, whereas
the carrier flow uses `Rc / 8`. These radii need not agree. The fixed initial
bump gives a smooth positive extension to the carrier tube. Its transported
scalar agrees with the ORIGINAL scalar wherever the actual inverse footpoint
lies in `R / 16`, including after multiplication by the original density.

Consumer: the retained-chart primitive comparison in `FamilyInputs.RetainedLeading`.
Sources: `app:ch_background:prop:bg-frame`, `app:ch_background:prop:bg-normalized`,
`app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport ActualFlow FlowAmplitude
open ContinuumRow ContinuumAdjoint.Canonical ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumAdjoint.Canonical.PhaseExtension PositiveReference

variable {n : ℕ}

/-- Extend the prescribed scalar using only its original norm domain. The
constant part ensures positivity outside the initial bump; it has no effect
on the supported transported scalar (`app:ch_background:prop:bg-frame`). -/
def positiveInitialExtension (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    Euclidean (n - 1) × Euclidean 3 → ℝ :=
  fun p ↦ initialBump z₀ hR p * initial p + (1 - initialBump z₀ hR p)

/-- The extension needs smoothness only on the ORIGINAL `R / 8` ball.
In particular it is smooth on every carrier initial ball, independently of
`Rc` (`app:ch_waves:eq:joint-tame`). -/
theorem positiveInitialExtension_contDiff (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ContDiffOn ℝ ∞ initial (ball ((0 : Euclidean (n - 1)), z₀) (R / 8))) :
    ContDiff ℝ ∞ (positiveInitialExtension z₀ hR initial) := by
  have hh : ContDiff ℝ ∞ (fun p ↦ initialBump z₀ hR p * initial p) :=
    Localization.contDiff_of_contDiffOn_support_neighborhood isOpen_ball
      ((initialBump z₀ hR).contDiff.contDiffOn.mul hi)
      (tsupport_mul_subset_left.trans (initialBump_tsupport_subset z₀ hR))
  exact hh.add (contDiff_const.sub (initialBump z₀ hR).contDiff)

/-- The prescribed positive scalar extends positively to every carrier
initial ball without assuming an inclusion between `Rc / 8` and `R / 8`
(`app:ch_background:prop:bg-frame`). -/
theorem positiveInitialExtension_pos (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hi : ∀ p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 8), 0 < initial p)
    (p : Euclidean (n - 1) × Euclidean 3) :
    0 < positiveInitialExtension z₀ hR initial p := by
  by_cases hp : initialBump z₀ hR p = 0
  · simp [positiveInitialExtension, hp]
  · have hmem := initialBump_tsupport_subset z₀ hR (subset_closure hp)
    have hpos := mul_pos (lt_of_le_of_ne (initialBump z₀ hR).nonneg (Ne.symm hp)) (hi p hmem)
    have hle := (initialBump z₀ hR).le_one (x := p)
    dsimp only [positiveInitialExtension]
    linarith

/-- The extension agrees on a neighborhood of every original scalar
footpoint in `R / 16`, hence preserves every ambient jet there
(`app:ch_waves:eq:joint-tame`). -/
theorem positiveInitialExtension_eventuallyEq (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {p : Euclidean (n - 1) × Euclidean 3}
    (hp : p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) :
    positiveInitialExtension z₀ hR initial =ᶠ[𝓝 p] initial := by
  filter_upwards [initialBump_eventuallyEq_one z₀ hR hp] with q hq
  simp [positiveInitialExtension, show initialBump z₀ hR q = 1 from hq]

variable {N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- At the SAME ODE inverse label the positive extension gives exactly the
original transported scalar, including any prescribed initial multiplier.
The multiplier is unrestricted, so this identity retains the original wider
density class of `app:ch_background:prop:bg-frame`. -/
theorem carrierScalarAmplitude_positiveInitialExtension_eq
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial weight : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {p : Euclidean n × CarrierParameter}
    (hp : densityFootpoint T y p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) :
    carrierScalarAmplitude T Q F row col φ y
        (fun q ↦ positiveInitialExtension z₀ hR initial q * weight q)
        (p.1, CanonicalCarrier.parameter p.2) =
      carrierScalarAmplitude T Q F row col φ y (fun q ↦ initial q * weight q)
        (p.1, CanonicalCarrier.parameter p.2) := by
  have he := (positiveInitialExtension_eventuallyEq z₀ hR initial hp).eq_of_nhds
  change positiveInitialExtension z₀ hR initial
      (y (coordinates (adaptedCoordinates T.data.adapted)
        (p.1, CanonicalCarrier.parameter p.2))) = _ at he
  simp only [carrierScalarAmplitude, transportFromFootpoint, characteristicTransport,
    scalarTransport, he]
  rfl

/-- The SAME null column, completion and initial multiplier give exactly the
same normal after the auxiliary positive extension. This preserves the full
normal factors in `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem normalField_positiveInitialExtension_eq
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : Euclidean 3) {R : ℝ} (hR : 0 < R)
    (initial weight : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {p : Euclidean n × CarrierParameter}
    (hp : densityFootpoint T y p ∈ ball ((0 : Euclidean (n - 1)), z₀) (R / 16)) :
    CanonicalCarrier.normalField T Q F row col φ y
        (fun q ↦ positiveInitialExtension z₀ hR initial q * weight q) p.1 p.2 =
      CanonicalCarrier.normalField T Q F row col φ y
        (fun q ↦ initial q * weight q) p.1 p.2 := by
  simp only [CanonicalCarrier.normalField,
    carrierScalarAmplitude_positiveInitialExtension_eq T Q F row col φ y z₀ hR initial weight hp]

/-- A cap chosen from the retained carrier forward map controls the original
scalar on a neighborhood of the COMPLETE supported carrier chart. No new
flow is selected. All inputs are exported by the full leading producer;
the original scalar domain and `Rc` remain distinct
(`app:ch_background:prop:bg-frame`, `app:ch_waves:eq:joint-tame`). -/
theorem exists_positiveInitialExtension_agreement_cap
    (z₀ : Euclidean 3) {R Rc τc Mc : ℝ}
    (hR : 0 < R) (hRc : 0 < Rc) (hτc : 0 < τc) (hMc : 0 < Mc) :
    ∃ cap > (0 : ℝ), ∀ {a : ℝ}, 0 < a → a < cap →
      ∀ (D : Set (ℝ × (Euclidean (n - 1) × Euclidean 3)))
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3),
      let pc := ((0 : Euclidean (n - 1)), z₀)
      Ioo (-τc) τc ×ˢ ball pc (Rc / 32) ⊆ D →
      MapsTo (fun q ↦ (q.1, y q)) D (Ioo (-τc) τc ×ˢ ball pc (Rc / 8)) →
      (∀ p ∈ ball pc (Rc / 8), φ (0, p) = p) →
      (∀ q ∈ D, φ (q.1, y q) = q.2) →
      ContDiffOn ℝ ∞ φ (Ioo (-(2 * τc)) (2 * τc) ×ˢ ball pc (Rc / 4)) →
      cNorm (Icc (-τc) τc ×ˢ closedBall pc (Rc / 8)) 1 φ ≤ Mc →
      MapsTo (densityFootpoint T y) (supportedChart z₀ (2 * a)) (ball pc (R / 16)) ∧
      ∀ (F : Euclidean n → Euclidean N) (row col : Fin n)
        (initial weight : Euclidean (n - 1) × Euclidean 3 → ℝ),
      ∀ p ∈ supportedChart z₀ a,
        (fun q : Euclidean n × CarrierParameter ↦ carrierScalarAmplitude T Q F row col φ y
          (fun v ↦ positiveInitialExtension z₀ hR initial v * weight v)
          (q.1, CanonicalCarrier.parameter q.2)) =ᶠ[𝓝 p]
        (fun q ↦ carrierScalarAmplitude T Q F row col φ y
          (fun v ↦ initial v * weight v) (q.1, CanonicalCarrier.parameter q.2)) := by
  obtain ⟨cap, hcap, hbuffer⟩ :=
    ContinuumAdjoint.Canonical.RetainedLeading.exists_supportedChart_initialBuffer_before_budgets
      T z₀ hR hRc hτc hMc
  refine ⟨cap / 2, by positivity, ?_⟩
  intro a ha hacap D φ y pc hcover hy hφ₀ hφy hφ hflow
  have htwo : 0 < 2 * a := by positivity
  have htwoCap : 2 * a < cap := by linarith
  obtain ⟨_, hfoot⟩ := hbuffer htwo htwoCap D φ y hcover hy hφ₀ hφy hφ hflow
  refine ⟨hfoot, ?_⟩
  intro F row col initial weight p hp
  have hmem := ContinuumAdjoint.Canonical.NormalInputs.supportedChart_subset_interior_supportedChart
    (n := n) (z₀ := z₀) (show a < 2 * a by linarith) hp
  filter_upwards [mem_interior_iff_mem_nhds.mp hmem] with q hq
  exact carrierScalarAmplitude_positiveInitialExtension_eq T Q F row col φ y z₀ hR
    initial weight (hfoot hq)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.RetainedLeading
