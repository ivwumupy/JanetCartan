module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedLabels
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedSelection.FrozenUnit

/-!
# Frozen density weights from the original selected product

The original forward domain and label bound place the full frozen mask in the
unchanged scalar class. The actual inverse identity then supplies the bounded
smooth input multiplier without another geometric selection.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.NormalizedSelection
open ActualCarriers FrozenMenu CurrentFullPhase CanonicalCarrier CanonicalConic
open ContinuumNormal FrozenModel FrozenModel.InitialMultiplier
open ContinuumNormal.CarrierVariation.FamilyInputs PositiveReference PositiveReference.FlowConstruction
open FullPhaseCharts ActualComparison NullTransport ActualFlow FlowAmplitude

/-- Construct the original square-root density's smooth label representative
from the selected density product. The time-zero inverse is identified using
the same seed chart, and the generic multiplier construction uses the original
`L/4` smoothness and `L/8` interval. Consumer: the positive-density part of
`InitializedFrozenSeedGap` on the measured incidence family
(`new:lem:scaling`, `app:ch_background:prop:bg-frame`,
`app:ch_background:eq:bg-realification`). -/
theorem exists_sqrt_labelWeight_on_original_density_product
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {Ω K : Set (Euclidean n × Euclidean 3)} {zCell : Euclidean 3}
    {Rc B τ : ℝ} {row col : Fin n} {F : Euclidean n → Euclidean N}
    (seed : Chart T Ω K ((0 : Euclidean (n - 1)), zCell) Rc B τ row col F)
    (hRc : 0 < Rc) (hτ : 0 < τ)
    {L R r a aMask : ℝ} (hL : 0 < L) (haMask : 0 < aMask)
    (haa : aMask ≤ a) (har : 6 * a ≤ 3 * r) {zRoot : Euclidean 3}
    {V : Set CarrierParameter}
    (houter : coefficientDomain zRoot r (6 * a) ⊆ ball (0 : Euclidean n) R ×ˢ V)
    (hflow : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V)
      (outputCylinder ((0 : Euclidean (n - 1)), zCell) Rc τ))
    (hlabel : ∀ p ∈ ball (0 : Euclidean n) R ×ˢ V,
      (densityCoordinates T p).2 ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64))
    (v : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hv : ContDiffOn ℝ ∞ v (ball ((0 : Euclidean (n - 1)), zCell) (L / 4)))
    (hden : ∀ q ∈ closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8),
      1 + v q ∈ Icc (1 / 2 : ℝ) (3 / 2)) :
    ∃ β : CarrierParameter → ℝ,
      ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ (∀ z, 0 ≤ β z) ∧ (∀ z, ‖β z‖ ≤ 4) ∧
      EqOn β (labelWeight seed.inverse (fun q ↦ Real.sqrt (1 + v q)))
        (carrierSupport zRoot (r := aMask)) ∧
      (∀ z ∈ carrierSupport zRoot (r := aMask),
        labelWeight seed.inverse (fun q ↦ Real.sqrt (1 + v q)) z = 1 + v (0, parameter z)) ∧
      ∀ z ∈ carrierSupport zRoot (r := aMask),
        (1 / 2 : ℝ) ≤ Real.sqrt (1 + v (seed.inverse (0, (0, parameter z)))) := by
  let Z := ball (zRoot 0) (2 * aMask) ×ˢ ball (spectatorCenter zRoot) (6 * aMask)
  let sectionMap := fun z : CarrierParameter ↦ ((0 : ℝ), ((0 : Euclidean (n - 1)), parameter z))
  let Dflow := sectionMap '' Z
  have hZE (z) (hz : z ∈ Z) : ((0 : Euclidean n), z) ∈ ball (0 : Euclidean n) R ×ˢ V := by
    apply houter
    exact ⟨mem_ball_self (by linarith), ball_subset_ball (by linarith) hz.1,
      ball_subset_ball (by linarith) hz.2⟩
  have hcoords : MapsTo (densityCoordinates T) (ball (0 : Euclidean n) R ×ˢ V) seed.D :=
    fun _ hp ↦ seed.small_subset ((outputCylinder_spec hRc hτ).2 (hflow hp))
  have hzero (z) (hz : z ∈ Z) : seed.inverse (sectionMap z) = (0, parameter z) :=
    RetainedLabels.inverseLabel_zero_of_retained_cell T hcoords Subset.rfl
      seed.forward seed.inverse seed.inverse_range seed.initial seed.forward_inverse (hZE z hz)
  have hlabelZ (z) (hz : z ∈ Z) : ((0 : Euclidean (n - 1)), parameter z) ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8) := by
    have hh := hlabel _ (hZE z hz)
    change (coordinates (adaptedCoordinates T.data.adapted) (0, parameter z)).2 ∈
      closedBall ((0 : Euclidean (n - 1)), zCell) (L / 64) at hh
    simp only [coordinates_apply, map_zero, Prod.snd_zero] at hh
    exact closedBall_subset_closedBall (show L / 64 ≤ L / 8 by linarith) hh
  have hDflow : Dflow ⊆ seed.D := by
    rintro _ ⟨z, hz, rfl⟩
    have hh := hcoords (hZE z hz)
    change coordinates (adaptedCoordinates T.data.adapted) (0, parameter z) ∈ seed.D at hh
    simpa only [sectionMap, coordinates_apply, map_zero, Prod.fst_zero, Prod.snd_zero] using hh
  have hrange : MapsTo seed.inverse Dflow (closedBall ((0 : Euclidean (n - 1)), zCell) (L / 8)) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [hzero z hz]
    exact hlabelZ z hz
  obtain ⟨β, hβ, hc, hn, hb, heq, _⟩ := exists_bounded_smooth_sqrt_labelWeight zRoot haMask
    (r := 2 * aMask) (by linarith) seed.inverse v
    (hv.mono (closedBall_subset_ball (by linarith))) hden
    (seed.inverse_smooth.mono hDflow) (fun z hz ↦ mem_image_of_mem sectionMap hz) hrange
  have hs {z} (hz : z ∈ carrierSupport zRoot (r := aMask)) : z ∈ Z :=
    ⟨closedBall_subset_ball (by linarith) hz.1, closedBall_subset_ball (by linarith) hz.2⟩
  refine ⟨β, hβ, hc, hn, hb, heq, ?_, ?_⟩
  · intro z hz
    rw [labelWeight, hzero z (hs hz), Real.sq_sqrt (by linarith [(hden _ (hlabelZ z (hs hz))).1])]
  · intro z hz
    rw [hzero z (hs hz)]
    apply Real.le_sqrt_of_sq_le
    linarith [(hden _ (hlabelZ z (hs hz))).1]

end JanetCartan.ContinuumRow.NormalizedSelection
