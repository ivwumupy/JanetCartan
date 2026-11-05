module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.WeakDerivatives.Cutoff
public import JanetCartan.Analysis.Sobolev.Local.Basic

/-!
# Weak jets of the unchanged raw slice integral

For `app:ch_waves:eq:individual-raw-slice` and `app:ch_waves:thm:individual`,
the original measurable bounded detector/high-pass and arbitrary `WideInput`
datum give a smooth compactly supported measured field. Its literal integral
jets satisfy all finite-order weak identities and belong to L². These jets
construct the existing weak-Sobolev extensions, without a derivative-interchange,
weak-identity or Sobolev-membership premise.

The primitive phase/amplitude smoothness and shifted-frequency containment
come from the larger WKB validity charts; the fixed physical cutoff must be
supported there. The differentiated slice assembly must instantiate these
inputs for its canonical derivative amplitude and prove its sharp
`K^(s+1/2)` estimate separately. Compactness here proves integrability only.
The original `cutoffCount K` and proved `4 K` input ceiling are retained.
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.SliceBounds

open RawInputPartition

variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Smoothness, compact support, exact integral jets, all weak identities,
and L² membership for the same measured field on arbitrary original wide data
(`app:ch_waves:eq:individual-raw-slice`). The codomain includes the canonical
Frobenius derivative matrix. No sharp frequency estimate is asserted. -/
theorem rawSlice_weightedWideDensity_regular
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V)
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {A : Euclidean n → Euclidean (n - 1) → F}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {χ : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    {ζ : Euclidean (n - 1)} {τ K : ℝ} (hζ : ζ ∈ V) (hK : 1 ≤ K)
    (hshift : ∀ η ∈ Metric.closedBall 0 (4 * K), ζ + τ • η ∈ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hdb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n (cutoffCount K)) :
    let g := fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ volume
      (weightedWideDensity d v) x
    let J := rawSliceIntegralJet χ S A ζ τ volume (weightedWideDensity d v)
    ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ j, J j = iteratedFDeriv ℝ j g) ∧
      (∀ s, Mollification.HasWeakJetOn volume g J univ s) ∧
      MemLp g 2 volume ∧ (∀ j, MemLp (J j) 2 volume) := by
  let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Euclidean (n - 1))
      (4 * K))) := isFiniteMeasure_restrict.mpr (isCompact_closedBall _ _).measure_lt_top.ne
  have hf := integrable_wideDensity hd hM hdb v
  have hfT : ∀ᵐ η ∂volume, η ∉ Metric.closedBall 0 (4 * K) →
      weightedWideDensity d v η = 0 := by
    filter_upwards [] with η hη
    exact wideDensity_eq_zero_of_four_mul_le hK d v (le_of_lt (by simpa using hη))
  have hg := contDiff_cut_rawPrimaryDemodulatedIntegral hU hV (isCompact_closedBall _ _)
    hS hA hχ hχU hζ hshift hf hfT
  have hgc := hasCompactSupport_cut_rawPrimaryDemodulatedIntegral hχc S A ζ τ volume
    (weightedWideDensity d v)
  have hJ := rawSliceIntegralJet_eq_iteratedFDeriv hU hV (isCompact_closedBall _ _)
    hS hA hχ hχU hζ hshift hf hfT
  refine ⟨hg, hgc, hJ, ?_, hg.continuous.memLp_of_hasCompactSupport hgc, ?_⟩
  · intro s
    have heq := funext hJ
    rw [heq]
    exact Mollification.hasWeakJetOn_of_contDiff volume (hg.of_le (by simp)) univ
  · intro j
    rw [hJ j]
    exact (hg.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
      (hgc.iteratedFDeriv j)

/-- Construct whole-space weak-Sobolev extensions of the actual measured
raw slice, with exactly its integral jets, for every finite order. The local
L² class is constructed from the same field, on any measurement set `Q`
(`app:ch_waves:eq:individual-raw-slice`). -/
theorem exists_rawSlice_weightedWideDensity_sobolevExtensions
    {U : Set (Euclidean n)} {V : Set (Euclidean (n - 1))}
    (hU : IsOpen U) (hV : IsOpen V)
    {S : Euclidean n → Euclidean (n - 1) → ℝ}
    {A : Euclidean n → Euclidean (n - 1) → F}
    (hS : ContDiffOn ℝ ∞ (Function.uncurry S) (U ×ˢ V))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (U ×ˢ V))
    {χ : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    {ζ : Euclidean (n - 1)} {τ K : ℝ} (hζ : ζ ∈ V) (hK : 1 ≤ K)
    (hshift : ∀ η ∈ Metric.closedBall 0 (4 * K), ζ + τ • η ∈ V)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hdb : ∀ η, ‖d η‖ ≤ M)
    (v : WideInput n (cutoffCount K)) (Q : Set (Euclidean n)) :
    let g := fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ volume
      (weightedWideDensity d v) x
    let J := rawSliceIntegralJet χ S A ζ τ volume (weightedWideDensity d v)
    ∃ u : LocalSobolev.LocalL2 Q F, g =ᵐ[volume.restrict Q] u ∧
      (∀ s, LocalSobolev.MemRestrictionSobolev Q s u) ∧
      ∀ s, ∃ e : LocalSobolev.SobolevExtension Q s u, e.toFun = g ∧ e.jet = J := by
  obtain ⟨_, _, _, hw, hg, hJ⟩ := rawSlice_weightedWideDensity_regular
    hU hV hS hA hχ hχc hχU hζ hK hshift hd hM hdb v
  dsimp only
  let g := fun x ↦ χ x • rawPrimaryDemodulatedIntegral S A ζ τ volume
    (weightedWideDensity d v) x
  let u := (hg.restrict Q).toLp g
  have hu : g =ᵐ[volume.restrict Q] u := (hg.restrict Q).coeFn_toLp.symm
  let e (s : ℕ) : LocalSobolev.SobolevExtension Q s u :=
    { toFun := g
      jet := rawSliceIntegralJet χ S A ζ τ volume (weightedWideDensity d v)
      weakJet := hw s
      memLp_fun := hg
      memLp_jet := fun j _ ↦ hJ j
      restrict_eq := hu }
  exact ⟨u, hu, fun s ↦ ⟨e s⟩, fun s ↦ ⟨e s, rfl, rfl⟩⟩

end JanetCartan.RawPrimary.SliceBounds
