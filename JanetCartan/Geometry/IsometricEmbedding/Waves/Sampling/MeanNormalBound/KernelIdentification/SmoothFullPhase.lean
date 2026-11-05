module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeanNormalBound.KernelIdentification.Assembly

/-!
# A constructed smooth majorant for the actual full-phase normal

This is the final assembly of the kernel/disintegration obligation in the
mask-free proof after `app:ch_waves:eq:sampling-operator-bounds`. The cutoff
and its support radius are constructed before every band, color and kernel.
Only primitive phase/amplitude/cutoff matching remains conditional, with
`RawPrimary.Construction.fullPrimaryWave`, `Leading`, and `FullPhaseCharts`
as its actual producers. Instantiating those inputs for the parent's same
wave family is not a consequence of this deduction. No norm estimate is
assumed or proved here.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped BigOperators ContDiff

namespace JanetCartan.Sampling.MeanNormalBound
open SamplingKernelBounds RawInputPartition SeparatedSampling BackgroundQuadrature ContinuumRow
open NormalComparison ColoredNormalComparison NormalizedFullPhase

/-- Construct one smooth majorant per original chart, then identify its
normal with the spectator integral of the actual full-phase band sum.
The original `ψ` remains in the unmasked mean on the left. The displayed
matching conditions are primitive equalities of phases, measured amplitudes
and input supports; the normal comparison and Bochner integrability are
proved. The consumer is the unmasked side of
`norm_refinedKernelPrefix_mean_le_unmasked`
(`app:ch_waves:eq:sampling-prefix-normal`,
`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_smooth_majorants_fullPhase_normal
    {A : Type*} [Fintype A] {ψ : A → Point → ℝ} {B : ℝ} {P : A → ℝ}
    (hψ : ∀ a, PatchBounds (ψ a) B (P a)) (hψc : ∀ a, Continuous (ψ a))
    {U : A → Set Point} (hU : ∀ a, IsOpen (U a))
    (hψU : ∀ a, tsupport (ψ a) ⊆ U a) :
    ∃ (χ : A → Point → ℝ) (R : A → ℝ),
      (∀ a, 0 < R a) ∧ (∀ a, ContDiff ℝ ∞ (χ a)) ∧
      (∀ a, HasCompactSupport (χ a)) ∧ (∀ a, PatchBounds (χ a) (R a) 1) ∧
      (∀ a, tsupport (χ a) ⊆ U a) ∧
      (∀ a, tsupport (ψ a) ⊆ interior {z | χ a z = 1}) ∧
      ∀ (m J p : ℕ)
        (D : A → BandKernelData (Fin J × ((Fin 3 → Fin (p + 1)) × Point)) (m + 1))
        (G : A → UniformNormalGeometry (m + 1) (m + 1)) (C : A → ℕ → ℝ)
        (F : (a : A) → (Fin 3 → Fin (p + 1)) → Fin J → Euclidean 2 →
          UniformNormalData (G a) (C a))
        (ε : A → (Fin 3 → Fin (p + 1)) → Fin J → Euclidean 2 → ℝ),
        (∀ a c j v, ε a c j v ∈ Set.Icc 0 (G a).ε₀) →
        (∀ a c (j : Fin J) v,
          ∀ u ∈ Set.Icc (-(R a)) (R a) ×ˢ wideBand (m + 1) 0, ∀ x,
            (D a).phase (((j, (c, carrierSamplingEquiv (u.1, v))),
              (2 : ℝ) ^ j.val • u.2), x) =
              (2 : ℝ) ^ j.val * (F a c j v).phase (ε a c j v) x
                (fullInputCoordinates m u)) →
        (∀ a c (j : Fin J) v,
          ∀ u ∈ Set.Icc (-(R a)) (R a) ×ˢ wideBand (m + 1) 0, ∀ x i,
            (Real.sqrt (((2 : ℝ) ^ j.val) ^ m) : ℂ) *
              (χ a (carrierSamplingEquiv (u.1, v)) : ℂ) *
              (Real.sqrt ‖(2 : ℝ) ^ j.val • u.2‖ : ℂ) *
              (D a).mask ((2 : ℝ) ^ j.val • u.2) *
              (D a).amplitude (((j, (c, carrierSamplingEquiv (u.1, v))),
                (2 : ℝ) ^ j.val • u.2), x) i =
            (normalOperatorScale (m + 1) ((2 : ℝ) ^ j.val) : ℂ) *
              (F a c j v).amplitude (ε a c j v) x (fullInputCoordinates m u) i) →
        (∀ a c j v w, w ∉ fullInputDomain m 0 (R a) → ∀ x,
          (F a c j v).amplitude (ε a c j v) x w = 0) →
        (∀ a c, Integrable (fun v : Euclidean 2 ↦ ∑ j : Fin J,
          ((F a c j v).uniformOscillatoryOperator
            ((2 : ℝ) ^ j.val) (ε a c j v)).comp
              ((F a c j v).uniformOscillatoryOperator
            ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint)) ∧
        (∑ a, ∑ c, ∫ z : Point,
          ψ a z • atomNormal (refinedKernelPrefix (D a) J (c, z))) ≤
          samplingOutputConjugation (m + 1)
            (∑ a, P a • ∑ c, ∫ v : Euclidean 2, ∑ j : Fin J,
              ((F a c j v).uniformOscillatoryOperator
                ((2 : ℝ) ^ j.val) (ε a c j v)).comp
                  ((F a c j v).uniformOscillatoryOperator
                ((2 : ℝ) ^ j.val) (ε a c j v)).adjoint) := by
  classical
  choose χ R hR hχs hc hb hs hp using
    fun a ↦ exists_smooth_patch_majorant (hψ a) (hU a) (hψU a)
  refine ⟨χ, R, hR, hχs, hc, hb, hs, hp, ?_⟩
  intro m J p D G C F ε hε hphase hamplitude hsupport
  constructor
  · exact integrable_matched_uniformNormal_sum D hb (fun a ↦ (hχs a).continuous)
      F ε hε hphase hamplitude hsupport
  · exact sum_integral_refinedKernelPrefix_normal_le_uniformNormal D hb
      (fun a ↦ (hχs a).continuous) F ε hε hphase hamplitude hsupport hψ hψc
      (fun a z hz ↦ interior_subset (s := {z | χ a z = 1})
        (hp a (subset_tsupport (ψ a) hz)))

end JanetCartan.Sampling.MeanNormalBound
