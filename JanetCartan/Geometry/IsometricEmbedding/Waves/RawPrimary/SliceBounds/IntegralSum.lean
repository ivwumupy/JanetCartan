module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BandIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.Atoms

/-!
# Reassembling the literal raw wide-band integral

The finite sum in `app:ch_waves:eq:individual-raw-slice` is the original
`weightedWideDensity` integral. Integrability is proved on the compact original
bands for arbitrary L² data. The sharp two-piece refinement never enters the
amplitude, and the physical cutoff is used only in the measured output.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.RawPrimary.SliceBounds
open RawInputPartition

variable {n J : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A continuous atom on an original wide band can be integrated against
every weighted Hilbert datum. This justifies finite integral reassembly in
`app:ch_waves:eq:individual-raw-slice`, without an assumed kernel realization. -/
theorem integrable_weightedWideBand_atom
    {d : Euclidean (n - 1) → ℂ} {M : ℝ} (hd : Measurable d)
    (hdb : ∀ η, ‖d η‖ ≤ M) (j : ℕ) (f : WideBandL2 n j)
    (B : Euclidean (n - 1) → E) (hB : ContinuousOn B (wideBand n j)) :
    Integrable (fun η ↦
      ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j η * f η) • B η) := by
  have hK : IsCompact (wideBand n j) :=
    (isCompact_closedBall _ _).diff Metric.isOpen_ball
  let : IsFiniteMeasure (volume.restrict (wideBand n j)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hf : IntegrableOn f (wideBand n j) volume :=
    (Lp.memLp f).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hw := hf.bdd_mul
    (measurable_weightedRadialBand hd j).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_weightedRadialBand_le hdb j))
  have hc : ContinuousOn (fun η ↦ (Real.sqrt ‖η‖ : ℂ) • B η) (wideBand n j) :=
    ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_norm)).continuousOn).smul hB
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  have hi := hw.smul_bdd C (hc.aestronglyMeasurable hK.measurableSet)
    ((ae_restrict_mem hK.measurableSet).mono (fun η hη ↦ hC η hη))
  have hi' : IntegrableOn (fun η ↦
      ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j η * f η) • B η)
      (wideBand n j) volume := by
    apply hi.congr
    filter_upwards [] with η
    change (weightedRadialBand d j η * f η) • ((Real.sqrt ‖η‖ : ℂ) • B η) =
      ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j η * f η) • B η
    rw [smul_smul]
    congr 1
    ring
  exact hi'.integrable_of_forall_notMem_eq_zero (fun η hη ↦ by
    simp [weightedRadialBand_eq_zero_off_wideBand d hη])

/-- The original finite wide input integrates as the sum of its original
smooth-band contributions (`app:ch_waves:eq:individual-raw-slice`). -/
theorem integral_weightedWideDensity_smul_eq_sum
    {d : Euclidean (n - 1) → ℂ} {M : ℝ} (hd : Measurable d)
    (hdb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J)
    (B : Euclidean (n - 1) → E)
    (hB : ∀ j : Fin J, ContinuousOn B (wideBand n j.val)) :
    (∫ η, weightedWideDensity d v η • B η) =
      ∑ j : Fin J, ∫ η,
        ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j.val η * v j η) • B η := by
  simp only [weightedWideDensity, Finset.sum_smul]
  exact integral_finsetSum _ (fun j _ ↦
    integrable_weightedWideBand_atom hd hdb j.val (v j) B (hB j))

variable {X : Type*}

/-- Reassembly is equality of the SAME cut demodulated integral. The
continuity premise is only for the density-free original atom on each compact
band; `contDiffOn_rawPrimaryDemodulatedAtom` produces it from the buffered
phase/amplitude charts (`app:ch_waves:eq:individual-raw-slice`). -/
theorem sum_rawSliceBandIntegral_eq_weightedWideDensity
    (S : X → Euclidean (n - 1) → ℝ) (A : X → Euclidean (n - 1) → E)
    (χ : X → ℝ) (ζ : Euclidean (n - 1)) (τ : ℝ)
    {d : Euclidean (n - 1) → ℂ} {M : ℝ} (hd : Measurable d)
    (hdb : ∀ η, ‖d η‖ ≤ M) (v : WideInput n J) (x : X)
    (hB : χ x ≠ 0 → ∀ j : Fin J, ContinuousOn
      (fun η ↦ Complex.exp (Complex.I * (rawPrimaryPhaseDifference S ζ τ x η : ℂ)) •
        A x (ζ + τ • η)) (wideBand n j.val)) :
    (∑ j : Fin J, rawSliceBandIntegral S A χ ζ τ
        (weightedRadialBand d j.val) j.val (v j) x) =
      (χ x : ℂ) • rawPrimaryDemodulatedIntegral S A ζ τ volume
        (weightedWideDensity d v) x := by
  by_cases hx : χ x = 0
  · simp [rawSliceBandIntegral, hx]
  simp only [rawSliceBandIntegral, ← Finset.smul_sum]
  congr 1
  symm
  unfold rawPrimaryDemodulatedIntegral
  simp_rw [smul_comm (Complex.exp _) (_ : ℂ)]
  exact integral_weightedWideDensity_smul_eq_sum hd hdb v _ (hB hx)

end JanetCartan.RawPrimary.SliceBounds
