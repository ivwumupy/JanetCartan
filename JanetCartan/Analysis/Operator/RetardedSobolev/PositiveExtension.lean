module

public import JanetCartan.Analysis.Operator.RetardedSobolev.WeightedMixedEnergy
public import JanetCartan.Analysis.Operator.RetardedSobolev.ClassicalOperator
public import JanetCartan.Analysis.Operator.RetardedSobolev.Spaces

/-!
# Nonnegative Sobolev extensions of the concrete retarded operators

The estimates of `app:ch_osc:prop:osc-retarded-tube` on the completion of actual
Cartesian L² jets. Support of the exterior cutoffs in the time strip turns the
classical strip estimates into ambient estimates. No classical bound is assumed.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.RetardedSobolev

open Spaces

variable {d : ℕ}

/-- Smooth compactly supported tests have all the mixed jets used in the
retarded estimates (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem mixedJetsMemLp_test (a b : ℝ) (m : ℕ) (f : Test d) :
    MixedJetsMemLp (fun i : Fin d ↦ Pi.single i (1 : ℝ)) volume a b m f := by
  intro k hk word j hj
  exact jet_memLp (volume.prod (volume.restrict (Icc a b)))
    (⟨⟨k, by omega⟩, word, ⟨j, by dsimp; omega⟩⟩ : JetIndex d m) f

/-- Restricting the domain of integration can only decrease test derivative
energy (`app:ch_osc:prop:osc-retarded-tube`). -/
theorem mixedSobolevEnergy_test_le_ambient (a b : ℝ) (m : ℕ) (f : Test d) :
    mixedSobolevEnergy (fun i : Fin d ↦ Pi.single i (1 : ℝ)) volume a b m f ≤
      jetEnergy (d := d) m volume f := by
  rw [← jetEnergy_eq_mixedSobolevEnergy]
  apply Finset.sum_le_sum
  intro i _
  exact integral_mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    (Filter.Eventually.of_forall (fun _ ↦ sq_nonneg _))
    ((memLp_two_iff_integrable_sq_norm (jet_memLp volume i f).aestronglyMeasurable).mp
      (jet_memLp volume i f))

/-- Ambient derivative-energy bounds for the two actual integrals, with every
analytic premise discharged from the fixed cutoff assumptions
(`app:ch_osc:prop:osc-retarded-tube`). -/
theorem retardedTest_energy_bounds (a b : ℝ) (hab : a ≤ b) (m : ℕ)
    (χin χout : ℝ × (Fin d → ℝ) → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hsin : HasCompactSupport χin) (hsout : HasCompactSupport χout)
    (hsin_time : tsupport χin ⊆ Icc a b ×ˢ univ)
    (hsout_time : tsupport χout ⊆ Icc a b ×ˢ univ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Test d,
      jetEnergy (d := d) m volume (lowerTest a χin χout hin hout hsout f) ≤ C * jetEnergy (d := d) m volume f ∧
      jetEnergy (d := d) m volume (upperTest b χin χout hin hout hsin f) ≤ C * jetEnergy (d := d) m volume f := by
  obtain ⟨C, hC, hb⟩ := mixedSobolev_bounds_of_contDiff_hasCompactSupport
    (fun i : Fin d ↦ Pi.single i (1 : ℝ)) volume a b hab m χin χout hin hout hsin hsout
  refine ⟨C, hC, fun f ↦ ?_⟩
  have h := hb f f.property.1 (mixedJetsMemLp_test a b m f)
  have hl := jetEnergy_prod_eq_mixedSobolevEnergy_of_support m volume a b
    (contDiff_lower a hin hout f.property.1)
    ((tsupport_lower_subset a χin χout f).trans hsout_time)
  have hu := jetEnergy_prod_eq_mixedSobolevEnergy_of_support m volume a b
    (contDiff_upper b hin hout f.property.1)
    ((tsupport_upper_subset b χin χout f).trans hsin_time)
  change jetEnergy (d := d) m (volume.prod volume) (Retarded.lower a χin χout f) ≤ _ ∧
    jetEnergy (d := d) m (volume.prod volume) (Retarded.upper b χin χout f) ≤ _
  rw [hl, hu]
  exact ⟨h.2.2.1.trans (mul_le_mul_of_nonneg_left (mixedSobolevEnergy_test_le_ambient a b m f) hC),
    h.2.2.2.trans (mul_le_mul_of_nonneg_left (mixedSobolevEnergy_test_le_ambient a b m f) hC)⟩

/-- Both literal retarded operators extend uniquely to bounded maps at every
nonnegative integer Sobolev order (`app:ch_osc:prop:osc-retarded-tube`).
The space is the completion of the actual Cartesian L² jets; the common norm
bound is chosen before the input. -/
theorem exists_retarded_sobolev_extensions (a b : ℝ) (hab : a ≤ b) (m : ℕ)
    (χin χout : ℝ × (Fin d → ℝ) → ℝ)
    (hin : ContDiff ℝ ∞ χin) (hout : ContDiff ℝ ∞ χout)
    (hsin : HasCompactSupport χin) (hsout : HasCompactSupport χout)
    (hsin_time : tsupport χin ⊆ Icc a b ×ˢ univ)
    (hsout_time : tsupport χout ⊆ Icc a b ×ˢ univ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ L U : Ambient d m →L[ℂ] Ambient d m,
      ‖L‖ ≤ C ∧ ‖U‖ ≤ C ∧
      (∀ f, L (ofTest m volume f) = ofTest m volume (lowerTest a χin χout hin hout hsout f)) ∧
      (∀ f, U (ofTest m volume f) = ofTest m volume (upperTest b χin χout hin hout hsin f)) ∧
      (∀ L' : Ambient d m →L[ℂ] Ambient d m,
        (∀ f, L' (ofTest m volume f) = ofTest m volume (lowerTest a χin χout hin hout hsout f)) →
        L' = L) ∧
      (∀ U' : Ambient d m →L[ℂ] Ambient d m,
        (∀ f, U' (ofTest m volume f) = ofTest m volume (upperTest b χin χout hin hout hsin f)) →
        U' = U) := by
  obtain ⟨C, hC, hb⟩ := retardedTest_energy_bounds a b hab m χin χout hin hout hsin hsout
    hsin_time hsout_time
  obtain ⟨L, hL, heL, huL⟩ := exists_unique_extension_of_energy_bound volume volume
    (lowerTest a χin χout hin hout hsout) hC (fun f ↦ (hb f).1)
  obtain ⟨U, hU, heU, huU⟩ := exists_unique_extension_of_energy_bound volume volume
    (upperTest b χin χout hin hout hsin) hC (fun f ↦ (hb f).2)
  exact ⟨_, Real.sqrt_nonneg _, L, U, hL, hU, heL, heU, huL, huU⟩

end JanetCartan.RetardedSobolev
