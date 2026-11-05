module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Synthesis of bounded atoms with a complex density

The integration step in `app:ch_lag:prop:lag-envelopes`. All syntheses below are
Bochner integrals. The density is integrable and the atoms are strongly measurable
and bounded almost everywhere. The results work in any complex Banach space, so
they apply separately in each fixed Sobolev space once its atomic estimates are
available. No atomic response or phase derivative estimate is asserted here.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace JanetCartan
namespace MeasureEnvelopes

variable {α E F : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {μ : Measure α} {ρ : α → ℂ} {a : α → E} {C : ℝ}

/-- `app:ch_lag:prop:lag-envelopes`: mass controlling integration against a complex density. -/
def densityMass (μ : Measure α) (ρ : α → ℂ) : ℝ := ∫ t, ‖ρ t‖ ∂μ

/-- `app:ch_lag:prop:lag-envelopes`: the complete field synthesized from its atoms. -/
def synthesis (μ : Measure α) (ρ : α → ℂ) (a : α → E) : E :=
  ∫ t, ρ t • a t ∂μ

/-- `app:ch_lag:prop:lag-envelopes`: the density mass is nonnegative. -/
theorem densityMass_nonneg (μ : Measure α) (ρ : α → ℂ) : 0 ≤ densityMass μ ρ :=
  integral_nonneg (fun _ ↦ norm_nonneg _)

/-- `app:ch_lag:prop:lag-envelopes`: bounded measurable atoms have an integrable weighted family. -/
theorem integrable_weightedAtoms (hρ : Integrable ρ μ)
    (ha : AEStronglyMeasurable a μ) (hb : ∀ᵐ t ∂μ, ‖a t‖ ≤ C) :
    Integrable (fun t ↦ ρ t • a t) μ := by
  apply (hρ.norm.mul_const C).mono' (hρ.aestronglyMeasurable.smul ha)
  filter_upwards [hb] with t ht
  change ‖ρ t • a t‖ ≤ ‖ρ t‖ * C
  simpa only [Pi.smul_apply, norm_smul] using mul_le_mul_of_nonneg_left ht (norm_nonneg (ρ t))

/-- `app:ch_lag:prop:lag-envelopes`: the atomic bound times the integral of the density norm. -/
theorem norm_synthesis_le (hρ : Integrable ρ μ) (hb : ∀ᵐ t ∂μ, ‖a t‖ ≤ C) :
    ‖synthesis μ ρ a‖ ≤ densityMass μ ρ * C := by
  calc
    _ ≤ ∫ t, ‖ρ t‖ * C ∂μ := by
      apply norm_integral_le_of_norm_le (hρ.norm.mul_const C)
      filter_upwards [hb] with t ht
      simpa only [Pi.smul_apply, norm_smul] using mul_le_mul_of_nonneg_left ht (norm_nonneg (ρ t))
    _ = _ := integral_mul_const C _

/-- `app:ch_lag:prop:lag-envelopes`: a bounded density over a finite measure gives finite mass. -/
theorem densityMass_le_measure_mul [IsFiniteMeasure μ] {R : ℝ}
    (hρ : ∀ᵐ t ∂μ, ‖ρ t‖ ≤ R) : densityMass μ ρ ≤ μ.real Set.univ * R := by
  exact (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
    (integrable_const R) hρ).trans_eq (by simp)

/-- `app:ch_lag:prop:lag-envelopes`: bounded measurable densities on finite measures are admissible. -/
theorem integrable_density_of_bound [IsFiniteMeasure μ] {R : ℝ}
    (hρ : AEStronglyMeasurable ρ μ) (hb : ∀ᵐ t ∂μ, ‖ρ t‖ ≤ R) : Integrable ρ μ :=
  (integrable_const R).mono' hρ hb

/-- `app:ch_lag:prop:lag-envelopes`: synthesis of a bounded measurable family against
a bounded complex density on a finite measure, with integrability and a mass bound. -/
theorem finiteMeasure_synthesis_bound [IsFiniteMeasure μ] {R : ℝ}
    (hρ : AEStronglyMeasurable ρ μ) (hR : ∀ᵐ t ∂μ, ‖ρ t‖ ≤ R)
    (ha : AEStronglyMeasurable a μ) (hC : 0 ≤ C) (hb : ∀ᵐ t ∂μ, ‖a t‖ ≤ C) :
    Integrable (fun t ↦ ρ t • a t) μ ∧
      ‖synthesis μ ρ a‖ ≤ (μ.real Set.univ * R) * C := by
  have hi := integrable_density_of_bound hρ hR
  exact ⟨integrable_weightedAtoms hi ha hb, (norm_synthesis_le hi hb).trans
    (mul_le_mul_of_nonneg_right (densityMass_le_measure_mul hR) hC)⟩

/-- `app:ch_lag:prop:lag-envelopes`: a fixed continuous complex-linear response commutes
with synthesis, including the entire source family. -/
theorem map_synthesis [CompleteSpace E] [CompleteSpace F] (L : E →L[ℂ] F) (hρ : Integrable ρ μ)
    (ha : AEStronglyMeasurable a μ) (hb : ∀ᵐ t ∂μ, ‖a t‖ ≤ C) :
    L (synthesis μ ρ a) = synthesis μ ρ (fun t ↦ L (a t)) := by
  rw [synthesis, ← L.integral_comp_comm (integrable_weightedAtoms hρ ha hb)]
  simp only [synthesis, map_smul]

/-- `app:ch_lag:eq:lag-recurrence`: the complete correction `W - Y` is synthesized
from the complete atomic corrections when `Y` is a fixed continuous linear response. -/
theorem sub_response_synthesis [CompleteSpace E] (L : E →L[ℂ] E)
    (hρ : Integrable ρ μ) (ha : AEStronglyMeasurable a μ) (hb : ∀ᵐ t ∂μ, ‖a t‖ ≤ C) :
    synthesis μ ρ a - L (synthesis μ ρ a) = synthesis μ ρ (fun t ↦ a t - L (a t)) := by
  simpa only [sub_apply, ContinuousLinearMap.id_apply] using
    map_synthesis (ContinuousLinearMap.id ℂ E - L) hρ ha hb

/-- `app:ch_lag:prop:lag-envelopes`: synthesis is additive in the complete density. -/
theorem synthesis_add_density {σ : α → ℂ} (hρ : Integrable ρ μ) (hσ : Integrable σ μ)
    (ha : AEStronglyMeasurable a μ) (hb : ∀ᵐ t ∂μ, ‖a t‖ ≤ C) :
    synthesis μ (ρ + σ) a = synthesis μ ρ a + synthesis μ σ a := by
  simp only [synthesis, Pi.add_apply, add_smul]
  exact integral_add (integrable_weightedAtoms hρ ha hb) (integrable_weightedAtoms hσ ha hb)

/-- `app:ch_lag:prop:lag-envelopes`: synthesis is complex homogeneous in the complete density. -/
theorem synthesis_smul_density (z : ℂ) :
    synthesis μ (z • ρ) a = z • synthesis μ ρ a := by
  simp only [synthesis, Pi.smul_apply, smul_eq_mul, mul_smul, integral_smul]

/-- `app:ch_lag:eq:lag-exact-phase`: a common scalar demodulation stays outside the integral. -/
theorem synthesis_smul_atoms (z : ℂ) :
    synthesis μ ρ (fun t ↦ z • a t) = z • synthesis μ ρ a := by
  simp only [synthesis, smul_comm (ρ _) z, integral_smul]

/-- `app:ch_lag:eq:lag-exact-phase`: the oscillatory factor at a real phase. -/
def phaseFactor (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

/-- `app:ch_lag:eq:lag-exact-phase`: real phase modulation has unit norm. -/
@[simp] theorem norm_phaseFactor (θ : ℝ) : ‖phaseFactor θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

/-- `app:ch_lag:eq:lag-exact-phase`: subtracting the single central phase leaves the phase
difference for every atom, rather than choosing a new central phase for each atom. -/
theorem demodulate_phaseFactor (θ θ₀ : ℝ) :
    phaseFactor (-θ₀) * phaseFactor θ = phaseFactor (θ - θ₀) := by
  simp only [phaseFactor, ← Complex.exp_add, Complex.ofReal_neg, Complex.ofReal_sub]
  congr 1
  ring

/-- `app:ch_lag:eq:lag-exact-phase`: exact common-phase demodulation of the complete field. -/
theorem demodulate_synthesis (θ : α → ℝ) (θ₀ : ℝ) :
    phaseFactor (-θ₀) • synthesis μ ρ (fun t ↦ phaseFactor (θ t) • a t) =
      synthesis μ ρ (fun t ↦ phaseFactor (θ t - θ₀) • a t) := by
  rw [← synthesis_smul_atoms]
  congr 1
  funext t
  rw [smul_smul, demodulate_phaseFactor]

/-- `app:ch_lag:prop:lag-envelopes`: a unit phase does not change the zeroth-order atomic bound.
Higher derivative bounds must be applied to the phase-modulated atoms themselves. -/
theorem norm_demodulate_synthesis_le (θ : α → ℝ) (θ₀ : ℝ)
    (hρ : Integrable ρ μ) (hb : ∀ᵐ t ∂μ, ‖a t‖ ≤ C) :
    ‖phaseFactor (-θ₀) • synthesis μ ρ (fun t ↦ phaseFactor (θ t) • a t)‖ ≤
      densityMass μ ρ * C := by
  rw [demodulate_synthesis]
  apply norm_synthesis_le hρ
  simpa only [norm_smul, norm_phaseFactor, one_mul] using hb

section Derivatives

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {A : X → α → E} {A' : X → α → X →L[ℝ] E} {x₀ : X} {s : Set X}
  {bound : α → ℝ}

/-- `app:ch_lag:prop:lag-envelopes`: derivative interchange under explicit domination of
the atomic derivatives on a common neighborhood. In particular this applies to all
finite-dimensional coordinate spaces. The dominating function includes the density norm. -/
theorem hasFDerivAt_synthesis (hs : s ∈ 𝓝 x₀) (hρ : Integrable ρ μ)
    (hA : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (A x) μ)
    (hA₀ : AEStronglyMeasurable (A x₀) μ) (hC : ∀ᵐ t ∂μ, ‖A x₀ t‖ ≤ C)
    (hA' : AEStronglyMeasurable (A' x₀) μ)
    (hb : ∀ᵐ t ∂μ, ∀ x ∈ s, ‖A' x t‖ ≤ bound t)
    (hi : Integrable (fun t ↦ ‖ρ t‖ * bound t) μ)
    (hd : ∀ᵐ t ∂μ, ∀ x ∈ s, HasFDerivAt (fun y ↦ A y t) (A' x t) x) :
    HasFDerivAt (fun x ↦ synthesis μ ρ (A x)) (synthesis μ ρ (A' x₀)) x₀ := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le hs
  · exact hA.mono fun _ hx ↦ hρ.aestronglyMeasurable.smul hx
  · exact integrable_weightedAtoms hρ hA₀ hC
  · exact hρ.aestronglyMeasurable.smul hA'
  · filter_upwards [hb] with t ht x hx
    simpa only [Pi.smul_apply, norm_smul] using mul_le_mul_of_nonneg_left (ht x hx) (norm_nonneg (ρ t))
  · exact hi
  · filter_upwards [hd] with t ht x hx
    exact (ht x hx).const_smul (ρ t)

end Derivatives

end MeasureEnvelopes
end JanetCartan
