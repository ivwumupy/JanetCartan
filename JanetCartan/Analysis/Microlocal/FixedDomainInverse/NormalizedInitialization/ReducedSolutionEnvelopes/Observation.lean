module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.Demodulation
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Restriction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.FiberMaps

/-!
# The literal demodulated solver observation on a restriction Sobolev source

The normalized inverse supplies the all-source Fourier bound for its actual
paired solver. The fixed interior bump permits zero extension of the source;
the compact primary phase supplies the demodulation cost. This gives the
observation bound used to estimate the SAME finite Neumann remainder in
`app:ch_response:eq:response-graded-reduced`.

The only solver estimate below is exactly the integer Fourier estimate already
returned by `exists_normalized_complete_smooth_fixed_inverse_of_selected_collar_on_enlarged_bands`
in `NormalizedBandInverse/Smooth` at solver order zero. Its one-high
coefficient term is kept visible. No finite-chain envelope or solution-envelope
estimate is an input to this deduction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff ENNReal NNReal

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential ResponseTransfer ResponseTransfer.Complement
open ArbitraryAccuracy.ResidualLocalization SmallSupport RegularSector.Realization

variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "RF" => EuclideanSpace ℝ (Fin r)
local notation "H" => Lp F 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Apply fixed-bump zero extension, the normalized solver's actual Fourier
estimate, and primary demodulation in that order. The resulting constant is
chosen before the domain, phase, frequency, solver, and source. In the inverse
application `χ` is its original `χ₃`, which fixes every corrected source and
every supported finite residual word. The one-high coefficient `high` is
unchanged (`app:ch_regular:eq:inverse-remainder`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_demodulated_bumped_solver_fourier_cost
    {x : E} (χ : ContDiffBump x) (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (s : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (U : Set E) (hU : MeasurableSet U),
      tsupport (χ : E → ℝ) ⊆ U →
      ∀ (ρ : ℝ), 1 ≤ ρ →
      ∀ (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ), HasCompactSupport φ →
        (∀ j, 1 ≤ j → j ≤ s → ∀ y,
          ‖iteratedFDeriv ℝ j φ y‖ ≤ P j * ρ ^ j) →
      ∀ (T : H →L[ℂ] H) (C high : ℝ), 0 ≤ C → 0 ≤ high →
        (∀ z : H, MemVectorFourierSobolev (s : ℝ) z →
          MemVectorFourierSobolev (s : ℝ) (T z) ∧
            vectorFourierSobolevNorm (s : ℝ) (T z) ≤
              C * (vectorFourierSobolevNorm (s : ℝ) z + high * ‖z‖)) →
      ∀ u : LocalL2 U F, MemRestrictionSobolev U s u →
        let z := zeroExtend hU (bumpL2 (p := 2) le_rfl χ u)
        let v := carrierMultiplication (-ρ) φ hφ.continuous (T z)
        MemVectorFourierSobolev (s : ℝ) v ∧
          vectorFourierSobolevNorm (s : ℝ) v ≤
            (D * C * (1 + high)) * ρ ^ (2 * s) * restrictionSobolevNorm U s u := by
  obtain ⟨D₀, hD₀, hdemod⟩ := exists_compactPhase_demodulation_fourier_cost (r := r) P hP s
  obtain ⟨D₁, hD₁, hbump⟩ := exists_bump_zeroExtension_fourier_constant (r := r) χ s
  refine ⟨D₀ * D₁, mul_nonneg hD₀ hD₁.le, ?_⟩
  intro U hU hχ ρ hρ φ hφ hcφ hphase T C high hC hhigh hT u hu z v
  obtain ⟨hzmem, hzbound⟩ := hbump U hU hχ u hu
  have hzL2 : ‖z‖ ≤ vectorFourierSobolevNorm (s : ℝ) z := by
    simpa only [vectorFourierSobolevNorm_zero] using
      (vectorFourierSobolevNorm_mono hzmem (show (0 : ℝ) ≤ s by positivity))
  obtain ⟨hTmem, hTbound⟩ := hT z hzmem
  obtain ⟨hvmem, hvbound⟩ := hdemod ρ hρ φ hφ hcφ hphase (T z) hTmem
  refine ⟨hvmem, hvbound.trans ?_⟩
  have hTbound' : vectorFourierSobolevNorm (s : ℝ) (T z) ≤
      C * (1 + high) * D₁ * restrictionSobolevNorm U s u := by
    apply hTbound.trans
    calc
      _ ≤ C * (D₁ * restrictionSobolevNorm U s u +
          high * (D₁ * restrictionSobolevNorm U s u)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hzbound (mul_le_mul_of_nonneg_left (hzL2.trans hzbound) hhigh)) hC
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hTbound'
    (mul_nonneg hD₀ (pow_nonneg (zero_le_one.trans hρ) _))).trans_eq (by ring)

/-- The same observation applies to the original real quadratures. Complex
inclusion is applied on their actual restriction measure, and its fixed norm
cost is derived from weak jets. The two resulting observations must be
combined as real plus `I` times imaginary before asserting a primary envelope;
this theorem supplies only their common polynomial cost
(`app:ch_response:eq:response-two-envelopes`). -/
theorem exists_real_demodulated_bumped_solver_fourier_cost
    {x : E} (χ : ContDiffBump x) (P : ℕ → ℝ) (hP : ∀ j, 0 ≤ P j) (s : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (U : Set E) (hU : MeasurableSet U),
      tsupport (χ : E → ℝ) ⊆ U →
      ∀ (ρ : ℝ), 1 ≤ ρ →
      ∀ (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ), HasCompactSupport φ →
        (∀ j, 1 ≤ j → j ≤ s → ∀ y,
          ‖iteratedFDeriv ℝ j φ y‖ ≤ P j * ρ ^ j) →
      ∀ (T : H →L[ℂ] H) (C high : ℝ), 0 ≤ C → 0 ≤ high →
        (∀ z : H, MemVectorFourierSobolev (s : ℝ) z →
          MemVectorFourierSobolev (s : ℝ) (T z) ∧
            vectorFourierSobolevNorm (s : ℝ) (T z) ≤
              C * (vectorFourierSobolevNorm (s : ℝ) z + high * ‖z‖)) →
      ∀ u : LocalL2 U RF, MemRestrictionSobolev U s u →
        let z := zeroExtend hU (bumpL2 (p := 2) le_rfl χ
          (l2ComplexInclusion (volume.restrict U) u))
        let v := carrierMultiplication (-ρ) φ hφ.continuous (T z)
        MemVectorFourierSobolev (s : ℝ) v ∧
          vectorFourierSobolevNorm (s : ℝ) v ≤
            (D * C * (1 + high)) * ρ ^ (2 * s) * restrictionSobolevNorm U s u := by
  obtain ⟨D, hD, hcomplex⟩ := exists_demodulated_bumped_solver_fourier_cost (r := r) χ P hP s
  let inc := euclideanComplexInclusion (ι := Fin r)
  refine ⟨D * (‖inc‖ + 1), mul_nonneg hD (by positivity), ?_⟩
  intro U hU hχ ρ hρ φ hφ hcφ hphase T C high hC hhigh hT u hu z v
  obtain ⟨hm, hb⟩ := compLp_restrictionSobolev_bound inc hu
  obtain ⟨hvmem, hvbound⟩ := hcomplex U hU hχ ρ hρ φ hφ hcφ hphase T C high hC hhigh hT
    (l2ComplexInclusion (volume.restrict U) u) hm
  refine ⟨hvmem, hvbound.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hb (by positivity :
    0 ≤ D * C * (1 + high) * ρ ^ (2 * s))).trans_eq (by ring)

end JanetCartan.FixedDomainInverse
