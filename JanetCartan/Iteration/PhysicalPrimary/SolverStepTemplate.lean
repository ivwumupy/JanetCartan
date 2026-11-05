module

public import JanetCartan.Iteration.PhysicalEllipticWords.PairedTransfer

/-!
# The original physical source mask in the solver step

These are exact deduction helpers for the SAME physical operator and source.
They retain the original input mask in the conclusion, using its proved plateau
on the source support, and apply the existing Sobolev multiplier estimate for
the original output mask. They do not construct an analytic solver estimate.
Consumers: the physical elliptic residual letter and the final SAME solver in
`actual_finite_residual_word_reserved_bounds_of_one_step`
(`app:ch_response:eq:response-graded-reduced`, `energy-complete-residual`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

open Set MeasureTheory
open scoped ContDiff
namespace JanetCartan.PhysicalPrimary
open PhysicalEllipticWords Pseudodifferential FourierIntegral FourierIntegral.LowBounds
open ResponseTransfer ResponseTransfer.Complement
open ResponseTransfer.DirectEvolution.AnnularSobolev
open FixedDomainInverse.FiniteResidualEnvelopes RegularSector.FiniteAssembly

variable {d : ℕ} {I : Type}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "Fibre" => EuclideanSpace ℂ (Fin (d+1))
local notation "H" => Lp Fibre 2 (volume : Measure E)

private theorem solver_sourceCut_carrier_commute
    (μ : E → ℝ) (hμ : Continuous μ) (hμb : ∀ y, ‖μ y‖ ≤ 1)
    (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ) (u : H) :
    sourceCutMultiplier μ hμ hμb (carrierMultiplication lam φ hφ u) =
      carrierMultiplication lam φ hφ (sourceCutMultiplier μ hμ hμb u) := by
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn μ hμ hμb (carrierMultiplication lam φ hφ u),
    carrierMultiplication_ae lam φ hφ u,
    carrierMultiplication_ae lam φ hφ (sourceCutMultiplier μ hμ hμb u),
    sourceCutMultiplier_coeFn μ hμ hμb u] with y h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  exact smul_comm _ _ _

private theorem solver_input_plateau (ν : E → ℝ) (hν : Continuous ν)
    (hνb : ∀ y, ‖ν y‖ ≤ 1) (S : Set E) (hS : IsCompact S)
    (hin : ∀ y ∈ S, ν y = 1) (a : E × Par → Fibre) (ha : ContDiff ℝ ∞ a)
    (has : ∀ q, q.1 ∉ S → a q = 0) (c : Par) (lam : ℝ)
    (φ : E → ℝ) (hφ : Continuous φ) :
    sourceCutMultiplier ν hν hνb
      (carrierMultiplication lam φ hφ (graphTestToLp (vectorOriginalDatumTest a ha hS has [] c))) =
      carrierMultiplication lam φ hφ (graphTestToLp (vectorOriginalDatumTest a ha hS has [] c)) := by
  let u := graphTestToLp (vectorOriginalDatumTest a ha hS has [] c)
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn ν hν hνb (carrierMultiplication lam φ hφ u),
    carrierMultiplication_ae lam φ hφ u, vectorOriginalDatumTest_toLp_ae a ha hS has [] c]
    with y h₁ h₂ h₃
  rw [h₁, h₂]
  by_cases hy : y ∈ S
  · rw [hin y hy, Complex.ofReal_one, one_smul]
  · rw [show u y = a (y,c) from h₃, has (y,c) hy, smul_zero, smul_zero]

/-- Retain the ORIGINAL source cut as the right input factor of the same
physical solver without changing its source datum or any natural reserve. No compactness of an
artificial constant output mask is needed (`app:ch_regular:lem:finite-chain`). -/
theorem reserved_bounds_input_plateau
    {V : Set Par} (T : I → H →L[ℂ] H) (lam A K : I → ℝ) (reserve : ℕ)
    (φ : I → E → Par → ℝ) (hφ : ∀ i c, Continuous (fun y ↦ φ i y c))
    (S : Set E) (hS : IsCompact S) (a : I → E × Par → Fibre)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (has : ∀ i q, q.1 ∉ S → a i q = 0)
    (ν : E → ℝ) (hν : Continuous ν) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (hin : ∀ y ∈ S, ν y = 1)
    (hA : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c) (T i)
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) A K reserve) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
        ((T i).comp (sourceCutMultiplier ν hν hνb))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) A K reserve := by
  have he : (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
      ((T i).comp (sourceCutMultiplier ν hν hνb))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) =
    (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c) (T i)
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) := by
    funext i c
    simp only [demodulatedL2Operator, ContinuousLinearMap.comp_apply]
    rw [solver_input_plateau ν hν hνb S hS hin (a i) (ha i) (has i) c
      (lam i) (fun y ↦ φ i y c) (hφ i c)]
  rw [he]
  exact hA

/-- Measure an already physical response with the ORIGINAL real output and
input masks. The only response premise is supplied by the actual elliptic,
algebraic or retarded producer; no estimate for the recut response is assumed
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem reserved_bounds_measured_of_input_plateau
    {V : Set Par} (hV : IsOpen V) (T : I → H →L[ℂ] H)
    (lam A K : I → ℝ) (reserve : ℕ)
    (φ : I → E → Par → ℝ) (hφ : ∀ i c, Continuous (fun y ↦ φ i y c))
    (S : Set E) (hS : IsCompact S) (a : I → E × Par → Fibre)
    (ha : ∀ i, ContDiff ℝ ∞ (a i)) (has : ∀ i q, q.1 ∉ S → a i q = 0)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hμc : HasCompactSupport μ)
    (hν : Continuous ν) (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    (hin : ∀ y ∈ S, ν y = 1)
    (hA : ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c) (T i)
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) A K reserve) :
    ReservedLetterBounds V
      (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
        (measuredOperator μ ν hμ.continuous hν hμb hνb (T i))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) A K reserve := by
  have hi := reserved_bounds_input_plateau T lam A K reserve φ hφ S hS a ha has ν hν hνb hin hA
  have hc := hi.cut hV μ hμ hμc hμb
  have he : (fun i c ↦ demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
      (measuredOperator μ ν hμ.continuous hν hμb hνb (T i))
      (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c))) =
    (fun i c ↦ sourceCutMultiplier μ hμ.continuous hμb
      (demodulatedL2Operator (lam i) (fun y ↦ φ i y c) (hφ i c)
        ((T i).comp (sourceCutMultiplier ν hν hνb))
        (graphTestToLp (vectorOriginalDatumTest (a i) (ha i) hS (has i) [] c)))) := by
    funext i c
    simp only [demodulatedL2Operator, measuredOperator, ContinuousLinearMap.comp_apply]
    exact (solver_sourceCut_carrier_commute μ hμ.continuous hμb (-(lam i))
      (fun y ↦ φ i y c) (hφ i c) _).symm
  rw [he]
  exact hc

end JanetCartan.PhysicalPrimary
