module

public import JanetCartan.Iteration.PhysicalPrimary.Jets
public import JanetCartan.Analysis.PhysicalSobolev.Cartesian

/-!
# Physical Fourier norms after the original spatial cutoff

Paper-v2 §15: the actual compact real field has a physical radian Bessel
norm bounded by its original local jets at the SAME order. Both the cutoff
and norm-conversion constants precede the field, its buffered source domain,
and all frequencies. No profile of the output field is an assumption.
Consumers: the physical primary and mean source producers for
`RevisedStage.increment_estimates_of_physicalSobolev_profiles`.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory FourierTransform
open scoped ContDiff

namespace JanetCartan.PhysicalPrimary

open UniformStep Pseudodifferential

/-- Lossless-order physical Sobolev control of the original cutoff field
on any open buffered source domain (`main:eq:primary-fixed-scales`,
`main:eq:mean-size`). The frequency is the physical covector `2π ξ`. -/
theorem exists_cutSchwartzOfSupport_physicalWeightedNorm_bound {n N : ℕ}
    (D : LocalDomain) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Euclidean n → Euclidean N)
      {U : Set (Euclidean n)} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
      (hsU : tsupport (physicalCutoff (n := n) D) ⊆ U),
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight (r : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify (cutSchwartzOfSupport D f hU hf hsU)) ξ) 2 volume).toReal ≤
        C * cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut) r f := by
  obtain ⟨A, hA, hfourier⟩ := PhysicalSobolev.exists_physicalWeightedNorm_le_jetL2 n N r
  obtain ⟨B, hB, hcut⟩ := exists_cutSchwartzOfSupport_jetL2_bound (n := n) (N := N) D r
  refine ⟨A * B, mul_nonneg hA.le hB, ?_⟩
  intro f U hU hf hsU
  exact (hfourier _).trans ((mul_le_mul_of_nonneg_left (hcut f hU hf hsU) hA.le).trans_eq
    (mul_assoc _ _ _).symm)

/-- The chart-specialized actual compact primary uses the identical
physical norm and loses no derivative order. -/
theorem exists_cutSchwartz_physicalWeightedNorm_bound {n N : ℕ}
    (D : LocalDomain) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Euclidean n → Euclidean N)
      (hf : ContDiffOn ℝ ∞ f (D.chart n)),
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight (r : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify (cutSchwartz D f hf)) ξ) 2 volume).toReal ≤
        C * cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut) r f := by
  obtain ⟨C, hC, hcut⟩ := exists_cutSchwartzOfSupport_physicalWeightedNorm_bound (n := n) (N := N) D r
  refine ⟨C, hC, fun f hf ↦ ?_⟩
  exact hcut f isOpen_ball hf (physicalCutoff_properties (n := n) D).2.1

end JanetCartan.PhysicalPrimary
