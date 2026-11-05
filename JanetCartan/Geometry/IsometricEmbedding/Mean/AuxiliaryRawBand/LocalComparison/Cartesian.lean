module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.LocalComparison.Measure
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRawBand.LocalComparison.Derivatives

/-!
# Physical Cartesian Sobolev comparison

For `app:ch_background:prop:bg-mixed-physical` this uses the existing
`LocalSobolev.cartesianJetNorm` of the actual Euclidean derivatives. It counts
each multiindex once, uses Lebesgue measure, and applies to both Euclidean
vectors and Frobenius tensors. It is not the infimum-over-extensions norm
`restrictionSobolevNorm`; that norm requires a separate extension construction.
All statements include dimension zero without a positivity hypothesis.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.AuxiliaryRawBand

open LocalSobolev PeriodicLocalL2

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every physical Cartesian derivative has a genuine local L² class
(`app:ch_background:prop:bg-mixed-physical`). Smoothness is needed only for
the periodic representative; open-chart agreement supplies the local derivatives. -/
theorem memLp_cartesianDerivative_of_eqOn_periodicLift
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    (hcell : W ⊆ halfOpenCell n)
    {g : EuclideanSpace ℝ (Fin n) → F} {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (heq : EqOn g (periodicLift f) W) (α : Fin n → ℕ) :
    MemLp (cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j g) α) 2
      (volume.restrict W) := by
  apply (memLp_periodicLift_on_subset_cell (hf.multiindexDeriv α).1 hcell).ae_eq
  exact (ae_restrict_mem hW.measurableSet).mono fun x hx ↦
    (cartesianJetDerivative_eqOn_of_eqOn_periodicLift hW hf heq α hx).symm

/-- Squared Cartesian derivative integrals transfer exactly to the quotient
chart, retaining physical Lebesgue measure (`app:not:fourier`). -/
theorem integral_cartesianDerivative_sq_eq_chart
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    (hcell : W ⊆ halfOpenCell n)
    {g : EuclideanSpace ℝ (Fin n) → F} {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (heq : EqOn g (periodicLift f) W) (α : Fin n → ℕ) :
    (∫ x in W, ‖cartesianJetDerivative (fun j ↦ iteratedFDeriv ℝ j g) α x‖ ^ 2) =
      ∫ z in torusChart W, ‖periodicMultiindexDeriv α f z‖ ^ 2 := by
  rw [← integral_norm_sq_periodicLift_chart hW.measurableSet hcell]
  exact setIntegral_congr_fun hW.measurableSet fun x hx ↦ congrArg (fun v ↦ ‖v‖ ^ 2)
    (cartesianJetDerivative_eqOn_of_eqOn_periodicLift hW hf heq α hx)

/-- Restricting a periodic output to an open physical chart decreases the
Cartesian derivative norm with constant one (`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem cartesianJetNorm_le_periodicDerivativeL2Norm_of_eqOn
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    (hcell : W ⊆ halfOpenCell n)
    {g : EuclideanSpace ℝ (Fin n) → F} {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (heq : EqOn g (periodicLift f) W) (s : ℕ) :
    cartesianJetNorm W s (fun j ↦ iteratedFDeriv ℝ j g) ≤ periodicDerivativeL2Norm s f := by
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro α _
  have h := integral_norm_sq_periodicLift_le (hf.multiindexDeriv (fun i ↦ α (some i))).1 hcell
  convert h using 1
  exact setIntegral_congr_fun hW.measurableSet fun x hx ↦ congrArg (fun v ↦ ‖v‖ ^ 2)
    (cartesianJetDerivative_eqOn_of_eqOn_periodicLift hW hf heq _ hx)

end JanetCartan.AuxiliaryRawBand

namespace JanetCartan.AuxiliaryRawBand

open LocalSobolev PeriodicLocalL2

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The physical field and full strain inherit the parent's Fourier Sobolev
bound with constant one, at every order and in every dimension
(`app:ch_background:eq:bg-Vaux-raw-band`). This is the actual Euclidean
Cartesian derivative norm, not an auxiliary torus norm assigned to physical data. -/
theorem cartesianJetNorm_le_periodicSobolevNorm_of_eqOn
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    (hcell : W ⊆ halfOpenCell n)
    {g : EuclideanSpace ℝ (Fin n) → F} {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (heq : EqOn g (periodicLift f) W) (s : ℕ) :
    cartesianJetNorm W s (fun j ↦ iteratedFDeriv ℝ j g) ≤ periodicSobolevNorm s f :=
  (cartesianJetNorm_le_periodicDerivativeL2Norm_of_eqOn hW hcell hf heq s).trans
    (periodicSobolevNorm_equiv_derivativeL2Norm hf s).1

/-- The within-jet version is the same local bound, for consumers using
intrinsic derivatives on the open immersion chart (`app:not:fourier`). -/
theorem cartesianJetNorm_within_le_periodicSobolevNorm_of_eqOn
    {W : Set (EuclideanSpace ℝ (Fin n))} (hW : IsOpen W)
    (hcell : W ⊆ halfOpenCell n)
    {g : EuclideanSpace ℝ (Fin n) → F} {f : Torus n → F}
    (hf : IsSmoothPeriodic f) (heq : EqOn g (periodicLift f) W) (s : ℕ) :
    cartesianJetNorm W s (fun j ↦ iteratedFDerivWithin ℝ j g W) ≤ periodicSobolevNorm s f := by
  convert cartesianJetNorm_le_periodicSobolevNorm_of_eqOn hW hcell hf heq s using 1
  unfold cartesianJetNorm cartesianJetEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro α _
  apply setIntegral_congr_fun hW.measurableSet
  intro x hx
  unfold cartesianJetDerivative
  dsimp only
  rw [iteratedFDerivWithin_of_isOpen _ hW hx]

end JanetCartan.AuxiliaryRawBand
