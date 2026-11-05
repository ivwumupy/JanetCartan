module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.DensityMultiplier.InputComparison.CoordinateTests
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierSobolev.TransverseWeight

/-!
# Finite-dimensional and transverse steps of the reverse mixed-jet estimate

For `app:ch_background:prop:bg-adjoint` and
`app:ch_background:eq:bg-density-adjoint`, coordinate expansion followed by
transverse Plancherel bounds mixed jets by a finite sum of raw Sobolev norms
of actual compact coordinate derivatives. The parent input comparison must
still discharge the parameter derivative estimate for those concrete tests.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.ContinuumAdjoint.DensityMultiplier
open ContinuumRow CarrierSobolev
variable {n : ℕ}

/-- Each weighted coordinate derivative of a compact test has finite scalar
L² energy on the literal carrier product measure. This justifies the finite
sum of L² norms in the reverse estimate of
`app:ch_background:eq:bg-density-adjoint`. -/
theorem memLp_weighted_inputCoordinateTest (k t : ℕ) (f : carrierInitialTestSpace n)
    (a : Fin k → (Unit ⊕ Fin 2)) :
    MemLp (fun x => etaBesselWeight t x • (inputCoordinateTest k f a).val x)
      2 (carrierMeasure n) := by
  exact ((continuous_etaBesselWeight t).smul
    (inputCoordinateTest k f a).property.1.continuous).memLp_of_hasCompactSupport
      ((inputCoordinateTest k f a).property.2.smul_left)

/-- The L² operator norm of a mixed carrier jet is controlled by the finite
sum of weighted coordinate-derivative norms. The bound uses all three carrier
directions and holds at order zero. Its consumer is
`lpNorm_weightedCarrierJet_le_sum_rawInputCoordinateTest` for
`app:ch_background:prop:bg-adjoint`. -/
theorem lpNorm_weightedCarrierJet_le_sum_inputCoordinateTest (k t : ℕ)
    (f : carrierInitialTestSpace n) :
    lpNorm (weightedCarrierJet k t f.val) 2 (carrierMeasure n) ≤
      ∑ a : Fin k → (Unit ⊕ Fin 2),
        lpNorm (fun x => etaBesselWeight t x • (inputCoordinateTest k f a).val x)
          2 (carrierMeasure n) := by
  classical
  let g (a : Fin k → (Unit ⊕ Fin 2)) (x : CarrierVariable n) : ℝ :=
    ‖etaBesselWeight t x • (inputCoordinateTest k f a).val x‖
  have hg a : MemLp (g a) 2 (carrierMeasure n) :=
    (memLp_weighted_inputCoordinateTest k t f a).norm
  have hpt (x : CarrierVariable n) : ‖weightedCarrierJet k t f.val x‖ ≤ ∑ a, g a x := by
    simpa only [weightedCarrierJet_apply_inputCarrierBasis, g] using
      norm_le_sum_inputCarrierBasis (weightedCarrierJet k t f.val x)
  calc
    _ ≤ lpNorm (fun x => ∑ a, g a x) 2 (carrierMeasure n) :=
      lpNorm_mono_real (memLp_finsetSum Finset.univ (fun a _ => hg a)) hpt
    _ = lpNorm (∑ a, g a) 2 (carrierMeasure n) := by
      congr 1
      ext x
      simp
    _ ≤ ∑ a, lpNorm (g a) 2 (carrierMeasure n) :=
      lpNorm_sum_le (fun a _ => hg a) (by norm_num)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      exact lpNorm_norm (memLp_weighted_inputCoordinateTest k t f a).aestronglyMeasurable 2

/-- The actual raw Sobolev norm controls the transverse Bessel weight of a
compact test with constant one. This applies the proved transverse Plancherel
estimate, retaining the literal measure and exact radian rescaling, for
`app:ch_background:eq:bg-density-adjoint`. It holds also when `n - 1 = 0`. -/
theorem lpNorm_etaBesselWeight_test_le_rawTestSobolev (s : ℕ)
    (f : carrierInitialTestSpace n) :
    lpNorm (fun x => etaBesselWeight s x • f.val x) 2 (carrierMeasure n) ≤
      ‖rawTestSobolev s f‖ := by
  rw [norm_rawTestSobolev]
  have he : (fun x => etaBesselWeight s x • f.val x) =ᵐ[carrierMeasure n]
      fun x => transverseBesselWeight s x • carrierInitialTestToLp f x := by
    filter_upwards [(carrierInitialTest_memLp f).coeFn_toLp] with x hx
    change carrierInitialTestToLp f x = f.val x at hx
    rw [hx]
    rfl
  apply ENNReal.toReal_mono (carrierInitialTest_memRawSobolev s f).eLpNorm_ne_top
  exact (eLpNorm_congr_ae he).le.trans
    (transverseBesselWeight_eLpNorm_le s (carrierInitialTestToLp f))

/-- A mixed carrier jet is bounded by the sum of the existing raw Sobolev
norms of its actual coordinate derivatives. Parameter Fourier differentiation
must still bound these derivative norms by the input norm of total order
`k + t`; this theorem proves the finite-dimensional and transverse-weight
steps for `app:ch_background:eq:bg-density-adjoint`. -/
theorem lpNorm_weightedCarrierJet_le_sum_rawInputCoordinateTest (k t : ℕ)
    (f : carrierInitialTestSpace n) :
    lpNorm (weightedCarrierJet k t f.val) 2 (carrierMeasure n) ≤
      ∑ a : Fin k → (Unit ⊕ Fin 2), ‖rawTestSobolev t (inputCoordinateTest k f a)‖ := by
  refine (lpNorm_weightedCarrierJet_le_sum_inputCoordinateTest k t f).trans ?_
  exact Finset.sum_le_sum (fun a _ =>
    lpNorm_etaBesselWeight_test_le_rawTestSobolev t (inputCoordinateTest k f a))

/-- Reduction of the reverse input comparison to the raw Sobolev norms of
actual carrier coordinate derivatives. The remaining parameter-Plancherel
step must control each summand by `‖rawTestSobolev s f‖`. Summing the `3^k`
coordinate terms will then supply the estimate consumed by
`InputApproximation.cauchySeq_testWeightedCarrierJet_of_rawTestSobolev_tendsto`
and `RawAssembly.exists_densityOutputs_rawSobolev_bound_of_test_inputs`
for `app:ch_background:eq:bg-density-adjoint`. -/
theorem mixedCarrierJetNorm_le_sum_rawInputCoordinateTest (s : ℕ)
    (f : carrierInitialTestSpace n) :
    mixedCarrierJetNorm s f.val ≤ ∑ k ∈ Finset.range (s + 1),
      ∑ a : Fin k → (Unit ⊕ Fin 2), ‖rawTestSobolev (s - k) (inputCoordinateTest k f a)‖ :=
  Finset.sum_le_sum (fun k _ => lpNorm_weightedCarrierJet_le_sum_rawInputCoordinateTest k (s - k) f)

end JanetCartan.ContinuumAdjoint.DensityMultiplier
