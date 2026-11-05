module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.PdoRestriction

/-!
# Fixed-plateau transfer of the actual operator costs

This comparison is used for the elapsed integrals and complete finite sums in
`app:ch_regular:lem:finite-chain`. Its Fourier cost is supplied by the concrete
PDO and separated-budget elapsed-integral theorems. The plateau equality must
hold for that same operator; bare zero extension is never asserted to preserve
positive Sobolev order.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped NNReal ENNReal
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization
open ResponseTransfer.Complement
open LocalSobolev Pseudodifferential FourierIntegral LowBounds ResponseTransfer
open RegularSector.Characteristic.RetardedLocalization
variable {d q : ℕ} {ι : Type*}
local notation "E" => Euclidean (d + 1)
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Transfer a proved Fourier cost through the existing restriction operator,
using an exact fixed source plateau. Consumer: the actual elapsed and complete
residual factors in `app:ch_regular:eq:chain-tail`. -/
theorem polynomialRestrictionCost_of_fourierCost_of_plateau
    (ρ : ι → ℝ) (hρ : ∀ i, 0 ≤ ρ i) (T : ι → H →L[ℂ] H)
    (hT : HasPolynomialSobolevCost vectorFourierSobolevScale vectorFourierSobolevScale
      ρ (fun i ↦ (T i).toLinearMap.restrictScalars ℝ))
    {x : E} (χ : ContDiffBump x) (U V : Set E)
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hs : tsupport (χ : E → ℝ) ⊆ U)
    (hp : ∀ i, (T i).comp
      (sourceCutMultiplier χ χ.continuous (SmallSupport.bump_norm_le_one χ)) = T i) :
    HasPolynomialSobolevCost (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU)
      (restrictionSobolevScale V (EuclideanSpace ℂ (Fin q)) hV) ρ
      (fun i ↦ (localRetardedOperator hU V (T i)).toLinearMap) := by
  intro s
  obtain ⟨t, c, D, hD, hbound⟩ := hT s
  obtain ⟨Kin, hKin, hin⟩ := exists_bump_zeroExtension_fourier_constant (r := q) χ t
  obtain ⟨Kout, hKout, hout⟩ := exists_restrictionScale_fourier_comparison (d + 1) q s
  refine ⟨t, c, Kout * D * Kin, by positivity, ?_⟩
  intro i u hu
  let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
  obtain ⟨hzmem, hznorm⟩ := hin U hU hs u hu
  have he : T i z = T i (SmallSupport.zeroExtend hU u) := by
    dsimp only [z]
    rw [← sourceCutMultiplier_zeroExtend_bump χ hU u]
    exact congrArg (fun Q : H →L[ℂ] H ↦ Q (SmallSupport.zeroExtend hU u)) (hp i)
  obtain ⟨hm, hn⟩ := hbound i z hzmem
  change MemVectorFourierSobolev (s : ℝ) (T i z) at hm
  change MemVectorFourierSobolev (t : ℝ) z at hzmem
  change vectorFourierSobolevScale.gradeNorm s (T i z) ≤ _ at hn
  rw [vectorFourierSobolevScale_gradeNorm s hm,
    vectorFourierSobolevScale_gradeNorm t hzmem] at hn
  change MemVectorFourierSobolev (s : ℝ) (T i z) at hm
  rw [he] at hm hn
  obtain ⟨hloc, hnorm⟩ := hout V hV _ (localRetardedOperator hU V (T i) u) hm
    (restrictL2_coeFn V (T i (SmallSupport.zeroExtend hU u))).symm
  refine ⟨hloc, hnorm.trans ?_⟩
  rw [restrictionSobolevScale_gradeNorm hU hu]
  calc
    _ ≤ Kout * (D * ρ i ^ c * vectorFourierSobolevNorm (t : ℝ) z) :=
      mul_le_mul_of_nonneg_left hn hKout.le
    _ ≤ Kout * (D * ρ i ^ c * (Kin * restrictionSobolevNorm U t u)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hznorm
        (mul_nonneg hD (Real.rpow_nonneg (hρ i) _))) hKout.le
    _ = _ := by ring

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
