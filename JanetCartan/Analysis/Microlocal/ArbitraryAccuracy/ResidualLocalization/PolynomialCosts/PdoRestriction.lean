module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.PdoMasks
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Restriction
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Restriction

/-!
# Actual PDO costs on the restriction scale

Apply the checked natural-order estimate to a fixed interior plateau, prove
that the plateau leaves the actual PDO unchanged, and use the two genuine
Sobolev comparisons. This constructs `hcost` for the diagonal factors of
`finiteChain_observation_rapidDecayAt` (`app:ch_regular:eq:chain-tail`).
The local operator is exactly the existing restriction of the same whole-space
operator applied to the existing zero extension. No new operator or scale is
introduced, and no positive-order regularity of bare zero extension is assumed.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff NNReal ENNReal Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization

open LocalSobolev Pseudodifferential FourierIntegral LowBounds AmplitudeBound
open RegularSector.Characteristic RegularSector.Characteristic.PdoRealization
open RegularSector.Characteristic.RetardedLocalization
open CharacteristicTransport.CompleteResidual ResponseTransfer

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Exact identity between the existing global multiplier and the existing
local bump followed by zero extension. Consumer: the fixed-plateau proof of
the PDO restriction cost (`app:ch_regular:lem:finite-chain`). -/
theorem sourceCutMultiplier_zeroExtend_bump {x : E} (χ : ContDiffBump x)
    {U : Set E} (hU : MeasurableSet U) (u : LocalL2 U (EuclideanSpace ℂ (Fin q))) :
    sourceCutMultiplier χ χ.continuous (SmallSupport.bump_norm_le_one χ)
      (SmallSupport.zeroExtend hU u) =
        SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u) := by
  apply Lp.ext
  filter_upwards [sourceCutMultiplier_coeFn χ χ.continuous
    (SmallSupport.bump_norm_le_one χ) (SmallSupport.zeroExtend hU u),
    SmallSupport.zeroExtend_coeFn hU u, zeroExtend_bumpL2_coeFn hU χ u] with y hy he hz
  rw [hy, he, hz, Complex.coe_smul]

/-- The actual physical PDO, forward or literal adjoint, has polynomial cost
on the EXISTING complex restriction scale. The sole extra geometric input is
a fixed interior plateau on its original source mask (the output mask in the
adjoint orientation). The plateau identity is proved from the literal kernel;
the analytic inputs are primitive symbol derivatives supplied by
`AlgebraicSymbols` and `EndpointPdoBounds`, with their original fixed reserve.
Consumer: `finiteChain_observation_rapidDecayAt.hcost`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem maskedPhysicalPDO_hasPolynomialRestrictionCost
    {ι : Type*} (ρ L : ι → ℝ) (hL : ∀ i, 1 ≤ L i) (hLρ : ∀ i, L i ≤ ρ i)
    (χout χsource : E → ℂ) (c : ι → E → E → Mat) (R M : ℝ)
    (hb : ∀ i, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol χout χsource (c i)) R M)
    (b : ℕ) (A : ℕ → ℝ) (hA : ∀ s, 0 ≤ A s)
    (hhi : ∀ s i ξ is, is.length ≤ 2 * (d + 1 + 1) + s → ∀ z,
      ‖matrixAmplitudeCoordinateDerivList is
        (maskedPhysicalPDOCycleSymbol χout χsource (c i) ξ) z‖ ≤ A s * L i ^ (s + b))
    (backward : Bool) {x : E} (χ : ContDiffBump x)
    (U V : Set E) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hs : tsupport (χ : E → ℝ) ⊆ U)
    (hp : ∀ y ∈ tsupport (if backward then χout else χsource), χ y = 1) :
    HasPolynomialSobolevCost (restrictionSobolevScale U (EuclideanSpace ℂ (Fin q)) hU)
      (restrictionSobolevScale V (EuclideanSpace ℂ (Fin q)) hV) ρ
      (fun i ↦ (localRetardedOperator hU V (if backward then
        (maskedPhysicalPDO χout χsource (c i)).adjoint
        else maskedPhysicalPDO χout χsource (c i))).toLinearMap) := by
  let T (i : ι) := if backward then (maskedPhysicalPDO χout χsource (c i)).adjoint
    else maskedPhysicalPDO χout χsource (c i)
  have hT (i : ι) : T i = maskedPhysicalPDO χout χsource (c i) ∨
      T i = (maskedPhysicalPDO χout χsource (c i)).adjoint := by
    cases backward <;> simp [T]
  have hmask (i : ι) : (T i).comp
      (sourceCutMultiplier χ χ.continuous (SmallSupport.bump_norm_le_one χ)) = T i := by
    cases backward with
    | false =>
      exact (maskedPhysicalPDO_plateau_identities χout χsource (c i) (fun _ ↦ 1) χ
        continuous_const χ.contDiff (fun _ ↦ by norm_num) (SmallSupport.bump_norm_le_one χ)
        (fun _ _ ↦ rfl) hp).2
    | true =>
      exact maskedPhysicalPDO_adjoint_source_plateau χout χsource (c i) χ (fun _ ↦ 1)
        χ.contDiff contDiff_const (SmallSupport.bump_norm_le_one χ) (fun _ ↦ by norm_num)
        hp (fun _ _ ↦ rfl)
  intro s
  obtain ⟨D, hD, hbound⟩ := exists_maskedPhysicalPDO_polynomial_fourier_constant
    (d := d) (q := q) R M s b (A s) (hA s)
  obtain ⟨Kin, hKin, hin⟩ := exists_bump_zeroExtension_fourier_constant (r := q) χ s
  obtain ⟨Kout, hKout, hout⟩ := exists_restrictionScale_fourier_comparison (d + 1) q s
  refine ⟨s, (s + b : ℕ), Kout * D * Kin, by positivity, ?_⟩
  intro i u hu
  let z := SmallSupport.zeroExtend hU (SmallSupport.bumpL2 (p := 2) le_rfl χ u)
  obtain ⟨hzmem, hznorm⟩ := hin U hU hs u hu
  have he : T i z = T i (SmallSupport.zeroExtend hU u) := by
    dsimp only [z]
    rw [← sourceCutMultiplier_zeroExtend_bump χ hU u]
    exact congrArg (fun Q : H →L[ℂ] H ↦ Q (SmallSupport.zeroExtend hU u)) (hmask i)
  obtain ⟨hm, hn⟩ := hbound (ρ i) (L i) (hL i) (hLρ i) χout χsource (c i)
    (hb i) (hhi s i) (T i) (hT i) z hzmem
  rw [he] at hm hn
  obtain ⟨hloc, hnorm⟩ := hout V hV _ (localRetardedOperator hU V (T i) u) hm
    (restrictL2_coeFn V (T i (SmallSupport.zeroExtend hU u))).symm
  refine ⟨hloc, hnorm.trans ?_⟩
  rw [restrictionSobolevScale_gradeNorm hU hu, Real.rpow_natCast]
  calc
    _ ≤ Kout * (D * ρ i ^ (s + b) * vectorFourierSobolevNorm (s : ℝ) z) :=
      mul_le_mul_of_nonneg_left hn hKout.le
    _ ≤ Kout * (D * ρ i ^ (s + b) * (Kin * restrictionSobolevNorm U s u)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hznorm
        (mul_nonneg hD (pow_nonneg (zero_le_one.trans ((hL i).trans (hLρ i))) _))) hKout.le
    _ = _ := by ring

end JanetCartan.ArbitraryAccuracy.ResidualLocalization
