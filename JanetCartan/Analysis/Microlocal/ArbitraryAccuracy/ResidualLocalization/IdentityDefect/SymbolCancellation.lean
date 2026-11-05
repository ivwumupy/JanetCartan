module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteMasks.ActualFamily

/-!
# Cancellation of the literal principal and angular symbols

These identities retain the fixed low-frequency bump and both physical
positions. They supply the symbol cancellation needed before estimating the
principal defect and terminal observation in `app:ch_regular:lem:finite-chain`.
They do not identify a sector operator with a newly chosen angular multiplier,
and do not assert an operator localization estimate.
-/

@[expose] public noncomputable section

open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect

open FourierIntegral CharacteristicTransport.CompleteResidual
open RegularSector.FiniteMasks RegularSector.Characteristic
open RegularSector.Characteristic.ResidualCoordinates
open RegularSector.Characteristic.EvolutionIntegral
open FourierIntegral.LowBounds.FrequencyCutoff
open CompatibleResponse

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ

/-- Subtracting the full identity from the original principal amplitude keeps
both physical shoulders and the literal scalar principal symbol. Consumer:
the principal branch of `app:ch_regular:eq:chain-tail`. -/
theorem principalAmplitude_sub_identity
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (W₁ : TwoTimeAmplitude d q) (bminus : E → E → Mat)
    (σ : E → Euclidean d → ℂ) (β χout χsource : E → ℂ) (x y ξ : E) :
    (χout x * χsource y) • directPDOSymbols A B W₁ bminus σ β 1 x ξ - 1 =
      (χout x * χsource y * (σ x (spatialPart ξ) * β ξ) - 1) • (1 : Mat) := by
  simp only [directPDOSymbols, Matrix.cons_val_one, Matrix.cons_val_zero,
    smul_smul, sub_smul, one_smul]

/-- The original source/spatial plateau cancels the scalar source symbol
against its own physical right mask, including the entire transition region.
The producer of the plateau is `ActualMaskFamily.conicSourceSymbol_eq_one`.
Consumer: the finite sum of principal branches in the terminal
`app:ch_regular:eq:resolved-angular-tail`. -/
theorem actualFamily_principalSymbol_eq_rightMask
    {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualFamily.ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (A : E → Fin (d + 1) → Mat) (B : E → Mat)
    (W₁ : TwoTimeAmplitude d q) (bminus : E → E → Mat) {y : E}
    (hy : physicalCoordinates (f.chart p).index y ∈ closedBall x (4 * f.physicalRadius))
    (ξ : E) :
    directPDOSymbols A B W₁ bminus
      (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
        (f.chart p).sourceMask)
      (fun ζ ↦ (dilatedConicMask (f.angularMask p) f.radialThreshold
        (physicalCoordinates (f.chart p).index ζ) : ℂ)) 1 y ξ =
      (dilatedConicMask (f.angularMask p) f.radialThreshold
        (physicalCoordinates (f.chart p).index ξ) : ℂ) • (1 : Mat) := by
  by_cases hξ : dilatedConicMask (f.angularMask p) f.radialThreshold
      (physicalCoordinates (f.chart p).index ξ) = 0
  · simp [directPDOSymbols, hξ]
  · have hp := f.conicSourceSymbol_eq_one p hy (subset_tsupport
        (dilatedConicMask (f.angularMask p) f.radialThreshold ∘
          physicalCoordinates (f.chart p).index) hξ)
    simp [directPDOSymbols, hp]

/-- Exact principal discrepancy before adding any low-frequency correction.
The second summand is the original fixed low-frequency bump; it cannot be
dropped when estimating the full terminal identity defect
(`app:ch_regular:eq:resolved-angular-tail`). -/
theorem sum_dilatedConicMask_sub_one {ι : Type*} [Fintype ι]
    (a : ι → E → ℝ) (R : ℝ) (ξ : E) :
    (∑ i, dilatedConicMask (a i) R ξ) - 1 =
      -dilatedConicMask (fun η ↦ 1 - ∑ i, a i η) R ξ -
        physicalCutoff 0 (R⁻¹ • ξ) := by
  linarith [dilatedConicMask_complete_partition a R ξ]

/-- The actual chart principal symbols, pulled back to the SAME physical
coordinates, have exactly the angular and bounded-frequency discrepancy from
the fixed finite partition. This is a symbol identity on the common source
plateau; identifying the sector's bounded finite sum remains its producer's
obligation. Consumer: `app:ch_regular:eq:resolved-angular-tail`. -/
theorem actualFamily_principalSum_sub_identity
    {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualFamily.ActualMaskFamily Ω x RQ A₀ K M)
    (A : f.centers → E → Fin (d + 1) → Mat) (B : f.centers → E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d q) (bminus : f.centers → E → E → Mat)
    {y : E} (hy : y ∈ closedBall x (4 * f.physicalRadius)) (ξ : E) :
    (∑ p, directPDOSymbols (A p) (B p) (W₁ p) (bminus p)
      (conicSourceSymbol (f.chart p).radialSection (conicMask (f.spatialMask p))
        (f.chart p).sourceMask)
      (fun ζ ↦ (dilatedConicMask (f.angularMask p) f.radialThreshold
        (physicalCoordinates (f.chart p).index ζ) : ℂ)) 1
      ((physicalCoordinates (f.chart p).index).symm y)
      ((physicalCoordinates (f.chart p).index).symm ξ)) - 1 =
      ((-dilatedConicMask (fun η ↦ 1 - ∑ p, f.angularMask p η) f.radialThreshold ξ -
        physicalCutoff 0 (f.radialThreshold⁻¹ • ξ) : ℝ) : ℂ) • (1 : Mat) := by
  have hp (p : f.centers) := actualFamily_principalSymbol_eq_rightMask f p
    (A p) (B p) (W₁ p) (bminus p)
    (y := (physicalCoordinates (f.chart p).index).symm y)
    (by simpa only [ContinuousLinearEquiv.apply_symm_apply] using hy)
    ((physicalCoordinates (f.chart p).index).symm ξ)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hp
  simp_rw [hp]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum]
  simpa only [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul] using
    congrArg (fun t : ℝ ↦ (t : ℂ) • (1 : Mat))
      (sum_dilatedConicMask_sub_one f.angularMask f.radialThreshold ξ)

/-- The literal finite principal mask has the required order-zero pointwise
bound, including the low-frequency transition. This discharges the scalar
integrability bound in `actualFamily_scalar_identity_defect_eq_fourier`;
no bound on an operator is assumed (`app:ch_regular:eq:resolved-angular-tail`). -/
theorem actualFamily_sum_dilatedConicMask_mem_Icc
    {Ω : Set E} {x : E} {RQ M : ℝ}
    {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set E}
    (f : ActualFamily.ActualMaskFamily Ω x RQ A₀ K M) (ξ : E) :
    (∑ p, dilatedConicMask (f.angularMask p) f.radialThreshold ξ) ∈ Icc (0 : ℝ) 1 := by
  simp only [dilatedConicMask, conicMask, radialSourceCutoff, ← Finset.mul_sum]
  have hn := Finset.sum_nonneg (s := Finset.univ) (fun p _ ↦
    (f.angularMask_range p (NormedSpace.normalize (f.radialThreshold⁻¹ • ξ))).1)
  have hsum := f.angularMask_sum_le_one (NormedSpace.normalize (f.radialThreshold⁻¹ • ξ))
  have hc := physicalCutoff_nonneg 0 (f.radialThreshold⁻¹ • ξ)
  have hc' := physicalCutoff_le_one 0 (f.radialThreshold⁻¹ • ξ)
  exact ⟨mul_nonneg (sub_nonneg.mpr hc') hn,
    (mul_le_of_le_one_left hn (by linarith)).trans hsum⟩

/-- On the protected angular plateau the principal discrepancy is exactly
the negative low bump, at every frequency, including its shoulders. This is
the bounded-frequency term in `app:ch_regular:eq:resolved-angular-tail`. -/
theorem sum_dilatedConicMask_sub_one_on_angular_plateau
    {ι : Type*} [Fintype ι] (a : ι → E → ℝ) {R : ℝ} (hR : 0 < R)
    {ξ : E} (ha : ∑ i, a i (NormedSpace.normalize ξ) = 1) :
    (∑ i, dilatedConicMask (a i) R ξ) - 1 = -physicalCutoff 0 (R⁻¹ • ξ) := by
  rw [sum_dilatedConicMask_sub_one]
  simp only [dilatedConicMask, conicMask, radialSourceCutoff,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr hR), ha, sub_self, mul_zero,
    neg_zero, zero_sub]

/-- The summed principal symbol is one only after the original radial
threshold has been passed and the original angular plateau has been entered.
Consumer: the terminal symbol cancellation in `app:ch_regular:eq:chain-tail`. -/
theorem sum_dilatedConicMask_eq_one_of_high_plateau
    {ι : Type*} [Fintype ι] (a : ι → E → ℝ) {R : ℝ} (hR : 0 < R)
    {ξ : E} (hξ : 2 * R ≤ ‖ξ‖)
    (ha : ∑ i, a i (NormedSpace.normalize ξ) = 1) :
    ∑ i, dilatedConicMask (a i) R ξ = 1 := by
  have hn : 2 ≤ ‖R⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hR.le)]
    exact (le_inv_mul_iff₀ hR).mpr (by simpa [mul_comm] using hξ)
  exact sum_conicMask_eq_one a hn
    (by simpa only [NormedSpace.normalize_smul_of_pos (inv_pos.mpr hR)] using ha)

/-- The protected plateau is a germ of equality, not just equality at a
single covector. This excludes the CLOSED support of the complementary
symbol, as required by the stationary-phase argument in
`app:ch_regular:eq:chain-tail`. The strict angular input is produced by
`ProtectedMasks.exists_physicalProtectedLocalizer`. -/
theorem sum_dilatedConicMask_eventuallyEq_one
    {ι : Type*} [Fintype ι] (a : ι → E → ℝ) {R : ℝ} (hR : 0 < R)
    {ξ : E} (hξ : 2 * R < ‖ξ‖)
    (ha : NormedSpace.normalize ξ ∈ interior {η | ∑ i, a i η = 1}) :
    (fun ζ ↦ ∑ i, dilatedConicMask (a i) R ζ) =ᶠ[𝓝 ξ] fun _ ↦ 1 := by
  have hne : ξ ≠ 0 := norm_pos_iff.mp (by linarith)
  have hn : ContinuousAt (NormedSpace.normalize : E → E) ξ :=
    (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hne)).smul continuousAt_id
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hξ),
    hn.eventually (isOpen_interior.mem_nhds ha)] with ζ hζ hζa
  exact sum_dilatedConicMask_eq_one_of_high_plateau a hR hζ.le
    (interior_subset (s := {η | ∑ i, a i η = 1}) hζa)

/-- The full two-position scalar defect vanishes as a germ on the buffered
physical and high-frequency angular plateau. Both source and output shoulders
are still present in the function whose closed support is excluded. Their
germs come from the actual physical masks, and the angular germ from the
protected localizer. Consumer: terminal nonstationarity in
`app:ch_regular:eq:chain-tail`. -/
theorem notMem_tsupport_masked_angular_defect
    {ι : Type*} [Fintype ι] (a : ι → E → ℝ) (χout χsource : E → ℝ)
    {R : ℝ} (hR : 0 < R) {x y ξ : E}
    (hx : χout =ᶠ[𝓝 x] fun _ ↦ 1) (hy : χsource =ᶠ[𝓝 y] fun _ ↦ 1)
    (hξ : 2 * R < ‖ξ‖)
    (ha : NormedSpace.normalize ξ ∈ interior {η | ∑ i, a i η = 1}) :
    ((x, y), ξ) ∉ tsupport (fun p : (E × E) × E ↦
      χout p.1.1 * χsource p.1.2 * (∑ i, dilatedConicMask (a i) R p.2) - 1) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  have hout := hx.comp_tendsto (continuous_fst.fst.tendsto ((x, y), ξ))
  have hsource := hy.comp_tendsto (continuous_fst.snd.tendsto ((x, y), ξ))
  have hang := (sum_dilatedConicMask_eventuallyEq_one a hR hξ ha).comp_tendsto
    (continuous_snd.tendsto ((x, y), ξ))
  filter_upwards [hout, hsource, hang] with p hp hs hg
  dsimp only [Function.comp_def] at hp hs hg
  simp only [hp, hs, hg, mul_one, sub_self, Pi.zero_apply]

/-- One fixed lower annular endpoint supplies a uniform radial threshold for
the complementary CLOSED support. The threshold uses the original fixed
low bump and is independent of the requested accuracy. The geometric inputs
are the actual physical shoulders and the angular/annular support supplied by
`ProtectedMasks.exists_physicalProtectedLocalizer`. Consumer: terminal
nonstationarity in `app:ch_regular:eq:chain-tail`. -/
theorem notMem_tsupport_masked_angular_defect_of_annular_buffer
    {ι : Type*} [Fintype ι] (a : ι → E → ℝ) (χout χsource : E → ℝ)
    {R lo ρ : ℝ} (hR : 0 < R) (hlo : 0 < lo) (hρ : 2 * R / lo < ρ)
    {x y ξ : E} (hx : χout =ᶠ[𝓝 x] fun _ ↦ 1)
    (hy : χsource =ᶠ[𝓝 y] fun _ ↦ 1) (hξ : lo ≤ ‖ξ‖)
    (ha : NormedSpace.normalize ξ ∈ interior {η | ∑ i, a i η = 1}) :
    ((x, y), ρ • ξ) ∉ tsupport (fun p : (E × E) × E ↦
      χout p.1.1 * χsource p.1.2 * (∑ i, dilatedConicMask (a i) R p.2) - 1) := by
  have hρpos : 0 < ρ := (div_pos (mul_pos (by norm_num) hR) hlo).trans hρ
  apply notMem_tsupport_masked_angular_defect a χout χsource hR hx hy
  · rw [norm_smul, Real.norm_of_nonneg hρpos.le]
    exact ((div_lt_iff₀ hlo).mp hρ).trans_le
      (mul_le_mul_of_nonneg_left hξ hρpos.le)
  · simpa only [NormedSpace.normalize_smul_of_pos hρpos] using ha

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.IdentityDefect
