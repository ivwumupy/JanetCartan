module
public import JanetCartan.Analysis.Microlocal.InitialSourceLocalization.ModulationCompact
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ScaleGap

/-!
# Original-stage control of the independent source shifts

The original carrier and fine exponents give one threshold placing the
literal Fourier modulation inside a prescribed positive source radius.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.InitialSourceLocalization
open ActualCarriers CurrentFullPhase FrozenMenu HamiltonPhase ProtectedFlow

/-- The original stage exponents put every independent Fourier shift into
the fixed source-compact radius. The one threshold precedes histories, radial
labels and Fourier cutoffs (`main:eq:all-pair-scales`,
`app:ch_regular:eq:source-tail`). -/
theorem exists_originalScale_source_shift_threshold {ε : ℝ} (hε : 0 < ε) (Cband : ℝ) :
    ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀ ≥ S, ∀ stage : ℕ,
      let R := historyScale R₀ growthExponent stage
      ∀ radial : ℝ, 1 ≤ radial → ∀ K : ℝ, 0 ≤ K → K ≤ Cband * R^fineExponent →
        |(radial * R^carrierExponent)⁻¹| * K ≤ ε := by
  obtain ⟨S,hS⟩ := eventually_atTop.1
    (eventually_mul_rpow_le_of_exponent_lt (Cband / ε)
      (by norm_num [fineExponent,meanSlack,carrierExponent] : fineExponent < carrierExponent))
  refine ⟨max 2 S,le_max_left _ _,?_⟩
  intro R₀ hR₀ stage R radial hradial K hK hKbound
  have hR₀one : 1 ≤ R₀ := (by norm_num : (1 : ℝ) ≤ 2).trans ((le_max_left _ _).trans hR₀)
  have hRone : 1 ≤ R := hR₀one.trans (le_historyScale hR₀one stage)
  have hRp : 0 < R := zero_lt_one.trans_le hRone
  have hlarge : S ≤ R := ((le_max_right _ _).trans hR₀).trans (le_historyScale hR₀one stage)
  have hlam : 0 < R^carrierExponent := Real.rpow_pos_of_pos hRp _
  have hprod : 0 < radial * R^carrierExponent := mul_pos (zero_lt_one.trans_le hradial) hlam
  rw [abs_of_pos (inv_pos.mpr hprod),inv_mul_eq_div]
  apply (div_le_iff₀ hprod).mpr
  calc
    K ≤ Cband * R^fineExponent := hKbound
    _ = ε * ((Cband / ε) * R^fineExponent) := by field_simp
    _ ≤ ε * R^carrierExponent := mul_le_mul_of_nonneg_left (hS R hlarge) hε.le
    _ ≤ ε * (radial * R^carrierExponent) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hlam.le hradial) hε.le

/-- The original single-source frequency and the unchanged coefficient exponent
satisfy the same fixed absorption gap as the signed source, before proof depth
or mask budgets. This discharges the scale premise in
`exists_initialized_originalModulation_firstMask_rapidDecayAt`
(`main:prop:current-scale`, `main:eq:all-pair-scales`). -/
theorem originalScale_primary_source_scale_gap {R₀ radial : ℝ}
    (hR₀ : 1 ≤ R₀) (stage : ℕ) (hradial : 1 ≤ radial) :
    let τ := (radial * historyScale R₀ growthExponent stage ^ carrierExponent)⁻¹
    0 < τ ∧ currentCoefficientScale R₀ stage ≤ τ⁻¹ ^ (1 - 1 / 1000 : ℝ) := by
  let R := historyScale R₀ growthExponent stage
  have hR : 1 ≤ R := hR₀.trans (le_historyScale hR₀ stage)
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hfrequency : 0 < radial * R^carrierExponent :=
    mul_pos (zero_lt_one.trans_le hradial) (Real.rpow_pos_of_pos hRp _)
  refine ⟨inv_pos.mpr hfrequency, ?_⟩
  simp only [inv_inv]
  calc
    currentCoefficientScale R₀ stage = R^coefficientExponent := rfl
    _ ≤ R^(carrierExponent * (1 - 1 / 1000 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hR
        (by norm_num [coefficientExponent,carrierExponent])
    _ = (R^carrierExponent)^(1 - 1 / 1000 : ℝ) :=
      Real.rpow_mul hRp.le _ _
    _ ≤ (radial * R^carrierExponent)^(1 - 1 / 1000 : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hRp.le _)
        (le_mul_of_one_le_left (Real.rpow_nonneg hRp.le _) hradial) (by norm_num)

end JanetCartan.InitialSourceLocalization
