module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Masks
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.Diagonal

/-!
# Order-zero grades of the literal selected source PDO

Use the proved common-ball source identity at the SAME doubled threshold,
then the fixed normalized multiplier budgets. Both literal orientations
retain the common endpoint output and original chart input. This includes
covariable derivatives in the complete packed amplitude, and a global
physical bound covering every noncomparable shell.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.Characteristic.ResidualCoordinates
open FourierIntegral FiniteChain.Graph KernelEstimates ResidualLocalization
open FiniteChain.Retarded.KernelDecay
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "Mat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- The exact source amplitude on the smaller common output. The original
source symbol at `2 * threshold` is preserved by an equality, using its actual
common-ball plateau (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selectedSourceAmplitude_eq_multiplier_masks
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    {threshold : ℝ} (ht : f.radialThreshold ≤ threshold)
    {output : E → ℝ} (hout : tsupport output ⊆ ball x f.physicalRadius)
    (y z ξ : E) :
    orientedMaskedPDOAmplitude false (endpointOutputMask f p output) (chartInputMask f p)
      (selectedSourceSymbol f p (2 * threshold)) y z ξ =
      selectedEndpointMultiplier f p threshold ξ •
        ((endpointOutputMask f p output y * chartInputMask f p z) • (1 : Mat)) := by
  by_cases hy : endpointOutputMask f p output y = 0
  · simp [orientedMaskedPDOAmplitude, hy]
  have hy' : output (physicalCoordinates (f.chart p).index y) ≠ 0 := by
    intro hh
    apply hy
    simp [endpointOutputMask, hh]
  have hball := mem_ball.mp (hout (subset_tsupport _ hy'))
  have hlarge : physicalCoordinates (f.chart p).index y ∈
      closedBall x (4 * f.physicalRadius) := by
    change dist _ x ≤ _
    linarith [f.physicalRadius_pos]
  have he := selectedSourceSymbol_on_common_ball_enlarged f p ht hlarge
    (physicalCoordinates (f.chart p).index ξ)
  simp only [ContinuousLinearEquiv.symm_apply_apply] at he
  change selectedSourceSymbol f p (2 * threshold) y ξ =
    selectedEndpointMultiplier f p threshold ξ • (1 : Mat) at he
  simp only [orientedMaskedPDOAmplitude, Bool.false_eq_true, ↓reduceIte, he]
  exact smul_comm _ _ _

/-- Order-zero joint normalized and physical grades for the literal selected
source in both orientations. Constants precede `L`, `ρ`, coefficients and
accuracy, and are uniform over the fixed finite family. The compact carrier
may be `CompleteFactor.Kpdo`; only its geometric exclusion of zero is used.
The physical bound holds at every frequency and position, hence on all
`normalizedGraphCarrier` shells with their order-zero weight.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`. -/
theorem exists_selected_source_symbol_grades
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (J : f.centers → Set V) (hJ : ∀ p, IsCompact (J p))
    (hzero : ∀ p, ∀ v ∈ J p, v.2.1 ≠ 0) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ → ∀ p backward,
      let A := orientedMaskedPDOAmplitude backward
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedSourceSymbol f p (2 * threshold))
      (∀ v ∈ J p, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
          D m * L ^ (m + 0)) ∧
      (∀ ξ (z : E × E) m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
          D m * L ^ (m + 0)) := by
  classical
  let I : V →L[ℝ] ℝ × V := (0 : V →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ V)
  have hI : ‖I‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro v
    change max ‖(0 : ℝ)‖ ‖v‖ ≤ 1 * ‖v‖
    simp
  have hIJ p : IsCompact (I '' J p) := (hJ p).image I.continuous
  have hIz p : ∀ v ∈ I '' J p, v.2.2.1 ≠ 0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hzero p v hv
  obtain ⟨Qt, Qs, Qg, _, _, hQg, hmask⟩ := exists_selected_elapsed_mask_profiles
    f threshold ht output ho hoc hout (fun p ↦ I '' J p) hIJ hIz
  let F := fun p (z : E × E) ↦
    (endpointOutputMask f p output z.1 * chartInputMask f p z.2) • (1 : Mat)
  have hF p : ContDiff ℝ ∞ (F p) :=
    (((endpointOutputMask_properties f p ho hoc hout).1.comp contDiff_fst).mul
      ((chartPhysicalMasks_properties f p).2.1.comp contDiff_snd)).smul contDiff_const
  have hcF p : HasCompactSupport (F p) := by
    apply HasCompactSupport.intro
      ((endpointOutputMask_properties f p ho hoc hout).2.1.prod
        (chartPhysicalMasks_properties f p).2.2.2.1)
    intro z hz
    by_cases hz₁ : z.1 ∈ tsupport (endpointOutputMask f p output)
    · have hz₂ : z.2 ∉ tsupport (chartInputMask f p) := fun hh ↦ hz ⟨hz₁, hh⟩
      simp [F, image_eq_zero_of_notMem_tsupport hz₂]
    · simp [F, image_eq_zero_of_notMem_tsupport hz₁]
  choose S hS hbS using fun p m ↦ (hcF p).exists_bound_iteratedFDeriv (hF p) m
  let B := fun m ↦ ∑ p, S p m
  have hB m : 0 ≤ B m := Finset.sum_nonneg (fun p _ ↦ hS p m)
  have hSB p m : S p m ≤ B m :=
    Finset.single_le_sum (fun p _ ↦ hS p m) (Finset.mem_univ p)
  let D := fun m ↦ derivativeConvolution Qg B m + B m
  have hD m : 0 ≤ D m := add_nonneg (derivativeConvolution_nonneg hQg hB m) (hB m)
  refine ⟨D, hD, ?_⟩
  intro L ρ hL hρ p backward A
  have hβ : ContDiff ℝ ∞ (fun w : V ↦ selectedEndpointMultiplier f p threshold (ρ • w.2.1)) :=
    (selectedEndpointMultiplier_bounds f p threshold).1.comp (contDiff_snd.fst.const_smul ρ)
  have hgb (v : V) (hv : v ∈ J p) m :
      ‖iteratedFDeriv ℝ m (fun w : V ↦
        selectedEndpointMultiplier f p threshold (ρ • w.2.1)) v‖ ≤ Qg m := by
    let g := fun w : ℝ × V ↦ selectedEndpointMultiplier f p threshold (ρ • w.2.2.1)
    have hg : ContDiff ℝ ∞ g :=
      (selectedEndpointMultiplier_bounds f p threshold).1.comp (contDiff_snd.snd.fst.const_smul ρ)
    have hb := (hmask 1 ρ le_rfl hρ p (I v) (mem_image_of_mem I hv) m).2.2
    simp only [one_pow, mul_one] at hb
    change ‖iteratedFDeriv ℝ m (g ∘ I) v‖ ≤ _
    rw [I.iteratedFDeriv_comp_right hg v (by simp)]
    apply ((iteratedFDeriv ℝ m g (I v)).norm_compContinuousLinearMap_le (fun _ ↦ I)).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (mul_le_mul hb (pow_le_one₀ (norm_nonneg _) hI) (by positivity) (hQg m)).trans_eq
      (mul_one _)
  let P := ContinuousLinearMap.fst ℝ (E × E) (E × E × E)
  have hfb (v : V) m : ‖iteratedFDeriv ℝ m (F p ∘ P) v‖ ≤ B m := by
    rw [P.iteratedFDeriv_comp_right (hF p) v (by simp)]
    apply ((iteratedFDeriv ℝ m (F p) (P v)).norm_compContinuousLinearMap_le (fun _ ↦ P)).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (mul_le_mul ((hbS p m m le_rfl _).trans (hSB p m))
      (pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ _ _))
      (by positivity) (hB m)).trans_eq (mul_one _)
  have hjoint (v : V) (hv : v ∈ J p) m :
      ‖iteratedFDeriv ℝ m (fun w : V ↦ selectedEndpointMultiplier f p threshold (ρ • w.2.1) •
        F p w.1) v‖ ≤ D m * L ^ (m + 0) := by
    have hb := norm_iteratedFDeriv_smul_le_amplitude_grades hβ ((hF p).comp P.contDiff)
      hQg (show 0 ≤ (1 : ℝ) by norm_num) 0 0 v
      (by simpa only [one_pow, mul_one] using hgb v hv)
      (S := 1) (by simpa only [one_pow, mul_one, one_mul] using hfb v) m
    simp only [one_pow, mul_one, one_mul] at hb
    exact hb.trans ((le_add_of_nonneg_right (hB m)).trans
      (le_mul_of_one_le_right (hD m) (one_le_pow₀ hL)))
  have hphysical (ξ : E) (z : E × E) m :
      ‖iteratedFDeriv ℝ m (fun w : E × E ↦
        selectedEndpointMultiplier f p threshold (ρ • ξ) • F p w) z‖ ≤ D m * L ^ (m + 0) := by
    rw [iteratedFDeriv_const_smul_apply' ((hF p).contDiffAt.of_le (by simp)), norm_smul]
    apply (mul_le_mul (selectedEndpointMultiplier_bounds f p threshold |>.2 _)
      ((hbS p m m le_rfl z).trans (hSB p m)) (norm_nonneg _) zero_le_one).trans
    rw [one_mul]
    exact (le_add_of_nonneg_left (derivativeConvolution_nonneg hQg hB m)).trans
      (le_mul_of_one_le_right (hD m) (one_le_pow₀ hL))
  have he y z ξ := selectedSourceAmplitude_eq_multiplier_masks f p hft hout y z ξ
  cases backward
  · constructor
    · intro v hv m
      simpa only [A, he] using hjoint v hv m
    · intro ξ z m
      simpa only [A, he] using hphysical ξ z m
  · have he' y z ξ : orientedMaskedPDOAmplitude true
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedSourceSymbol f p (2 * threshold)) y z ξ =
          (selectedEndpointMultiplier f p threshold ξ • F p (y, z)).conjTranspose :=
      congrArg Matrix.conjTranspose (he y z ξ)
    constructor
    · intro v hv m
      simpa only [A, he', norm_iteratedFDeriv_transport_conjTranspose] using hjoint v hv m
    · intro ξ z m
      simpa only [A, he', norm_iteratedFDeriv_transport_conjTranspose] using hphysical ξ z m

open PhysicalShells PhysicalShells.Comparable PhysicalShells.Noncomparable
open KernelEstimates.NoncomparableGeometry

/-- The source branch supplies exactly the two symbol-grade inputs of
`exists_completePhysicalResidual_restriction_bound`, on its `Kpdo` and on
every noncomparable shell. Its order is zero and its fixed offset is zero;
both literal orientations share one profile. All masks and the doubled
threshold are the original selected ones (`app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_source_completeFactor_grades
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (threshold : ℝ) (ht : 1 ≤ threshold) (hft : f.radialThreshold ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    {a b : ℝ} (ha : 0 < a) :
    let Kb := fun p ↦ tsupport (endpointOutputMask f p output) ×ˢ tsupport (chartInputMask f p)
    let Kpdo := fun p ↦ comparableJointCarrier 1 1 a b
      ((Prod.fst '' Kb p) ×ˢ frequencyAnnulus
        (a / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b)))
      (Kb p) (frequencyAnnulus a b)
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ → ∀ p backward,
      let A := orientedMaskedPDOAmplitude backward
        (endpointOutputMask f p output) (chartInputMask f p)
        (selectedSourceSymbol f p (2 * threshold))
      (∀ v ∈ Kpdo p, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
          ρ ^ (0 : ℝ) * D m * L ^ (m + 0)) ∧
      (∀ low l, ∀ ξ ∈ normalizedGraphCarrier ρ low l, ∀ z ∈ Kb p, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (branchRadius low l)) ^ (0 : ℝ) * D m * L ^ (m + 0)) := by
  intro Kb Kpdo
  have hKb p : IsCompact (Kb p) :=
    (endpointOutputMask_properties f p ho hoc hout).2.1.prod
      (chartPhysicalMasks_properties f p).2.2.2.1
  have hKpdo p : IsCompact (Kpdo p) :=
    isCompact_comparableJointCarrier 1 1 a b
      (((hKb p).image continuous_fst).prod (isCompact_frequencyAnnulus _ _))
      (hKb p) (isCompact_frequencyAnnulus _ _)
  have hzero p : ∀ v ∈ Kpdo p, v.2.1 ≠ 0 := by
    intro v hv hz
    have hn := hv.1.2.1.1
    change a / (16 * annulusFactor 1 1) ≤ ‖v.2.1‖ at hn
    rw [hz, norm_zero] at hn
    have hf := two_le_annulusFactor 1 1
    have : 0 < a / (16 * annulusFactor 1 1) := div_pos ha (by linarith)
    linarith
  obtain ⟨D, hD, hg⟩ := exists_selected_source_symbol_grades f threshold ht hft output
    ho hoc hout Kpdo hKpdo hzero
  refine ⟨D, hD, ?_⟩
  intro L ρ hL hρ p backward A
  obtain ⟨hj, hp⟩ := hg L ρ hL hρ p backward
  refine ⟨?_, ?_⟩
  · simpa only [Real.rpow_zero, one_mul] using hj
  · intro low l ξ _ z _ m
    simpa only [Real.rpow_zero, one_mul] using hp ξ z m

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
