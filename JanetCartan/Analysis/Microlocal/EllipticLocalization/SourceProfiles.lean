module

public import JanetCartan.Analysis.Microlocal.EllipticLocalization.Support
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.PdoGrades.SourceEndpoint.Source

/-!
# Order-zero mixed grades of the actual elliptic source

The fixed elliptic angular mask is substituted into the existing normalized
conic-mask estimate. Both physical masks and the doubled collar are retained.
The compact joint carrier may be the diagonal consumer's comparable carrier;
the spatial estimate covers every noncomparable shell
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticLocalization
open FiniteMasks.ActualFamily FiniteMasks EllipticComplement
open ArbitraryAccuracy.ResidualLocalization ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FourierIntegral.PrimitiveProfiles FiniteChain.Graph
open KernelEstimates
open FiniteChain.Retarded.KernelDecay
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
variable {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)
local notation "χo" => fun y ↦ (f.outputMask y : ℂ)
local notation "χs" => fun z ↦ (f.inputMask z : ℂ)

/-- The literal elliptic source supplies joint normalized and global spatial
grades, with degree zero and zero slow-scale offset in both orientations.
Only the actual fixed compact carrier excluding zero is supplied; neither
symbol derivatives nor operator estimates are hypotheses
(`app:ch_regular_base:eq:sector-theorem-identity`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_ellipticSource_masked_symbol_grades
    (χout : E → ℂ) (hout : ContDiff ℝ ∞ χout) (hcout : HasCompactSupport χout)
    (threshold : ℝ) (ht : 1 ≤ threshold)
    (J : Set V) (hJ : IsCompact J) (hzero : ∀ v ∈ J, v.2.1 ≠ 0) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ → ∀ backward,
      let A := orientedMaskedPDOAmplitude backward χout (χs) (ellipticSourceSymbol f hK threshold)
      (∀ v ∈ J, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤ D m * L ^ m) ∧
      (∀ ξ (z : E × E) m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤ D m * L ^ m) := by
  let π : V →L[ℝ] ℝ × E := (0 : V →L[ℝ] ℝ).prod
    ((ContinuousLinearMap.fst ℝ E (E × E)).comp (ContinuousLinearMap.snd ℝ (E × E) (E × E × E)))
  let β : E → ℂ := fun ξ ↦ (ellipticSourceMask f hK threshold ξ : ℂ)
  let Jβ := π '' J
  have hJβ : IsCompact Jβ := hJ.image π.continuous
  have hJzero : ∀ v ∈ Jβ, v.2 ≠ 0 := by
    rintro _ ⟨v, hv, rfl⟩
    exact hzero v hv
  have hβm m : BoundedNormalizedSeminorm Jβ m (fun w : ℝ × E ↦ β w.2) :=
    boundedNormalizedSeminorm_dilatedConicMask (ellipticAngularMask_spec f hK).1
      (show 1 ≤ 2*threshold by linarith) hJβ hJzero m
  have hβ : ContDiff ℝ ∞ β := Complex.ofRealCLM.contDiff.comp
    (ellipticSourceMask_properties f hK threshold).1
  let G m := normalizedSeminorm Jβ m (fun w : ℝ × E ↦ β w.2) * ‖π‖ ^ m
  have hG m : 0 ≤ G m := mul_nonneg (normalizedSeminorm_nonneg _ _ _)
    (pow_nonneg (norm_nonneg _) _)
  let F : E × E → CMat := fun z ↦ (χout z.1 * (f.inputMask z.2 : ℂ)) • (1 : CMat)
  have hF : ContDiff ℝ ∞ F :=
    ((hout.comp contDiff_fst).mul
      ((Complex.ofRealCLM.contDiff.comp f.inputMask_smooth).comp contDiff_snd)).smul contDiff_const
  have hcF : HasCompactSupport F := by
    apply HasCompactSupport.intro (hcout.prod (f.inputMask_compact.comp_left Complex.ofReal_zero))
    intro z hz
    by_cases hy : z.1 ∈ tsupport χout
    · have hh := image_eq_zero_of_notMem_tsupport (fun hh ↦ hz ⟨hy, hh⟩)
      change (f.inputMask z.2 : ℂ) = 0 at hh
      simp only [F, hh, mul_zero, zero_smul]
    · have hh := image_eq_zero_of_notMem_tsupport hy
      simp [F, hh]
  choose B hB hb using fun m ↦ hcF.exists_bound_iteratedFDeriv hF m
  let D m := derivativeConvolution G B m + B m
  have hD m : 0 ≤ D m := add_nonneg (derivativeConvolution_nonneg hG hB m) (hB m)
  refine ⟨D, hD, ?_⟩
  intro L ρ hL hρ backward A
  have hn : ContDiff ℝ ∞ (normalizedField ρ (fun w : ℝ × E ↦ β w.2)) :=
    hβ.comp (contDiff_snd.const_smul ρ)
  have hgb (v : V) (hv : v ∈ J) m :
      ‖iteratedFDeriv ℝ m (fun w : V ↦ β (ρ • w.2.1)) v‖ ≤ G m := by
    change ‖iteratedFDeriv ℝ m ((normalizedField ρ (fun w : ℝ × E ↦ β w.2)) ∘ π) v‖ ≤ _
    rw [π.iteratedFDeriv_comp_right hn v (by simp)]
    apply ((iteratedFDeriv ℝ m (normalizedField ρ (fun w : ℝ × E ↦ β w.2))
      (π v)).norm_compContinuousLinearMap_le (fun _ ↦ π)).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right
      ((norm_iteratedFDeriv_le_cNorm hJβ (hn.of_le (by simp))
        (mem_image_of_mem π hv) le_rfl).trans (cNorm_normalizedField_le (hβm m) hρ))
      (pow_nonneg (norm_nonneg _) _)
  let P := ContinuousLinearMap.fst ℝ (E × E) (E × E × E)
  have hfb (v : V) m : ‖iteratedFDeriv ℝ m (F ∘ P) v‖ ≤ B m := by
    rw [P.iteratedFDeriv_comp_right hF v (by simp)]
    apply ((iteratedFDeriv ℝ m F (P v)).norm_compContinuousLinearMap_le (fun _ ↦ P)).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (mul_le_mul (hb m m le_rfl _) (pow_le_one₀ (norm_nonneg _)
      (ContinuousLinearMap.norm_fst_le ℝ _ _)) (by positivity) (hB m)).trans_eq (mul_one _)
  have hjoint (v : V) (hv : v ∈ J) m :
      ‖iteratedFDeriv ℝ m (fun w : V ↦ β (ρ • w.2.1) • F w.1) v‖ ≤ D m * L ^ m := by
    have hh := norm_iteratedFDeriv_smul_le_amplitude_grades
      (hβ.comp (contDiff_snd.fst.const_smul ρ)) (hF.comp P.contDiff)
      hG (show 0 ≤ (1 : ℝ) by norm_num) 0 0 v
      (by simpa only [Function.comp_def, one_pow, mul_one] using hgb v hv)
      (S := 1) (by simpa only [one_pow, mul_one, one_mul] using hfb v) m
    simp only [one_pow, mul_one, one_mul] at hh
    exact hh.trans ((le_add_of_nonneg_right (hB m)).trans
      (le_mul_of_one_le_right (hD m) (one_le_pow₀ hL)))
  have hphysical (ξ : E) (z : E × E) m :
      ‖iteratedFDeriv ℝ m (fun w : E × E ↦ β (ρ • ξ) • F w) z‖ ≤ D m * L ^ m := by
    rw [iteratedFDeriv_const_smul_apply' (hF.contDiffAt.of_le (by simp)), norm_smul]
    have hβb : ‖β (ρ • ξ)‖ ≤ 1 := by
      have hh := (ellipticSourceMask_properties f hK threshold).2 (ρ • ξ)
      simpa only [β, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hh.1] using hh.2
    apply (mul_le_mul hβb (hb m m le_rfl z) (norm_nonneg _) zero_le_one).trans
    rw [one_mul]
    exact (le_add_of_nonneg_left (derivativeConvolution_nonneg hG hB m)).trans
      (le_mul_of_one_le_right (hD m) (one_le_pow₀ hL))
  have he y z ξ : orientedMaskedPDOAmplitude false χout (χs)
      (ellipticSourceSymbol f hK threshold) y z ξ = β ξ • F (y, z) := by
    simp only [orientedMaskedPDOAmplitude, Bool.false_eq_true, ↓reduceIte, ellipticSourceSymbol]
    exact smul_comm _ _ _
  cases backward
  · exact ⟨by simpa only [A, he] using hjoint, by simpa only [A, he] using hphysical⟩
  · have he' y z ξ : orientedMaskedPDOAmplitude true χout (χs)
        (ellipticSourceSymbol f hK threshold) y z ξ = (β ξ • F (y, z)).conjTranspose :=
      congrArg Matrix.conjTranspose (he y z ξ)
    constructor
    · simpa only [A, he', norm_iteratedFDeriv_transport_conjTranspose] using hjoint
    · simpa only [A, he', norm_iteratedFDeriv_transport_conjTranspose] using hphysical

open PhysicalShells PhysicalShells.Comparable PhysicalShells.Noncomparable
open KernelEstimates.NoncomparableGeometry

/-- Apply the source producer on the exact comparable carrier and every
noncomparable shell used by the diagonal leakage estimate. Both orientations
retain degree zero, the original physical supports, and zero offset
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_ellipticSource_masked_diagonal_grades
    (χout : E → ℂ) (hout : ContDiff ℝ ∞ χout) (hcout : HasCompactSupport χout)
    (threshold : ℝ) (ht : 1 ≤ threshold) {a b : ℝ} (ha : 0 < a) :
    let Kb := tsupport χout ×ˢ tsupport (χs)
    let Kpdo := comparableJointCarrier 1 1 a b
      ((Prod.fst '' Kb) ×ˢ frequencyAnnulus
        (a / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b)))
      Kb (frequencyAnnulus a b)
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ → ∀ backward,
      let A := orientedMaskedPDOAmplitude backward χout (χs) (ellipticSourceSymbol f hK threshold)
      (∀ v ∈ Kpdo, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
          ρ ^ (0 : ℝ) * D m * L ^ (m+0)) ∧
      (∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j, ∀ z ∈ Kb, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (branchRadius low j)) ^ (0 : ℝ) * D m * L ^ (m+0)) := by
  intro Kb Kpdo
  have hKb : IsCompact Kb := hcout.prod (f.inputMask_compact.comp_left Complex.ofReal_zero)
  have hKpdo : IsCompact Kpdo := isCompact_comparableJointCarrier 1 1 a b
    ((hKb.image continuous_fst).prod (isCompact_frequencyAnnulus _ _)) hKb
    (isCompact_frequencyAnnulus _ _)
  have hzero : ∀ v ∈ Kpdo, v.2.1 ≠ 0 := by
    intro v hv hz
    have hn := hv.1.2.1.1
    change a / (16 * annulusFactor 1 1) ≤ ‖v.2.1‖ at hn
    rw [hz, norm_zero] at hn
    have hf := two_le_annulusFactor 1 1
    have hp : 0 < a / (16 * annulusFactor 1 1) := div_pos ha (by linarith)
    linarith
  obtain ⟨D, hD, hb⟩ := exists_ellipticSource_masked_symbol_grades f hK χout hout hcout threshold ht Kpdo hKpdo hzero
  refine ⟨D, hD, ?_⟩
  intro L ρ hL hρ backward A
  obtain ⟨hj, hp⟩ := hb L ρ hL hρ backward
  refine ⟨?_, ?_⟩
  · simpa only [Real.rpow_zero, one_mul, Nat.add_zero] using hj
  · intro low j ξ _ z _ m
    simpa only [Real.rpow_zero, one_mul, Nat.add_zero] using hp ξ z m

/-- The literal elliptic source supplies joint normalized and global spatial
grades, with degree zero and zero slow-scale offset in both orientations.
Only the actual fixed compact carrier excluding zero is supplied; neither
symbol derivatives nor operator estimates are hypotheses
(`app:ch_regular_base:eq:sector-theorem-identity`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_ellipticSource_symbol_grades
    (threshold : ℝ) (ht : 1 ≤ threshold)
    (J : Set V) (hJ : IsCompact J) (hzero : ∀ v ∈ J, v.2.1 ≠ 0) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ → ∀ backward,
      let A := orientedMaskedPDOAmplitude backward (χo) (χs) (ellipticSourceSymbol f hK threshold)
      (∀ v ∈ J, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤ D m * L ^ m) ∧
      (∀ ξ (z : E × E) m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤ D m * L ^ m) := by
  exact exists_ellipticSource_masked_symbol_grades f hK (χo)
    (Complex.ofRealCLM.contDiff.comp f.outputMask_smooth)
    (f.outputMask_compact.comp_left Complex.ofReal_zero) threshold ht J hJ hzero

/-- Apply the source producer on the exact comparable carrier and every
noncomparable shell used by the diagonal leakage estimate. Both orientations
retain degree zero, the original physical supports, and zero offset
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_ellipticSource_diagonal_grades
    (threshold : ℝ) (ht : 1 ≤ threshold) {a b : ℝ} (ha : 0 < a) :
    let Kb := tsupport (χo) ×ˢ tsupport (χs)
    let Kpdo := comparableJointCarrier 1 1 a b
      ((Prod.fst '' Kb) ×ˢ frequencyAnnulus
        (a / (16 * annulusFactor 1 1)) (4 * max 1 (4 * annulusFactor 1 1 * b)))
      Kb (frequencyAnnulus a b)
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧
      ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ → ∀ backward,
      let A := orientedMaskedPDOAmplitude backward (χo) (χs) (ellipticSourceSymbol f hK threshold)
      (∀ v ∈ Kpdo, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) v‖ ≤
          ρ ^ (0 : ℝ) * D m * L ^ (m+0)) ∧
      (∀ low j, ∀ ξ ∈ normalizedGraphCarrier ρ low j, ∀ z ∈ Kb, ∀ m,
        ‖iteratedFDeriv ℝ m (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (branchRadius low j)) ^ (0 : ℝ) * D m * L ^ (m+0)) := by
  exact exists_ellipticSource_masked_diagonal_grades f hK (χo)
    (Complex.ofRealCLM.contDiff.comp f.outputMask_smooth)
    (f.outputMask_compact.comp_left Complex.ofReal_zero) threshold ht (b := b) ha

end JanetCartan.RegularSector.EllipticLocalization
