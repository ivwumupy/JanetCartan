module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Localizers
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Amplitudes
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades.Coordinates
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Comparable.SupportedCarrier

/-!
# Comparable amplitude grades from the selected elapsed symbol

The actual three physical masks and both literal orientations are retained.
This supplies the `hglobalGrades` deduction for `CompleteFactor`, conditional
on the normalized residual symbol profile. Its actual construction from the
retained order seminorms remains an explicit obligation of the parent.
Source: `app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteMasks RegularSector.FiniteMasks.ActualFamily
open RegularSector.FinitePdo RegularSector.FiniteAlgebraic
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open EvolutionLocalization EvolutionLocalization.PrimitiveGrades EvolutionIntegratedLocalization
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FourierIntegral.PrimitiveProfiles
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Comparable
open FiniteChain.Graph.PhysicalShells.Noncomparable
open FiniteChain.Graph.KernelEstimates.NoncomparableGeometry
open FiniteChain.Retarded.KernelDecay
variable {d q : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "V" => ℝ × JointVariables E

/-- Derive the comparable `HasAmplitudeGrades` input of
`ResidualLocalization.exists_completePhysicalResidual_restriction_bound`
from the normalized elapsed-symbol profile, preserving order minus one.
The actual masks have the literal doubled threshold. Their grades and the
physical graph/output cutoff grades are proved here, with zero offsets.

`hbudget` must be instantiated for the smooth direct residual from
`selected_common_smooth_direct_residual`, using the original retained
`exists_selected_amplitude_order_profile` and the radial dilation or
vanishing alternative in `exists_selected_direct_residual_carriers`.
This implication does not assert that that remaining transfer has been
constructed (`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_selected_elapsed_comparable_profiles
    (f : ActualMaskFamily Ω x RQ A₀ K M)
    (threshold : ℝ) (hthreshold : 1 ≤ threshold)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output)
    (hoc : HasCompactSupport output) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (Δ c C a₀ b₀ : ℝ) (ha₀ : 0 < a₀)
    (Kglobal : f.centers → Set (JointVariables E))
    (hK : ∀ p, IsCompact (Kglobal p))
    (hzero : ∀ p, ∀ v ∈ Kglobal p, v.2.1 ≠ 0)
    (mi mo : f.centers → LocalizerSymbol (d+1))
    (Ki Ii Ko Oo : f.centers → Set (E × E))
    (hi : ∀ p, IsBufferedLocalizer (mi p) (Ki p) (Ii p))
    (hmo : ∀ p, IsBufferedLocalizer (mo p) (Ko p) (Oo p))
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ D : AmplitudeProfiles,
      D.symbolOffset = 0 ∧ D.graphCutoffOffset = 0 ∧ D.outputCutoffOffset = 0 ∧
      D.inputMaskOffset = 0 ∧ D.outputMaskOffset = 0 ∧
      ∀ L ρ : ℝ, 1 ≤ L → 1 ≤ ρ →
      ∀ b : f.centers → TwoTimeAmplitude d q,
      (∀ p, ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude (b p))) →
      (∀ p, ∀ r ∈ Icc 0 Δ, ∀ v ∈ Kglobal p, ∀ j,
        ‖iteratedFDeriv ℝ j (normalizedElapsedSymbol ρ (b p)) (r, v)‖ ≤
          ρ ^ (-1 : ℝ) * B j * L ^ j) →
      ∀ p backward low j k, IsComparablePair c C a₀ b₀ ρ low j k →
      ∀ r ∈ Icc 0 Δ, ∀ y,
        HasAmplitudeGrades D ρ (ρ ^ (-1 : ℝ)) L
          (orientedElapsedAmplitude backward (b p) (endpointOutputMask f p output)
            (chartInputMask f p) (selectedEndpointMultiplier f p threshold) r)
          (mi p) (fun _ ↦ 0) (graphBranchCutoff low j) (outputCutoff k) 0 y (Kglobal p) := by
  let J := fun p ↦ Icc 0 Δ ×ˢ Kglobal p
  have hJ p : IsCompact (J p) := isCompact_Icc.prod (hK p)
  obtain ⟨Qt, Qs, Qg, hQt, hQs, hQg, hmasks⟩ :=
    exists_selected_elapsed_mask_profiles f threshold hthreshold output ho hoc hout J hJ
      (fun p v hv ↦ hzero p v.2 hv.2)
  obtain ⟨Qi, O, W, hQi, _, _, hiGrade, _, _, _⟩ :=
    exists_selected_elapsed_localizer_profiles f J hJ mi mo Ki Ii Ko Oo hi hmo
  let Bs := derivativeConvolution Qt (derivativeConvolution Qs (derivativeConvolution Qg B))
  have hBs : ∀ j, 0 ≤ Bs j := derivativeConvolution_nonneg hQt
    (derivativeConvolution_nonneg hQs (derivativeConvolution_nonneg hQg hB))
  let H := (8 * annulusFactor c C) / a₀
  have hH : 0 ≤ H := by have := two_le_annulusFactor c C; positivity
  let D : AmplitudeProfiles :=
    { symbol := Bs
      graphCutoff := comparableCutoffProfile (d+1) H
      outputCutoff := comparableCutoffProfile (d+1) H
      inputMask := Qi
      outputMask := fun _ ↦ 0
      symbol_nonneg := hBs
      graphCutoff_nonneg := comparableCutoffProfile_nonneg hH
      outputCutoff_nonneg := comparableCutoffProfile_nonneg hH
      inputMask_nonneg := hQi
      outputMask_nonneg := fun _ ↦ le_rfl
      symbolOffset := 0
      graphCutoffOffset := 0
      outputCutoffOffset := 0
      inputMaskOffset := 0
      outputMaskOffset := 0 }
  refine ⟨D, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro L ρ hL hρ b hb hbudget p backward low j k hpair r hr y
  let χt := endpointOutputMask f p output
  let χs := chartInputMask f p
  let β := selectedEndpointMultiplier f p threshold
  have ht : ContDiff ℝ ∞ χt := (endpointOutputMask_properties f p ho hoc hout).1
  have hs : ContDiff ℝ ∞ χs := (chartPhysicalMasks_properties f p).2.1
  have hg : ContDiff ℝ ∞ β := (selectedEndpointMultiplier_bounds f p threshold).1
  have hbn : ContDiff ℝ ∞ (normalizedElapsedSymbol ρ (b p)) := by
    have he : normalizedElapsedSymbol ρ (b p) =
        normalizedField ρ (SymbolBudgets.jointAmplitude (b p)) ∘ elapsedJointCoordinates := by
      funext w
      simp [normalizedElapsedSymbol, normalizedField, SymbolBudgets.jointAmplitude,
        elapsedJointCoordinates, spatialPart_smul]
    rw [he]
    exact ((hb p).comp (contDiff_fst.prodMk (contDiff_snd.const_smul ρ))).comp
      (elapsedJointCoordinates (d := d)).contDiff
  have hforward : ContDiff ℝ ∞ (fun v : V ↦
      elapsedAmplitude (b p) χt χs β v.1 v.2.1.1 v.2.1.2 (ρ • v.2.2.1)) :=
    (((ht.comp contDiff_snd.fst.fst).mul (hs.comp contDiff_snd.fst.snd)).mul
      (hg.comp (contDiff_snd.snd.fst.const_smul ρ))).smul hbn
  have hA : ContDiff ℝ ∞ (fun v : (E × E) × E ↦
      orientedElapsedAmplitude backward (b p) χt χs β r v.1.1 v.1.2 v.2) := by
    have hh := contDiff_uncurry_elapsedAmplitude (b p) χt χs β (hb p) ht hs hg r
    cases backward
    · exact hh
    · exact (Matrix.conjTransposeLinearEquiv (Fin q) (Fin q) ℝ ℂ).toContinuousLinearEquiv.contDiff.comp hh
  have hJoint : ContDiff ℝ ∞ (fun v : V ↦
      orientedElapsedAmplitude backward (b p) χt χs β v.1 v.2.1.1 v.2.1.2 (ρ • v.2.2.1)) := by
    cases backward
    · exact hforward
    · exact (Matrix.conjTransposeLinearEquiv (Fin q) (Fin q) ℝ ℂ).toContinuousLinearEquiv.contDiff.comp hforward
  have hinr : ‖ContinuousLinearMap.inr ℝ ℝ (JointVariables E)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro w; simp [Prod.norm_def])
  apply hasAmplitudeGrades_of_factor_bounds (D := D) (zero_le_one.trans hL) y hA
    (hi p).smooth (contDiff_graphBranchCutoff low j) (contDiff_outputCutoff k)
  · intro l v hv
    have hm m := hmasks L ρ hL hρ p (r, v) ⟨hr, hv⟩ m
    have hb' := norm_iteratedFDeriv_orientedElapsedAmplitude_le backward ρ (b p) χt χs β
      (ht.comp contDiff_snd.fst.fst) (hs.comp contDiff_snd.fst.snd)
      (hg.comp (contDiff_snd.snd.fst.const_smul ρ)) hbn hQt hQs hQg
      (zero_le_one.trans hL) 0 0 0 0 (r, v)
      (fun m ↦ by simpa using (hm m).1)
      (fun m ↦ by simpa using (hm m).2.1)
      (fun m ↦ by simpa using (hm m).2.2)
      (fun m ↦ by simpa using hbudget p r hr v hv m) l
    have hslice := norm_iteratedFDeriv_affine_contraction_le
      (ContinuousLinearMap.inr ℝ ℝ (JointVariables E))
      hinr (r, 0)
      isOpen_univ hJoint.contDiffOn (mem_univ _) l (p := v)
    simp only [ContinuousLinearMap.inr_apply, Prod.mk_add_mk, zero_add, add_zero] at hslice
    exact hslice.trans hb'
  · intro l v _
    apply (norm_iteratedFDeriv_joint_graphCutoff_le ha₀ hρ hpair l v).trans
    exact le_mul_of_one_le_right (D.graphCutoff_nonneg l) (one_le_pow₀ hL)
  · intro l v _
    apply (norm_iteratedFDeriv_joint_outputCutoff_le ha₀ hρ hpair l v).trans
    exact le_mul_of_one_le_right (D.outputCutoff_nonneg l) (one_le_pow₀ hL)
  · intro l v _
    have hg' : ContDiff ℝ ∞ (fun w : V ↦ (mi p (y, w.2.2.2.1) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ((hi p).smooth.comp
        (contDiff_const.prodMk contDiff_snd.snd.snd.fst))
    have hslice := norm_iteratedFDeriv_affine_contraction_le
      (ContinuousLinearMap.inr ℝ ℝ (JointVariables E))
      hinr (0 : V)
      isOpen_univ hg'.contDiffOn (mem_univ _) l (p := v)
    simp only [ContinuousLinearMap.inr_apply, add_zero] at hslice
    exact hslice.trans (hiGrade L hL p y (0, v) l)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
