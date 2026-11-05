module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredGraphRealizations
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionLocalization.PrimitiveGrades.Coordinates

/-!
# Measurement profiles for the actual full PDO amplitudes

Fixed smooth measurement cutoffs contribute only a Leibniz profile. Symbol
orders and every slow-scale offset are retained in both literal orientations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Retarded.KernelDecay EvolutionLocalization.PrimitiveGrades
open ResidualLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => Matrix (Fin q) (Fin q) ℂ
local notation "V" => JointVariables E

/-- The two fixed measurement cutoffs give a compact two-position carrier
for the joint jet bounds (`app:ch_regular:eq:high-amplitude`). -/
private theorem measurement_product_compact
    (μ ν : E → ℝ) (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν) :
    HasCompactSupport (fun z : E × E ↦ (μ z.1 : ℂ)*(ν z.2 : ℂ)) := by
  apply (hμc.isCompact.prod hνc.isCompact).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ ((isClosed_tsupport μ).prod (isClosed_tsupport ν))
  intro z hz
  constructor
  · apply subset_tsupport
    intro h
    exact hz (by simp [h])
  · apply subset_tsupport
    intro h
    exact hz (by simp [h])

/-- The original measurement pair has a uniform joint derivative profile
in every orthonormal physical chart, before any coefficients or source scale.
Consumer: measured full-amplitude grades for the selected residual letters
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular_base:eq:measured-adjoint`). -/
theorem exists_measurement_pair_joint_profile
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν) :
    ∃ D : ℕ → ℝ, (∀ k, 0 ≤ D k) ∧
      ∀ e : E ≃ₗᵢ[ℝ] E,
      (∀ (k : ℕ) (z : E × E), ‖iteratedFDeriv ℝ k
        (fun w : E × E ↦ (μ (e w.1) : ℂ)*(ν (e w.2) : ℂ)) z‖ ≤ D k) ∧
      (∀ (k : ℕ) (v : V), ‖iteratedFDeriv ℝ k
        (fun w : V ↦ (μ (e w.1.1) : ℂ)*(ν (e w.1.2) : ℂ)) v‖ ≤ D k) ∧
      (∀ (k : ℕ) (v : ℝ × V), ‖iteratedFDeriv ℝ k
        (fun w : ℝ × V ↦ (μ (e w.2.1.1) : ℂ)*(ν (e w.2.1.2) : ℂ)) v‖ ≤ D k) := by
  let m : E × E → ℂ := fun z ↦ (μ z.1 : ℂ)*(ν z.2 : ℂ)
  have hm : ContDiff ℝ ∞ m :=
    (Complex.ofRealCLM.contDiff.comp (hμ.comp contDiff_fst)).mul
      (Complex.ofRealCLM.contDiff.comp (hν.comp contDiff_snd))
  choose D hD hbound using fun k ↦ (measurement_product_compact μ ν hμc hνc).exists_bound_iteratedFDeriv hm k
  refine ⟨D, hD, ?_⟩
  intro e
  let ec : E →L[ℝ] E := e.toContinuousLinearEquiv.toContinuousLinearMap
  let ep : E × E →L[ℝ] E × E := ec.prodMap ec
  have hep : ‖ep‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro z
    simp [ep, ec, Prod.norm_def]
  have hp (k : ℕ) (z : E × E) : ‖iteratedFDeriv ℝ k (fun w ↦ m (ep w)) z‖ ≤ D k := by
    have h := norm_iteratedFDeriv_affine_contraction_le ep hep 0
      isOpen_univ hm.contDiffOn (mem_univ (ep z+0)) k
    simp only [add_zero] at h
    exact h.trans (hbound k k le_rfl (ep z))
  have hmp : ContDiff ℝ ∞ (fun w ↦ m (ep w)) := hm.comp ep.contDiff
  let pj : V →L[ℝ] E × E := ContinuousLinearMap.fst ℝ _ _
  have hpj : ‖pj‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (by intro z; simpa [pj] using norm_fst_le z)
  have hj (k : ℕ) (z : V) : ‖iteratedFDeriv ℝ k (fun w ↦ m (ep (pj w))) z‖ ≤ D k := by
    have h := norm_iteratedFDeriv_affine_contraction_le pj hpj 0
      isOpen_univ hmp.contDiffOn (mem_univ (pj z+0)) k
    simp only [add_zero] at h
    exact h.trans (hp k (pj z))
  let pe : (ℝ × V) →L[ℝ] V := ContinuousLinearMap.snd ℝ _ _
  have hpe : ‖pe‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (by intro z; simpa [pe] using norm_snd_le z)
  refine ⟨hp, hj, ?_⟩
  intro k z
  have h := norm_iteratedFDeriv_affine_contraction_le pe hpe 0
    isOpen_univ (hmp.comp pj.contDiff).contDiffOn (mem_univ (pe z+0)) k
  simp only [add_zero] at h
  exact h.trans (hj k (pe z))

/-- Both original real measurement masks multiply the full oriented PDO
amplitude, including its literal matrix adjoint. Consumer: the measured
comparable and shell grades (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem measured_orientedPDOAmplitude_eq
    (μ ν : E → ℝ) (e : E ≃ₗᵢ[ℝ] E) (χout χsource : E → ℂ)
    (c : E → E → Mat) (backward : Bool) (x y ξ : E) :
    orientedMaskedPDOAmplitude backward
        (fun z ↦ (μ (e z) : ℂ)*χout z) (fun z ↦ (ν (e z) : ℂ)*χsource z) c x y ξ =
      ((μ (e x) : ℂ)*(ν (e y) : ℂ)) •
        orientedMaskedPDOAmplitude backward χout χsource c x y ξ := by
  cases backward
  · simp only [orientedMaskedPDOAmplitude, Bool.false_eq_true, ite_false, smul_smul]
    congr 1
    ring
  · simp only [orientedMaskedPDOAmplitude, ite_true, Matrix.conjTranspose_smul,
      map_mul, Complex.star_def, Complex.conj_ofReal, smul_smul]
    congr 1
    ring

/-- Apply the fixed measurement cutoffs to the existing full PDO symbol
profile, preserving its order and all offsets. Both comparable full-frequency
jets and physical shell jets are proved for the literal measured amplitude.
Consumer: the selected measured PDO leakage deduction, using the actual
`exists_selected_threePDO_grades_of_joint_localizer_profile` output
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_measured_maskedPDO_symbol_profiles
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (D : AmplitudeProfiles) :
    ∃ Dm : AmplitudeProfiles,
      Dm.symbolOffset = D.symbolOffset ∧ Dm.inputMask = D.inputMask ∧
      Dm.outputMask = D.outputMask ∧ Dm.inputMaskOffset = D.inputMaskOffset ∧
      Dm.outputMaskOffset = D.outputMaskOffset ∧ Dm.offset = D.offset ∧
    ∀ (e : E ≃ₗᵢ[ℝ] E) (χout χsource : E → ℂ) (c : E → E → Mat) (backward : Bool),
    let A := orientedMaskedPDOAmplitude backward χout χsource c
    let Am := orientedMaskedPDOAmplitude backward
      (fun z ↦ (μ (e z) : ℂ)*χout z) (fun z ↦ (ν (e z) : ℂ)*χsource z) c
    ContDiff ℝ ∞ (fun p : (E × E) × E ↦ A p.1.1 p.1.2 p.2) →
    ∀ (ρ L s : ℝ), 1 ≤ L →
    ∀ (K : Set V) (Kb : Set (E × E)),
    (∀ k p, p ∈ K → ‖iteratedFDeriv ℝ k
      (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) p‖ ≤
        ρ ^ s * D.symbol k * L ^ (k+D.symbolOffset)) →
    (∀ low j, ∀ ξ ∈ PhysicalShells.normalizedGraphCarrier ρ low j,
      ∀ z ∈ Kb, ∀ k, ‖iteratedFDeriv ℝ k
        (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (PhysicalShells.Noncomparable.branchRadius low j)) ^ s * D.symbol k * L ^ (k+D.symbolOffset)) →
    (∀ k p, p ∈ K → ‖iteratedFDeriv ℝ k
      (fun w : V ↦ Am w.1.1 w.1.2 (ρ • w.2.1)) p‖ ≤
        ρ ^ s * Dm.symbol k * L ^ (k+Dm.symbolOffset)) ∧
    (∀ low j, ∀ ξ ∈ PhysicalShells.normalizedGraphCarrier ρ low j,
      ∀ z ∈ Kb, ∀ k, ‖iteratedFDeriv ℝ k
        (fun w : E × E ↦ Am w.1 w.2 (ρ • ξ)) z‖ ≤
          (max 1 (PhysicalShells.Noncomparable.branchRadius low j)) ^ s * Dm.symbol k * L ^ (k+Dm.symbolOffset)) := by
  obtain ⟨C, hC, hprofile⟩ := exists_measurement_pair_joint_profile μ ν hμ hν hμc hνc
  let Dm : AmplitudeProfiles := { D with
    symbol := derivativeConvolution C D.symbol
    symbol_nonneg := derivativeConvolution_nonneg hC D.symbol_nonneg }
  refine ⟨Dm, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro e χout χsource c backward A Am hA ρ L s hL K Kb hsymbol hbase
  have he : ∀ x y ξ, Am x y ξ = ((μ (e x) : ℂ)*(ν (e y) : ℂ)) • A x y ξ :=
    measured_orientedPDOAmplitude_eq μ ν e χout χsource c backward
  have hpair : ContDiff ℝ ∞ (fun z : E × E ↦ (μ (e z.1) : ℂ)*(ν (e z.2) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (hμ.comp (e.contDiff.comp contDiff_fst))).mul
      (Complex.ofRealCLM.contDiff.comp (hν.comp (e.contDiff.comp contDiff_snd)))
  constructor
  · intro k p hp
    have hAs : ContDiff ℝ ∞ (fun w : V ↦ A w.1.1 w.1.2 (ρ • w.2.1)) :=
      hA.comp (contDiff_fst.prodMk (contDiff_snd.fst.const_smul ρ))
    have hm (j : ℕ) : ‖iteratedFDeriv ℝ j
        (fun w : V ↦ (μ (e w.1.1) : ℂ)*(ν (e w.1.2) : ℂ)) p‖ ≤ C j * L ^ (j+0) :=
      ((hprofile e).2.1 j p).trans (le_mul_of_one_le_right (hC j) (one_le_pow₀ hL))
    have hh := norm_iteratedFDeriv_smul_le_amplitude_grades
      (hpair.comp contDiff_fst) hAs hC (zero_le_one.trans hL) 0 D.symbolOffset p hm
      (fun j ↦ hsymbol j p hp) k
    simpa only [he, Function.comp_apply, zero_add, Dm] using hh
  · intro low j ξ hξ z hz k
    have hAs : ContDiff ℝ ∞ (fun w : E × E ↦ A w.1 w.2 (ρ • ξ)) :=
      hA.comp (contDiff_id.prodMk contDiff_const)
    have hm (l : ℕ) : ‖iteratedFDeriv ℝ l
        (fun w : E × E ↦ (μ (e w.1) : ℂ)*(ν (e w.2) : ℂ)) z‖ ≤ C l * L ^ (l+0) :=
      ((hprofile e).1 l z).trans (le_mul_of_one_le_right (hC l) (one_le_pow₀ hL))
    have hh := norm_iteratedFDeriv_smul_le_amplitude_grades hpair hAs hC
      (zero_le_one.trans hL) 0 D.symbolOffset z hm (fun l ↦ hbase low j ξ hξ z hz l) k
    simpa only [he, Function.comp_apply, zero_add, Dm] using hh

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
