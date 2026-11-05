module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Comparable.SupportedCarrier

/-!
# Comparable leakage with a fixed profile for the varying proof masks

The quantitative selected-family PDO deduction needs its constants before the
coefficient-dependent even masks. These variants reuse the existing buffered
integration-by-parts estimate with the supplied common mask profile.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Graph.PhysicalShells FiniteChain.Graph.PhysicalShells.Comparable
open FiniteChain.Graph.PhysicalShells.Noncomparable
open KernelEstimates.NoncomparableGeometry JanetCartan.Localization FiniteChain.Retarded.HalfSpace
variable {n r : ℕ}
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 256

/-- The common joint mask profile determines the comparable constants before
choosing the input and output masks. This is the buffered kernel input for the
uniform selected PDO leakage deduction (`app:ch_regular:eq:chain-tail`). -/
theorem exists_buffered_comparable_constants_of_uniform_masks
    {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (backward : Bool) (s : ℝ) (m : ℕ)
    (D : AmplitudeProfiles) {K : Set (JointVariables (Euclidean n))} (hK : IsCompact K)
    {a b δ G : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) (P O : ℕ → ℝ) (hO : ∀ j, 0 ≤ O j) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ (mi mo : LocalizerSymbol n) {I Ko Oo : Set (Euclidean n × Euclidean n)}
      , tsupport mi ⊆ I → IsBufferedLocalizer mo Ko Oo →
      (∀ j p, ‖iteratedFDeriv ℝ j mo p‖ ≤ O j) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ (φ : Euclidean n → Euclidean n → ℝ)
        (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
        (Dφ : Set (Euclidean n × Euclidean n)),
      (if backward then ReverseChartControl φ κ I Dφ a b
        else ForwardChartControl φ κ I Dφ a b) →
      (∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1-mo q), δ ≤ dist (κ q) q') →
      ∀ (A : FullAmplitude n r) (χA χo : Euclidean n → ℝ) (x y : Euclidean n),
      HasAmplitudeGrades D ρ (ρ ^ s) L A mi (fun _ => 0) χA χo 0 y K →
      ContDiff ℝ ∞ (jointPhase backward φ 0 y) →
      tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) ⊆ K →
      (∀ p ∈ tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y),
        (p.1.1, p.2.1) ∈ Dφ) →
      (∀ p ∈ K, ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ G) →
      (∀ p ∈ K, ∀ j, 1 ≤ j →
        ‖iteratedFDeriv ℝ (j + 1) (jointPhase backward φ x y) p‖ ≤ P j * L ^ j) →
      ∀ (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m
          (fun t => regularizedJointKernel backward ρ φ A mi mo χA χo t y) x v‖ ≤
        C q * ρ ^ ((m : ℝ) + (s + (3 * n : ℕ))) *
          L ^ (m + D.offset) * (L / ρ) ^ q := by
  obtain ⟨W, hW, hw⟩ := exists_outputJointWave_profile_on_jointCarrier hK
  let C := fun q => jointNormalization n *
    decayConstant e (bufferedPhaseGap e δ a b) (G + 1) P (D.outputJetProfile W O m) q *
      (jointMeasure n).real K
  refine ⟨C, fun q => mul_nonneg (mul_nonneg (jointNormalization_nonneg n)
    (decayConstant_nonneg e _ _ P _ (D.outputJetProfile_nonneg hW hO m) q))
      measureReal_nonneg, ?_⟩
  intro mi mo I Ko Oo hi ho hmoJoint ρ L hL hLρ φ κ Dφ H hbuffer A χA χo x y hgrades hφ hsK hDφ hupper hp q v hv
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hm : ∀ p ∈ K, ∀ j, ‖iteratedFDeriv ℝ j (fun t : Euclidean n × Euclidean n =>
      (mo (x + ρ⁻¹ • t.1, t.2) : ℂ)) (0, p.2.2.2)‖ ≤ O j * L ^ (j + 0) := by
    intro p _ j
    exact ((norm_iteratedFDeriv_rescaled_graphMask_le ho.smooth hρ x j
      (0, p.2.2.2)).trans (hmoJoint j _)).trans
      (le_mul_of_one_le_right (hO j) (one_le_pow₀ hL))
  simpa only [C, Nat.add_zero] using
    norm_iteratedFDeriv_regularizedJointKernel_le_of_buffer e backward
      (zero_lt_one.trans_le hρ) hL s φ κ ha hb hδ H x y hi ho.smooth hbuffer hgrades hφ
      hK hsK hDφ hupper P hp hW hO 0 m q v hv hw hm

/-- Local conic phase extension preserves the uniform mask constants and the
literal output jets. Consumer: the supported comparable pair estimate for the
selected PDO factors (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem exists_localPhase_comparable_constants_of_uniform_masks
    {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (backward : Bool) (s : ℝ) (m : ℕ)
    (X Y : Set (Euclidean n))
    (D : AmplitudeProfiles) {K : Set (JointVariables (Euclidean n))} (hK : IsCompact K)
    {a b δ G : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) (P O : ℕ → ℝ) (hO : ∀ j, 0 ≤ O j) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ (mi mo : LocalizerSymbol n) {I Ko Oo : Set (Euclidean n × Euclidean n)}
      , tsupport mi ⊆ I → IsBufferedLocalizer mo Ko Oo →
      (∀ y ∉ Y, ∀ η, mi (y, η) = 0) →
      (∀ j p, ‖iteratedFDeriv ℝ j mo p‖ ≤ O j) →
      ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ →
      ∀ (φ : Euclidean n → Euclidean n → ℝ)
        (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
        (Dφ U T : Set (Euclidean n × Euclidean n)),
      IsOpen U → IsCompact T → T ⊆ U →
      ContDiffOn ℝ ∞ (Function.uncurry φ) U → Dφ ⊆ T →
      (∀ p ∈ K, (p.1.1, p.2.1) ∈ Dφ) →
      (if backward then
        (∀ q ∈ I, (q.1, (κ q).2) ∈ T) ∧
          (∀ q ∈ I, ∀ p ∈ Dφ, (q.1, p.2) ∈ T)
        else (∀ q ∈ I, ((κ q).1, q.2) ∈ T) ∧
          (∀ q ∈ I, ∀ p ∈ Dφ, (p.1, q.2) ∈ T)) →
      (if backward then ReverseChartControl φ κ I Dφ a b
        else ForwardChartControl φ κ I Dφ a b) →
      (∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1-mo q),
        δ ≤ dist (κ q) q') →
      ∀ (A : FullAmplitude n r) (χA χo : Euclidean n → ℝ),
      (∀ u z ξ, A u z (ρ • ξ) ≠ 0 → χA (ρ • ξ) ≠ 0 → (u, ξ) ∈ T) →
      (∀ y ∈ Y, HasAmplitudeGrades D ρ (ρ ^ s) L A mi (fun _ => 0) χA χo 0 y K) →
      (∀ y ∈ Y, tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) ⊆ K) →
      (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ K,
        ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ G) →
      (∀ x ∈ X, ∀ y ∈ Y, ∀ p ∈ K, ∀ j, 1 ≤ j →
        ‖iteratedFDeriv ℝ (j + 1) (jointPhase backward φ x y) p‖ ≤ P j * L ^ j) →
      ∀ x ∈ X, ∀ y (q : ℕ) (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m
          (fun t => regularizedJointKernel backward ρ φ A mi mo χA χo t y) x v‖ ≤
        C q * ρ ^ ((m : ℝ) + (s + (3 * n : ℕ))) *
          L ^ (m + D.offset) * (L / ρ) ^ q := by
  obtain ⟨C, hC, hbound⟩ := exists_buffered_comparable_constants_of_uniform_masks
    (r := r) (G := G) e backward s m D hK ha hb hδ P O hO
  refine ⟨C, hC, ?_⟩
  intro mi mo I Ko Oo hi ho hiy hmoJoint ρ L hL hLρ φ κ Dφ U T hU hT hTU hφ hDT hproj hpoints H hbuffer
    A χA χo hcarrier hgrades hsK hupper hp x hx y q v hv
  have hρ : 0 < ρ := zero_lt_one.trans_le (hL.trans hLρ)
  by_cases hy : y ∈ Y
  · obtain ⟨ψ, hψ, heq, _, hkernel⟩ :=
      exists_normalizedPhaseExtension φ A χA ρ hU hT hTU hφ hcarrier
    have Hψ : if backward then ReverseChartControl ψ κ I Dφ a b
        else ForwardChartControl ψ κ I Dφ a b := by
      cases backward
      · exact forwardChartControl_congr_phase H heq hDT hpoints.1 hpoints.2
      · exact reverseChartControl_congr_phase H heq hDT hpoints.1 hpoints.2
    have hj p (hp' : p ∈ K) :=
      jointPhase_eventuallyEq_of_phase backward x y p (heq _ (hDT (hproj p hp')))
    have hk : (fun t => regularizedJointKernel backward ρ φ A mi mo χA χo t y) =
        fun t => regularizedJointKernel backward ρ ψ A mi mo χA χo t y :=
      funext fun t => hkernel backward mi mo χo t y
    rw [hk]
    apply hbound mi mo hi ho hmoJoint ρ L hL hLρ ψ κ Dφ Hψ hbuffer A χA χo x y (hgrades y hy)
      (contDiff_jointPhase_of_contDiff_phase backward ψ hψ 0 y) (hsK y hy)
      (fun p hp' => hproj p (hsK y hy hp'))
    · intro p hp'
      rw [(hj p hp').fderiv_eq]
      exact hupper x hx y hy p hp'
    · intro p hp' j hj'
      rw [((hj p hp').iteratedFDeriv ℝ (j + 1)).eq_of_nhds]
      exact hp x hx y hy p hp' j hj'
    · exact hv
  · have hz : (fun t => regularizedJointKernel backward ρ φ A mi mo χA χo t y) =
        fun _ => 0 := funext fun t =>
      normalizedJointKernel_eq_zero_of_input_zero backward ρ φ A mi mo χA χo t y (hiy y hy)
    rw [hz]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, zero_apply, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (hC q) (Real.rpow_pos_of_pos hρ _).le)
      (pow_nonneg (zero_le_one.trans hL) _)) (pow_nonneg (div_nonneg (zero_le_one.trans hL) hρ.le) _)

/-- The actual comparable graph/output cutoff pair has constants independent
of the varying even masks. All cutoff grades are instantiated; only the common
primitive symbol, phase and mask profiles remain as inputs. Consumer: the
uniform physical shell sum (`app:ch_regular:eq:chain-tail`). -/
theorem exists_supported_comparable_pair_constants_of_uniform_masks
    {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (backward : Bool) (s : ℝ) (m : ℕ) (c C a b : ℝ) (ha : 0 < a)
    (X : Set (Euclidean n))
    {Z Kb : Set (Euclidean n × Euclidean n)} {Ki Kη : Set (Euclidean n)}
    (hZ : IsCompact Z) (hKb : IsCompact Kb) (hKi : IsCompact Ki) (hKη : IsCompact Kη)
    (D : AmplitudeProfiles) {aChart bChart δ G : ℝ}
    (haChart : 0 ≤ aChart) (hbChart : 0 ≤ bChart) (hδ : 0 < δ) (P O : ℕ → ℝ) (hO : ∀ j, 0 ≤ O j) :
    let H := (8 * annulusFactor c C) / a
    let D' := comparableAmplitudeProfiles (n := n) D H
      (by have := two_le_annulusFactor c C; positivity)
    let K := comparableJointCarrier c C a b Z Kb Kη
    ∃ (B : ℕ → ℝ) (B₀ : ℝ), (∀ q, 0 ≤ B q) ∧ 0 ≤ B₀ ∧
    ∀ (mi mo : LocalizerSymbol n) {I Ko Oo : Set (Euclidean n × Euclidean n)},
    tsupport mi ⊆ I → ContDiff ℝ ∞ mi → IsBufferedLocalizer mo Ko Oo →
    tsupport mi ⊆ Ki ×ˢ Kη → (∀ j p, ‖iteratedFDeriv ℝ j mo p‖ ≤ O j) →
    ∀ (ρ L : ℝ), 1 ≤ L → L ≤ ρ → ∀ (low : Bool) (j k : ℕ),
    IsComparablePair c C a b ρ low j k →
    ∀ (S φ : Euclidean n → Euclidean n → ℝ)
      (κ : (Euclidean n × Euclidean n) → Euclidean n × Euclidean n)
      (U T : Set (Euclidean n × Euclidean n)),
    (∀ u ξ, S u (ρ • ξ) = ρ * φ u ξ) → Continuous (Function.uncurry S) →
    IsOpen U → IsCompact T → T ⊆ U → ContDiffOn ℝ ∞ (Function.uncurry φ) U → Z ⊆ T →
    (if backward then
      (∀ q ∈ I, (q.1, (κ q).2) ∈ T) ∧ (∀ q ∈ I, ∀ p ∈ Z, (q.1, p.2) ∈ T)
      else (∀ q ∈ I, ((κ q).1, q.2) ∈ T) ∧ (∀ q ∈ I, ∀ p ∈ Z, (p.1, q.2) ∈ T)) →
    (if backward then ReverseChartControl φ κ I Z aChart bChart
      else ForwardChartControl φ κ I Z aChart bChart) →
    (∀ q ∈ tsupport mi, ∀ q' ∈ tsupport (fun q => 1 - mo q), δ ≤ dist (κ q) q') →
    ∀ A : FullAmplitude n r,
    ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n => A p.1.1 p.1.2 p.2) →
    (∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0) →
    (∀ u z ξ, A u z (ρ • ξ) ≠ 0 → graphBranchCutoff low j (ρ • ξ) ≠ 0 → (u, ξ) ∈ Z) →
    (∀ l p, p ∈ K → ‖iteratedFDeriv ℝ l (fun p : JointVariables (Euclidean n) =>
      A p.1.1 p.1.2 (ρ • p.2.1)) p‖ ≤ ρ ^ s * D.symbol l * L ^ (l + D.symbolOffset)) →
    (∀ y ∈ Ki, ∀ l p, p ∈ K → ‖iteratedFDeriv ℝ l (fun p : JointVariables (Euclidean n) =>
      (mi (y, p.2.2.1) : ℂ)) p‖ ≤ D.inputMask l * L ^ (l + D.inputMaskOffset)) →
    (∀ x ∈ X, ∀ y ∈ Ki, ∀ p ∈ K, ‖fderiv ℝ (jointPhase backward φ x y) p‖ ≤ G) →
    (∀ x ∈ X, ∀ y ∈ Ki, ∀ p ∈ K, ∀ l, 1 ≤ l →
      ‖iteratedFDeriv ℝ (l + 1) (jointPhase backward φ x y) p‖ ≤ P l * L ^ l) →
    (∀ x ∈ X, ∀ y q (v : Fin m → Euclidean n), (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ m (fun t => KernelLimits.regularizedJointKernel backward S A
          (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
          (graphBranchCutoff low j) (outputCutoff k) t y) x v‖ ≤
        B q * ρ ^ ((m : ℝ) + (s + (3 * n : ℕ))) * L ^ (m + D'.offset) * (L / ρ) ^ q) ∧
    (∀ x y, ‖KernelLimits.regularizedJointKernel backward S A
        (fun p => mi (p.1, ρ⁻¹ • p.2)) (fun p => mo (p.1, ρ⁻¹ • p.2))
        (graphBranchCutoff low j) (outputCutoff k) x y‖ ≤
      B₀ * ρ ^ (s + (3 * n : ℕ)) * L ^ D'.offset) := by
  intro H D' K
  have hK : IsCompact K := isCompact_comparableJointCarrier c C a b hZ hKb hKη
  obtain ⟨B, hB, hbound⟩ := exists_localPhase_comparable_constants_of_uniform_masks
    (r := r) (G := G) e backward s m X Ki D' hK haChart hbChart hδ P O hO
  let B₀ := jointNormalization n * (jointMeasure n).real K * D'.productProfile 0
  have hB₀ : 0 ≤ B₀ := mul_nonneg
    (mul_nonneg (jointNormalization_nonneg n) measureReal_nonneg) (D'.productProfile_nonneg 0)
  refine ⟨B, B₀, hB, hB₀, ?_⟩
  intro mi mo I Ko Oo hi hiSmooth ho hiSupport hmoJoint ρ L hL hLρ low j k hpair S φ κ U T hscale hS hU hT hTU hφ hZT
    hpoints hchart hgap A hA hbase hcarrier hsymbol hin hupper hp
  have hiy : ∀ y ∉ Ki, ∀ η, mi (y, η) = 0 := by
    intro y hy η
    exact image_eq_zero_of_notMem_tsupport (fun hh => hy (hiSupport hh).1)
  have hiη : ∀ y, tsupport (fun η => mi (y, η)) ⊆ Kη := by
    intro y
    apply closure_minimal _ hKη.isClosed
    intro η hη
    exact (hiSupport (subset_tsupport _ hη)).2
  have hρ : 1 ≤ ρ := hL.trans hLρ
  have hρ0 := zero_lt_one.trans_le hρ
  let carriers : KernelLimits.RegularizedCarriers A mi (graphBranchCutoff low j) (outputCutoff k) := {
    amplitudeBase := Kb
    inputBase := Ki
    inputFrequency := Kη
    compact_amplitudeBase := hKb
    compact_inputBase := hKi
    compact_inputFrequency := hKη
    compact_graphCutoff := hasCompactSupport_graphBranchCutoff low j
    compact_outputCutoff := hasCompactSupport_outputCutoff k
    amplitude_zero := hbase
    input_zero := fun y η h => image_eq_zero_of_notMem_tsupport (fun hh => h (hiSupport hh)) }
  have hgrades y (hy : y ∈ Ki) : HasAmplitudeGrades D' ρ (ρ ^ s) L A mi (fun _ => 0)
      (graphBranchCutoff low j) (outputCutoff k) 0 y K := by
    apply hasAmplitudeGrades_of_factor_bounds (D := D') (zero_le_one.trans hL) y hA hiSmooth
      (contDiff_graphBranchCutoff low j) (contDiff_outputCutoff k) hsymbol
    · intro l p _
      apply (norm_iteratedFDeriv_joint_graphCutoff_le ha hρ hpair l p).trans
      change comparableCutoffProfile n H l ≤ comparableCutoffProfile n H l * L ^ (l + 0)
      exact le_mul_of_one_le_right (D'.graphCutoff_nonneg l) (one_le_pow₀ hL)
    · intro l p _
      apply (norm_iteratedFDeriv_joint_outputCutoff_le ha hρ hpair l p).trans
      change comparableCutoffProfile n H l ≤ comparableCutoffProfile n H l * L ^ (l + 0)
      exact le_mul_of_one_le_right (D'.outputCutoff_nonneg l) (one_le_pow₀ hL)
    · exact hin y hy
  have hsK y : tsupport (jointAmplitude ρ A mi (fun _ => 0)
      (graphBranchCutoff low j) (outputCutoff k) 0 y) ⊆ K :=
    tsupport_jointAmplitude_subset_comparableJointCarrier hρ hpair A mi (fun _ => 0) 0 y
      hZ hKb hKη hbase (hiη y) hcarrier
  constructor
  · intro x hx y q v hv
    rw [iteratedFDeriv_physicalJointKernel_eq_normalized backward S φ A mi mo
      (graphBranchCutoff low j) (outputCutoff k) x y hρ0 hscale hS hA.continuous
      hiSmooth.continuous ho.smooth.continuous (contDiff_graphBranchCutoff low j).continuous
      (contDiff_outputCutoff k).continuous carriers]
    exact hbound mi mo hi ho hiy hmoJoint ρ L hL hLρ φ κ Z U T hU hT hTU hφ hZT (fun _ h => h.2)
      hpoints hchart hgap A _ _ (fun u z ξ hA hg => hZT (hcarrier u z ξ hA hg))
      hgrades (fun y _ => hsK y) hupper hp x hx y q v hv
  · intro x y
    rw [regularizedJointKernel_eq_normalized backward S φ A mi mo
      (graphBranchCutoff low j) (outputCutoff k) x y hρ0 hscale hS hA.continuous
      hiSmooth.continuous ho.smooth.continuous (contDiff_graphBranchCutoff low j).continuous
      (contDiff_outputCutoff k).continuous carriers]
    by_cases hy : y ∈ Ki
    · exact norm_normalizedJointKernel_le_crude backward hρ0 hL s φ A mi mo _ _ x y
        ho.range hK (hgrades y hy) (hsK y)
    · rw [normalizedJointKernel_eq_zero_of_input_zero backward ρ φ A mi mo _ _ x y (hiy y hy), norm_zero]
      exact mul_nonneg (mul_nonneg hB₀ (Real.rpow_pos_of_pos hρ0 _).le)
        (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.ArbitraryAccuracy.ResidualLocalization.UniformDiagonal
