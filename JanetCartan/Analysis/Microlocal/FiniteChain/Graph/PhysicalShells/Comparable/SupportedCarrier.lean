module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Profiles
public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Comparable.Grades

/-!
# Comparable estimates on the actual conic carrier

The common joint carrier is intersected with the phase carrier. Consequently
the phase need not be smooth at unused directions in a rectangular frequency
carrier. The actual cutoff profiles and normalized frequency supports are
discharged here; the remaining inputs are primitive full-symbol, input-mask,
phase and chart estimates (`app:ch_regular:eq:chain-tail`).
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Comparable
open FourierIntegral KernelEstimates Noncomparable
open KernelEstimates.NoncomparableGeometry
variable {n r : ℕ}
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 256

/-- The common comparable joint carrier uses only the actual compact phase
domain, even when the physical frequency regularizer is radial
(`app:ch_regular:eq:joint-kernel-phase`). -/
def comparableJointCarrier (c C a b : ℝ)
    (Z Kb : Set (Euclidean n × Euclidean n)) (Kη : Set (Euclidean n)) :
    Set (JointVariables (Euclidean n)) :=
  jointCarrier Kb
      (frequencyAnnulus (a / (16 * annulusFactor c C))
        (4 * max 1 (4 * annulusFactor c C * b))) Kη
      (Metric.closedBall 0 (2 * max 1 (4 * annulusFactor c C * b))) ∩
    (fun p => (p.1.1, p.2.1)) ⁻¹' Z

/-- The conic restriction of the common comparable carrier is compact
(`app:ch_regular:eq:chain-tail`). -/
theorem isCompact_comparableJointCarrier (c C a b : ℝ)
    {Z Kb : Set (Euclidean n × Euclidean n)} {Kη : Set (Euclidean n)}
    (hZ : IsCompact Z) (hKb : IsCompact Kb) (hKη : IsCompact Kη) :
    IsCompact (comparableJointCarrier c C a b Z Kb Kη) :=
  (isCompact_jointCarrier hKb (isCompact_frequencyAnnulus _ _) hKη
    (isCompact_closedBall _ _)).inter_right
      (hZ.isClosed.preimage (continuous_fst.fst.prodMk continuous_snd.fst))

/-- Replace just the frequency-cutoff profiles by their proved constants.
The symbol and input-mask profiles retain their primitive offsets; the
frequency cutoffs add no new fixed scale loss
(`app:ch_regular:eq:high-amplitude`). -/
def comparableAmplitudeProfiles (D : AmplitudeProfiles) (H : ℝ) (hH : 0 ≤ H) :
    AmplitudeProfiles :=
  { D with
    graphCutoff := comparableCutoffProfile n H
    outputCutoff := comparableCutoffProfile n H
    graphCutoff_nonneg := comparableCutoffProfile_nonneg hH
    outputCutoff_nonneg := comparableCutoffProfile_nonneg hH
    graphCutoffOffset := 0
    outputCutoffOffset := 0 }

/-- Primitive amplitude support in the phase carrier is enough to restrict
the joint amplitude there. No phase regularity is required at the unused
directions of the radial cutoff (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem tsupport_jointAmplitude_subset_comparableJointCarrier
    {c C a b ρ : ℝ} (hρ : 1 ≤ ρ) {low : Bool} {j k : ℕ}
    (hpair : IsComparablePair c C a b ρ low j k)
    (A : FullAmplitude n r) (mi mo : LocalizerSymbol n) (x y : Euclidean n)
    {Z Kb : Set (Euclidean n × Euclidean n)} {Kη : Set (Euclidean n)}
    (hZ : IsCompact Z) (hKb : IsCompact Kb) (hKη : IsCompact Kη)
    (hbase : ∀ u z ξ, (u, z) ∉ Kb → A u z ξ = 0)
    (hi : tsupport (fun η => mi (y, η)) ⊆ Kη)
    (hphase : ∀ u z ξ, A u z (ρ • ξ) ≠ 0 →
      graphBranchCutoff low j (ρ • ξ) ≠ 0 → (u, ξ) ∈ Z) :
    tsupport (jointAmplitude ρ A mi mo (graphBranchCutoff low j) (outputCutoff k) x y) ⊆
      comparableJointCarrier c C a b Z Kb Kη := by
  have hρ0 := zero_lt_one.trans_le hρ
  have hg := (tsupport_rescaled_graphBranchCutoff_subset (n := n) hρ0.ne' low j).trans
    (comparableGraphCarrier_subset hρ hpair)
  have ho := (tsupport_rescaled_outputCutoff_subset (n := n) hρ0.ne' k).trans
    (comparableOutputCarrier_subset hρ hpair)
  have hs := tsupport_jointAmplitude_subset ρ A mi mo (graphBranchCutoff low j) (outputCutoff k)
    x y hKb (isCompact_frequencyAnnulus _ _) hKη (isCompact_closedBall _ _)
      hbase hg hi ho
  apply closure_minimal _ (isCompact_comparableJointCarrier c C a b hZ hKb hKη).isClosed
  intro p hp
  refine ⟨hs (subset_tsupport _ hp), ?_⟩
  apply hphase p.1.1 p.1.2 p.2.1
  · intro hz
    exact hp (by simp [jointAmplitude, hz])
  · intro hz
    exact hp (by simp [jointAmplitude, hz])

/-- Comparable physical output jets, with the cutoff profiles and support
premises instantiated for the actual independent pair. The phase is smooth
on its original open conic domain and is extended only through agreement
near `Z` and the chart's mixed points. Constants precede the varying scales,
phases, full symbols and pair indices. The accompanying zeroth estimate is
uniform in both external bases (`app:ch_regular:eq:chain-tail`). -/
theorem exists_supported_comparable_pair_constants
    {ι : Type*} [Fintype ι] (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (backward : Bool) (s : ℝ) (m : ℕ) (c C a b : ℝ) (ha : 0 < a)
    {mi mo : LocalizerSymbol n} {I Ko Oo : Set (Euclidean n × Euclidean n)}
    (hi : tsupport mi ⊆ I) (hiSmooth : ContDiff ℝ ∞ mi)
    (ho : IsBufferedLocalizer mo Ko Oo) (X : Set (Euclidean n))
    {Z Kb : Set (Euclidean n × Euclidean n)} {Ki Kη : Set (Euclidean n)}
    (hZ : IsCompact Z) (hKb : IsCompact Kb) (hKi : IsCompact Ki) (hKη : IsCompact Kη)
    (hiSupport : tsupport mi ⊆ Ki ×ˢ Kη)
    (D : AmplitudeProfiles) {aChart bChart δ G : ℝ}
    (haChart : 0 ≤ aChart) (hbChart : 0 ≤ bChart) (hδ : 0 < δ) (P : ℕ → ℝ) :
    let H := (8 * annulusFactor c C) / a
    let D' := comparableAmplitudeProfiles (n := n) D H
      (by have := two_le_annulusFactor c C; positivity)
    let K := comparableJointCarrier c C a b Z Kb Kη
    ∃ (B : ℕ → ℝ) (B₀ : ℝ), (∀ q, 0 ≤ B q) ∧ 0 ≤ B₀ ∧
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
  have hiy : ∀ y ∉ Ki, ∀ η, mi (y, η) = 0 := by
    intro y hy η
    exact image_eq_zero_of_notMem_tsupport (fun hh => hy (hiSupport hh).1)
  have hiη : ∀ y, tsupport (fun η => mi (y, η)) ⊆ Kη := by
    intro y
    apply closure_minimal _ hKη.isClosed
    intro η hη
    exact (hiSupport (subset_tsupport _ hη)).2
  obtain ⟨B, hB, hbound⟩ := exists_localPhase_comparable_constants
    (r := r) (G := G) e backward s m hi ho X Ki hiy D' hK haChart hbChart hδ P
  let B₀ := jointNormalization n * (jointMeasure n).real K * D'.productProfile 0
  have hB₀ : 0 ≤ B₀ := mul_nonneg
    (mul_nonneg (jointNormalization_nonneg n) measureReal_nonneg) (D'.productProfile_nonneg 0)
  refine ⟨B, B₀, hB, hB₀, ?_⟩
  intro ρ L hL hLρ low j k hpair S φ κ U T hscale hS hU hT hTU hφ hZT
    hpoints hchart hgap A hA hbase hcarrier hsymbol hin hupper hp
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
    exact hbound ρ L hL hLρ φ κ Z U T hU hT hTU hφ hZT (fun _ h => h.2)
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

end JanetCartan.FiniteChain.Graph.PhysicalShells.Comparable
