module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Comparable.Phase

/-!
# Comparable estimates on the actual phase domain

These are the two analytic inputs for the physical cutoff-pair estimate:
arbitrary output jets on a fixed output carrier, and a crude zeroth estimate
on the whole output space. The only analytic premises are primitive grades,
compact carriers, and buffered chart geometry. In particular no decay outside
the output carrier is required for `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Comparable
open FourierIntegral KernelEstimates
variable {n r : ℕ}
set_option maxHeartbeats 800000

/-- The input shoulder gives exact vanishing outside its base carrier, for
both orientations and every output base (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem normalizedJointKernel_eq_zero_of_input_zero
    (backward : Bool) (ρ : ℝ) (φ : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (mi mo : LocalizerSymbol n)
    (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (hi : ∀ η, mi (y, η) = 0) :
    regularizedJointKernel backward ρ φ A mi mo χA χo x y = 0 := by
  simp [regularizedJointKernel, jointAmplitude, hi]

/-- Uniform comparable constants on a prescribed output carrier, with all
input bases allowed. The phase is smooth only on `U`; its compact extension
carrier includes every mixed point used by the chart control. Primitive joint
phase grades are unchanged by extension. The fixed losses are `s + 3*n` and
`m + D.offset`, also for negative `s` and the weighted reverse amplitude.
Consumer: the physical high/low cutoff pairs in `app:ch_regular:eq:chain-tail`.
-/
theorem exists_localPhase_comparable_constants
    {ι : Type*} [Fintype ι]
    (e : Module.Basis ι ℝ (JointVariables (Euclidean n)))
    (backward : Bool) (s : ℝ) (m : ℕ)
    {mi mo : LocalizerSymbol n} {I Ko Oo : Set (Euclidean n × Euclidean n)}
    (hi : tsupport mi ⊆ I) (ho : IsBufferedLocalizer mo Ko Oo)
    (X Y : Set (Euclidean n)) (hiy : ∀ y ∉ Y, ∀ η, mi (y, η) = 0)
    (D : AmplitudeProfiles) {K : Set (JointVariables (Euclidean n))} (hK : IsCompact K)
    {a b δ G : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) (P : ℕ → ℝ) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
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
  obtain ⟨C, hC, hbound⟩ := exists_buffered_comparable_kernel_constants
    (r := r) e backward s m hi ho D hK ha hb hδ P
  refine ⟨C, hC, ?_⟩
  intro ρ L hL hLρ φ κ Dφ U T hU hT hTU hφ hDT hproj hpoints H hbuffer
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
    apply hbound ρ L hL hLρ ψ κ Dφ Hψ hbuffer A χA χo x y (hgrades y hy)
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

/-- A globally uniform crude bound, independent of the external bases and of
all phase derivatives. The complementary mask has norm at most one. This is
the zeroth-kernel domination used outside the compact output carrier in
`app:ch_regular:eq:chain-tail`; it asserts no rapid decay there. -/
theorem norm_normalizedJointKernel_le_crude
    (backward : Bool) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 1 ≤ L) (s : ℝ)
    (φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ) (x y : Euclidean n)
    (hmo : ∀ p, mo p ∈ Icc (0 : ℝ) 1)
    {D : AmplitudeProfiles} {K : Set (JointVariables (Euclidean n))}
    (hK : IsCompact K)
    (hgrades : HasAmplitudeGrades D ρ (ρ ^ s) L A mi (fun _ => 0) χA χo 0 y K)
    (hsK : tsupport (jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y) ⊆ K) :
    ‖regularizedJointKernel backward ρ φ A mi mo χA χo x y‖ ≤
      (jointNormalization n * (jointMeasure n).real K * D.productProfile 0) *
        ρ ^ (s + (3 * n : ℕ)) * L ^ D.offset := by
  have he p : jointAmplitude ρ A mi mo χA χo x y p =
      ((1 - mo (x, p.2.2.2) : ℝ) : ℂ) •
        jointAmplitude ρ A mi (fun _ => 0) χA χo 0 y p := by
    simp only [jointAmplitude, sub_zero, mul_one, smul_smul, ← Complex.ofReal_mul]
    congr 2
    ring
  have hm (p : JointVariables (Euclidean n)) : ‖((1 - mo (x, p.2.2.2) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmo _).2)]
    linarith [(hmo (x, p.2.2.2)).1]
  have hzero p (hp : p ∉ K) :
      JanetCartan.Localization.phaseOscillation (ρ • jointPhase backward φ x y) p •
        jointAmplitude ρ A mi mo χA χo x y p = 0 := by
    rw [he, image_eq_zero_of_notMem_tsupport (fun h => hp (hsK h)), smul_zero, smul_zero]
  have hi := norm_setIntegral_le_of_norm_le_const (μ := jointMeasure n) hK.measure_lt_top
    (C := ρ ^ s * D.productProfile 0 * L ^ D.offset)
    (f := fun p => JanetCartan.Localization.phaseOscillation (ρ • jointPhase backward φ x y) p •
      jointAmplitude ρ A mi mo χA χo x y p) (by
        intro p hp
        rw [norm_smul, JanetCartan.Localization.norm_phaseOscillation, one_mul, he, norm_smul]
        apply (mul_le_mul_of_nonneg_right (hm p) (norm_nonneg _)).trans
        simpa only [one_mul, norm_iteratedFDeriv_zero, zero_add] using
          hgrades.norm_iteratedFDeriv_jointAmplitude_le hL p hp 0)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero] at hi
  unfold regularizedJointKernel
  rw [norm_smul, Real.norm_of_nonneg
    (mul_nonneg (jointNormalization_nonneg n) (pow_nonneg hρ.le _))]
  apply (mul_le_mul_of_nonneg_left hi
    (mul_nonneg (jointNormalization_nonneg n) (pow_nonneg hρ.le _))).trans_eq
  rw [Real.rpow_add hρ, Real.rpow_natCast]
  ring

end JanetCartan.FiniteChain.Graph.PhysicalShells.Comparable
