module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.InverseJets.Jacobian.Jets

/-!
# Absolute transport Jacobian: transfer to the supplied density coefficient

The literal coefficient `J` in `bg-full-complex-amplitude` is identified on
an open input chart with the genuine Jacobian. The estimates below transfer
to every normalized shell in the working ball. All constants precede `Y`,
`J`, and the primitive high-norm sequence. The high forward estimates remain
an explicit obligation of the producer of `bg-mixed-input`.
-/

@[expose] public noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n : ℕ}

/-- Transfer of the one-high Jacobian estimate to a supplied coefficient
identified with the literal determinant on the open chart. Restriction to a
normalized shell `K` is allowed. Source: `app:ch_background:eq:bg-jacobian`
and `app:ch_background:prop:bg-frame`, Step 1. -/
theorem exists_suppliedTransportJacobian_oneHigh_bound
    (c : TransportSliceCoordinates n) (a : InputVariables n)
    {ρ : ℝ} (hρ : 0 < ρ) {W : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) {K : Set (InputVariables n)} (hK : K ⊆ closedBall a ρ)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ) (m : ℕ) :
    ∃ C > (0 : ℝ), ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (J : InputVariables n → ℝ),
      ContDiffOn ℝ ∞ (transportAveragedGradient Y) W →
      EqOn J (transportAbsoluteJacobian c Y) W →
      cNorm (closedBall a ρ) 1 (transportAveragedGradient Y) ≤ M →
      (∀ p ∈ closedBall a ρ, δ ≤ transportAbsoluteJacobian c Y p) →
      cNorm K m J + cNorm K m (fun p ↦ (J p)⁻¹) ≤
        C * (1 + cNorm (closedBall a ρ) (m + 1) (transportAveragedGradient Y)) := by
  obtain ⟨C, hC, hb⟩ := exists_transportAbsoluteJacobian_oneHigh_bound
    c a hρ hW hball hM hδ m
  refine ⟨C, hC, ?_⟩
  intro Y J hY hJ hlow hgap
  have hA := transportSliceDifferential_contDiffOn c Y hW hY
  have hj (p) (hp : p ∈ closedBall a ρ) :
      ContDiffAt ℝ ∞ (transportAbsoluteJacobian c Y) p :=
    (NormalComparison.contDiff_normalJacobianDet.contDiffAt.abs
      (abs_pos.mp (hδ.trans_le (hgap p hp)))).comp p
      (hA.contDiffAt (hW.mem_nhds (hball hp)))
  have hi (p) (hp : p ∈ closedBall a ρ) :
      ContDiffAt ℝ ∞ (fun q ↦ (transportAbsoluteJacobian c Y q)⁻¹) p :=
    (hj p hp).inv (ne_of_gt (hδ.trans_le (hgap p hp)))
  have he (p) (hp : p ∈ K) : J =ᶠ[𝓝 p] transportAbsoluteJacobian c Y :=
    (hW.eventually_mem (hball (hK hp))).mono (fun q hq ↦ hJ hq)
  have hei (p) (hp : p ∈ K) : (fun q ↦ (J q)⁻¹) =ᶠ[𝓝 p]
      (fun q ↦ (transportAbsoluteJacobian c Y q)⁻¹) :=
    (he p hp).mono (fun q hq ↦ congrArg Inv.inv hq)
  rw [GeometricProfile.cNorm_eq_of_eventuallyEq he m,
    GeometricProfile.cNorm_eq_of_eventuallyEq hei m]
  apply le_trans (add_le_add
    (cNorm_mono_set_of_contDiffAt hK (isCompact_closedBall a ρ)
      (fun p hp ↦ (hj p hp).of_le (by simp : (m : ℕ∞ω) ≤ ∞)))
    (cNorm_mono_set_of_contDiffAt hK (isCompact_closedBall a ρ)
      (fun p hp ↦ (hi p hp).of_le (by simp : (m : ℕ∞ω) ≤ ∞))))
  exact hb Y hY hlow hgap

/-- Primitive forward high bounds of fixed shift `D` give Jacobian and
reciprocal bounds of fixed shift `D+1`, with one high norm. Constants precede
both the geometry `Y` and the supplied `J`. This is the conditional Jacobian
input to the inverse-jet assembly and the literal amplitude in
`app:ch_background:prop:bg-frame`, Step 1. The producer of the last premise
is `jc-continuum-transport-forward-mixed-jets`, from `bg-mixed-input`. -/
theorem exists_suppliedTransportJacobian_fixedShift_bound
    (c : TransportSliceCoordinates n) (a : InputVariables n)
    {ρ : ℝ} (hρ : 0 < ρ) {W : Set (InputVariables n)} (hW : IsOpen W)
    (hball : closedBall a ρ ⊆ W) {K : Set (InputVariables n)} (hK : K ⊆ closedBall a ρ)
    {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (D : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) :
    ∃ C : ℕ → ℝ, (∀ m, 0 < C m) ∧ ∀
      (Y : Euclidean n × (ℝ × Euclidean 2) → Euclidean (n - 1))
      (J : InputVariables n → ℝ) (H : ℕ → ℝ),
      ContDiffOn ℝ ∞ (transportAveragedGradient Y) W →
      EqOn J (transportAbsoluteJacobian c Y) W →
      cNorm (closedBall a ρ) 1 (transportAveragedGradient Y) ≤ M →
      (∀ p ∈ closedBall a ρ, δ ≤ transportAbsoluteJacobian c Y p) →
      (∀ j, 0 ≤ H j) →
      (∀ j, cNorm (closedBall a ρ) j (transportAveragedGradient Y) ≤
        B j * (1 + H (j + D))) →
      ∀ m, cNorm K m J + cNorm K m (fun p ↦ (J p)⁻¹) ≤
        C m * (1 + H (m + (D + 1))) := by
  choose C hC hb using
    exists_suppliedTransportJacobian_oneHigh_bound c a hρ hW hball hK hM hδ
  refine ⟨fun m ↦ C m * (1 + B (m + 1)),
    fun m ↦ mul_pos (hC m) (by linarith [hB (m + 1)]), ?_⟩
  intro Y J H hY hJ hlow hgap hH hhigh m
  have hh := hb m Y J hY hJ hlow hgap
  have hb' := hhigh (m + 1)
  have hindex : m + 1 + D = m + (D + 1) := by omega
  rw [hindex] at hb'
  apply hh.trans
  calc
    _ ≤ C m * (1 + B (m + 1) * (1 + H (m + (D + 1)))) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hb') (hC m).le
    _ ≤ _ := by nlinarith [mul_nonneg (hC m).le (hH (m + (D + 1)))]

end JanetCartan.ContinuumNormalReduction.TransportSymbol
