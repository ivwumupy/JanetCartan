module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.PrimitiveBounds.QuadraticJets

/-!
# Uniform order-zero normal jets from primitive shell bounds

The finite reserve for the low graph estimate is independent of shell radius.
All assumptions concern the original amplitudes (including every cutoff), the
Jacobian and the actual inverse. Source: actual-calculus Step 1,
`app:ch_regular_base:eq:actual-normal-amplitude`.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Order-zero primitive shell inputs for the low normal budget. `a` and `b`
measure the two original amplitudes; `M`, `L` and `δ` measure only geometry.
Hamilton and compatible geometry supply `jacobianJets` and `gap`; the inverse
coefficient producer supplies `inverseJets`. The parent must bound the full
original cutoff amplitudes on these open shells, including their shoulders.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
structure PrimitiveNormalShellInputs
    (A B : E → E → Mat) (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    (ρ : ℝ) (N : ℕ) (M L δ a b : ℝ) (U V : Set (NormalVariables n)) : Prop where
  open_domain : IsOpen U
  open_range : IsOpen V
  inverse_smooth : ContDiffOn ℝ ∞ (normalInverseCoordinates (normalizedNormalInverse ρ η)) U
  mapsTo : MapsTo (normalInverseCoordinates (normalizedNormalInverse ρ η)) U V
  input_smooth : ContDiffOn ℝ ∞
    (normalInputCoefficients (normalizedNormalMatrix ρ 0 A) (normalizedNormalMatrix ρ 0 B)
      (normalizedNormalJacobian ρ J)) V
  gap : ∀ z ∈ V, δ ≤ |(normalizedNormalJacobian ρ J z.1 z.2.1 z.2.2).det|
  jacobianJets : ∀ z ∈ V, ∀ i ≤ N, ‖iteratedFDeriv ℝ i
    (fun q : NormalVariables n ↦ normalizedNormalJacobian ρ J q.1 q.2.1 q.2.2) z‖ ≤ M
  leftJets : ∀ z ∈ V, ∀ i ≤ N, ‖iteratedFDeriv ℝ i
    (fun q : NormalVariables n ↦ normalizedNormalMatrix ρ 0 A q.1 q.2.2) z‖ ≤ a
  rightJets : ∀ z ∈ V, ∀ i ≤ N, ‖iteratedFDeriv ℝ i
    (fun q : NormalVariables n ↦ normalizedNormalMatrix ρ 0 B q.2.1 q.2.2) z‖ ≤ b
  inverseJets : ∀ z ∈ U, ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i
    (normalInverseCoordinates (normalizedNormalInverse ρ η)) z‖ ≤ L

private theorem norm_iteratedFDeriv_dilation_le
    (f : NormalVariables n → Mat) {ρ : ℝ} (hρ : 1 ≤ ρ)
    (k : ℕ) (z : NormalVariables n) :
    ‖iteratedFDeriv ℝ k f (normalFrequencyDilation ρ z)‖ ≤
      ‖iteratedFDeriv ℝ k (f ∘ normalFrequencyDilation ρ) z‖ := by
  have hpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hcontract (v : NormalVariables n) : ‖normalFrequencyDilation ρ⁻¹ v‖ ≤ ‖v‖ := by
    simp only [normalFrequencyDilation_apply, Prod.norm_def]
    apply max_le_max le_rfl (max_le_max le_rfl _)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hpos.le)]
    exact mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hρ)
  apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
  intro v
  have he := iteratedFDeriv_normalFrequencyDilation f hpos.ne' k z
    (fun i ↦ normalFrequencyDilation ρ⁻¹ (v i))
  simp only [normalFrequencyDilation_apply, smul_inv_smul₀ hpos.ne', Prod.mk.eta] at he
  simp only [normalFrequencyDilation_apply]
  rw [← he]
  apply (ContinuousMultilinearMap.le_opNorm _ _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hcontract (v i))

/-- Uniform full joint jets from order-zero primitive shell bounds. The
constant is independent of the shell, amplitude sizes and regularization
radius. Nonnegative sizes, including zero, give the exact bilinear budget.
This is consumed by the paired-position derivative bound for the low normal
PDO in actual-calculus Step 1. Source:
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_extendedCrossNormalAmplitude_orderZero_bilinear_bound
    (N : ℕ) (M L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (S : E → E → ℝ) (A B : E → E → Mat) (η : E → E → E → E)
      (J : E → E → E → E →L[ℝ] E) (Ω W K : Set (NormalVariables n))
      (V : ℕ → Set (NormalVariables n)) (a b : ℝ), 0 ≤ a → 0 ≤ b →
      (∀ j, PrimitiveNormalShellInputs A B η J ((2 : ℝ)^j) N M L δ a b
        (normalDyadicShell Ω j) (V j)) →
      MapsTo (normalInverseCoordinates η) Ω W →
      (∀ z ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η z) = z) →
      (∀ z ∈ W, A z.1 z.2.2 ≠ 0 → B z.2.1 z.2.2 ≠ 0 → z ∈ K) →
      IsClosed (normalForwardCoordinates S '' K) → normalForwardCoordinates S '' K ⊆ Ω →
      ∀ z, ∀ k ≤ N,
        ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) z‖ ≤ C * a * b := by
  obtain ⟨C, hC, hb⟩ := exists_crossNormalAmplitude_bilinear_jet_bound (n := n) (r := r) N M L hδ
  refine ⟨C, hC, ?_⟩
  intro S A B η J Ω W K V a b ha hb' hinputs hmap hright hsupp hclosed hbuffer z k hk
  by_cases hz : z ∈ Ω
  · obtain ⟨j, w, hw, he, _, _⟩ := normalDyadicShell_cover Ω hz
    have hρ : 0 < (2 : ℝ)^j := by positivity
    have h := hinputs j
    have heq : (extendedCrossNormalAmplitude Ω A B η J ∘ normalFrequencyDilation ((2 : ℝ)^j))
        =ᶠ[𝓝 w] (fun q : NormalVariables n ↦ crossNormalAmplitude
          (normalizedNormalMatrix ((2 : ℝ)^j) 0 A) (normalizedNormalMatrix ((2 : ℝ)^j) 0 B)
          (normalizedNormalInverse ((2 : ℝ)^j) η) (normalizedNormalJacobian ((2 : ℝ)^j) J)
          q.1 q.2.1 q.2.2) := by
      filter_upwards [h.open_domain.mem_nhds hw] with q hq
      rw [crossNormalAmplitude_normalized A B η J hρ 0 0 q]
      simp only [add_zero, neg_zero, Real.rpow_zero, one_smul, Function.comp_apply]
      exact indicator_of_mem hq.1 _
    rw [← he]
    apply (norm_iteratedFDeriv_dilation_le _ (one_le_pow₀ (by norm_num)) k w).trans
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds]
    exact hb _ _ _ _ _ _ a b ha hb' h.open_domain h.open_range h.inverse_smooth h.mapsTo
      h.input_smooth h.gap h.jacobianJets h.leftJets h.rightJets h.inverseJets w hw k hk
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq_zero S A B η J
      hmap hright hsupp hclosed hbuffer hz k, norm_zero]
    exact mul_nonneg (mul_nonneg hC.le ha) hb'

end JanetCartan.FourierIntegral.LowBounds
