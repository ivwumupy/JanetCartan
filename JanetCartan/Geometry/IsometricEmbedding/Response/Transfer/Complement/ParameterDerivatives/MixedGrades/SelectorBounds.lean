module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.Normalization
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase.AmplitudeBudgets.Calculus

/-!
# Primitive bounds for the moving complementary selector

The scalar input to the carrier coefficient budget is derived here from the
original selector and carrier jets. The physical covector can be arbitrary:
its size never enters the bound. Consumer: the normalized full-amplitude grades
for `GraphDecay.hAj`. Source: `app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section

open scoped ContDiff Topology

namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades

variable {X Y F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite primitive profile majorant. Only entries through the specified
order enter the constant in `app:ch_response:thm:response-literal-transfer`. -/
def primitiveJetPrefix (Q : ℕ → ℝ) (j : ℕ) : ℝ :=
  1 + ∑ i ∈ Finset.range (j + 1), |Q i|

/-- Positivity of the primitive majorant in the complementary selector bound
of `app:ch_response:thm:response-literal-transfer`. -/
theorem one_le_primitiveJetPrefix (Q : ℕ → ℝ) (j : ℕ) :
    1 ≤ primitiveJetPrefix Q j := by
  unfold primitiveJetPrefix
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

/-- Every required primitive entry is included in the finite profile for
`app:ch_response:thm:response-literal-transfer`. -/
theorem le_primitiveJetPrefix (Q : ℕ → ℝ) {i j : ℕ} (hi : i ≤ j) :
    Q i ≤ primitiveJetPrefix Q j := by
  apply (le_abs_self _).trans
  exact (Finset.single_le_sum (fun i _ ↦ abs_nonneg (Q i))
    (Finset.mem_range_succ_iff.mpr hi)).trans (by unfold primitiveJetPrefix; linarith)

/-- The actual moving selector's profile, before carrier multiplication.
It is independent of frequency, physical covector and parameter value.
Source: `app:ch_response:thm:response-literal-transfer`. -/
def complementarySelectorBudget (Q Z : ℕ → ℝ) (j : ℕ) : ℝ :=
  1 + (j.factorial : ℝ) * primitiveJetPrefix Q j * primitiveJetPrefix Z j ^ j

/-- Nonnegativity for the scalar coefficient budget in
`app:ch_response:thm:response-literal-transfer`. -/
theorem complementarySelectorBudget_nonneg (Q Z : ℕ → ℝ) (j : ℕ) :
    0 ≤ complementarySelectorBudget Q Z j := by
  have hQ := (zero_le_one.trans (one_le_primitiveJetPrefix Q j))
  have hZ := (zero_le_one.trans (one_le_primitiveJetPrefix Z j))
  unfold complementarySelectorBudget
  positivity

/-- The selector chain rule retains scale degree `j`, uniformly in the
normalized covector. The only input bounds are for the original `q` and `ζ`.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_complementarySelector_le
    {q : Y → ℂ} {ζ : X → Y} {C : Set X}
    (hC : IsOpen C) (hζ : ContDiffOn ℝ ∞ ζ C) (hq : ContDiff ℝ ∞ q)
    (Q Z : ℕ → ℝ) {L : ℝ} (hL : 1 ≤ L) {c : X} (hc : c ∈ C)
    (ξ : Y) (j : ℕ)
    (hqjet : ∀ i ≤ j, ∀ δ, ‖iteratedFDeriv ℝ i q δ‖ ≤ Q i)
    (hζjet : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i ζ c‖ ≤ Z i * L ^ i) :
    ‖iteratedFDeriv ℝ j (fun d ↦ 1 - q (ξ - ζ d)) c‖ ≤
      complementarySelectorBudget Q Z j * L ^ j := by
  have ho : ContDiffOn ℝ ∞ (fun d ↦ ξ - ζ d) C := contDiffOn_const.sub hζ
  have hcomp := norm_iteratedFDerivWithin_comp_le hq.contDiffOn ho
    (n := j) (by simp) uniqueDiffOn_univ hC.uniqueDiffOn
    (fun _ _ ↦ Set.mem_univ _) hc
    (C := primitiveJetPrefix Q j) (D := primitiveJetPrefix Z j * L)
    (fun i hi ↦ by
      rw [iteratedFDerivWithin_univ]
      exact (hqjet i hi _).trans (le_primitiveJetPrefix Q hi))
    (fun i hi hij ↦ by
      rw [iteratedFDerivWithin_of_isOpen _ hC hc]
      change ‖iteratedFDeriv ℝ i ((fun _ : X ↦ ξ) - ζ) c‖ ≤ _
      rw [iteratedFDeriv_sub_apply contDiffAt_const
        ((hζ.contDiffAt (hC.mem_nhds hc)).of_le (by simp)),
        iteratedFDeriv_const_of_ne (by omega : i ≠ 0)]
      simp only [Pi.zero_apply, zero_sub, norm_neg]
      apply (hζjet i hi hij).trans
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right
        ((le_primitiveJetPrefix Z hij).trans
          (le_self_pow₀ (one_le_primitiveJetPrefix Z j) (by omega)))
        (pow_nonneg (zero_le_one.trans hL) _))
  rw [iteratedFDerivWithin_of_isOpen _ hC hc] at hcomp
  have hqd : ContDiffAt ℝ j (fun d ↦ q (ξ - ζ d)) c :=
    ((hq.comp_contDiffOn ho).contDiffAt (hC.mem_nhds hc)).of_le (by simp)
  change ‖iteratedFDeriv ℝ j ((fun _ : X ↦ (1 : ℂ)) - (fun d ↦ q (ξ - ζ d))) c‖ ≤ _
  rw [iteratedFDeriv_sub_apply contDiffAt_const hqd]
  apply (norm_sub_le _ _).trans
  have hconst : ‖iteratedFDeriv ℝ j (fun _ : X ↦ (1 : ℂ)) c‖ ≤ L ^ j := by
    cases j with
    | zero => simp
    | succ j => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]; positivity
  apply (add_le_add hconst hcomp).trans_eq
  simp only [complementarySelectorBudget, mul_pow]
  ring

/-- Adding the two physical spectator variables does not change the selector
grade. This is the actual scalar input to `carrierCoefficientBudget`, with
`ξ = ρ⁻¹ • η` at application. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem norm_iteratedFDeriv_complementarySelector_joint_le
    {q : Y → ℂ} {ζ : X → Y} {C : Set X}
    (hC : IsOpen C) (hζ : ContDiffOn ℝ ∞ ζ C) (hq : ContDiff ℝ ∞ q)
    (Q Z : ℕ → ℝ) {L : ℝ} (hL : 1 ≤ L) {c : X} (hc : c ∈ C)
    (ξ : Y) (w : F) (j : ℕ)
    (hqjet : ∀ i ≤ j, ∀ δ, ‖iteratedFDeriv ℝ i q δ‖ ≤ Q i)
    (hζjet : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i ζ c‖ ≤ Z i * L ^ i) :
    ‖iteratedFDeriv ℝ j (fun p : X × F ↦ 1 - q (ξ - ζ p.1)) (c, w)‖ ≤
      complementarySelectorBudget Q Z j * L ^ j := by
  have hs : ContDiffOn ℝ ∞ (fun d ↦ 1 - q (ξ - ζ d)) C :=
    contDiffOn_const.sub (hq.comp_contDiffOn (contDiffOn_const.sub hζ))
  have h := ParameterAmplitudeBudget.norm_jet_comp_contraction_le
    (ContinuousLinearMap.fst ℝ X F)
    (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun p ↦ by simpa using norm_fst_le p))
    hC (hs.of_le (show (j : ℕ∞ω) ≤ ∞ by simp)) le_rfl (p := (c, w)) hc
  exact h.trans (norm_iteratedFDeriv_complementarySelector_le hC hζ hq Q Z hL hc
    ξ j hqjet hζjet)

/-- Smoothness on a neighborhood of the compact parameter box supplies
uniform primitive carrier profiles. No estimate for a modified amplitude is
postulated. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem exists_carrierJet_profile_on_compact
    {ζ : X → Y} {C K : Set X} (hC : IsOpen C) (hK : IsCompact K)
    (hKC : K ⊆ C) (hζ : ContDiffOn ℝ ∞ ζ C) :
    ∃ Z : ℕ → ℝ, (∀ j, 0 ≤ Z j) ∧
      ∀ j c, c ∈ K → ‖iteratedFDeriv ℝ j ζ c‖ ≤ Z j := by
  have hb (j : ℕ) : ∃ B : ℝ, ∀ c ∈ K, ‖iteratedFDeriv ℝ j ζ c‖ ≤ B :=
    hK.exists_bound_of_continuousOn (fun c hc ↦
      ((hζ.contDiffAt (hC.mem_nhds (hKC hc))).continuousAt_iteratedFDeriv
        (by simp)).continuousWithinAt)
  choose B hB using hb
  exact ⟨fun j ↦ max 0 (B j), fun j ↦ le_max_left _ _,
    fun j c hc ↦ (hB j c hc).trans (le_max_right _ _)⟩

/-- The fixed smooth compact selector has a global primitive profile, so its
translated evaluation is uniformly controlled for every physical covector.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem exists_selectorJet_profile
    {q : Y → ℂ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    ∃ Q : ℕ → ℝ, (∀ j, 0 ≤ Q j) ∧
      ∀ j δ, ‖iteratedFDeriv ℝ j q δ‖ ≤ Q j := by
  have hb (j : ℕ) := (hqc.iteratedFDeriv j).exists_bound_of_continuous
    (hq.continuous_iteratedFDeriv (by simp))
  choose B hB using hb
  exact ⟨fun j ↦ max 0 (B j), fun j ↦ le_max_left _ _,
    fun j δ ↦ (hB j δ).trans (le_max_right _ _)⟩

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.MixedGrades
