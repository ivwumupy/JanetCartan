module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Quantitative.SymbolBounds.Rescaling

/-!
# Conic symbol grading of the literal full normal amplitude

This is the conditional deduction in Step 1 of
`app:ch_regular_base:thm:actual-calculus`. The inputs are the original matrices
of orders `p`, `q`, the actual full inverse of order one, and the original
averaged-gradient Jacobian of order zero. No bound on transformed jets is an
input. The Hamilton phase, compatible chart geometry, and inverse coefficient
constructions must instantiate these primitive assumptions in the parent
normal-amplitude construction.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}

/-- Primitive data on one normalized shell for
`app:ch_regular_base:setup:finite-calculus`. The domains are open neighborhoods
of a shell, allowing the jets to be ambient derivatives. The two matrices
include all their original physical and frequency cutoffs. Composition needs
only positive-order inverse-coordinate jets, recorded in `inverseJets`. -/
structure NormalAmplitudeShellInputs
    (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
    (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (ρ p q : ℝ) (N : ℕ) (M L δ : ℝ) (U V : Set (NormalVariables n)) : Prop where
  open_domain : IsOpen U
  open_range : IsOpen V
  inverse_smooth : ContDiffOn ℝ ∞ (normalInverseCoordinates (normalizedNormalInverse ρ η)) U
  mapsTo : MapsTo (normalInverseCoordinates (normalizedNormalInverse ρ η)) U V
  input_smooth : ContDiffOn ℝ ∞
    (normalInputCoefficients (normalizedNormalMatrix ρ p A) (normalizedNormalMatrix ρ q B)
      (normalizedNormalJacobian ρ J)) V
  gap : ∀ z ∈ V, δ ≤ |(normalizedNormalJacobian ρ J z.1 z.2.1 z.2.2).det|
  inputJets : ∀ z ∈ V, ∀ i ≤ N, ‖iteratedFDeriv ℝ i
    (normalInputCoefficients (normalizedNormalMatrix ρ p A) (normalizedNormalMatrix ρ q B)
      (normalizedNormalJacobian ρ J)) z‖ ≤ M
  inverseJets : ∀ z ∈ U, ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i
    (normalInverseCoordinates (normalizedNormalInverse ρ η)) z‖ ≤ L

/-- Uniform mixed estimates on a shell for the literal zero extension. This
uses the primitive input jets, with a constant independent of the shell, the
orders, and the actual fields. Both physical positions are retained.
Source: `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_extendedCrossNormalAmplitude_shell_bound (N : ℕ) (M L : ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀
      (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
      (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
      (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
      (Ω U V : Set (NormalVariables n)) (ρ p q : ℝ), 0 < ρ →
      NormalAmplitudeShellInputs A B η J ρ p q N M L δ U V →
      MapsTo (normalFrequencyDilation ρ) U Ω →
      ∀ z ∈ U, ∀ k ≤ N, ∀ (s : Finset (Fin k)) (v : Fin k → NormalVariables n),
      (∀ i ∈ s, (v i).1 = 0 ∧ (v i).2.1 = 0) →
      (∀ i ∉ s, (v i).2.2 = 0) → (∀ i, ‖v i‖ ≤ 1) →
      ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J)
        (normalFrequencyDilation ρ z) v‖ ≤ ρ ^ (p + q - s.card) * C := by
  obtain ⟨C, hC, hb⟩ := exists_crossNormalAmplitude_finiteJet_bound
    (n := n) (r := r) N M L hδ
  refine ⟨C, hC, ?_⟩
  intro A B η J Ω U V ρ p q hρ h hsub z hz k hk s v hvξ hvxy hv
  apply norm_iteratedFDeriv_mixed_le_of_normalized _ hρ (p + q) k z s v hvξ hvxy hv
  have he : (fun w ↦ ρ ^ (-(p + q)) •
      extendedCrossNormalAmplitude Ω A B η J (normalFrequencyDilation ρ w)) =ᶠ[𝓝 z]
      (fun w : NormalVariables n ↦ crossNormalAmplitude
        (normalizedNormalMatrix ρ p A) (normalizedNormalMatrix ρ q B)
        (normalizedNormalInverse ρ η) (normalizedNormalJacobian ρ J) w.1 w.2.1 w.2.2) := by
    filter_upwards [h.open_domain.mem_nhds hz] with w hw
    rw [crossNormalAmplitude_normalized A B η J hρ p q w]
    unfold extendedCrossNormalAmplitude
    rw [indicator_of_mem (hsub hw)]
    rfl
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact hb _ _ _ _ U V h.open_domain h.open_range h.inverse_smooth h.mapsTo
    h.input_smooth h.gap h.inputJets h.inverseJets z hz k hk

/-- Comparison of physical and shell frequency weights, shared by the finite
and one-high symbol estimates for `app:ch_regular_base:eq:actual-normal-amplitude`.
The loss depends only on the exponent, not on the shell. -/
theorem normalAmplitude_rpow_le_shell_weight {ρ w : ℝ} (hρ : 0 < ρ)
    (h₁ : ρ ≤ w) (h₂ : w ≤ 2 * ρ) (t : ℝ) :
    ρ ^ t ≤ 2 ^ |t| * w ^ t := by
  have hw : 0 < w := hρ.trans_le h₁
  by_cases ht : 0 ≤ t
  · exact (Real.rpow_le_rpow hρ.le h₁ ht).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hw.le _)
        (Real.one_le_rpow (by norm_num) (abs_nonneg _)))
  · have ht' : t ≤ 0 := le_of_not_ge ht
    calc
      ρ ^ t ≤ (w / 2) ^ t := Real.rpow_le_rpow_of_nonpos (by positivity)
        (by linarith) ht'
      _ = 2 ^ |t| * w ^ t := by
        rw [Real.div_rpow hw.le (by norm_num), abs_of_nonpos ht',
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        ring

/-- The full literal normal has order `p + q` in the paper's weighted
seminorm, from uniform primitive normalized dyadic-shell jets. The zeroth
shell includes the fixed low-frequency piece. `hcover` and `hsub` are only
geometric coverage of the original inverse chart by open shell neighborhoods;
all jets in `hinputs` are of `A`, `B`, `J`, and the supplied full inverse `η`.
The support hypotheses are exactly the checked buffered zero-extension laws.
Constants precede the fields, and the statement covers every mixed direction
in both physical positions, with one weight gained per covector derivative.

Source: `app:ch_regular_base:setup:finite-calculus` and
`app:ch_regular_base:eq:actual-normal-amplitude`, actual-calculus Step 1.
The parent normal-amplitude task must instantiate the primitive shell inputs
and the support/coverage laws from the actual phase and inverse constructions. -/
theorem exists_extendedCrossNormalAmplitude_symbol_bound_of_shell_cover
    (N : ℕ) (M L p q : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀
      (S : Euclidean n → Euclidean n → ℝ)
      (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
      (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
      (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
      (Ω W K : Set (NormalVariables n)) (U V : ℕ → Set (NormalVariables n)),
      (∀ j, NormalAmplitudeShellInputs A B η J ((2 : ℝ) ^ j) p q N M L δ (U j) (V j)) →
      (∀ j, MapsTo (normalFrequencyDilation ((2 : ℝ) ^ j)) (U j) Ω) →
      (∀ z ∈ Ω, ∃ j : ℕ, ∃ w ∈ U j,
        normalFrequencyDilation ((2 : ℝ) ^ j) w = z ∧
        (2 : ℝ) ^ j ≤ Real.sqrt (1 + ‖z.2.2‖ ^ 2) ∧
        Real.sqrt (1 + ‖z.2.2‖ ^ 2) ≤ 2 * (2 : ℝ) ^ j) →
      MapsTo (normalInverseCoordinates η) Ω W →
      (∀ z ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η z) = z) →
      (∀ z ∈ W, A z.1 z.2.2 ≠ 0 → B z.2.1 z.2.2 ≠ 0 → z ∈ K) →
      IsClosed (normalForwardCoordinates S '' K) →
      normalForwardCoordinates S '' K ⊆ Ω →
      ∀ z, ∀ k ≤ N, ∀ (s : Finset (Fin k)) (v : Fin k → NormalVariables n),
      (∀ i ∈ s, (v i).1 = 0 ∧ (v i).2.1 = 0) →
      (∀ i ∉ s, (v i).2.2 = 0) → (∀ i, ‖v i‖ ≤ 1) →
      (Real.sqrt (1 + ‖z.2.2‖ ^ 2)) ^ (-(p + q) + s.card) *
        ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) z v‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_extendedCrossNormalAmplitude_shell_bound
    (n := n) (r := r) N M L hδ
  let D := max 1 (∑ b ∈ Finset.range (N + 1), (2 : ℝ) ^ |p + q - b|)
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨D * C, mul_pos hD hC, ?_⟩
  intro S A B η J Ω W K U V hinputs hsub hcover hmap hright hsupp hclosed hbuffer
    z k hk s v hvξ hvxy hv
  by_cases hz : z ∈ Ω
  · obtain ⟨j, w, hw, he, hlow, hhigh⟩ := hcover z hz
    have hρ : 0 < (2 : ℝ) ^ j := by positivity
    have hj := hb A B η J Ω (U j) (V j) _ p q hρ (hinputs j) (hsub j)
      w hw k hk s v hvξ hvxy hv
    rw [he] at hj
    have hsc : s.card ≤ N := (le_trans (Finset.card_le_univ s) (by simp)).trans hk
    have hterm : (2 : ℝ) ^ |p + q - s.card| ≤ D :=
      (Finset.single_le_sum (f := fun b : ℕ ↦ (2 : ℝ) ^ |p + q - b|)
        (fun b _ ↦ Real.rpow_nonneg (by norm_num) _)
        (Finset.mem_range.mpr (by omega : s.card < N + 1))).trans (le_max_right _ _)
    let a := Real.sqrt (1 + ‖z.2.2‖ ^ 2)
    have ha : 0 < a := hρ.trans_le hlow
    have hbound : ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) z v‖ ≤
        a ^ (p + q - s.card) * (D * C) := by
      calc
        _ ≤ ((2 : ℝ) ^ j) ^ (p + q - s.card) * C := hj
        _ ≤ ((2 : ℝ) ^ |p + q - s.card| * a ^ (p + q - s.card)) * C :=
          mul_le_mul_of_nonneg_right (normalAmplitude_rpow_le_shell_weight hρ hlow hhigh _) hC.le
        _ ≤ (D * a ^ (p + q - s.card)) * C := by
          gcongr
        _ = _ := by ring
    have hh := mul_le_mul_of_nonneg_left hbound
      (Real.rpow_nonneg ha.le (-(p + q) + s.card))
    calc
      _ ≤ a ^ (-(p + q) + s.card) * (a ^ (p + q - s.card) * (D * C)) := hh
      _ = D * C := by
        rw [← mul_assoc, ← Real.rpow_add ha]
        rw [show -(p + q) + (s.card : ℝ) + (p + q - s.card) = 0 by ring,
          Real.rpow_zero, one_mul]
  · rw [iteratedFDeriv_extendedCrossNormalAmplitude_eq_zero S A B η J
      hmap hright hsupp hclosed hbuffer hz k]
    simp only [zero_apply, norm_zero, mul_zero]
    exact (mul_pos hD hC).le

/-- Shell neighborhoods in normalized physical covectors, open when `Ω` is
open. The shell
`j = 0` contains zero frequency, so the fixed low-frequency piece is retained.
The wider interval supplies room around both boundaries of the dyadic shell.
Source: `app:ch_regular_base:setup:finite-calculus`. -/
def normalDyadicShell (Ω : Set (NormalVariables n)) (j : ℕ) : Set (NormalVariables n) :=
  {z | normalFrequencyDilation ((2 : ℝ) ^ j) z ∈ Ω ∧
    (2 : ℝ) ^ j / 2 < Real.sqrt (1 + ‖((2 : ℝ) ^ j) • z.2.2‖ ^ 2) ∧
    Real.sqrt (1 + ‖((2 : ℝ) ^ j) • z.2.2‖ ^ 2) < 4 * (2 : ℝ) ^ j}

/-- The explicit normalized neighborhoods cover every physical covector,
including zero. This geometric lemma is shared by the finite and one-high
symbol bounds in `app:ch_regular_base:setup:finite-calculus`. -/
theorem normalDyadicShell_cover (Ω : Set (NormalVariables n))
    {z : NormalVariables n} (hz : z ∈ Ω) :
    ∃ j : ℕ, ∃ w ∈ normalDyadicShell Ω j,
      normalFrequencyDilation ((2 : ℝ) ^ j) w = z ∧
      (2 : ℝ) ^ j ≤ Real.sqrt (1 + ‖z.2.2‖ ^ 2) ∧
      Real.sqrt (1 + ‖z.2.2‖ ^ 2) ≤ 2 * (2 : ℝ) ^ j := by
  have ha : 1 ≤ Real.sqrt (1 + ‖z.2.2‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖z.2.2‖])
  obtain ⟨j, hj₁, hj₂⟩ := exists_nat_pow_near ha (by norm_num : (1 : ℝ) < 2)
  have hρ : 0 < (2 : ℝ) ^ j := by positivity
  let w := normalFrequencyDilation (((2 : ℝ) ^ j)⁻¹) z
  have he : normalFrequencyDilation ((2 : ℝ) ^ j) w = z := by
    simp [w, smul_inv_smul₀ hρ.ne']
  have hj₂' : Real.sqrt (1 + ‖z.2.2‖ ^ 2) ≤ 2 * (2 : ℝ) ^ j := by
    simpa [pow_succ, mul_comm] using hj₂.le
  refine ⟨j, w, ?_, he, hj₁, hj₂'⟩
  change normalFrequencyDilation ((2 : ℝ) ^ j) w ∈ Ω ∧
    (2 : ℝ) ^ j / 2 < Real.sqrt (1 + ‖(normalFrequencyDilation ((2 : ℝ) ^ j) w).2.2‖ ^ 2) ∧
    Real.sqrt (1 + ‖(normalFrequencyDilation ((2 : ℝ) ^ j) w).2.2‖ ^ 2) < 4 * (2 : ℝ) ^ j
  rw [he]
  exact ⟨hz, by linarith, by linarith⟩

/-- Primitive normalized jets on the explicit dyadic neighborhoods imply the
paper's full weighted symbol estimate of order `p + q`. Dyadic coverage and
all transformed-jet bounds are proved here; the only analytic inputs are jets
of the original matrices/Jacobian and order-one inverse. The actual support
laws are those of the checked literal zero extension. This is the interface
consumed by the parent normal-amplitude construction.

Source: `app:ch_regular_base:setup:finite-calculus` and
`app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_extendedCrossNormalAmplitude_symbol_bound
    (N : ℕ) (M L p q : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀
      (S : Euclidean n → Euclidean n → ℝ)
      (A B : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
      (η : Euclidean n → Euclidean n → Euclidean n → Euclidean n)
      (J : Euclidean n → Euclidean n → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
      (Ω W K : Set (NormalVariables n)) (V : ℕ → Set (NormalVariables n)),
      (∀ j, NormalAmplitudeShellInputs A B η J ((2 : ℝ) ^ j) p q N M L δ
        (normalDyadicShell Ω j) (V j)) →
      MapsTo (normalInverseCoordinates η) Ω W →
      (∀ z ∈ Ω, normalForwardCoordinates S (normalInverseCoordinates η z) = z) →
      (∀ z ∈ W, A z.1 z.2.2 ≠ 0 → B z.2.1 z.2.2 ≠ 0 → z ∈ K) →
      IsClosed (normalForwardCoordinates S '' K) →
      normalForwardCoordinates S '' K ⊆ Ω →
      ∀ z, ∀ k ≤ N, ∀ (s : Finset (Fin k)) (v : Fin k → NormalVariables n),
      (∀ i ∈ s, (v i).1 = 0 ∧ (v i).2.1 = 0) →
      (∀ i ∉ s, (v i).2.2 = 0) → (∀ i, ‖v i‖ ≤ 1) →
      (Real.sqrt (1 + ‖z.2.2‖ ^ 2)) ^ (-(p + q) + s.card) *
        ‖iteratedFDeriv ℝ k (extendedCrossNormalAmplitude Ω A B η J) z v‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_extendedCrossNormalAmplitude_symbol_bound_of_shell_cover
    (n := n) (r := r) N M L p q hδ
  refine ⟨C, hC, ?_⟩
  intro S A B η J Ω W K V hinputs hmap hright hsupp hclosed hbuffer
  apply hb S A B η J Ω W K (normalDyadicShell Ω) V hinputs
    (fun _ _ hw ↦ hw.1) _ hmap hright hsupp hclosed hbuffer
  intro z hz
  exact normalDyadicShell_cover Ω hz

end JanetCartan.FourierIntegral
