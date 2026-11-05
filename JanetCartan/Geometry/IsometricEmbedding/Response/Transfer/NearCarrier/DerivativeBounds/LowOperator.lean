module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.AmplitudeJets
public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.DerivativeTransfer.Iteration

/-!
# Low operator bounds from finite primitive amplitude jets

The fixed reserve step in `app:ch_response:eq:direct-envelope-profile`.
The low L² calculus is an explicit premise; bounds for its modified amplitudes
are conclusions. The operator space may be the literal Euclidean Lebesgue L²
space, and no identification with a torus is made.
-/

@[expose] public noncomputable section
open scoped ContDiff BigOperators

namespace JanetCartan.IsometricEmbedding.Response.NearCarrier

variable {X E ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace AmplitudeExpression

/-- A finite constant for all low seminorms required by the L² calculus in
`app:ch_response:eq:direct-envelope-profile`. -/
def lowJetConstant (M : ι → ℕ → ℝ) (e : AmplitudeExpression X E ι) (c : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (c + 1), e.jetConstant M j

/-- Nonnegativity of the common low constant in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem lowJetConstant_nonneg (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (e : AmplitudeExpression X E ι) (c : ℕ) : 0 ≤ e.lowJetConstant M c :=
  Finset.sum_nonneg fun j _ => e.jetConstant_nonneg M hM j

/-- With `R > c + 2`, every low seminorm of the actual modified amplitude
costs at most `L ^ k`, where `k` is its total derivative budget. The extra
two primitive orders are retained explicitly, as in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_lowJet_evaluate_le
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (e : AmplitudeExpression X E ι) (c R k : ℕ) (hR : c + 2 < R)
    (hcost : e.derivativeCost ≤ k)
    (L : ℝ) (hL : 1 ≤ L) (a : ι → X → E) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (hjet : ∀ i j, j ≤ c + k → ∀ x,
      ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R))
    (j : ℕ) (hj : j ≤ c) (x : X) :
    ‖iteratedFDeriv ℝ j (e.evaluate a) x‖ ≤ e.lowJetConstant M c * L ^ k := by
  have hb := e.norm_iteratedFDeriv_evaluate_le a ha M hM L hL (R - 2) (c + k) x
    (fun i q hq => by
      have he : q - (R - 2) = q + 2 - R := by omega
      simpa only [he] using hjet i q hq x) j (by omega)
  have hc : e.jetConstant M j ≤ e.lowJetConstant M c :=
    Finset.single_le_sum (fun q _ => e.jetConstant_nonneg M hM q)
      (Finset.mem_range.mpr (by omega))
  exact hb.trans (mul_le_mul hc (pow_le_pow_right₀ hL (by omega))
    (pow_nonneg (le_trans zero_le_one hL) _) (e.lowJetConstant_nonneg M hM c))

variable {H K : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

/-- Quantifiers for `app:ch_response:eq:direct-envelope-profile`: the
constant is chosen before the scale, primitive fields, operator realization,
and datum. Only the low L² theorem is a norm premise. Admissibility `P` may
record the original supports and phase sector; it need not assert any bound.
Every modified-amplitude seminorm is proved from primitive jets. -/
theorem exists_lowOperator_constant
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (e : AmplitudeExpression X E ι) (c R k : ℕ) (hR : c + 2 < R)
    (hcost : e.derivativeCost ≤ k) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (a : ι → X → E), (∀ i, ContDiff ℝ ∞ (a i)) →
      (∀ i j, j ≤ c + k → ∀ x,
        ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R)) →
      ∀ (T : (X → E) → H →L[ℂ] K) (P : (X → E) → Prop),
      (∀ b, P b → ContDiff ℝ ∞ b → ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ c → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ A) → ‖T b‖ ≤ C₀ * A) →
      P (e.evaluate a) →
      ‖T (e.evaluate a)‖ ≤ C * L ^ k ∧
        ∀ f, ‖T (e.evaluate a) f‖ ≤ (C * L ^ k) * ‖f‖ := by
  refine ⟨C₀ * e.lowJetConstant M c,
    mul_nonneg hC₀ (e.lowJetConstant_nonneg M hM c), ?_⟩
  intro L hL a ha hjet T P hlow hP
  have hb := hlow _ hP (e.contDiff_evaluate a ha)
    (e.lowJetConstant M c * L ^ k)
    (mul_nonneg (e.lowJetConstant_nonneg M hM c) (pow_nonneg (by linarith) _))
    (e.norm_lowJet_evaluate_le M hM c R k hR hcost L hL a ha hjet)
  rw [← mul_assoc] at hb
  exact ⟨hb, fun f => (T (e.evaluate a)).le_of_opNorm_le hb f⟩

/-- The existing ordered-transfer enumeration gives the precise exponent
`s - r` for a branch of `app:ch_response:eq:direct-envelope-profile`.
The structural input is the number of derivative nodes in its literal
amplitude expression, not an amplitude estimate. -/
theorem exists_orderedBranch_lowOperator_constant
    {J : Type*} (is : List J) (p : List J × List J)
    (hp : p ∈ Pseudodifferential.orderedTransferTerms is)
    (M : ι → ℕ → ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (e : AmplitudeExpression X E ι) (hcost : e.derivativeCost ≤ p.1.length)
    (c R : ℕ) (hR : c + 2 < R) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ (a : ι → X → E), (∀ i, ContDiff ℝ ∞ (a i)) →
      (∀ i j, j ≤ c + (is.length - p.2.length) → ∀ x,
        ‖iteratedFDeriv ℝ j (a i) x‖ ≤ M i j * L ^ (j + 2 - R)) →
      ∀ (T : (X → E) → H →L[ℂ] K) (P : (X → E) → Prop),
      (∀ b, P b → ContDiff ℝ ∞ b → ∀ A : ℝ, 0 ≤ A →
        (∀ j, j ≤ c → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ A) → ‖T b‖ ≤ C₀ * A) →
      P (e.evaluate a) →
      ‖T (e.evaluate a)‖ ≤ C * L ^ (is.length - p.2.length) ∧
        ∀ f, ‖T (e.evaluate a) f‖ ≤ (C * L ^ (is.length - p.2.length)) * ‖f‖ := by
  apply e.exists_lowOperator_constant M hM c R (is.length - p.2.length) hR _ C₀ hC₀
  simpa only [Pseudodifferential.orderedTransferTerms_transfer_count is p hp] using hcost

end AmplitudeExpression
end JanetCartan.IsometricEmbedding.Response.NearCarrier
