module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.SymbolBudget
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Operators

/-!
# Original-covector budgets for modified elapsed amplitudes

The consumer is `app:ch_response:eq:direct-envelope-profile`; the counting
argument is `paper-v2.tex`, `new:eq:carrier-coefficient`, after restoring the
carrier in `new:eq:carrier-ibp`. Normalization is literally `ξ = lam • θ`.
There is no covector translation or change of graph phase. Both physical
positions, all masks, and the beta/high-pass transition stay inside the
primitive fields. The scalar `lam^p` is retained outside the expression, so the
order-minus-one gain is not discarded by an order-zero estimate.

`jc-direct-evolution-coefficient-jets` supplies the primitive budgets;
`jc-direct-evolution-compact-transfer` supplies identification with the actual differentiated integral. These are
independent of the implication proved here.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.ModifiedLow
open FourierIntegral FullAmplitudePrimitiveBudget.Local PrimitiveProfiles
open FourierIntegral.SourceExpansion
open IsometricEmbedding.Response.NearCarrier NearCarrierSymbol
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- The actual order-`p` amplitude restored at the original physical covector,
for `new:eq:carrier-ibp`. In particular `p = -1` retains a factor `lam⁻¹`. -/
def modifiedAmplitude (lam : ℝ) (p : ℤ) (f : Point n → Mat) : FullAmplitude n r :=
  physicalAmplitudeOfNormalized lam ((lam ^ p) • f)

/-- The literal normalization of the restored amplitude, including both
positions and all masks (`new:eq:carrier-coefficient`). -/
theorem normalizedField_modifiedAmplitude {lam : ℝ} (hlam : lam ≠ 0)
    (p : ℤ) (f : Point n → Mat) :
    normalizedField lam (uncurry (modifiedAmplitude lam p f)) = (lam ^ p) • f :=
  normalizedField_physicalAmplitudeOfNormalized hlam _

/-- An actual amplitude identified by compact integration by parts is exactly
the restored expression, not a different graph amplitude. Consumer:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem modifiedAmplitude_eq_of_normalized {lam : ℝ} (hlam : lam ≠ 0)
    (p : ℤ) (f : Point n → Mat) (A : FullAmplitude n r)
    (he : normalizedField lam (uncurry A) = (lam ^ p) • f) :
    modifiedAmplitude lam p f = A := by
  funext x y ξ
  have h := congrFun he ((x, y), lam⁻¹ • ξ)
  simpa [modifiedAmplitude, physicalAmplitudeOfNormalized, normalizedField,
    uncurry, smul_smul, hlam] using h.symm

/-- Primitive smoothness gives smoothness of the actual restored amplitude,
with Frobenius matrix norms (`new:eq:carrier-coefficient`). -/
theorem contDiff_modifiedAmplitude (lam : ℝ) (p : ℤ) {f : Point n → Mat}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (uncurry (modifiedAmplitude lam p f)) :=
  contDiff_physicalAmplitudeOfNormalized lam (hf.const_smul (lam ^ p))

/-- Physical admissibility follows from the literal normalized support. No
modified-symbol estimate is part of this support premise. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem admissible_modifiedAmplitude {lam : ℝ} (hlam : lam ≠ 0)
    (p : ℤ) {f : Point n → Mat} (hf : ContDiff ℝ ∞ f)
    {X₀ Y₀ F₀ : Set E}
    (hs : ∀ q ∈ tsupport f, q.1.1 ∈ X₀ ∧ q.1.2 ∈ Y₀ ∧ lam • q.2 ∈ F₀) :
    ForwardAmplitudeAdmissible X₀ Y₀ F₀ (modifiedAmplitude lam p f) := by
  refine ⟨(contDiff_modifiedAmplitude lam p hf).comp
    ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd), ?_⟩
  intro x y ξ hout
  by_cases hz : f ((x, y), lam⁻¹ • ξ) = 0
  · simp [modifiedAmplitude, physicalAmplitudeOfNormalized, hz]
  · have hm := hs ((x, y), lam⁻¹ • ξ) (subset_tsupport f hz)
    simp only [smul_smul, mul_inv_cancel₀ hlam, one_smul] at hm
    rcases hout with hx | hy | hξ
    · exact (hx hm.1).elim
    · exact (hy hm.2.1).elim
    · exact (hξ hm.2.2).elim

/-- Finite primitive expression jets imply the full source-symbol bound of
the actual order-`p` amplitude. The only extra reserve is the fixed `c`; the
derivative cost `k` changes no loss. This proves the low-calculus input for
`app:ch_response:eq:direct-envelope-profile`, including `p = -1`. -/
theorem hasFullSourceSymbolBound_modifiedAmplitude
    {ι : Type*} (a : ι → Point n → Mat) (ha : ∀ i, ContDiff ℝ ∞ (a i))
    (e : AmplitudeExpression (Point n) Mat ι)
    (Pj : ι → ℕ → ℝ) (hPj : ∀ i j, 0 ≤ Pj i j)
    (c Rstar k : ℕ) (hRstar : c + 2 < Rstar) (hcost : e.derivativeCost ≤ k)
    {L lam b : ℝ} (hL : 1 ≤ L) (hlam : 1 ≤ lam) (hb : 0 ≤ b) (p : ℤ)
    (hj : ∀ i j, j ≤ c + k → ∀ q,
      ‖iteratedFDeriv ℝ j (a i) q‖ ≤ Pj i j * L ^ (j + 2 - Rstar))
    (hs : ∀ q ∈ tsupport (e.evaluate a), ‖q.2‖ ≤ b) :
    HasFullSourceSymbolBound (modifiedAmplitude lam p (e.evaluate a)) c
      (((1 + b) ^ c * e.lowJetConstant Pj c) * lam ^ p * L ^ k) := by
  have hlampos : 0 < lam := zero_lt_one.trans_le hlam
  have hp : 0 ≤ lam ^ p := (zpow_pos hlampos p).le
  have he := e.contDiff_evaluate a ha
  have hs' : ∀ q ∈ tsupport ((lam ^ p) • e.evaluate a), ‖q.2‖ ≤ b :=
    fun q hq ↦ hs q (tsupport_smul_subset_right (fun _ ↦ lam ^ p) (e.evaluate a) hq)
  have h := hasFullSourceSymbolBound_of_normalized_jets
    (contDiff_modifiedAmplitude lam p he) hlam hb
    (mul_nonneg hp (mul_nonneg (e.lowJetConstant_nonneg Pj hPj c)
      (pow_nonneg (zero_le_one.trans hL) k))) c
    (support_physicalAmplitudeOfNormalized hlampos hs')
    (fun j hjc q ↦ by
      rw [normalizedField_modifiedAmplitude hlampos.ne' p,
        iteratedFDeriv_const_smul_apply (he.of_le (by simp)).contDiffAt,
        norm_smul, Real.norm_of_nonneg hp]
      exact mul_le_mul_of_nonneg_left
        (e.norm_lowJet_evaluate_le Pj hPj c Rstar k hRstar hcost L hL a ha hj j hjc q) hp)
  convert h using 1
  ring

/-- The order-minus-one specialization keeps the physical gain `lam⁻¹` in the
full source-symbol budget (`app:ch_response:eq:direct-envelope-profile`). -/
theorem modifiedAmplitude_neg_one (lam : ℝ) (f : Point n → Mat) :
    modifiedAmplitude lam (-1) f = physicalAmplitudeOfNormalized lam (lam⁻¹ • f) := by
  simp [modifiedAmplitude]

end JanetCartan.ResponseTransfer.DirectEvolution.ModifiedLow
