module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.LowBounds.FrequencyCutoff.Basic
public import JanetCartan.Analysis.Microlocal.FourierIntegral.NormalAmplitude.Smooth

/-!
# Uniform normalized scalar cutoff jets

These are the scalar factors in the primitive amplitude jets for
`app:ch_regular_base:eq:actual-normal-amplitude`, actual-calculus Step 1.
The source-frequency comparison is supplied by `CutoffJets.Range`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.LowBounds
open FrequencyCutoff
variable {n : ℕ}
local notation "E" => Euclidean n

private theorem normalized_cutoff_jet_le (k : ℕ) {C Q ρ : ℝ}
    (hQ : 0 ≤ Q) (hρ : 0 ≤ ρ)
    (hbound : ∀ j (u : E),
      ‖iteratedFDeriv ℝ k (physicalCutoff j) u‖ * (1 + ‖u‖)^k ≤ C)
    (j : ℕ) (z : NormalVariables n) (hz : ρ ≤ Q * (1 + ‖ρ • z.2.2‖)) :
    ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
      complexPhysicalCutoff j (ρ • q.2.2)) z‖ ≤ C * Q^k := by
  let P : NormalVariables n →L[ℝ] E :=
    (ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E × E))
  let f : E → ℂ := fun u ↦ complexPhysicalCutoff j (ρ • u)
  have hf : ContDiff ℝ ∞ f := (complexPhysicalCutoff_contDiff j).comp
    (contDiff_id.const_smul ρ)
  have hp (v : NormalVariables n) : ‖P v‖ ≤ ‖v‖ :=
    (norm_snd_le v.2).trans (norm_snd_le v)
  have hproj : ‖iteratedFDeriv ℝ k (f ∘ P) z‖ ≤ ‖iteratedFDeriv ℝ k f (P z)‖ := by
    rw [P.iteratedFDeriv_comp_right hf z (by simp)]
    apply ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _)
    intro v
    simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    apply (ContinuousMultilinearMap.le_opNorm _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hp (v i))
  apply hproj.trans
  change ‖iteratedFDeriv ℝ k (fun u : E ↦ complexPhysicalCutoff j (ρ • u)) z.2.2‖ ≤ _
  rw [iteratedFDeriv_comp_const_smul ρ ((complexPhysicalCutoff_contDiff j).of_le (by simp)),
    norm_smul, Real.norm_of_nonneg (pow_nonneg hρ _)]
  have he : ‖iteratedFDeriv ℝ k (complexPhysicalCutoff (n := n) j) (ρ • z.2.2)‖ =
      ‖iteratedFDeriv ℝ k (physicalCutoff j) (ρ • z.2.2)‖ :=
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left (physicalCutoff_contDiff j).contDiffAt (by simp)
  rw [he]
  calc
    _ ≤ (Q * (1 + ‖ρ • z.2.2‖))^k *
        ‖iteratedFDeriv ℝ k (physicalCutoff j) (ρ • z.2.2)‖ := by gcongr
    _ = (‖iteratedFDeriv ℝ k (physicalCutoff j) (ρ • z.2.2)‖ *
        (1 + ‖ρ • z.2.2‖)^k) * Q^k := by rw [mul_pow]; ring
    _ ≤ C * Q^k := mul_le_mul_of_nonneg_right (hbound j _) (pow_nonneg hQ _)

/-- A single constant controls all scalar cutoff jets up to the fixed reserve,
for every cutoff index and every normalized source point obeying the frequency
comparison. The consumer is the bilinear primitive amplitude estimate in
actual-calculus Step 1, `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem exists_normalizedCutoff_jet_bound (N : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C > 0, ∀ (ρ : ℝ), 0 ≤ ρ → ∀ (j : ℕ) (z : NormalVariables n),
      ρ ≤ Q * (1 + ‖ρ • z.2.2‖) → ∀ k ≤ N,
      ‖iteratedFDeriv ℝ k (fun q : NormalVariables n ↦
        complexPhysicalCutoff j (ρ • q.2.2)) z‖ ≤ C := by
  choose B hB hbound using (physicalCutoff_uniform_symbol_bound (n := n))
  let C := 1 + (∑ i ∈ Finset.range (N + 1), B i) * (max 1 Q)^N
  have hsum : 0 ≤ ∑ i ∈ Finset.range (N + 1), B i :=
    Finset.sum_nonneg (fun i _ ↦ hB i)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ρ hρ j z hz k hk
  apply (normalized_cutoff_jet_le k hQ hρ (hbound k) j z hz).trans
  have hb : B k ≤ ∑ i ∈ Finset.range (N + 1), B i :=
    Finset.single_le_sum (fun i _ ↦ hB i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hp : Q^k ≤ (max 1 Q)^N :=
    (pow_le_pow_left₀ hQ (le_max_right _ _) k).trans
      (pow_le_pow_right₀ (le_max_left _ _) hk)
  have hh := mul_le_mul hb hp (pow_nonneg hQ k) hsum
  dsimp [C]
  linarith

end JanetCartan.FourierIntegral.LowBounds
