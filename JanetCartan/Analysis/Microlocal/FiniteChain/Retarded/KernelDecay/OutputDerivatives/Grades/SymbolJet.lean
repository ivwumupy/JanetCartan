module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Grades.MixedJets
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.KernelDecay.OutputDerivatives.Grades.Masks

/-!
# Grades for the residual output-symbol jet

The Fourier character has a fixed joint derivative profile on the compact
normalized output carrier. Its product with the complementary symbol retains
the identity term and all mixed derivatives (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
open scoped ContDiff
attribute [local fun_prop] ContDiff.inner
namespace JanetCartan.FiniteChain.Retarded.KernelDecay
open LocalizedKernel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The fixed Fourier character is jointly smooth in increment and normalized
covector, as used in `app:ch_regular:eq:chain-tail`. -/
theorem contDiff_outputJointWave :
    ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × E) => wave p.2 p.1) := by
  have hcoe : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  unfold wave pairing
  fun_prop

/-- The common compact normalized covector carrier gives a single all-order
profile for the fixed Fourier character. The constants precede all frequencies,
external bases, output directions and integration orders
(`app:ch_regular:lem:finite-chain`). -/
theorem exists_outputJointWave_profile {Ko : Set (ℝ × E)} (hKo : IsCompact Ko) :
    ∃ W : ℕ → ℝ, (∀ n, 0 ≤ W n) ∧ ∀ n ξ, ξ ∈ Ko →
      ‖iteratedFDeriv ℝ n (fun p : (ℝ × E) × (ℝ × E) => wave p.2 p.1) (0, ξ)‖ ≤ W n := by
  have hb n := hKo.exists_bound_of_continuousOn
    (((contDiff_outputJointWave (E := E)).iteratedFDeriv_right (m := ∞) (i := n) (by simp)).continuous.comp
      ((continuous_const (y := (0 : ℝ × E))).prodMk continuous_id)).continuousOn
  choose C hC using hb
  exact ⟨fun n => max 0 (C n), fun n => le_max_left _ _,
    fun n ξ hξ => (hC n ξ hξ).trans (le_max_right _ _)⟩

/-- The residual output jet appearing in the exact `ρ^m` factorization
(`app:ch_regular:eq:chain-tail`). -/
def rescaledOutputSymbolJet (ρ : ℝ) (mo : (ℝ × E) → (ℝ × E) → ℂ)
    (xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E) (ξ : ℝ × E) : ℂ :=
  iteratedFDeriv ℝ m (fun y => wave ξ y * (1 - mo (xo + ρ⁻¹ • y) (ρ • ξ))) 0 v

/-- Smoothness of the residual jet allows the existing Leibniz grade estimate
to be applied to its product with the output-independent amplitude
(`app:ch_regular:eq:chain-tail`). -/
theorem contDiff_rescaledOutputSymbolJet (ρ : ℝ)
    {mo : (ℝ × E) → (ℝ × E) → ℂ} (ho : ContDiff ℝ ∞ (Function.uncurry mo))
    (xo : ℝ × E) (m : ℕ) (v : Fin m → ℝ × E) :
    ContDiff ℝ ∞ (rescaledOutputSymbolJet ρ mo xo m v) := by
  have hs : ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × E) =>
      wave p.2 p.1 * (1 - mo (xo + ρ⁻¹ • p.1) (ρ • p.2))) := by
    apply contDiff_outputJointWave.mul
    apply contDiff_const.sub
    exact ho.comp (show ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × E) =>
      (xo + ρ⁻¹ • p.1, ρ • p.2)) from by fun_prop)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => ℝ × E) ℂ v).contDiff.comp
    ((contDiff_outputJet hs m).comp (contDiff_const.prodMk contDiff_id))

/-- A primitive joint output-symbol profile gives every frequency derivative
of the actual residual output jet. The complementary identity costs `1+O`,
and the fixed output order contributes the offset `m`, independently of the
integration order (`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem norm_iteratedFDeriv_rescaledOutputSymbolJet_le
    (ρ : ℝ) {mo : (ℝ × E) → (ℝ × E) → ℂ}
    (ho : ContDiff ℝ ∞ (Function.uncurry mo)) (xo : ℝ × E)
    {W O : ℕ → ℝ} (hW : ∀ j, 0 ≤ W j) (hO : ∀ j, 0 ≤ O j)
    {S L : ℝ} (hS : 1 ≤ S) (hL : 1 ≤ L) (bo m j : ℕ)
    (v : Fin m → ℝ × E) (hv : ∀ i, ‖v i‖ ≤ 1) (ξ : ℝ × E)
    (hw : ∀ k, ‖iteratedFDeriv ℝ k
      (fun p : (ℝ × E) × (ℝ × E) => wave p.2 p.1) (0, ξ)‖ ≤ W k)
    (hb : ∀ k, ‖iteratedFDeriv ℝ k (fun p : (ℝ × E) × (ℝ × E) =>
      mo (xo + ρ⁻¹ • p.1) (ρ • p.2)) (0, ξ)‖ ≤ S * O k * L ^ (k + bo)) :
    ‖iteratedFDeriv ℝ j (rescaledOutputSymbolJet ρ mo xo m v) ξ‖ ≤
      S * derivativeConvolution W (fun k => 1 + O k) (m + j) * L ^ (j + (m + bo)) := by
  let o : (ℝ × E) × (ℝ × E) → ℂ := fun p => mo (xo + ρ⁻¹ • p.1) (ρ • p.2)
  have hso : ContDiff ℝ ∞ o := ho.comp (show ContDiff ℝ ∞ (fun p : (ℝ × E) × (ℝ × E) =>
      (xo + ρ⁻¹ • p.1, ρ • p.2)) from by fun_prop)
  have hs := contDiff_outputJointWave.mul ((contDiff_const (c := (1 : ℂ))).sub hso)
  apply (norm_iteratedFDeriv_outputJet_apply_le hs m j v hv 0 ξ).trans
  have hw' k : ‖iteratedFDeriv ℝ k
      (fun p : (ℝ × E) × (ℝ × E) => wave p.2 p.1) (0, ξ)‖ ≤
      1 * W k * L ^ (k + 0) := by
    simpa using (hw k).trans (le_mul_of_one_le_right (hW k) (one_le_pow₀ hL))
  have hc k := norm_iteratedFDeriv_one_sub_le_grades hso hS hL bo (0, ξ) hb k
  have h := norm_iteratedFDeriv_mul_le_grades contDiff_outputJointWave
    (contDiff_const.sub hso) hW (fun k => by linarith [hO k])
    zero_le_one (zero_le_one.trans hS) (zero_le_one.trans hL) 0 bo (0, ξ) hw' hc (m + j)
  simpa only [one_mul, zero_add, Nat.add_assoc, Nat.add_comm m j] using h

end JanetCartan.FiniteChain.Retarded.KernelDecay
