module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.PhysicalShells.Comparable.Estimates

/-!
# Primitive grades for the independent physical cutoff pairs

This packages only bounds on the original symbol and cutoffs for the consumer
`exists_physical_comparable_pair_constants`. Quantitative frequency-cutoff
profiles and normalized support bounds are supplied by
`jc-graph-physical-cutoff-geometry`; the actual full-symbol and input-mask
profiles are supplied by the parent graph factor construction. No bound on a
composed amplitude or kernel is an input (`app:ch_regular:eq:high-amplitude`).
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.PhysicalShells.Comparable
open FourierIntegral KernelEstimates
variable {n r : ℕ}

/-- Package primitive factor estimates for the physical full symbol, leaving
its two positions and physical frequency argument unchanged. The zero output
mask is supplied here; the actual complementary output is handled by the
buffered output-jet estimate (`app:ch_regular:eq:chain-tail`). -/
theorem hasAmplitudeGrades_of_factor_bounds
    {ρ S L : ℝ} (hL : 0 ≤ L) {D : AmplitudeProfiles}
    {A : FullAmplitude n r} {mi : LocalizerSymbol n}
    {χA χo : Euclidean n → ℝ} (y : Euclidean n)
    {K : Set (JointVariables (Euclidean n))}
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : ContDiff ℝ ∞ mi)
    (hg : ContDiff ℝ ∞ χA) (ho : ContDiff ℝ ∞ χo)
    (hsymbol : ∀ j p, p ∈ K →
      ‖iteratedFDeriv ℝ j (fun p : JointVariables (Euclidean n) =>
        A p.1.1 p.1.2 (ρ • p.2.1)) p‖ ≤ S * D.symbol j * L ^ (j + D.symbolOffset))
    (hgraph : ∀ j p, p ∈ K →
      ‖iteratedFDeriv ℝ j (fun p : JointVariables (Euclidean n) =>
        (χA (ρ • p.2.1) : ℂ)) p‖ ≤ D.graphCutoff j * L ^ (j + D.graphCutoffOffset))
    (hout : ∀ j p, p ∈ K →
      ‖iteratedFDeriv ℝ j (fun p : JointVariables (Euclidean n) =>
        (χo (ρ • p.2.2.2) : ℂ)) p‖ ≤ D.outputCutoff j * L ^ (j + D.outputCutoffOffset))
    (hin : ∀ j p, p ∈ K →
      ‖iteratedFDeriv ℝ j (fun p : JointVariables (Euclidean n) =>
        (mi (y, p.2.2.1) : ℂ)) p‖ ≤ D.inputMask j * L ^ (j + D.inputMaskOffset)) :
    HasAmplitudeGrades D ρ S L A mi (fun _ => 0) χA χo 0 y K where
  symbol_smooth := hA.comp (contDiff_fst.prodMk (contDiff_snd.fst.const_smul ρ))
  graphCutoff_smooth := Complex.ofRealCLM.contDiff.comp
    (hg.comp (contDiff_snd.fst.const_smul ρ))
  outputCutoff_smooth := Complex.ofRealCLM.contDiff.comp
    (ho.comp (contDiff_snd.snd.snd.const_smul ρ))
  inputMask_smooth := Complex.ofRealCLM.contDiff.comp
    (hi.comp (contDiff_const.prodMk contDiff_snd.snd.fst))
  outputMask_smooth := contDiff_const
  symbol_bound := hsymbol
  graphCutoff_bound := hgraph
  outputCutoff_bound := hout
  inputMask_bound := hin
  outputMask_bound := by
    intro j p _
    simp only [Complex.ofReal_zero, iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
    exact mul_nonneg (D.outputMask_nonneg j) (pow_nonneg hL _)

end JanetCartan.FiniteChain.Graph.PhysicalShells.Comparable
