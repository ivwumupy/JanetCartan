module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphDecay.Grades
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Assembly.Costs

/-!
# Removing the fixed frequency normalization in the same graph

These exact identities and Sobolev estimates connect the normalized branch
estimates to the actual Leibniz terms of
`app:ch_response:thm:response-literal-transfer`. They preserve the physical
`(2π)^(-n)` integral and both positions of the weighted reverse amplitude.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open FourierIntegral Pseudodifferential LowEnvelope ArbitraryAccuracy MixedGrades
variable {n r : ℕ} {P ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Frequency normalization commutes with the literal forward graph integral,
including its two original carriers. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem forwardDemodulatedGraph_normalizedCarrierJet
    (S : E → E → ℝ) (φ : E → ℝ) (A : FullAmplitude n r)
    (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ)
    (ρ : ℝ) (k : ℕ) (v : Fin k → P) (c : P) (f : E → Fin r → ℂ) (x : E) :
    forwardDemodulatedGraph S φ (normalizedComplementaryCarrierJet A q ζ ψ ρ k v c)
      (ζ c) ρ f x =
    (ρ ^ (2 * k))⁻¹ • forwardDemodulatedGraph S φ
      (complementaryCarrierJet A q ζ ψ ρ k v c) (ζ c) ρ f x := by
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inv, Complex.ofReal_pow]
  simp only [forwardDemodulatedGraph, normalizedComplementaryCarrierJet, graphOperator,
    Matrix.smul_mulVec]
  simp_rw [smul_comm (graphOscillation S _ _ _) (((ρ : ℂ) ^ (2 * k))⁻¹), integral_smul]
  simp only [smul_comm _ (((ρ : ℂ) ^ (2 * k))⁻¹)]

/-- The same normalization identity for the complete weighted reverse graph.
`A` keeps its output/source order and may contain the literal `j_S U⁻¹`.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem reverseDemodulatedGraph_normalizedCarrierJet
    (S : E → E → ℝ) (φ : E → ℝ) (A : FullAmplitude n r)
    (q : E → ℂ) (ζ : P → E) (ψ : P → E → E → ℝ)
    (ρ : ℝ) (k : ℕ) (v : Fin k → P) (c : P) (f : E → Fin r → ℂ) (x : E) :
    reverseDemodulatedGraph S φ (normalizedComplementaryCarrierJet A q ζ ψ ρ k v c)
      (ζ c) ρ f x =
    (ρ ^ (2 * k))⁻¹ • reverseDemodulatedGraph S φ
      (complementaryCarrierJet A q ζ ψ ρ k v c) (ζ c) ρ f x := by
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_inv, Complex.ofReal_pow]
  simp only [reverseDemodulatedGraph, normalizedComplementaryCarrierJet,
    ReverseDerivative.reverseGraph, Matrix.smul_mulVec]
  simp_rw [smul_comm (star (graphOscillation S _ _ _)) (((ρ : ℂ) ^ (2 * k))⁻¹), integral_smul]
  simp only [smul_comm _ (((ρ : ℂ) ^ (2 * k))⁻¹)]

/-- Exact real scalar homogeneity on the original vector Fourier Sobolev
space, used only for the fixed frequency normalization of the parameter
branches. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem vectorFourierSobolevNorm_parameter_real_smul (s : ℕ) (a : ℝ) {f : H}
    (hf : MemVectorFourierSobolev (s : ℝ) f) :
    MemVectorFourierSobolev (s : ℝ) (a • f) ∧
      vectorFourierSobolevNorm (s : ℝ) (a • f) = |a| * vectorFourierSobolevNorm (s : ℝ) f := by
  let G : GradedScale H := vectorFourierSobolevScale
  have hsm : a • f ∈ G.level s := (G.level s).smul_mem a hf
  refine ⟨hsm, ?_⟩
  rw [← vectorFourierSobolevScale_gradeNorm s hsm, ← vectorFourierSobolevScale_gradeNorm s hf]
  change G.gradeNorm s (a • f) = |a| * G.gradeNorm s f
  rw [G.gradeNorm_eq hsm, G.gradeNorm_eq hf]
  exact (map_smul_eq_mul (G.seminorm s) a (⟨f, hf⟩ : G.level s)).trans
    (by rw [Real.norm_eq_abs])

/-- Normalizing the actual branch only decreases its fixed all-input Sobolev
cost when `ρ ≥ 1`. Thus the normalized graph theorem needs no new analytic
premise about the normalized operator.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem normalizedCarrierJet_sobolev_cost (T : H →L[ℂ] H)
    (s t k : ℕ) {ρ D d : ℝ} (hρ : 1 ≤ ρ)
    (hT : ∀ f, MemVectorFourierSobolev (t : ℝ) f →
      MemVectorFourierSobolev (s : ℝ) (T f) ∧
      vectorFourierSobolevNorm (s : ℝ) (T f) ≤
        D * ρ ^ d * vectorFourierSobolevNorm (t : ℝ) f) :
    ∀ f, MemVectorFourierSobolev (t : ℝ) f →
      MemVectorFourierSobolev (s : ℝ) (((ρ ^ (2 * k))⁻¹ • T) f) ∧
      vectorFourierSobolevNorm (s : ℝ) (((ρ ^ (2 * k))⁻¹ • T) f) ≤
        D * ρ ^ d * vectorFourierSobolevNorm (t : ℝ) f := by
  intro f hf
  obtain ⟨hmem, hb⟩ := hT f hf
  obtain ⟨hmem', he⟩ := vectorFourierSobolevNorm_parameter_real_smul s (ρ ^ (2 * k))⁻¹ hmem
  refine ⟨hmem', ?_⟩
  change vectorFourierSobolevNorm (s : ℝ) ((ρ ^ (2 * k))⁻¹ • T f) ≤ _
  rw [he, abs_of_nonneg (by positivity : 0 ≤ (ρ ^ (2 * k))⁻¹)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ (one_le_pow₀ hρ))).trans hb

/-- The fixed normalization loss is absorbed by greater internal precision.
The conclusion concerns the same original L² output, not a new envelope.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem rapidDecayAt_of_normalizedCarrierJet (f : ι → H) (ρ a : ι → ℝ) (s k : ℕ)
    (hρ : ∀ i, 0 < ρ i)
    (hf : RapidDecayAt vectorFourierSobolevScale s ρ a
      (fun i ↦ (ρ i ^ (2 * k))⁻¹ • f i)) :
    RapidDecayAt vectorFourierSobolevScale s ρ a f := by
  apply rapidDecayAt_polynomial_observation vectorFourierSobolevScale
    vectorFourierSobolevScale _ f ρ a s s 1 (2 * k) hρ zero_le_one hf
  intro i hm
  have he : ρ i ^ (2 * k) • ((ρ i ^ (2 * k))⁻¹ • f i) = f i :=
    smul_inv_smul₀ (pow_ne_zero _ (ne_of_gt (hρ i))) _
  obtain ⟨hmem, hn⟩ := vectorFourierSobolevNorm_parameter_real_smul s (ρ i ^ (2 * k)) hm
  rw [he] at hmem hn
  refine ⟨hmem, ?_⟩
  rw [vectorFourierSobolevScale_gradeNorm s hmem, vectorFourierSobolevScale_gradeNorm s hm,
    hn, abs_of_pos (pow_pos (hρ i) _), one_mul]
  rw [show (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) by norm_cast, Real.rpow_natCast]

end JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
