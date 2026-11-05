module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.CoefficientJets

/-!
# Primitive normal shell inputs from coordinate symbol bounds

This is the amplitude-field producer for
`LowBounds.exists_graphL2_of_primitive_inputs`, used coefficient by coefficient
in `app:ch_regular_base:thm:actual-calculus`, Step 1. Only the original geometric
fields of `PrimitiveNormalShellInputs` are assumed. The original amplitude's
smoothness and coordinate symbol bound supply its smooth input array and both
normalized multilinear jet fields.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open SourceExpansion LowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ

/-- Instantiate the actual primitive shell interface from original coordinate
symbol jets. The geometry producer supplies inverse and Jacobian smoothness,
range, gap and finite jets on the entire shell, together with the scale
comparison on its inverse range. No amplitude shell jet is assumed.
Consumer: `LowBounds.exists_graphL2_of_primitive_inputs` for each actual
`matrixCoefficient`; source: `app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem primitiveNormalShellInputs_of_coefficientSymbolBound
    (a : E → E → Mat) (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (η : E → E → E → E) (J : E → E → E → E →L[ℝ] E)
    {N : ℕ} {B ρ c M L δ : ℝ} (hb : HasCoefficientSymbolBound a N B)
    (hρ : 0 ≤ ρ) (hc : 1 ≤ c) (U V : Set (NormalVariables n))
    (hU : IsOpen U) (hV : IsOpen V)
    (hη : ContDiffOn ℝ ∞ (normalInverseCoordinates (normalizedNormalInverse ρ η)) U)
    (hmap : MapsTo (normalInverseCoordinates (normalizedNormalInverse ρ η)) U V)
    (hJ : ContDiffOn ℝ ∞
      (fun q : NormalVariables n ↦ normalizedNormalJacobian ρ J q.1 q.2.1 q.2.2) V)
    (hgap : ∀ z ∈ V, δ ≤ |(normalizedNormalJacobian ρ J z.1 z.2.1 z.2.2).det|)
    (hJjet : ∀ z ∈ V, ∀ i ≤ N, ‖iteratedFDeriv ℝ i
      (fun q : NormalVariables n ↦ normalizedNormalJacobian ρ J q.1 q.2.1 q.2.2) z‖ ≤ M)
    (hηjet : ∀ z ∈ U, ∀ i, 1 ≤ i → i ≤ N → ‖iteratedFDeriv ℝ i
      (normalInverseCoordinates (normalizedNormalInverse ρ η)) z‖ ≤ L)
    (hscale : ∀ z ∈ V, ρ ≤ c * (1 + ‖ρ • z.2.2‖)) :
    PrimitiveNormalShellInputs a a η J ρ N M L δ
      (normalizedCoefficientJetConstant n N c * B)
      (normalizedCoefficientJetConstant n N c * B) U V := by
  have hl : ContDiff ℝ ∞ (fun q : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 a q.1 q.2.2) := by
    simpa only [normalizedNormalMatrix, neg_zero, Real.rpow_zero, one_smul,
      Function.comp_def, Function.uncurry_def] using
      ha.comp (contDiff_fst.prodMk (contDiff_snd.snd.const_smul ρ))
  have hr : ContDiff ℝ ∞ (fun q : NormalVariables n ↦
      normalizedNormalMatrix ρ 0 a q.2.1 q.2.2) := by
    simpa only [normalizedNormalMatrix, neg_zero, Real.rpow_zero, one_smul,
      Function.comp_def, Function.uncurry_def] using
      ha.comp (contDiff_snd.fst.prodMk (contDiff_snd.snd.const_smul ρ))
  exact
    { open_domain := hU
      open_range := hV
      inverse_smooth := hη
      mapsTo := hmap
      input_smooth := hJ.prodMk (hl.contDiffOn.prodMk hr.contDiffOn)
      gap := hgap
      jacobianJets := hJjet
      leftJets := fun z hz i hi ↦ (normalized_coefficient_jets_le ha hb hρ hc z (hscale z hz) hi).1
      rightJets := fun z hz i hi ↦ (normalized_coefficient_jets_le ha hb hρ hc z (hscale z hz) hi).2
      inverseJets := hηjet }

end JanetCartan.FourierIntegral.FullLowBounds
