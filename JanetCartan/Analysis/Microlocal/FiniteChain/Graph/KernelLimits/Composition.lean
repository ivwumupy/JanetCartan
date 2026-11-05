module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Fubini

/-!
# Literal regularized compositions

Expansion of the actual operators in `app:ch_regular:eq:joint-kernel-phase`.
The right symbol is expressed in physical covectors; substituting
`mi (y, ρ⁻¹ • η)` recovers the proof localizer. Matrix actions pass through
integrals only after absolute integrability has been proved from its carriers.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}
attribute [local instance] sourceSymbolContinuousENorm sourceSymbolPseudoMetrizableSpace
set_option synthInstance.maxSize 256
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-- A matrix acts inside both integrals of the actual right localizer. The
primitive input support proves the required integrability, including the source
shoulders (`app:ch_regular:eq:joint-kernel-phase`). -/
theorem rightLocalizer_matrix_action
    (A : FullAmplitude n r) (mi : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo) (hi : Continuous mi)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f)
    (M : Matrix (Fin r) (Fin r) ℂ) (z : Euclidean n) :
    M.mulVec (rightLocalizer 1 mi f z) = ((2 * Real.pi) ^ n : ℂ)⁻¹ •
      ∫ η, ∫ y, (graphOscillation (fun a b => inner ℝ a b) z y η *
        (mi (y, η) : ℂ)) • M.mulVec (f y) := by
  change Euclidean n × Euclidean n → ℝ at mi
  let F : Euclidean n × Euclidean n → Fin r → ℂ := fun p =>
    (graphOscillation (fun a b => inner ℝ a b) z p.2 p.1 *
      (mi (p.2, p.1) : ℂ)) • f p.2
  have hcont : Continuous F := by
    change Continuous (mi : Euclidean n × Euclidean n → ℝ) at hi
    unfold F graphOscillation
    fun_prop
  have hs : HasCompactSupport F := by
    apply HasCompactSupport.intro (c.compact_inputFrequency.prod c.compact_inputBase)
    intro p hp
    have hm := c.input_zero p.2 p.1 (fun h => hp ⟨h.2, h.1⟩)
    simp [F, hm]
  have hint : Integrable F (volume.prod volume) := hcont.integrable_of_hasCompactSupport hs
  have hinner (η : Euclidean n) : Integrable (fun y => F (η, y)) := by
    apply (hcont.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    apply HasCompactSupport.intro c.compact_inputBase
    intro y hy
    have hm := c.input_zero y η (fun h => hy h.1)
    simp [F, hm]
  let L := sourceMatrixAction (r := r) M
  have houter := (L.integral_comp_comm hint.integral_prod_left).symm
  have hinner' (η : Euclidean n) := (L.integral_comp_comm (hinner η)).symm
  simp only [rightLocalizer, graphOperator, inv_one, one_smul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul]
  congr 1
  change L (∫ η, ∫ y, F (η, y)) = _
  rw [houter]
  simp_rw [hinner']
  simp only [F, map_smul]
  rfl

/-- Exact forward composition with the regularized complementary left symbol,
in the literal operator integration order. The phase and full matrix amplitude
are exactly those of `app:ch_regular:eq:joint-kernel-phase`. Repacking the
integrals as `regularizedJointKernel` is a separate Fubini step. -/
theorem forward_composition_iterated (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo) (hi : Continuous mi)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n) :
    leftLocalizer 1 (fun q => χo q.2 * (1 - mo q))
      (graphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ)
        (rightLocalizer 1 mi f)) x =
      jointNormalization n • ∫ ζ, ∫ u, ∫ ξ, ∫ z, ∫ η, ∫ y,
        (regularizedJointIntegrand false S A mi mo χA χo x y
          ((u, z), (ξ, η, ζ))).mulVec (f y) := by
  simp only [leftLocalizer, graphOperator, inv_one, one_smul, Matrix.smul_mulVec,
    Matrix.one_mulVec, rightLocalizer_matrix_action A mi χA χo c hi f hf]
  simp only [regularizedJointIntegrand, jointPhase, Bool.false_eq_true, ite_false,
    regularizedJointAmplitude, Matrix.smul_mulVec,
    ← forward_oscillation_product, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  simp_rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with ζ
  apply integral_congr_ae
  filter_upwards [] with u
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_smul, jointNormalization_eq_cube]
  congr 1
  ring
/-- Exact literal reverse composition, preserving the original amplitude
positions and the identity part of the output symbol
(`app:ch_regular:eq:joint-kernel-phase`). -/
theorem reverse_composition_iterated (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (c : RegularizedCarriers A mi χA χo) (hi : Continuous mi)
    (f : Euclidean n → Fin r → ℂ) (hf : Continuous f) (x : Euclidean n) :
    leftLocalizer 1 (fun q => χo q.2 * (1 - mo q))
      (reverseGraphOperator S (fun u z ξ => (χA ξ : ℂ) • A u z ξ)
        (rightLocalizer 1 mi f)) x =
      jointNormalization n • ∫ ζ, ∫ z, ∫ ξ, ∫ u, ∫ η, ∫ y,
        (regularizedJointIntegrand true S A mi mo χA χo x y
          ((u, z), (ξ, η, ζ))).mulVec (f y) := by
  simp only [leftLocalizer, graphOperator, reverseGraphOperator, inv_one, one_smul, Matrix.smul_mulVec,
    Matrix.one_mulVec, rightLocalizer_matrix_action A mi χA χo c hi f hf]
  simp only [regularizedJointIntegrand, jointPhase, ite_true,
    regularizedJointAmplitude, Matrix.smul_mulVec,
    ← reverse_oscillation_product, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  simp_rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with ζ
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with ξ
  apply integral_congr_ae
  filter_upwards [] with u
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [smul_smul, jointNormalization_eq_cube]
  congr 1
  ring
end JanetCartan.FiniteChain.Graph.KernelLimits
