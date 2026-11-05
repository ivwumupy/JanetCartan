module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FourierReconstruction.Compact
/-!
# Compact graph reconstruction on low-support L² envelopes

The literal forward and reverse graph formulas in
`app:ch_response:thm:response-literal-transfer`, packaged together with absolute
integrability in both physical frequency variables. Complementary selectors
preserve all amplitude cutoffs and the compact source-frequency support.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.LowEnvelope
open JanetCartan.Localization FourierIntegral
variable {n r : ℕ}
private theorem compact_source_slice {a : Euclidean n × Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hc : HasCompactSupport a) (η : Euclidean n) : HasCompactSupport (fun y ↦ a (η, y)) :=
  HasCompactSupport.of_support_subset_isCompact (hc.image continuous_snd) (by
    intro y hy
    exact ⟨(η, y), subset_tsupport _ hy, rfl⟩)

/-- Full compact-frequency forward reconstruction and joint Fourier integrability
for `app:ch_response:thm:response-literal-transfer`. No physical L¹ hypothesis. -/
theorem compact_forward_lowSupport_reconstruction
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ζ : Euclidean n) (ρ : ℝ) (x : Euclidean n) (hS : Continuous (S x))
    (ha : Continuous (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1))
    (hc : HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      (sourceKernel (forwardSourcePhase S ζ ρ x p.1 p.2) A x p.1).mulVec
        (paperL2FourierTransform f p.2)) (volume.prod volume) ∧
    graphOperator S A (fun y ↦ carrier ρ (fun z ↦ inner ℝ z ζ) y • ⇑(f y)) x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (forwardSourcePhase S ζ ρ x η θ) A x η).mulVec
          (paperL2FourierTransform f θ) := by
  refine ⟨integrable_sourceKernel_mulVec A x ha hc (forwardSourcePhase S ζ ρ x) ?_
    (paperL2FourierTransform_lowSupport_L1 f hΛ hs).1, ?_⟩
  · unfold forwardSourcePhase
    exact (hS.comp (continuous_fst.comp continuous_fst)).sub (by fun_prop)
  · exact graphOperator_lowSupport_reconstruction S A ζ ρ x
      (fun η ↦ ha.comp (continuous_const.prodMk continuous_id))
      (compact_source_slice hc) f hΛ hs

/-- Full compact-frequency reverse reconstruction for an arbitrary full amplitude,
including `complementaryAmplitude (reverseFullAmplitude ...)`. This is the literal
reverse integral in `app:ch_response:thm:response-literal-transfer`. -/
theorem compact_reverse_lowSupport_reconstruction
    (S : Euclidean n → Euclidean n → ℝ) (hS : Continuous (Function.uncurry S))
    (A : FullAmplitude n r) (φ : Euclidean n → ℝ) (hφ : Continuous φ)
    (ρ : ℝ) (y : Euclidean n)
    (ha : Continuous (fun p : Euclidean n × Euclidean n ↦ A y p.2 p.1))
    (hc : HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A y p.2 p.1))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      (sourceKernel (reverseSourcePhase S φ ρ y p.1 p.2) A y p.1).mulVec
        (paperL2FourierTransform f p.2)) (volume.prod volume) ∧
    (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
      star (graphOscillation S x y η) • (A y x η).mulVec (carrier ρ φ x • ⇑(f x))) =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (reverseSourcePhase S φ ρ y η θ) A y η).mulVec
          (paperL2FourierTransform f θ) := by
  refine ⟨integrable_sourceKernel_mulVec A y ha hc (reverseSourcePhase S φ ρ y) ?_
    (paperL2FourierTransform_lowSupport_L1 f hΛ hs).1, ?_⟩
  · unfold reverseSourcePhase
    have hSc : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦ S p.1.2 p.1.1) :=
      hS.comp ((continuous_snd.comp continuous_fst).prodMk
        (continuous_fst.comp continuous_fst))
    exact ((by fun_prop : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      inner ℝ y p.1.1)).sub hSc |>.add
      (continuous_const.mul (hφ.comp (continuous_snd.comp continuous_fst)))).add (by fun_prop)
  · exact reverseGraph_lowSupport_reconstruction S A φ hφ ρ y
      (fun η ↦ hS.comp (continuous_id.prodMk continuous_const))
      (fun η ↦ ha.comp (continuous_const.prodMk continuous_id))
      (compact_source_slice hc) f hΛ hs

/-- The complete complement retains compact full source-frequency support.
This supplies the amplitude hypotheses of both compact reconstruction theorems
in `app:ch_response:thm:response-literal-transfer`, without dropping any cutoff. -/
theorem complementaryAmplitude_compact_sourceFrequency
    (A : FullAmplitude n r) (ζ : Euclidean n) (ρ : ℝ)
    (q : Euclidean n → ℂ) (hq : Continuous q) (x : Euclidean n)
    (ha : Continuous (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1))
    (hc : HasCompactSupport (fun p : Euclidean n × Euclidean n ↦ A x p.2 p.1)) :
    Continuous (fun p : Euclidean n × Euclidean n ↦
      complementaryAmplitude A ζ ρ q x p.2 p.1) ∧
    HasCompactSupport (fun p : Euclidean n × Euclidean n ↦
      complementaryAmplitude A ζ ρ q x p.2 p.1) := by
  constructor
  · exact (continuous_const.sub (hq.comp (continuous_fst.sub continuous_const))).smul ha
  · exact hc.smul_left (f := fun p : Euclidean n × Euclidean n ↦ 1 - q (p.1 - ρ • ζ))
end JanetCartan.ResponseTransfer.LowEnvelope
