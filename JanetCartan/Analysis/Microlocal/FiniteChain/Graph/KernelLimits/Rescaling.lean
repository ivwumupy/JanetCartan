module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Graph.KernelLimits.Integrability

/-!
# The three-frequency Jacobian

Exact change of variables for `app:ch_regular:eq:joint-kernel-phase`.
Only the three physical covectors are rescaled; the two amplitude positions
and the external source base remain unchanged.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.FiniteChain.Graph.KernelLimits
open FourierIntegral
variable {n r : ℕ}
attribute [local instance] matrixContinuousENorm matrixPseudoMetrizableSpace
set_option synthInstance.maxSize 256

local instance : (volume : Measure (Euclidean n × Euclidean n)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

local instance : (volume : Measure (Euclidean n × Euclidean n × Euclidean n)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure volume volume

/-- Three independent physical frequencies give the full `ρ^(3*n)` Jacobian
in `app:ch_regular:eq:joint-kernel-phase`. -/
theorem integral_frequencyTriple_rescale
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Euclidean n × Euclidean n × Euclidean n → F) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ ω, f ω) = ρ ^ (3 * n) • ∫ ω, f (ρ • ω) := by
  rw [Measure.integral_comp_smul_of_nonneg volume f ρ (hR := hρ.le), smul_smul]
  have hrank : Module.finrank ℝ (Euclidean n × Euclidean n × Euclidean n) = 3 * n := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    omega
  rw [hrank, mul_inv_cancel₀ (pow_ne_zero _ hρ.ne'), one_smul]

/-- The absolutely convergent regularized joint kernel equals the normalized
phase/amplitude formula with its exact Jacobian. This is the normalization step
of `app:ch_regular:eq:joint-kernel-phase`; composition and cutoff removal are
separate obligations. -/
theorem regularizedJointKernel_rescale (backward : Bool)
    (S φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (mi mo : LocalizerSymbol n) (χA χo : Euclidean n → ℝ)
    (x y : Euclidean n) {ρ : ℝ} (hρ : 0 < ρ)
    (hφ : ∀ u ξ, S u (ρ • ξ) = ρ * φ u ξ)
    (hS : Continuous (Function.uncurry S))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n =>
      A p.1.1 p.1.2 p.2)) (hi : Continuous mi) (ho : Continuous mo)
    (hg : Continuous χA) (hc : Continuous χo)
    (c : RegularizedCarriers A (fun q => mi (q.1, ρ⁻¹ • q.2)) χA χo) :
    regularizedJointKernel backward S A
      (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2)) χA χo x y =
      jointNormalization n • (ρ ^ (3 * n) •
        ∫ b : Euclidean n × Euclidean n, ∫ ω : Euclidean n × Euclidean n × Euclidean n,
          Complex.exp (Complex.I * ((ρ * jointPhase backward φ x y (b, ω) : ℝ) : ℂ)) •
            jointAmplitude ρ A mi mo χA χo x y (b, ω)) := by
  have hscale : Continuous (fun q : Euclidean n × Euclidean n => (q.1, ρ⁻¹ • q.2)) :=
    continuous_fst.prodMk (continuous_snd.const_smul ρ⁻¹)
  have hint := regularizedJointIntegrand_integrable backward S A
    (fun q => mi (q.1, ρ⁻¹ • q.2)) (fun q => mo (q.1, ρ⁻¹ • q.2)) χA χo
    hS hA (hi.comp hscale) (ho.comp hscale) hg hc c x y
  unfold regularizedJointKernel
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint]
  conv_lhs =>
    arg 2
    arg 2
    ext b
    rw [integral_frequencyTriple_rescale (n := n) _ hρ]
  rw [integral_smul]
  congr 2
  apply integral_congr_ae
  filter_upwards [] with b
  apply integral_congr_ae
  filter_upwards [] with ω
  unfold regularizedJointIntegrand
  rw [jointPhase_rescale backward S φ x y ρ (b, ω) (hφ _ _),
    regularizedJointAmplitude_rescale A mi mo χA χo x y hρ.ne' (b, ω)]

end JanetCartan.FiniteChain.Graph.KernelLimits
