module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.SupportedCalculus
public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Kernels
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Literal normalized forward and adjoint carrier kernels

The change `ξ = ρ θ` in `paper-v2.tex`, `app:ch_response:lem:energy-carrier-jets`.
The physical Fourier normalization, scaling Jacobian, both physical positions,
and matrix action are retained. The adjoint phase is the actual reversed phase.
These identities concern actual integral formulas, not strong limits.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer

open FourierIntegral

variable {n r : ℕ} {P F : Type}

/-- The literal reversed demodulated phase. The first integration component
is the original output position, now the adjoint source. Source:
`app:ch_response:lem:energy-carrier-jets`, adjoint version of `new:eq:carrier-ibp`. -/
def adjointCarrierPhase (Θ : Euclidean n → Euclidean n → ℝ)
    (φ : Euclidean n → P → ℝ) (q : Euclidean n × P)
    (w : CarrierVariables n) : ℝ :=
  inner ℝ q.1 w.snd - Θ w.fst w.snd + φ w.fst q.2 - φ q.1 q.2

/-- The adjoint reverses the original two-position phase, rather than
substituting a fixed-transverse retarded phase (`new:eq:carrier-ibp`). -/
theorem adjointCarrierPhase_eq_neg_swapped
    (Θ : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → P → ℝ)
    (q : Euclidean n × P) (w : CarrierVariables n) :
    adjointCarrierPhase Θ φ q w =
      -carrierPhase Θ φ (w.fst, q.2) (WithLp.toLp 2 (q.1, w.snd)) := by
  simp only [adjointCarrierPhase, carrierPhase, WithLp.toLp_fst, WithLp.toLp_snd]
  ring

/-- Exact carrier removal for the conjugated graph oscillation, retaining
the original source in the reversed phase (`new:eq:carrier-ibp`). -/
theorem demodulated_adjointGraphOscillation_eq
    (Θ : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → P → ℝ)
    (ρ : ℝ) (q : Euclidean n × P) (w : CarrierVariables n)
    (hΘ : Θ w.fst (ρ • w.snd) = ρ * Θ w.fst w.snd) :
    carrier (-ρ) (fun x ↦ φ x q.2) q.1 *
        star (graphOscillation Θ w.fst q.1 (ρ • w.snd)) *
        carrier ρ (fun z ↦ φ z q.2) w.fst =
      oscillation (adjointCarrierPhase Θ φ) ρ q w := by
  simp only [carrier, graphOscillation, oscillation, adjointCarrierPhase,
    hΘ, inner_smul_right, RCLike.star_def, ← Complex.exp_conj,
    map_mul, Complex.conj_I, Complex.conj_ofReal, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The physical frequency Jacobian in the carrier normalization. Its
exponent is the covector dimension, not the dimension of the joint variables.
Source: frequency localization before `new:eq:carrier-ibp`. -/
theorem integral_eq_frequency_rescale (h : Euclidean n → F) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ ξ, h ξ) = ρ ^ n • ∫ θ, h (ρ • θ) := by
  rw [Measure.integral_comp_smul_of_nonneg volume h ρ (hR := hρ.le)]
  simp [smul_smul, hρ.ne']

/-- The joint Hilbert-product volume is exactly the source/covector product
volume. The order is chosen to match the published physical graph kernels.
Source: the joint integral in `new:eq:carrier-ibp`. -/
theorem integral_joint_eq_frequency_source
    {g : CarrierVariables n → F} (hg : Integrable g) :
    (∫ w, g w) = ∫ θ : Euclidean n, ∫ z : Euclidean n, g (WithLp.toLp 2 (z, θ)) := by
  have hi := (WithLp.volume_preserving_toLp (Euclidean n) (Euclidean n)).integrable_comp
    hg.aestronglyMeasurable |>.mpr hg
  rw [← (WithLp.volume_preserving_toLp (Euclidean n) (Euclidean n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  rw [Measure.volume_eq_prod] at hi ⊢
  dsimp only [Function.comp_def] at hi
  rw [integral_prod _ hi, integral_integral_swap hi]

/-- Forward carrier removal and physical frequency rescaling of the actual
matrix kernel. `A` is the full amplitude, including the literal high-pass,
annular and physical masks. No mask is moved through the matrix action.
Source: frequency localization preceding `new:eq:carrier-ibp`. -/
theorem demodulated_graphOperator_eq_normalized
    (Θ : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → P → ℝ)
    (A : FullAmplitude n r) (a : Euclidean n → Fin r → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (q : Euclidean n × P)
    (hΘ : ∀ z θ, A q.1 z (ρ • θ) ≠ 0 → Θ q.1 (ρ • θ) = ρ * Θ q.1 θ) :
    carrier (-ρ) (fun x ↦ φ x q.2) q.1 •
        graphOperator Θ A (fun z ↦ carrier ρ (fun y ↦ φ y q.2) z • a z) q.1 =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • (ρ ^ n •
        ∫ θ : Euclidean n, ∫ z : Euclidean n,
          oscillation (carrierPhase Θ φ) ρ q (WithLp.toLp 2 (z, θ)) •
            (A q.1 z (ρ • θ)).mulVec (a z)) := by
  unfold graphOperator
  rw [smul_comm (carrier (-ρ) _ _) (((2 * Real.pi) ^ n : ℂ)⁻¹)]
  congr 1
  rw [integral_eq_frequency_rescale (ρ := ρ) _ hρ, smul_comm]
  congr 1
  simp_rw [← integral_smul, Matrix.mulVec_smul, ← smul_assoc]
  apply integral_congr_ae
  filter_upwards [] with θ
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : A q.1 z (ρ • θ) = 0
  · simp [hz]
  · have he := demodulated_graphOscillation_eq Θ φ ρ q (WithLp.toLp 2 (z, θ)) (hΘ z θ hz)
    simp only [WithLp.toLp_fst, WithLp.toLp_snd] at he
    simpa only [smul_eq_mul] using congrArg
      (fun c : ℂ ↦ c • (A q.1 z (ρ • θ)).mulVec (a z)) he

/-- The literal adjoint kernel has the exchanged conjugate-transposed full
amplitude and the actual reversed phase. The physical normalization and
frequency Jacobian are the same as in the forward identity.
Source: the adjoint case of `app:ch_response:lem:energy-carrier-jets`. -/
theorem demodulated_reverseGraphOperator_eq_normalized
    (Θ : Euclidean n → Euclidean n → ℝ) (φ : Euclidean n → P → ℝ)
    (A : FullAmplitude n r) (a : Euclidean n → Fin r → ℂ)
    {ρ : ℝ} (hρ : 0 < ρ) (q : Euclidean n × P)
    (hΘ : ∀ z θ, A z q.1 (ρ • θ) ≠ 0 → Θ z (ρ • θ) = ρ * Θ z θ) :
    carrier (-ρ) (fun x ↦ φ x q.2) q.1 •
        reverseGraphOperator Θ (fun x z ξ ↦ (A x z ξ).conjTranspose)
          (fun z ↦ carrier ρ (fun y ↦ φ y q.2) z • a z) q.1 =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • (ρ ^ n •
        ∫ θ : Euclidean n, ∫ z : Euclidean n,
          oscillation (adjointCarrierPhase Θ φ) ρ q (WithLp.toLp 2 (z, θ)) •
            (A z q.1 (ρ • θ)).conjTranspose.mulVec (a z)) := by
  unfold reverseGraphOperator
  rw [smul_comm (carrier (-ρ) _ _) (((2 * Real.pi) ^ n : ℂ)⁻¹)]
  congr 1
  rw [integral_eq_frequency_rescale (ρ := ρ) _ hρ, smul_comm]
  congr 1
  simp_rw [← integral_smul, Matrix.mulVec_smul, ← smul_assoc]
  apply integral_congr_ae
  filter_upwards [] with θ
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : A z q.1 (ρ • θ) = 0
  · simp [hz]
  · have he := demodulated_adjointGraphOscillation_eq Θ φ ρ q (WithLp.toLp 2 (z, θ)) (hΘ z θ hz)
    simp only [WithLp.toLp_fst, WithLp.toLp_snd] at he
    simpa only [smul_eq_mul] using congrArg
      (fun c : ℂ ↦ c • (A z q.1 (ρ • θ)).conjTranspose.mulVec (a z)) he

open RegularSector.Characteristic.EvolutionIntegral

/-- The actual elapsed-time amplitude after frequency normalization, with both
physical masks, the original high-pass `β`, and the annular mask `π` literal.
The time `r` is fixed throughout `new:eq:carrier-ibp`. -/
theorem normalized_elapsedAmplitude_with_annular_mask {d : ℕ}
    (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ)
    {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) (x z θ : Euclidean (d + 1)) :
    frequencyCutFullAmplitude (fun ξ ↦ π (ρ⁻¹ • ξ))
        (elapsedAmplitude b χout χsource β t) x z (ρ • θ) =
      (π θ * (χout x * χsource z * β (ρ • θ))) •
        b (x 0) (x 0 - t) (spatialPart x) (spatialPart (ρ • θ)) := by
  simp only [frequencyCutFullAmplitude, elapsedAmplitude, smul_smul,
    inv_mul_cancel₀ hρ, one_smul]

/-- The same full masks in the literal adjoint. Conjugation occurs once,
and the original output position `z` determines the two physical times.
Source: the adjoint version of `app:ch_response:lem:energy-carrier-jets`. -/
theorem normalized_adjoint_elapsedAmplitude_with_annular_mask {d : ℕ}
    (b : TwoTimeAmplitude d r)
    (χout χsource β π : Euclidean (d + 1) → ℂ)
    {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℝ) (x z θ : Euclidean (d + 1)) :
    (frequencyCutFullAmplitude (fun ξ ↦ π (ρ⁻¹ • ξ))
        (elapsedAmplitude b χout χsource β t) z x (ρ • θ)).conjTranspose =
      star (π θ * (χout z * χsource x * β (ρ • θ))) •
        (b (z 0) (z 0 - t) (spatialPart z) (spatialPart (ρ • θ))).conjTranspose := by
  rw [normalized_elapsedAmplitude_with_annular_mask b χout χsource β π hρ]
  simp only [Matrix.conjTranspose_smul]

end JanetCartan.ResponseTransfer.DirectEvolution.CompactTransfer
