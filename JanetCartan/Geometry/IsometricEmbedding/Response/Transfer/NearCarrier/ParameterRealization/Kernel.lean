module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ParameterPhase
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.Demodulation
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Parameter derivatives of the literal selected kernels

The first parameter step of `app:ch_response:eq:direct-envelope-profile`.
The operator phase and frequency are fixed. Only the carrier, the selector, and
the datum vary. Both positions of the full matrix amplitude are retained.
The reverse specialization therefore includes the literal `j_S U⁻¹` weight.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.NearCarrierParameter

open FourierIntegral

variable {n r : ℕ} {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The selected full amplitude at the physical shifted covector, for
`app:ch_response:eq:direct-envelope-profile`. The selector is normalized. -/
def selectedFamily (A : FullAmplitude n r) (q : P × Euclidean n → ℂ)
    (ζ : P → Euclidean n) (ρ : ℝ) (c : P) : FullAmplitude n r :=
  fun x y δ ↦ parameterSelectedAmplitude A q (fun _ ↦ x) (fun _ ↦ y)
    ζ (fun _ ↦ δ) ρ c

/-- The actual parameter amplitude derivative, including the selector term,
used in `app:ch_response:eq:direct-envelope-profile`. Neither physical position
is suppressed; only their parameter velocities are zero. -/
def selectedAmplitudeDifferential (A : FullAmplitude n r)
    (q : P × Euclidean n → ℂ) (ζ : P → Euclidean n) (ρ : ℝ) (c v : P) :
    FullAmplitude n r := fun x y δ ↦
  q (c, ρ⁻¹ • δ) •
      fderiv ℝ (fun z : Euclidean n × Euclidean n × Euclidean n ↦ A z.1 z.2.1 z.2.2)
        (x, y, ρ • ζ c + δ) (0, 0, ρ • fderiv ℝ ζ c v) +
    fderiv ℝ q (c, ρ⁻¹ • δ) (v, 0) • A x y (ρ • ζ c + δ)

/-- Specialization of the published amplitude chain rule to fixed physical
positions and frequency (`app:ch_response:eq:direct-envelope-profile`). -/
theorem hasLineDerivAt_selectedFamily
    (A : FullAmplitude n r) (q : P × Euclidean n → ℂ)
    (ζ : P → Euclidean n) (ρ : ℝ) (c v : P) (x y δ : Euclidean n)
    (hζ : DifferentiableAt ℝ ζ c)
    (hA : DifferentiableAt ℝ
      (fun z : Euclidean n × Euclidean n × Euclidean n ↦ A z.1 z.2.1 z.2.2)
      (x, y, ρ • ζ c + δ)) (hq : DifferentiableAt ℝ q (c, ρ⁻¹ • δ)) :
    HasLineDerivAt ℝ (fun a ↦ selectedFamily A q ζ ρ a x y δ)
      (selectedAmplitudeDifferential A q ζ ρ c v x y δ) c v := by
  have h := hasFDerivAt_parameterSelectedAmplitude A q (fun _ ↦ x) (fun _ ↦ y)
    ζ (fun _ ↦ δ) ρ c 0 0 (fderiv ℝ ζ c) 0 _ _
    (hasFDerivAt_const _ _) (hasFDerivAt_const _ _) hζ.hasFDerivAt
    (hasFDerivAt_const _ _) hA.hasFDerivAt hq.hasFDerivAt
  convert h.hasLineDerivAt v using 1
  · rfl
  · dsimp [selectedAmplitudeDifferential]
    simp only [add_zero]
    change _ = q (c, ρ⁻¹ • δ) •
        fderiv ℝ (fun z : Euclidean n × Euclidean n × Euclidean n ↦ A z.1 z.2.1 z.2.2)
          (x, y, ρ • ζ c + δ) (0, 0, ρ • fderiv ℝ ζ c v) +
      fderiv ℝ q (c, ρ⁻¹ • δ) (v, ρ⁻¹ • (0 : Euclidean n)) • A x y (ρ • ζ c + δ)
    rw [smul_zero]

/-- Coordinates of the already proved parameter phase coefficient. These are
the `C_l` multiplying datum derivatives in
`app:ch_response:eq:direct-envelope-profile`. -/
def phaseCoefficient (S : Euclidean n → Euclidean n → ℝ)
    (ζ : P → Euclidean n) (ρ : ℝ) (c v : P) (x δ : Euclidean n) (l : Fin n) : ℝ :=
  parameterPhaseCoefficient S ζ x (ρ⁻¹ • δ) c (EuclideanSpace.single l 1) v

/-- The physical displacement is expanded in the standard basis, so the
parameter phase derivative is exactly `∑ l, C_l δ_l`, with no extra `2π`.
Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem parameterPhaseCoefficient_eq_sum
    (S : Euclidean n → Euclidean n → ℝ) (ζ : P → Euclidean n)
    (ρ : ℝ) (c v : P) (x δ : Euclidean n) :
    parameterPhaseCoefficient S ζ x (ρ⁻¹ • δ) c δ v =
      ∑ l, phaseCoefficient S ζ ρ c v x δ l * δ l := by
  have he : δ = ∑ l, δ l • EuclideanSpace.single l (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => arg 1; arg 2; rw [he]
  simp [phaseCoefficient, mul_comm]

private theorem hasLineDerivAt_matrixKernel
    (e : P → ℂ) (a : P → Matrix (Fin r) (Fin r) ℂ) (u : P → Fin r → ℂ)
    (e' : ℂ) (a' : Matrix (Fin r) (Fin r) ℂ) (u' : Fin r → ℂ) (c v : P)
    (he : HasLineDerivAt ℝ e e' c v) (ha : HasLineDerivAt ℝ a a' c v)
    (hu : HasLineDerivAt ℝ u u' c v) :
    HasLineDerivAt ℝ (fun b ↦ e b • (a b).mulVec (u b))
      (e' • (a c).mulVec (u c) + e c • ((a' ).mulVec (u c) + (a c).mulVec u')) c v := by
  have h := ReverseDerivative.matrixAction.hasFDerivAt_of_bilinear
    ha.hasFDerivAt hu.hasFDerivAt
  have hm := h.hasDerivAt
  have hs := HasDerivAt.smul he hm
  simp only [zero_smul, add_zero] at hs
  change HasLineDerivAt ℝ (fun b ↦ e b • (a b).mulVec (u b))
    (e c • ((a c).mulVec ((1 : ℝ) • u') + ((1 : ℝ) • a').mulVec (u c)) +
      e' • (a c).mulVec (u c)) c v at hs
  simp only [one_smul] at hs
  simpa only [add_comm] using hs

/-- The forward oscillation has the positive parameter phase contribution.
The phase-trade identity is obtained from primitive homogeneity and the buffered
chart, rather than assumed. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_forwardOscillation
    {S : Euclidean n → Euclidean n → ℝ} {ζ : P → Euclidean n}
    {D : Set (Euclidean n)} (hD : IsOpen D) (hcD : Convex ℝ D)
    (hD0 : (0 : Euclidean n) ∉ D) {x : Euclidean n}
    (hS : ContDiffOn ℝ ∞ (S x) D) (hhom : PosHomogeneousOne (S x))
    {c : P} (hζ : DifferentiableAt ℝ ζ c) (hζD : ζ c ∈ D)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : Euclidean n} (hend : ζ c + ρ⁻¹ • δ ∈ D)
    (y : Euclidean n) (v : P) :
    HasLineDerivAt ℝ (fun a ↦ graphOscillation (phaseIncrement S (ζ a) ρ) x y δ)
      ((Complex.I * ((∑ l, phaseCoefficient S ζ ρ c v x δ l * δ l : ℝ) : ℂ)) *
        graphOscillation (phaseIncrement S (ζ c) ρ) x y δ) c v := by
  have h := hasFDerivAt_phaseIncrement_parameter_of_chart
    hD hcD hD0 hS hhom hζ hζD hρ hend
  have he := (((Complex.ofRealCLM.hasFDerivAt.comp c
    (h.sub_const (inner ℝ y δ))).const_mul Complex.I).cexp).hasLineDerivAt v
  simpa [graphOscillation, parameterPhaseCoefficient_eq_sum, mul_comm] using he

/-- The reverse oscillation has the opposite parameter sign. The source
coefficient after integration by parts is therefore `-C B⁻¹`, including its
source divergence. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_reverseOscillation
    {S : Euclidean n → Euclidean n → ℝ} {ζ : P → Euclidean n}
    {D : Set (Euclidean n)} (hD : IsOpen D) (hcD : Convex ℝ D)
    (hD0 : (0 : Euclidean n) ∉ D) {x : Euclidean n}
    (hS : ContDiffOn ℝ ∞ (S x) D) (hhom : PosHomogeneousOne (S x))
    {c : P} (hζ : DifferentiableAt ℝ ζ c) (hζD : ζ c ∈ D)
    {ρ : ℝ} (hρ : 0 < ρ) {δ : Euclidean n} (hend : ζ c + ρ⁻¹ • δ ∈ D)
    (y : Euclidean n) (v : P) :
    HasLineDerivAt ℝ (fun a ↦ ReverseDerivative.oscillation S (ζ a) ρ y x δ)
      (-((Complex.I * ((∑ l, phaseCoefficient S ζ ρ c v x δ l * δ l : ℝ) : ℂ)) *
        ReverseDerivative.oscillation S (ζ c) ρ y x δ)) c v := by
  have h := hasFDerivAt_phaseIncrement_parameter_of_chart
    hD hcD hD0 hS hhom hζ hζD hρ hend
  have he := (((Complex.ofRealCLM.hasFDerivAt.comp c
    (h.const_sub (inner ℝ y δ))).const_mul Complex.I).cexp).hasLineDerivAt v
  simpa [ReverseDerivative.oscillation, parameterPhaseCoefficient_eq_sum,
    mul_comm] using he

section SelectedKernels

variable {S : Euclidean n → Euclidean n → ℝ} {ζ : P → Euclidean n}
  {D : Set (Euclidean n)} (hD : IsOpen D) (hcD : Convex ℝ D)
  (hD0 : (0 : Euclidean n) ∉ D) {x : Euclidean n}
  (hS : ContDiffOn ℝ ∞ (S x) D) (hhom : PosHomogeneousOne (S x))
  {c : P} (hζ : DifferentiableAt ℝ ζ c) (hζD : ζ c ∈ D)
  {ρ : ℝ} (hρ : 0 < ρ) {δ : Euclidean n} (hend : ζ c + ρ⁻¹ • δ ∈ D)

include hD hcD hD0 hS hhom hζ hζD hρ hend

/-- Actual directional derivative of the forward selected full kernel,
including the independent parameter derivative of the datum. All inputs are
primitive pointwise derivatives. Source: `app:ch_response:eq:direct-envelope-profile`.
-/
theorem hasLineDerivAt_forwardSelectedKernel
    (A : FullAmplitude n r) (q : P × Euclidean n → ℂ)
    (u : P → Euclidean n → Fin r → ℂ) (u' : Euclidean n → Fin r → ℂ)
    (y : Euclidean n) (v : P)
    (hA : DifferentiableAt ℝ
      (fun z : Euclidean n × Euclidean n × Euclidean n ↦ A z.1 z.2.1 z.2.2)
      (x, y, ρ • ζ c + δ)) (hq : DifferentiableAt ℝ q (c, ρ⁻¹ • δ))
    (hu : HasLineDerivAt ℝ (fun a ↦ u a y) (u' y) c v) :
    HasLineDerivAt ℝ
      (fun a ↦ graphOscillation (phaseIncrement S (ζ a) ρ) x y δ •
        (selectedFamily A q ζ ρ a x y δ).mulVec (u a y))
      (((Complex.I * ((∑ l, phaseCoefficient S ζ ρ c v x δ l * δ l : ℝ) : ℂ)) *
          graphOscillation (phaseIncrement S (ζ c) ρ) x y δ) •
          (selectedFamily A q ζ ρ c x y δ).mulVec (u c y) +
        graphOscillation (phaseIncrement S (ζ c) ρ) x y δ •
          ((selectedAmplitudeDifferential A q ζ ρ c v x y δ).mulVec (u c y) +
            (selectedFamily A q ζ ρ c x y δ).mulVec (u' y))) c v := by
  exact hasLineDerivAt_matrixKernel _ _ _ _ _ _ c v
    (hasLineDerivAt_forwardOscillation hD hcD hD0 hS hhom hζ hζD hρ hend y v)
    (hasLineDerivAt_selectedFamily A q ζ ρ c v x y δ hζ hA hq) hu

/-- Actual directional derivative of the reverse selected full kernel,
with the negative phase contribution and the datum derivative. Substituting
`ReverseDerivative.literalAmplitude` retains `j_S U⁻¹` and every cutoff.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem hasLineDerivAt_reverseSelectedKernel
    (A : FullAmplitude n r) (q : P × Euclidean n → ℂ)
    (u : P → Euclidean n → Fin r → ℂ) (u' : Euclidean n → Fin r → ℂ)
    (y : Euclidean n) (v : P)
    (hA : DifferentiableAt ℝ
      (fun z : Euclidean n × Euclidean n × Euclidean n ↦ A z.1 z.2.1 z.2.2)
      (y, x, ρ • ζ c + δ)) (hq : DifferentiableAt ℝ q (c, ρ⁻¹ • δ))
    (hu : HasLineDerivAt ℝ (fun a ↦ u a x) (u' x) c v) :
    HasLineDerivAt ℝ
      (fun a ↦ ReverseDerivative.oscillation S (ζ a) ρ y x δ •
        (selectedFamily A q ζ ρ a y x δ).mulVec (u a x))
      ((-((Complex.I * ((∑ l, phaseCoefficient S ζ ρ c v x δ l * δ l : ℝ) : ℂ)) *
          ReverseDerivative.oscillation S (ζ c) ρ y x δ)) •
          (selectedFamily A q ζ ρ c y x δ).mulVec (u c x) +
        ReverseDerivative.oscillation S (ζ c) ρ y x δ •
          ((selectedAmplitudeDifferential A q ζ ρ c v y x δ).mulVec (u c x) +
            (selectedFamily A q ζ ρ c y x δ).mulVec (u' x))) c v := by
  exact hasLineDerivAt_matrixKernel _ _ _ _ _ _ c v
    (hasLineDerivAt_reverseOscillation hD hcD hD0 hS hhom hζ hζD hρ hend y v)
    (hasLineDerivAt_selectedFamily A q ζ ρ c v y x δ hζ hA hq) hu

end SelectedKernels

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
/-- The reverse selected family is the existing literal selected weighted
amplitude, including the Jacobian, matrix inverse and all masks.
Source: `app:ch_regular_base:eq:actual-matrix-inverse`. -/
theorem selectedFamily_literalAmplitude
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (q : P × Euclidean n → ℂ)
    (ζ : P → Euclidean n) (ρ : ℝ) (c : P) :
    selectedFamily (ReverseDerivative.literalAmplitude S U χs χt χg) q ζ ρ c =
      ReverseDerivative.selectedWeightedAmplitude S U χs χt χg (ζ c) ρ
        (fun δ ↦ q (c, ρ⁻¹ • δ)) := rfl

end JanetCartan.ResponseTransfer.NearCarrierParameter
