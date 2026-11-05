module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.GradedPrimitives.Amplitude.Selected
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Weighted

/-!
# Reserve-graded literal coordinate-inverse amplitude

The amplitude `j_S U⁻¹` in `app:ch_response:eq:direct-envelope-profile` is
`FourierIntegral.reverseWeight`, with the actual `phaseJacobian`. Its positive
inverse jets are derived from transport jets and a zeroth-order inverse gap.
The source, target, and frequency masks are the literal masks of
`ReverseDerivative.literalAmplitude`, before carrier selection.

The finite-order inputs below are precisely profiles of the normalized actual
Jacobian, transport, and mask product on the buffered annular chart. The response
geometry producer must establish these uniformly in frequency and scale. No
profile of an inverse derivative, selected amplitude, or graph operator is an
input. The parent construction retains the global cutoff-extension obligation.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.GradedPrimitives
open FourierIntegral

private theorem amplitude_inverseConstant_nonneg {T : ℕ → ℝ}
    (hT : ∀ j, 0 ≤ T j) (M : ℝ) (k : ℕ) : 0 ≤ inverseConstant M T k :=
  compositionConstant_nonneg
    (fun j ↦ mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (zero_le_one.trans (le_max_left 1 M)) (j + 1))) hT k

/-- The literal inverse-weight constant in
`app:ch_response:eq:direct-envelope-profile`, independent of frequency and scale. -/
def reverseWeightConstant (r : ℕ) (J T : ℕ → ℝ) (M : ℝ) (k : ℕ) : ℝ :=
  bilinearConstant (ContinuousLinearMap.lsmul ℝ ℝ :
    ℝ →L[ℝ] (Matrix (Fin r) (Fin r) ℂ) →L[ℝ] Matrix (Fin r) (Fin r) ℂ)
    J (inverseConstant M T) k

/-- Nonnegative constants for the literal inverse primitive in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem reverseWeightConstant_nonneg (r : ℕ) {J T : ℕ → ℝ}
    (hJ : ∀ j, 0 ≤ J j) (hT : ∀ j, 0 ≤ T j) (M : ℝ) (k : ℕ) :
    0 ≤ reverseWeightConstant r J T M k :=
  mul_nonneg (norm_nonneg (ContinuousLinearMap.lsmul ℝ ℝ :
    ℝ →L[ℝ] (Matrix (Fin r) (Fin r) ℂ) →L[ℝ] Matrix (Fin r) (Fin r) ℂ))
    (Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hJ _))
      (amplitude_inverseConstant_nonneg hT M _))

private theorem reverseWeight_eq_real_smul {r : ℕ} (j : ℝ)
    (U : Matrix (Fin r) (Fin r) ℂ) : reverseWeight j U = j • U⁻¹ := by
  ext i k
  simp [reverseWeight, Complex.real_smul]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {r : ℕ}

/-- Smoothness of the literal weighted inverse follows from smooth primitive
factors and invertibility. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem reverseWeight_contDiffOn {j : X → ℝ}
    {t : X → Matrix (Fin r) (Fin r) ℂ} {V : Set X} {N : ℕ}
    (hj : ContDiffOn ℝ N j V) (ht : ContDiffOn ℝ N t V)
    (hu : ∀ x ∈ V, IsUnit (t x)) :
    ContDiffOn ℝ N (fun x ↦ reverseWeight (j x) (t x)) V := by
  simp_rw [reverseWeight_eq_real_smul, Matrix.nonsing_inv_eq_ringInverse]
  exact hj.smul (contDiffOn_ringInverse_units.comp ht hu)

/-- The actual inverse-weight jets are consequences of primitive jets and
the value of the transport inverse. All differentiated factors share the total
budget `k`; no positive-order inverse bound is assumed. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem norm_jet_reverseWeight_le {j : X → ℝ}
    {t : X → Matrix (Fin r) (Fin r) ℂ} {V : Set X} {N k R : ℕ}
    (hV : IsOpen V) (hj : ContDiffOn ℝ N j V) (ht : ContDiffOn ℝ N t V)
    (hu : ∀ x ∈ V, IsUnit (t x)) {J T : ℕ → ℝ} {M L : ℝ}
    (hJ : ∀ i, 0 ≤ J i) (hT : ∀ i, 0 ≤ T i) (hL : 1 ≤ L)
    (hjjet : ∀ i ≤ N, ∀ x ∈ V, ‖iteratedFDeriv ℝ i j x‖ ≤ J i * L ^ (i - R))
    (htjet : ∀ i, 1 ≤ i → i ≤ N → ∀ x ∈ V,
      ‖iteratedFDeriv ℝ i t x‖ ≤ T i * L ^ (i - R))
    (hk : k ≤ N) {x : X} (hx : x ∈ V) (hgap : ‖(t x)⁻¹‖ ≤ M) :
    ‖iteratedFDeriv ℝ k (fun y ↦ reverseWeight (j y) (t y)) x‖ ≤
      reverseWeightConstant r J T M k * L ^ (k - R) := by
  have hi : ContDiffOn ℝ N (fun y ↦ Ring.inverse (t y)) V :=
    contDiffOn_ringInverse_units.comp ht hu
  have hgap' : ‖Ring.inverse (t x)‖ ≤ M := by
    simpa only [Matrix.nonsing_inv_eq_ringInverse] using hgap
  simp_rw [reverseWeight_eq_real_smul, Matrix.nonsing_inv_eq_ringInverse]
  exact norm_jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℝ) hV hj hi hk hx
    J (inverseConstant M T) hJ (amplitude_inverseConstant_nonneg hT M) hL R
    (fun i hik ↦ hjjet i (hik.trans hk) x hx)
    (fun i hik ↦ norm_jet_inverse_le (ht.contDiffAt (hV.mem_nhds hx))
      (hik.trans hk) (hu x hx) hgap' T hT hL R
      (fun a ha hai ↦ htjet a ha (hai.trans (hik.trans hk)) x hx))

variable {n : ℕ}

/-- The complete normalized product of source, frequency, and target masks
in the literal coordinate inverse (`app:ch_regular_base:eq:actual-matrix-inverse`).
Its two physical positions remain independent. -/
def normalizedReverseMask (χs χt χg : Euclidean n → ℝ) (ρ : ℝ)
    (v : Euclidean n × Euclidean n × Euclidean n) : ℂ :=
  (χs v.1 : ℂ) * (χg (ρ • v.2.2) : ℂ) * (χt v.2.1 : ℂ)

/-- Masked inverse constant for the primitive interface in
`app:ch_response:eq:direct-envelope-profile`. -/
def literalAmplitudeConstant (r : ℕ) (F J T : ℕ → ℝ) (M : ℝ) (k : ℕ) : ℝ :=
  bilinearConstant (ContinuousLinearMap.lsmul ℝ ℂ :
    ℂ →L[ℝ] (Matrix (Fin r) (Fin r) ℂ) →L[ℝ] Matrix (Fin r) (Fin r) ℂ)
    F (reverseWeightConstant r J T M) k

/-- Nonnegative full masked inverse constants for
`app:ch_response:eq:direct-envelope-profile`. -/
theorem literalAmplitudeConstant_nonneg (r : ℕ) {F J T : ℕ → ℝ}
    (hF : ∀ j, 0 ≤ F j) (hJ : ∀ j, 0 ≤ J j) (hT : ∀ j, 0 ≤ T j)
    (M : ℝ) (k : ℕ) : 0 ≤ literalAmplitudeConstant r F J T M k :=
  mul_nonneg (norm_nonneg (ContinuousLinearMap.lsmul ℝ ℂ :
    ℂ →L[ℝ] (Matrix (Fin r) (Fin r) ℂ) →L[ℝ] Matrix (Fin r) (Fin r) ℂ))
    (Finset.sum_nonneg fun _ _ ↦
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hF _))
      (reverseWeightConstant_nonneg r hJ hT M _))

section Literal
variable {S : Euclidean n → Euclidean n → ℝ}
  {t : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
  {χs χt χg : Euclidean n → ℝ} {ρ : ℝ} {N : ℕ}
  {V : Set (Euclidean n × Euclidean n × Euclidean n)}
  (hmask : ContDiffOn ℝ N (normalizedReverseMask χs χt χg ρ) V)
  (hj : ContDiffOn ℝ N (fun v : Euclidean n × Euclidean n × Euclidean n ↦
    phaseJacobian S v.2.1 (ρ • v.2.2)) V)
  (ht : ContDiffOn ℝ N (fun v : Euclidean n × Euclidean n × Euclidean n ↦
    t v.2.1 (ρ • v.2.2)) V)
  (hu : ∀ v ∈ V, IsUnit (t v.2.1 (ρ • v.2.2)))

include hmask hj ht hu

/-- Finite smoothness of the actual masked coordinate-inverse amplitude is
derived before selection. The Jacobian is the absolute mixed determinant in
`FourierIntegral.phaseJacobian`. Source:
`app:ch_response:eq:direct-envelope-profile`. -/
theorem normalizedLiteralAmplitude_contDiffOn :
    ContDiffOn ℝ N
      (normalizedFullAmplitude (ReverseDerivative.literalAmplitude S t χs χt χg) ρ) V :=
  hmask.smul (reverseWeight_contDiffOn hj ht hu)

/-- The precise annular input signature for the literal coordinate inverse.
Only finite jets of the actual normalized Jacobian and transport, fixed jets of
the complete mask product, and a zeroth-order transport inverse gap are inputs.
This supplies the amplitude primitive for `app:ch_response:eq:direct-envelope-profile`.
Neither the constant nor the derivative budget depends on frequency or scale. -/
theorem norm_jet_normalizedLiteralAmplitude_le (hV : IsOpen V)
    {k R : ℕ} {F J T : ℕ → ℝ} {M L : ℝ}
    (hF : ∀ i, 0 ≤ F i) (hJ : ∀ i, 0 ≤ J i) (hT : ∀ i, 0 ≤ T i) (hL : 1 ≤ L)
    (hmaskjet : ∀ i ≤ N, ∀ v ∈ V,
      ‖iteratedFDeriv ℝ i (normalizedReverseMask χs χt χg ρ) v‖ ≤ F i)
    (hjjet : ∀ i ≤ N, ∀ v ∈ V,
      ‖iteratedFDeriv ℝ i
        (fun w : Euclidean n × Euclidean n × Euclidean n ↦
          phaseJacobian S w.2.1 (ρ • w.2.2)) v‖ ≤ J i * L ^ (i - R))
    (htjet : ∀ i, 1 ≤ i → i ≤ N → ∀ v ∈ V,
      ‖iteratedFDeriv ℝ i
        (fun w : Euclidean n × Euclidean n × Euclidean n ↦
          t w.2.1 (ρ • w.2.2)) v‖ ≤ T i * L ^ (i - R))
    (hk : k ≤ N) {v : Euclidean n × Euclidean n × Euclidean n} (hv : v ∈ V)
    (hgap : ‖(t v.2.1 (ρ • v.2.2))⁻¹‖ ≤ M) :
    ‖iteratedFDeriv ℝ k
      (normalizedFullAmplitude (ReverseDerivative.literalAmplitude S t χs χt χg) ρ) v‖ ≤
      literalAmplitudeConstant r F J T M k * L ^ (k - R) := by
  exact norm_jet_bilinear_le (ContinuousLinearMap.lsmul ℝ ℂ) hV
    hmask (reverseWeight_contDiffOn hj ht hu) hk hv
    F (reverseWeightConstant r J T M) hF (reverseWeightConstant_nonneg r hJ hT M) hL R
    (fun i hik ↦ (hmaskjet i (hik.trans hk) v hv).trans
      (le_mul_of_one_le_right (hF i) (one_le_pow₀ hL)))
    (fun i hik ↦ norm_jet_reverseWeight_le hV hj ht hu hJ hT hL hjjet htjet
      (hik.trans hk) hv hgap)

end Literal
end JanetCartan.ResponseTransfer.GradedPrimitives
