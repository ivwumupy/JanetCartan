module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Definitions
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Calculus

/-!
# The exact joint WKB matrix polynomial

Fixed continuous linear and bilinear maps retain the Frobenius matrix norm.
The physical derivative is restricted from the full joint differential, so
all patch and carrier derivatives remain visible. The formulas implement
`app:ch_waves:eq:exact-W-amplitude` and
`app:ch_waves:eq:WKB-amplitude-difference`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RawPrimary.AmplitudeGrades.Polynomial

/-- The unsigned tensor, with its actual Frobenius target; the leading
matrix is its negative (`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
def normalTensor (n N : ℕ) :
    Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin N) →L[ℝ] Matrix (Fin N) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun ξ ↦ LinearMap.toContinuousLinearMap
        { toFun := fun ν i j ↦ (ξ j : ℂ) * ν i
          map_add' := by intro a b; ext i j; change (ξ j : ℂ) * (a i + b i) = _; simp [Matrix.add_apply, mul_add]
          map_smul' := by intro a b; ext i j; change (ξ j : ℂ) * ((a : ℂ) * b i) = _; simp [Matrix.smul_apply, mul_left_comm] }
      map_add' := by intro a b; ext ν i j; change ((a j + b j : ℝ) : ℂ) * ν i = (a j : ℂ) * ν i + (b j : ℂ) * ν i; simp [add_mul]
      map_smul' := by intro a b; ext ν i j; change ((a * b j : ℝ) : ℂ) * ν i = (a : ℂ) * ((b j : ℂ) * ν i); simp [mul_assoc] }
/-- Coordinate identity for the actual Frobenius tensor
(`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
@[simp] theorem normalTensor_apply (n N : ℕ) (ξ : Euclidean n)
    (ν : EuclideanSpace ℂ (Fin N)) (i : Fin N) (j : Fin n) :
    normalTensor n N ξ ν i j = (ξ j : ℂ) * ν i := rfl

/-- The physical differential as a Frobenius matrix, used in every correction
coefficient of `app:ch_waves:eq:WKB-amplitude-difference`. -/
def differentialMatrix (n N : ℕ) :
    (Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin N)) →L[ℝ] Matrix (Fin N) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun D i j ↦ D (EuclideanSpace.single j 1) i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Restrict the full joint differential to physical directions, retaining
all parameter dependence (`app:ch_waves:eq:WKB-amplitude-difference`). -/
def physicalJacobian (f : Euclidean n × Z → EuclideanSpace ℂ (Fin N))
    (w : Euclidean n × Z) : Matrix (Fin N) (Fin n) ℂ :=
  differentialMatrix n N ((fderiv ℝ f w).comp (ContinuousLinearMap.inl ℝ _ _))

/-- The joint restriction equals the literal physical derivative at every
smooth point (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem physicalJacobian_apply {f : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    {w : Euclidean n × Z} (hf : DifferentiableAt ℝ f w) (i : Fin N) (j : Fin n) :
    physicalJacobian f w i j =
      fderiv ℝ (fun x ↦ f (x, w.2)) w.1 (EuclideanSpace.single j 1) i := by
  have h := (hf.hasFDerivAt.comp w.1
    ((hasFDerivAt_id (𝕜 := ℝ) w.1).prodMk (hasFDerivAt_const w.2 w.1))).fderiv
  exact congrArg (fun D : Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin N) ↦
    D (EuclideanSpace.single j 1) i) h.symm

/-- Joint smoothness of the differentiated coefficient on the original
open wave domain (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem contDiffOn_physicalJacobian
    {Ω : Set (Euclidean n × Z)} (hΩ : IsOpen Ω)
    {f : Euclidean n × Z → EuclideanSpace ℂ (Fin N)} (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (physicalJacobian f) Ω :=
  (differentialMatrix n N).contDiff.comp_contDiffOn
    ((hf.fderiv_of_isOpen hΩ (m := ∞) (by simp)).clm_comp contDiffOn_const)

/-- One physical differentiation costs exactly one joint jet, with a fixed
Frobenius conversion constant (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem jet_physicalJacobian_le
    {f : Euclidean n × Z → EuclideanSpace ℂ (Fin N)} {w : Euclidean n × Z}
    (hf : ContDiffAt ℝ ∞ f w) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (physicalJacobian f) w‖ ≤
      ‖differentialMatrix n N‖ * ‖iteratedFDeriv ℝ (j + 1) f w‖ := by
  have h := (differentialMatrix n N).norm_iteratedFDeriv_comp_left
    (f := fun y ↦ (fderiv ℝ f y).comp (ContinuousLinearMap.inl ℝ (Euclidean n) Z))
    ((hf.fderiv_right (m := ∞) (by simp)).clm_comp contDiffAt_const)
    (by simp : (j : ℕ∞ω) ≤ ∞)
  exact h.trans (mul_le_mul_of_nonneg_left
    (norm_iteratedFDeriv_restricted_fderiv_le hf _
      (ContinuousLinearMap.norm_inl_le_one ..) j) (norm_nonneg (differentialMatrix n N)))

/-- The exact coefficient of `τ` in the Frobenius derivative polynomial
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
def correctionOne (ξ : Euclidean n × Z → Euclidean n)
    (ν₀ ν₁ V₀ : Euclidean n × Z → EuclideanSpace ℂ (Fin N))
    (w : Euclidean n × Z) : Matrix (Fin N) (Fin n) ℂ :=
  -(normalTensor n N (ξ w) (ν₁ w)) +
    Complex.I • (normalTensor n N (ξ w) (V₀ w) + physicalJacobian ν₀ w)

/-- The exact coefficient of `τ²`, with both first derivatives retained
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
def correctionTwo (ξ : Euclidean n × Z → Euclidean n)
    (ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N))
    (w : Euclidean n × Z) : Matrix (Fin N) (Fin n) ℂ :=
  Complex.I • (normalTensor n N (ξ w) (V₁ w) + physicalJacobian ν₁ w) +
    physicalJacobian V₀ w

/-- The exact error polynomial, including `τ³ dV₁`, used only after
identifying the SAME published amplitude
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
def derivativeError (τ : ℝ) (ξ : Euclidean n × Z → Euclidean n)
    (ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N))
    (w : Euclidean n × Z) : Matrix (Fin N) (Fin n) ℂ :=
  (τ : ℂ) • correctionOne ξ ν₀ ν₁ V₀ w +
    (τ : ℂ)^2 • correctionTwo ξ ν₁ V₀ V₁ w + (τ : ℂ)^3 • physicalJacobian V₁ w

/-- The literal leading tensor plus all three error powers
(`app:ch_waves:eq:WKB-amplitude-difference`). -/
def derivativePolynomial (τ : ℝ) (ξ : Euclidean n × Z → Euclidean n)
    (ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N))
    (w : Euclidean n × Z) : Matrix (Fin N) (Fin n) ℂ :=
  -(normalTensor n N (ξ w) (ν₀ w)) + derivativeError τ ξ ν₀ ν₁ V₀ V₁ w

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] in
/-- Joint evaluation of the exact displacement polynomial commutes with
freezing the spectator parameters (`app:ch_waves:eq:exact-W-amplitude`). -/
theorem reconstructionAmplitude_slice (τ : ℝ)
    (ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)) (w : Euclidean n × Z) :
    WKB.reconstructionAmplitude τ⁻¹ ν₀ ν₁ V₀ V₁ w =
      WKB.reconstructionAmplitude τ⁻¹ (fun x ↦ ν₀ (x, w.2)) (fun x ↦ ν₁ (x, w.2))
        (fun x ↦ V₀ (x, w.2)) (fun x ↦ V₁ (x, w.2)) w.1 := rfl

/-- `WKB.derivative_expansion` identifies the full matrix polynomial with
the physical derivative of the SAME displacement. The phase covector is
literal, not an independent replacement (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem derivativePolynomial_apply {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n × Z → ℝ}
    {ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    {w : Euclidean n × Z} (hS : DifferentiableAt ℝ S w)
    (hν₀ : DifferentiableAt ℝ ν₀ w) (hν₁ : DifferentiableAt ℝ ν₁ w)
    (hV₀ : DifferentiableAt ℝ V₀ w) (hV₁ : DifferentiableAt ℝ V₁ w)
    (i : Fin N) (j : Fin n) :
    derivativePolynomial τ
      (fun p ↦ LeadingWave.scalarDifferential (fun x ↦ S (x, p.2)) p.1)
      ν₀ ν₁ V₀ V₁ w i j =
      waveFirstAmplitude τ⁻¹ (fun x ↦ S (x, w.2))
        (fun x ↦ WKB.reconstructionAmplitude τ⁻¹ ν₀ ν₁ V₀ V₁ (x, w.2))
        w.1 (EuclideanSpace.single j 1) i := by
  have hd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : Euclidean n × Z → E} (hf : DifferentiableAt ℝ f w) :
      DifferentiableAt ℝ (fun x ↦ f (x, w.2)) w.1 :=
    hf.comp w.1 (differentiableAt_id.prodMk (differentiableAt_const _))
  have he := WKB.derivative_expansion (inv_ne_zero hτ) (hd hS) (hd hν₀) (hd hν₁)
    (hd hV₀) (hd hV₁) (EuclideanSpace.single j 1)
  rw [demodulated_fderiv_modulatedWave (hd hS)
    (WKB.differentiableAt_reconstructionAmplitude (hd hν₀) (hd hν₁) (hd hV₀) (hd hV₁))] at he
  have he' := congrArg (fun v : EuclideanSpace ℂ (Fin N) ↦ v i) he
  simp only [Complex.ofReal_inv, inv_inv] at he'
  rw [show (fun x ↦ WKB.reconstructionAmplitude τ⁻¹ ν₀ ν₁ V₀ V₁ (x, w.2)) =
      WKB.reconstructionAmplitude τ⁻¹ (fun x ↦ ν₀ (x, w.2)) (fun x ↦ ν₁ (x, w.2))
        (fun x ↦ V₀ (x, w.2)) (fun x ↦ V₁ (x, w.2)) by rfl, he']
  simp only [derivativePolynomial, derivativeError, correctionOne, correctionTwo,
    Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
    physicalJacobian_apply hν₀, physicalJacobian_apply hν₁,
    physicalJacobian_apply hV₀, physicalJacobian_apply hV₁]
  simp only [normalTensor_apply, WKB.leadingDerivativeAmplitude,
    WKB.derivativeCorrection₁, WKB.derivativeCorrection₂,
    LeadingWave.scalarDifferential, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    neg_mul]
  dsimp only [WithLp.ofLp_toLp, partialDeriv]
  ring

/-- The factored error identity is also the literal specialization of
`WKB.derivative_amplitude_difference`, retaining the `τ² dV₁` term inside
the factor `τ` (`app:ch_waves:eq:WKB-amplitude-difference`). -/
theorem derivativeError_apply {τ : ℝ} (hτ : τ ≠ 0)
    {S : Euclidean n × Z → ℝ}
    {ν₀ ν₁ V₀ V₁ : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    {w : Euclidean n × Z} (hS : DifferentiableAt ℝ S w)
    (hν₀ : DifferentiableAt ℝ ν₀ w) (hν₁ : DifferentiableAt ℝ ν₁ w)
    (hV₀ : DifferentiableAt ℝ V₀ w) (hV₁ : DifferentiableAt ℝ V₁ w)
    (i : Fin N) (j : Fin n) :
    derivativeError τ
      (fun p ↦ LeadingWave.scalarDifferential (fun x ↦ S (x, p.2)) p.1)
      ν₀ ν₁ V₀ V₁ w i j =
      waveFirstAmplitude τ⁻¹ (fun x ↦ S (x, w.2))
        (fun x ↦ WKB.reconstructionAmplitude τ⁻¹ ν₀ ν₁ V₀ V₁ (x, w.2))
        w.1 (EuclideanSpace.single j 1) i -
      WKB.leadingDerivativeAmplitude (fun x ↦ S (x, w.2)) (fun x ↦ ν₀ (x, w.2))
        w.1 (EuclideanSpace.single j 1) i := by
  have hd {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : Euclidean n × Z → E} (hf : DifferentiableAt ℝ f w) :
      DifferentiableAt ℝ (fun x ↦ f (x, w.2)) w.1 :=
    hf.comp w.1 (differentiableAt_id.prodMk (differentiableAt_const _))
  have he := WKB.derivative_amplitude_difference (inv_ne_zero hτ) (hd hS) (hd hν₀)
    (hd hν₁) (hd hV₀) (hd hV₁) (EuclideanSpace.single j 1)
  rw [demodulated_fderiv_modulatedWave (hd hS)
    (WKB.differentiableAt_reconstructionAmplitude (hd hν₀) (hd hν₁) (hd hV₀) (hd hV₁))] at he
  have he' := congrArg (fun v : EuclideanSpace ℂ (Fin N) ↦ v i) he
  simp only [Complex.ofReal_inv, inv_inv, PiLp.sub_apply] at he'
  rw [show (fun x ↦ WKB.reconstructionAmplitude τ⁻¹ ν₀ ν₁ V₀ V₁ (x, w.2)) =
      WKB.reconstructionAmplitude τ⁻¹ (fun x ↦ ν₀ (x, w.2)) (fun x ↦ ν₁ (x, w.2))
        (fun x ↦ V₀ (x, w.2)) (fun x ↦ V₁ (x, w.2)) by rfl, he']
  simp only [derivativeError, correctionOne, correctionTwo,
    Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply,
    physicalJacobian_apply hν₀, physicalJacobian_apply hν₁,
    physicalJacobian_apply hV₀, physicalJacobian_apply hV₁,
    normalTensor_apply, WKB.derivativeCorrection₁, WKB.derivativeCorrection₂,
    LeadingWave.scalarDifferential, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    neg_mul]
  dsimp only [WithLp.ofLp_toLp, partialDeriv]
  ring

end JanetCartan.RawPrimary.AmplitudeGrades.Polynomial
