module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.MatrixMultiplication
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.StrainIdentity

/-!
# Quantitative transfer of the actual angular residual

The Gram/frame multiplier in `app:ch_response:eq:response-graded-strain`, with
the exact factor two. Coefficient jet bounds and reduced residual estimates are
conditional analytic inputs from `jc-current-coefficient-scale` and
`jc-response-transfer`. No ambient estimate is an input. The coordinate Hilbert
norm uses every matrix entry, hence the Frobenius tensor convention.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
open JanetCartan.Pseudodifferential JanetCartan.IsometricEmbedding.Reconstruction
namespace JanetCartan.ResponseTransfer

variable {n m : ℕ}
local notation "E" => Euclidean n
local notation "L2" => Lp ℂ 2 (volume : Measure E)

/-- The actual localized inverse-Gram/frame coefficient, including the factor
`2` of `app:ch_response:eq:response-full-identity`. -/
def stressResidualCoefficient (ψ : E → ℝ) (Q : E → Fin m → MetricTensor n)
    (ij : Fin n × Fin n) (j : Fin m) (x : E) : ℂ :=
  2 * (ψ x : ℂ) * ∑ i, ((WKB.stressGram (Q x))⁻¹ i j : ℂ) * (Q x i ij.1 ij.2 : ℂ)

/-- Literal coefficient expansion of the tensor in
`app:ch_response:eq:response-full-identity`, retaining both quadratures. -/
theorem stressResidualCoefficient_apply (ψ : E → ℝ)
    (Q : E → Fin m → MetricTensor n) (v : Fin m → ℂ) (x : E) (ij : Fin n × Fin n) :
    ∑ j, stressResidualCoefficient ψ Q ij j x * v j =
      ((ψ x : ℂ) • ((2 : ℂ) • WKB.stressReconstruction (Q x) v)) ij.1 ij.2 := by
  simp only [stressResidualCoefficient, WKB.stressReconstruction,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.map_apply, smul_eq_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Pair-indexed Hilbert coordinates agree with the Frobenius tensor norm in
`app:ch_response:eq:response-graded-strain`; no supremum norm is substituted. -/
theorem tensorCoordinates_norm (T : Matrix (Fin n) (Fin n) ℂ) :
    ‖(WithLp.toLp 2 (fun ij : Fin n × Fin n ↦ T ij.1 ij.2) :
      EuclideanSpace ℂ (Fin n × Fin n))‖ = ‖T‖ := by
  simp only [PiLp.norm_eq_of_L2, Matrix.frobenius_norm_def,
    Fintype.sum_prod_type, Real.sqrt_eq_rpow, Real.rpow_two]

/-- The actual L² Gram/frame residual used in
`app:ch_response:eq:response-graded-strain`. -/
def localizedStressResidual (ψ : E → ℝ) (Q : E → Fin m → MetricTensor n)
    (hc : ∀ ij j, ContDiff ℝ ∞ (stressResidualCoefficient ψ Q ij j))
    (hcs : ∀ ij j, HasCompactSupport (stressResidualCoefficient ψ Q ij j))
    (r : PiLp 2 (fun _ : Fin m ↦ L2)) : PiLp 2 (fun _ : Fin n × Fin n ↦ L2) :=
  localizedMatrixProduct (stressResidualCoefficient ψ Q) hc hcs r

/-- Identification of the L² tensor with the precise Gram/frame formula in
`app:ch_response:eq:response-full-identity`. -/
theorem localizedStressResidual_ae (ψ : E → ℝ) (Q : E → Fin m → MetricTensor n)
    (hc : ∀ ij j, ContDiff ℝ ∞ (stressResidualCoefficient ψ Q ij j))
    (hcs : ∀ ij j, HasCompactSupport (stressResidualCoefficient ψ Q ij j))
    (r : PiLp 2 (fun _ : Fin m ↦ L2)) (ij : Fin n × Fin n) :
    localizedStressResidual ψ Q hc hcs r ij =ᵐ[volume] fun x ↦
      ((ψ x : ℂ) • ((2 : ℂ) • WKB.stressReconstruction (Q x) (fun j ↦ r j x))) ij.1 ij.2 := by
  filter_upwards [localizedMatrixProduct_ae (stressResidualCoefficient ψ Q) hc hcs r ij]
    with x hx
  exact hx.trans (stressResidualCoefficient_apply ψ Q _ x ij)

/-- Higher internal precision absorbs the fixed polynomial Gram/frame cost in
`app:ch_response:eq:response-graded-strain`. The finite jet budget is chosen
before `ρ` and the requested accuracy `q`. Output membership is part of the
conclusion, on literal Euclidean Lebesgue L² spaces. -/
theorem localizedStressResidual_precision_bound (k : ℕ) {s : ℝ} (hs : s ≤ k)
    (ψ : E → ℝ) (Q : E → Fin m → MetricTensor n)
    (hc : ∀ ij j, ContDiff ℝ ∞ (stressResidualCoefficient ψ Q ij j))
    (hcs : ∀ ij j, HasCompactSupport (stressResidualCoefficient ψ Q ij j))
    (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) {ρ A B q b : ℝ} (hρ : 0 < ρ)
    (hbudget : ∀ ij j l, l ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ l (stressResidualCoefficient ψ Q ij j) x‖ ≤ C l * ρ ^ b)
    (r : PiLp 2 (fun _ : Fin m ↦ L2)) (hr : MemMatrixFourierSobolev (k : ℝ) r)
    (hrb : matrixFourierSobolevNorm (k : ℝ) r ≤ B * A * ρ ^ (-(q + b))) :
    MemMatrixFourierSobolev s (localizedStressResidual ψ Q hc hcs r) ∧
      matrixFourierSobolevNorm s (localizedStressResidual ψ Q hc hcs r) ≤
        ((n : ℝ) * n * m * localizedMultiplierConstant n k *
          ∑ l ∈ Finset.range (k + 1), C (k - l)) * B * A * ρ ^ (-q) := by
  simpa only [localizedStressResidual, Fintype.card_prod, Fintype.card_fin,
    Nat.cast_mul, mul_assoc] using
    localizedMatrixProduct_precision_bound k hs (stressResidualCoefficient ψ Q)
      hc hcs C hC hρ hbudget r hr hrb

/-- The localized strain of the SAME completed variation has an actual Sobolev
representative and the bound of `app:ch_response:eq:response-graded-strain`.
The only equation premises are the two reduced physical equations; the ambient
identity is derived. The parent must supply the geometric hypotheses, the actual
reduced residual representative, and its higher-precision estimate. -/
theorem completedVariationComplex_strain_graded_precision {N : ℕ}
    (k : ℕ) {s : ℝ} (hsk : s ≤ k)
    {F : E → Euclidean N} {u : E → EuclideanSpace ℂ (Fin n)}
    {h : E → Matrix (Fin n) (Fin n) ℂ} {Ω : Set E} (hΩ : IsOpen Ω)
    (hF : ContDiffOn ℝ ∞ F Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (himm : IsImmersionOn F Ω) (hrank : HasFullNormalRankOn F Ω)
    (hhSmooth : ContDiffOn ℝ ∞ h Ω) (hh : ∀ x ∈ Ω, (h x).IsSymm)
    (ψ : E → ℝ) (hψ : Function.support ψ ⊆ Ω)
    (Q : E → Fin m → MetricTensor n)
    (hQ : ∀ x ∈ Ω, LinearIndependent ℝ (Q x))
    (hspan : ∀ x ∈ Ω,
      (Submodule.span ℝ (Set.range (Q x)) : Set (MetricTensor n)) = stressSpace F x)
    (z : E → Fin m → ℂ) (T : (E → Fin m → ℂ) →ₗ[ℂ] (E → Fin m → ℂ))
    (hphysicalRe : ∀ x ∈ Ω, ∀ j, tensorPairing (Q x j)
      (symmCovariantDeriv F (fun y ↦ WithLp.toLp 2 (fun l ↦ (u y l).re)) x) =
      (1 / 2 : ℝ) * tensorPairing (Q x j) (fun i l ↦ (h x i l).re) +
        (T z x j - z x j).re)
    (hphysicalIm : ∀ x ∈ Ω, ∀ j, tensorPairing (Q x j)
      (symmCovariantDeriv F (fun y ↦ WithLp.toLp 2 (fun l ↦ (u y l).im)) x) =
      (1 / 2 : ℝ) * tensorPairing (Q x j) (fun i l ↦ (h x i l).im) +
        (T z x j - z x j).im)
    (hc : ∀ ij j, ContDiff ℝ ∞ (stressResidualCoefficient ψ Q ij j))
    (hcs : ∀ ij j, HasCompactSupport (stressResidualCoefficient ψ Q ij j))
    (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) {ρ L A B q : ℝ}
    (hL : 1 ≤ L) (hLρ : L ≤ ρ)
    (hbudget : ∀ ij j l, l ≤ k → ∀ x,
      ‖iteratedFDeriv ℝ l (stressResidualCoefficient ψ Q ij j) x‖ ≤ C l * L ^ l)
    (r : PiLp 2 (fun _ : Fin m ↦ L2))
    (hrrep : ∀ j, r j =ᵐ[volume] fun x ↦ T z x j - z x j)
    (hr : MemMatrixFourierSobolev (k : ℝ) r)
    (hrb : matrixFourierSobolevNorm (k : ℝ) r ≤ B * A * ρ ^ (-(q + k))) :
    ∃ R : PiLp 2 (fun _ : Fin n × Fin n ↦ L2),
      (∀ ij, R ij =ᵐ[volume] fun x ↦
        ((ψ x : ℂ) • (WKB.complexLinearizedMetric F (completedVariationComplex F u h) x -
          h x)) ij.1 ij.2) ∧
      MemMatrixFourierSobolev s R ∧ matrixFourierSobolevNorm s R ≤
        ((n : ℝ) * n * m * localizedMultiplierConstant n k *
          ∑ l ∈ Finset.range (k + 1), C (k - l)) * B * A * ρ ^ (-q) := by
  have hb := localizedMatrixProduct_graded_precision_bound k hsk
    (stressResidualCoefficient ψ Q) hc hcs C hC hL hLρ hbudget r hr hrb
  refine ⟨localizedStressResidual ψ Q hc hcs r, ?_, ?_⟩
  swap
  · simpa only [localizedStressResidual, Fintype.card_prod, Fintype.card_fin,
      Nat.cast_mul, mul_assoc] using hb
  intro ij
  filter_upwards [localizedStressResidual_ae ψ Q hc hcs r ij, ae_all_iff.mpr hrrep]
    with x hx hxrep
  rw [hx]
  by_cases hzero : ψ x = 0
  · simp [hzero]
  have hxΩ : x ∈ Ω := hψ hzero
  have hid := completedVariationComplex_error_eq_full_residual hΩ hF hu himm hrank
    hhSmooth hxΩ (hh x hxΩ) (hQ x hxΩ) (hspan x hxΩ) z T
    (hphysicalRe x hxΩ) (hphysicalIm x hxΩ)
  rw [hid]
  simp only [hxrep]

end JanetCartan.ResponseTransfer
