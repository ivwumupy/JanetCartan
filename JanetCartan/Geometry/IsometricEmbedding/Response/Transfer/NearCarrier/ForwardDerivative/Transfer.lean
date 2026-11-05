module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative.Source

/-!
# The forward transfer identity at each physical covector

This is the source integration step in
`app:ch_response:thm:response-literal-transfer`. Its consumer is the weak output
derivative identity for `app:ch_response:eq:direct-envelope-profile`.
The supplied phase identity must be instantiated with `phaseIncrement` by the
parent construction; it is not inferred from a graph estimate.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer
open FourierIntegral
variable {n r : ℕ}

/-- Exact source transfer at a fixed physical covector. The geometric hypothesis
is precisely `dₓ ΔS = Bδ`. No derivative transfer formula is assumed.
Source: `app:ch_response:thm:response-literal-transfer`, forward paragraph. -/
theorem integral_forwardOutputAmplitude_transfer
    (Φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (u : Euclidean n → Fin r → ℂ) (x δ : Euclidean n) (j : Fin n)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 δ))
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (hphase : partialDeriv (fun z ↦ Φ z δ) x j = ∑ l, B x δ j l * δ l) :
    (∫ y, graphOscillation Φ x y δ • (forwardOutputAmplitude Φ A j x y δ).mulVec (u y)) =
      (∫ y, graphOscillation Φ x y δ • (forwardRemainderAmplitude B A j x y δ).mulVec (u y)) +
      ∑ l, ∫ y, graphOscillation Φ x y δ •
        (forwardDatumAmplitude B A j l x y δ).mulVec (partialDeriv u y l) := by
  let e := fun y ↦ graphOscillation Φ x y δ
  let a := fun y ↦ A x y δ
  let dx := fun y ↦ partialDeriv (fun z ↦ A z y δ) x j
  let dy := fun l y ↦ partialDeriv a y l
  let b := fun l ↦ (B x δ j l : ℂ)
  let c := Complex.I * ((partialDeriv (fun z ↦ Φ z δ) x j : ℝ) : ℂ)
  have ha : ContDiff ℝ ∞ a := hA.comp (contDiff_const.prodMk contDiff_id)
  have hdx : Continuous dx := by
    exact (((hA.comp (contDiff_snd.prodMk contDiff_fst)).fderiv
      (contDiff_const : ContDiff ℝ ∞ (fun _ : Euclidean n ↦ x)) (by simp)).clm_apply
        contDiff_const).continuous
  have hi := integrable_graphOscillation_mulVec Φ x δ a u ha.continuous hu.continuous hus
  have hix := integrable_graphOscillation_mulVec Φ x δ dx u hdx hu.continuous hus
  have hiy (l : Fin n) := integrable_graphOscillation_mulVec Φ x δ (dy l) u
    ((ha.continuous_fderiv (by simp)).clm_apply continuous_const) hu.continuous hus
  have hsum : c • (∫ y, e y • (a y).mulVec (u y)) =
      ∑ l, b l • ((∫ y, e y • (dy l y).mulVec (u y)) +
        ∫ y, e y • (a y).mulVec (partialDeriv u y l)) := by
    have hc : c = ∑ l, b l * (Complex.I * (δ l : ℂ)) := by
      dsimp [c, b]
      rw [hphase, Complex.ofReal_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Complex.ofReal_mul]
      ring
    rw [hc, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro l _
    rw [mul_smul, graphOscillation_source_mulVec_integration_by_parts Φ x δ l a u ha hu hus]
  have hout : (∫ y, graphOscillation Φ x y δ •
      (forwardOutputAmplitude Φ A j x y δ).mulVec (u y)) =
      (∫ y, e y • (dx y).mulVec (u y)) + c • (∫ y, e y • (a y).mulVec (u y)) := by
    simp only [forwardOutputAmplitude, Matrix.add_mulVec, Matrix.smul_mulVec, smul_add]
    change (∫ y, e y • (dx y).mulVec (u y) + e y • c • (a y).mulVec (u y)) = _
    simp_rw [smul_comm (e _) c]
    simpa only [Pi.smul_apply, integral_smul] using integral_add hix (hi.smul c)
  have hrem : (∫ y, graphOscillation Φ x y δ •
      (forwardRemainderAmplitude B A j x y δ).mulVec (u y)) =
      (∫ y, e y • (dx y).mulVec (u y)) +
      ∑ l, b l • (∫ y, e y • (dy l y).mulVec (u y)) := by
    simp only [forwardRemainderAmplitude, Matrix.add_mulVec, Matrix.sum_mulVec,
      Matrix.smul_mulVec, smul_add, Finset.smul_sum]
    simp_rw [smul_comm (graphOscillation Φ x _ δ) (B x δ j _ : ℂ)]
    have hiy' (l : Fin n) : Integrable (fun y ↦ b l • e y • (dy l y).mulVec (u y)) :=
      (hiy l).smul (b l)
    change (∫ y, e y • (dx y).mulVec (u y) + ∑ l, b l • e y • (dy l y).mulVec (u y)) = _
    rw [integral_add hix (integrable_finsetSum Finset.univ (fun l _ ↦ hiy' l)),
      integral_finsetSum Finset.univ (fun l _ ↦ hiy' l)]
    simp only [integral_smul]
    rfl
  rw [hout, hrem, hsum]
  simp only [forwardDatumAmplitude, Matrix.smul_mulVec]
  simp_rw [smul_comm (graphOscillation Φ x _ δ) (B x δ j _ : ℂ), integral_smul]
  simp only [smul_add, Finset.sum_add_distrib, add_assoc]
  rfl

/-- The transfer identity after the actual frequency integration, preserving
`graphOperator`'s `(2π)⁻ⁿ` normalization. The frequency integrability premises
apply to the literal regularized amplitudes, not to an abstract replacement
operator. Source: `app:ch_response:thm:response-literal-transfer`. -/
theorem graphOperator_forwardOutputAmplitude_transfer
    (Φ : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (u : Euclidean n → Fin r → ℂ) (x : Euclidean n) (j : Fin n)
    (hA : ∀ δ, ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 δ))
    (hu : ContDiff ℝ ∞ u) (hus : HasCompactSupport u)
    (hphase : ∀ δ, partialDeriv (fun z ↦ Φ z δ) x j = ∑ l, B x δ j l * δ l)
    (hr : Integrable (fun δ ↦ ∫ y, graphOscillation Φ x y δ •
      (forwardRemainderAmplitude B A j x y δ).mulVec (u y)))
    (hd : ∀ l, Integrable (fun δ ↦ ∫ y, graphOscillation Φ x y δ •
      (forwardDatumAmplitude B A j l x y δ).mulVec (partialDeriv u y l))) :
    graphOperator Φ (forwardOutputAmplitude Φ A j) u x =
      graphOperator Φ (forwardRemainderAmplitude B A j) u x +
      ∑ l, graphOperator Φ (forwardDatumAmplitude B A j l) (fun y ↦ partialDeriv u y l) x := by
  simp only [graphOperator]
  simp_rw [integral_forwardOutputAmplitude_transfer Φ A B u x _ j (hA _) hu hus (hphase _)]
  rw [integral_add hr (integrable_finsetSum _ (fun l _ ↦ hd l)),
    integral_finsetSum _ (fun l _ ↦ hd l), smul_add, Finset.smul_sum]

end JanetCartan.ResponseTransfer
