module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Reconstruction.Coefficients
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Differential
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Carrier

/-!
# Complex extension and demodulation of the actual completion

Exact identities for `app:ch_response:eq:response-two-envelopes`. The response
below extends the published real completion on both quadratures. No inverse,
coefficient bound or Sobolev estimate is assumed by these algebraic identities.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

set_option backward.isDefEq.respectTransparency false

namespace JanetCartan.ResponseTransfer

/-- The two existing physical-carrier conventions agree
(`app:ch_response:eq:response-two-envelopes`). -/
theorem carrier_eq_waveCarrier {n : ℕ} (ρ : ℝ) (φ : Euclidean n → ℝ) :
    carrier ρ φ = waveCarrier ρ φ := by
  funext x
  simp only [carrier, waveCarrier, Complex.ofReal_mul, mul_assoc]

/-- The complex extension of the actual three reconstruction coefficients
(`app:ch_response:eq:response-full-map`). The tensor input is a complex matrix
with the existing Frobenius norm. -/
def completedVariationComplex {n N : ℕ} (F : Euclidean n → Euclidean N)
    (u : Euclidean n → EuclideanSpace ℂ (Fin n))
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) (x : Euclidean n) :
    EuclideanSpace ℂ (Fin N) :=
  complexCoefficient (reconstructionValueCoefficient F x) (fun j ↦ u x j) +
  complexCoefficient (reconstructionDerivativeCoefficient F x)
    (fun ij ↦ partialDeriv (fun y ↦ u y ij.2) x ij.1) +
  complexCoefficient (reconstructionSourceCoefficient F x) (fun ij ↦ h x ij.1 ij.2)

private theorem partialDeriv_re {n : ℕ} {f : Euclidean n → ℂ} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (i : Fin n) :
    partialDeriv (fun y ↦ (f y).re) x i = (partialDeriv f x i).re := by
  exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
    ((Complex.reCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv)

private theorem partialDeriv_im {n : ℕ} {f : Euclidean n → ℂ} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (i : Fin n) :
    partialDeriv (fun y ↦ (f y).im) x i = (partialDeriv f x i).im := by
  exact congrArg (fun L : Euclidean n →L[ℝ] ℝ ↦ L (EuclideanSpace.single i 1))
    ((Complex.imCLM.hasFDerivAt.comp x hf.hasFDerivAt).fderiv)

/-- The real quadrature is precisely the published `completedVariation`
(`app:ch_response:prop:response-ambient`). -/
theorem completedVariationComplex_re {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)}
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (k : Fin N) :
    (completedVariationComplex F u h x k).re =
      AmbientResponse.completedVariation F
        (fun y ↦ WithLp.toLp 2 (fun j ↦ (u y j).re))
        (fun y i j ↦ (h y i j).re) x k := by
  rw [completedVariation_eq_coefficients]
  simp only [completedVariationComplex, PiLp.add_apply, Complex.add_re,
    complexCoefficient_re]
  rw [show (fun ij : Fin n × Fin n ↦
      partialDeriv (fun y ↦ (u y ij.2).re) x ij.1) =
      (fun ij ↦ (partialDeriv (fun y ↦ u y ij.2) x ij.1).re) by
    funext ij
    exact partialDeriv_re ((differentiableAt_piLp 2).mp hu ij.2) ij.1]

/-- The imaginary quadrature uses exactly the same real completion, with no
discarded channel (`app:ch_response:prop:response-ambient`). -/
theorem completedVariationComplex_im {n N : ℕ} (F : Euclidean n → Euclidean N)
    {u : Euclidean n → EuclideanSpace ℂ (Fin n)}
    (h : Euclidean n → Matrix (Fin n) (Fin n) ℂ) {x : Euclidean n}
    (hu : DifferentiableAt ℝ u x) (k : Fin N) :
    (completedVariationComplex F u h x k).im =
      AmbientResponse.completedVariation F
        (fun y ↦ WithLp.toLp 2 (fun j ↦ (u y j).im))
        (fun y i j ↦ (h y i j).im) x k := by
  rw [completedVariation_eq_coefficients]
  simp only [completedVariationComplex, PiLp.add_apply, Complex.add_im,
    complexCoefficient_im]
  rw [show (fun ij : Fin n × Fin n ↦
      partialDeriv (fun y ↦ (u y ij.2).im) x ij.1) =
      (fun ij ↦ (partialDeriv (fun y ↦ u y ij.2) x ij.1).im) by
    funext ij
    exact partialDeriv_im ((differentiableAt_piLp 2).mp hu ij.2) ij.1]

/-- Literal demodulated reconstruction, retaining the carrier contribution
`i ρ dφ g` in the first derivative and the fixed source cutoff
(`app:ch_response:eq:response-graded-displacement`). -/
def reconstructionAmplitude {n N : ℕ} (F : Euclidean n → Euclidean N)
    (ρ : ℝ) (φ χ : Euclidean n → ℝ)
    (g : Euclidean n → EuclideanSpace ℂ (Fin n))
    (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ) (x : Euclidean n) :
    EuclideanSpace ℂ (Fin N) :=
  complexCoefficient (reconstructionValueCoefficient F x) (fun j ↦ g x j) +
  complexCoefficient (reconstructionDerivativeCoefficient F x)
    (fun ij ↦ waveFirstAmplitude ρ φ (fun y ↦ g y ij.2) x
      (EuclideanSpace.single ij.1 1)) +
  (χ x : ℂ) • complexCoefficient (reconstructionSourceCoefficient F x)
    (fun ij ↦ a x ij.1 ij.2)

/-- The physical completed variation is the carrier times the explicit
amplitude, not a separately chosen ambient field
(`app:ch_response:eq:response-graded-displacement`). -/
theorem completedVariationComplex_modulated {n N : ℕ}
    (F : Euclidean n → Euclidean N) {ρ : ℝ} {φ : Euclidean n → ℝ}
    (χ : Euclidean n → ℝ) {g : Euclidean n → EuclideanSpace ℂ (Fin n)}
    (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ) {x : Euclidean n}
    (hφ : DifferentiableAt ℝ φ x) (hg : DifferentiableAt ℝ g x) :
    completedVariationComplex F (modulatedWave ρ φ g)
      (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y)) x =
      waveCarrier ρ φ x • reconstructionAmplitude F ρ φ χ g a x := by
  have hd (i j : Fin n) :
      partialDeriv (fun y ↦ modulatedWave ρ φ g y j) x i =
      waveCarrier ρ φ x * waveFirstAmplitude ρ φ (fun y ↦ g y j) x
        (EuclideanSpace.single i 1) :=
    fderiv_modulatedWave hφ ((differentiableAt_piLp 2).mp hg j) _
  simp only [completedVariationComplex, hd, reconstructionAmplitude]
  change complexCoefficient _ (waveCarrier ρ φ x • (fun j ↦ g x j)) +
    complexCoefficient _ (waveCarrier ρ φ x • _) +
    complexCoefficient _ (waveCarrier ρ φ x • ((χ x : ℂ) • _)) = _
  rw [map_smul, map_smul, map_smul, map_smul, smul_add, smul_add]

/-- The observation cutoff is applied after the same reconstruction, as in
`app:ch_response:eq:response-two-envelopes`. -/
theorem demodulated_completedVariationComplex {n N : ℕ}
    (F : Euclidean n → Euclidean N) {ρ : ℝ} {φ : Euclidean n → ℝ}
    (χ ψ : Euclidean n → ℝ) {g : Euclidean n → EuclideanSpace ℂ (Fin n)}
    (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ) {x : Euclidean n}
    (hφ : DifferentiableAt ℝ φ x) (hg : DifferentiableAt ℝ g x) :
    waveCarrier (-ρ) φ x • ((ψ x : ℂ) •
      completedVariationComplex F (modulatedWave ρ φ g)
        (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y)) x) =
      (ψ x : ℂ) • reconstructionAmplitude F ρ φ χ g a x := by
  rw [completedVariationComplex_modulated F χ a hφ hg, smul_comm (ψ x : ℂ),
    smul_smul, waveCarrier_neg_mul, one_smul]

/-- The demodulated **physical** derivative of the same response has the
additional `i ρ dφ` term (`app:ch_response:eq:response-graded-derivative`).
The observation cutoff is not differentiated. Differentiability of the
explicit amplitude is a regularity input here; no bound on it is assumed. -/
theorem demodulated_physicalDerivative_completedVariationComplex {n N : ℕ}
    (F : Euclidean n → Euclidean N) {ρ : ℝ} {φ : Euclidean n → ℝ}
    (χ ψ : Euclidean n → ℝ) {g : Euclidean n → EuclideanSpace ℂ (Fin n)}
    (a : Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hφ : Differentiable ℝ φ) (hg : Differentiable ℝ g) (x v : Euclidean n)
    (hB : DifferentiableAt ℝ (reconstructionAmplitude F ρ φ χ g a) x) :
    waveCarrier (-ρ) φ x • ((ψ x : ℂ) •
      fderiv ℝ (completedVariationComplex F (modulatedWave ρ φ g)
        (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y))) x v) =
      (ψ x : ℂ) •
        ((Complex.I * (ρ : ℂ) * (fderiv ℝ φ x v : ℂ)) •
          reconstructionAmplitude F ρ φ χ g a x +
          fderiv ℝ (reconstructionAmplitude F ρ φ χ g a) x v) := by
  have he : completedVariationComplex F (modulatedWave ρ φ g)
      (fun y ↦ waveCarrier ρ φ y • ((χ y : ℂ) • a y)) =
      modulatedWave ρ φ (reconstructionAmplitude F ρ φ χ g a) := by
    funext y
    exact completedVariationComplex_modulated F χ a (hφ y) (hg y)
  rw [he, smul_comm (waveCarrier (-ρ) φ x),
    demodulated_fderiv_modulatedWave (hφ x) hB]
  rfl

end JanetCartan.ResponseTransfer
