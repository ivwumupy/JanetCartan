module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.Projection
public import JanetCartan.Geometry.IsometricEmbedding.Waves.ProductSum
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.Hermitian
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# The physical metric of the same sampled current family

Connect the physical primary sum in `main:eq:self-off` to the complete matrix
sources of `ProductSum`. The complex fields must be the final mean-updated
family, with its own full derivative amplitudes. This calculus and algebra
does not construct the fields, select a sample or prove their analytic bounds.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.UniformStep

variable {n N : ℕ} {ι : Type*} [Fintype ι]

/-- The actual real primary synthesis in `main:eq:self-off`. Its input is the
same complex family after all finite mean updates, including both quadratures. -/
def sampledPrimary (b : ℝ) (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) : Euclidean n → Euclidean N :=
  (b * Real.sqrt 2) • ∑ i, Real.sqrt (μ i) • (euclideanRealPart ∘ Z i)

/-- Full coordinate derivative of a sampled complex field, consumed by
`ProductSum.offSelfSource` (`app:ch_pairs:eq:pairs-exact-offself`). -/
def sampledDerivative (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (i : ι) (x : Euclidean n) : Matrix (Fin N) (Fin n) ℂ :=
  fun a j ↦ partialDeriv (Z i) x j a

/-- The literal full derivative amplitude of the final sampled field on its
original phase (`app:ch_pairs:eq:pairs-exact-offself`). This construction
supplies the global factorization used by the signed-sum identities. Analytic
profiles still have to be proved on the fixed source supports, where the
retained amplitude formula is identified with this same derivative. -/
def sampledDerivativeAmplitude
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    (i : ι) (x : Euclidean n) : Matrix (Fin N) (Fin n) ℂ :=
  wavePhase (-θ i x) • sampledDerivative Z i x

omit [Fintype ι] in
/-- `app:ch_pairs:lem:pairs-ledger`: the constructed full amplitude factors
the actual derivative everywhere. No global factorization premise is requested
from a producer whose formulas are valid only on its physical chart. -/
theorem sampledDerivative_eq_phase_smul_amplitude
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    (i : ι) (x : Euclidean n) :
    sampledDerivative Z i x = wavePhase (θ i x) • sampledDerivativeAmplitude Z θ i x := by
  rw [sampledDerivativeAmplitude, smul_smul, ← wavePhase_add]
  simp [wavePhase]

omit [Fintype ι] in
/-- A retained amplitude formula on its original chart agrees there with
the constructed sampled amplitude (`app:ch_response:eq:current-atomic-amplitudes`).
This transfers its local source estimates to the amplitude used by `ProductSum`
without identifying independently chosen fields or requiring equality outside
the validity chart. -/
theorem sampledDerivativeAmplitude_eqOn_of_factorization
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ)
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ) {U : Set (Euclidean n)}
    (h : ∀ i, Set.EqOn (sampledDerivative Z i) (fun x ↦ wavePhase (θ i x) • A i x) U) :
    ∀ i, Set.EqOn (sampledDerivativeAmplitude Z θ i) (A i) U := by
  intro i x hx
  rw [sampledDerivativeAmplitude, h i hx, smul_smul, ← wavePhase_add]
  simp [wavePhase]

/-- Smoothness of the physical sum follows from the same actual finite family
(`main:thm:step`), independently of signs and zero sample weights. -/
theorem contDiff_sampledPrimary (b : ℝ) (μ : ι → ℝ)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, ContDiff ℝ ∞ (Z i)) : ContDiff ℝ ∞ (sampledPrimary b μ Z) := by
  convert (ContDiff.sum (s := Finset.univ)
      (fun i _ ↦ (euclideanRealPart.contDiff.comp (hZ i)).const_smul
        (Real.sqrt (μ i)))).const_smul (b * Real.sqrt 2) using 1
  ext x a
  simp [sampledPrimary, Finset.sum_apply]

/-- `main:eq:primary` for the retained local atoms: their real weighted
synthesis is smooth on the SAME physical chart. This supplies the chart
regularity consumed by the fixed-cutoff periodization and metric ledger,
without extending or changing the complex fields. -/
theorem contDiffOn_sampledPrimary (b : ℝ) (μ : ι → ℝ)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)} {U : Set (Euclidean n)}
    (hZ : ∀ i, ContDiffOn ℝ ∞ (Z i) U) :
    ContDiffOn ℝ ∞ (sampledPrimary b μ Z) U := by
  convert (ContDiffOn.sum (s := Finset.univ)
    (fun i _ ↦ (euclideanRealPart.contDiff.comp_contDiffOn (hZ i)).const_smul
      (Real.sqrt (μ i)))).const_smul (b * Real.sqrt 2) using 1
  funext x
  simp only [sampledPrimary, Pi.smul_apply, Finset.sum_apply]

/-- The derivative of the physical primary is the literal real matrix sum
used in the signed-product theorem (`app:ch_pairs:lem:pairs-ledger`). -/
theorem differentialMatrix_sampledPrimary (b : ℝ) (μ : ι → ℝ)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)} {x : Euclidean n}
    (hZ : ∀ i, DifferentiableAt ℝ (Z i) x) :
    differentialMatrix (sampledPrimary b μ Z) x =
      realWaveMatrixSum b μ (fun i ↦ sampledDerivative Z i x) := by
  have hr (i : ι) : DifferentiableAt ℝ (euclideanRealPart ∘ Z i) x :=
    euclideanRealPart.differentiableAt.comp x (hZ i)
  have hd (i : ι) : fderiv ℝ (euclideanRealPart ∘ Z i) x =
      euclideanRealPart.comp (fderiv ℝ (Z i) x) :=
    (euclideanRealPart.hasFDerivAt.comp x (hZ i).hasFDerivAt).fderiv
  ext a j
  simp only [differentialMatrix, sampledPrimary, partialDeriv,
    fderiv_const_smul (DifferentiableAt.sum (fun i _ ↦ (hr i).const_smul _)),
    fderiv_sum (fun i _ ↦ (hr i).const_smul (Real.sqrt (μ i))),
    fderiv_const_smul (hr _), hd]
  simp [realWaveMatrixSum, Matrix.sum_apply, sampledDerivative, partialDeriv, Finset.sum_apply]

/-- The self/off splitting in `main:eq:self-off` is the actual induced metric
of the physical primary, with the SAME full amplitude family used by the mean.
No metric identity is assumed. The amplitude's analytic construction remains
with the corrected-atom and current-mean producers. -/
theorem offSelfSource_sampledDerivative (b : ℝ) (μ : ι → ℝ)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, Differentiable ℝ (Z i))
    (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ) :
    ProductSum.offSelfSource b μ (sampledDerivative Z) A =
      inducedMetric (sampledPrimary b μ Z) -
        b ^ 2 • CurrentMean.weightedHermitianTensor μ (fun x i ↦ A i x) := by
  funext x
  rw [Pi.sub_apply, inducedMetric_eq_transpose_mul,
    differentialMatrix_sampledPrimary b μ (fun i ↦ hZ i x)]
  rfl

/-- The complete signed source for the actual physical primary
(`app:ch_pairs:eq:pairs-exact-offself`). Its derivative factorization must come
from the same final mean-updated atoms; no replacement self tensor is chosen.
The doubled carriers remain in the plus sum. -/
theorem sampledPrimary_offSelf_eq_signedSum [DecidableEq ι] (b : ℝ) (μ : ι → ℝ)
    (hμ : ∀ i, 0 ≤ μ i)
    {Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)}
    (hZ : ∀ i, Differentiable ℝ (Z i))
    (θ : ι → Euclidean n → ℝ) (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hderivative : ∀ i x, sampledDerivative Z i x = wavePhase (θ i x) • A i x) :
    inducedMetric (sampledPrimary b μ Z) -
        b ^ 2 • CurrentMean.weightedHermitianTensor μ (fun x i ↦ A i x) =
      ProductSum.weightedSignedSum b μ (ProductSum.plusSource θ A) (ProductSum.minusSource θ A) := by
  rw [← offSelfSource_sampledDerivative b μ hZ A]
  exact ProductSum.offSelfSource_eq_weightedSignedSum b μ hμ θ _ A hderivative

/-- Unit phases cancel in the complete self tensor (`main:eq:self-off`). Thus
the mean recurrence on the literal derivatives and the signed-product theorem
on the full demodulated amplitudes use exactly the same `H`. -/
theorem weightedHermitian_sampledDerivative (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N))
    (θ : ι → Euclidean n → ℝ) (A : ι → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hderivative : ∀ i x, sampledDerivative Z i x = wavePhase (θ i x) • A i x) :
    CurrentMean.weightedHermitianTensor μ (fun x i ↦ sampledDerivative Z i x) =
      CurrentMean.weightedHermitianTensor μ (fun x i ↦ A i x) := by
  funext x
  unfold CurrentMean.weightedHermitianTensor
  apply Finset.sum_congr rfl
  intro i _
  change μ i • hermitianTensor (sampledDerivative Z i x) = μ i • hermitianTensor (A i x)
  rw [hderivative, hermitianTensor_smul]
  simp [wavePhase, Complex.normSq_eq_norm_sq]

/-- `main:eq:self-off`: the constructed sampled amplitude has exactly the
Hermitian tensor of the SAME physical derivatives used by the current mean.
Phase cancellation is proved for the actual amplitude, without a factorization
or self-tensor identity as an input. -/
theorem weightedHermitian_sampledDerivativeAmplitude (μ : ι → ℝ)
    (Z : ι → Euclidean n → EuclideanSpace ℂ (Fin N)) (θ : ι → Euclidean n → ℝ) :
    CurrentMean.weightedHermitianTensor μ (fun x i ↦ sampledDerivative Z i x) =
      CurrentMean.weightedHermitianTensor μ (fun x i ↦ sampledDerivativeAmplitude Z θ i x) :=
  weightedHermitian_sampledDerivative μ Z θ (sampledDerivativeAmplitude Z θ)
    (sampledDerivative_eq_phase_smul_amplitude Z θ)

end JanetCartan.UniformStep
