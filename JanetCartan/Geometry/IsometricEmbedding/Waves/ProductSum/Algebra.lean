module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.SignedExpansion
public import JanetCartan.Analysis.Operator.WeightedFamily.Synthesis

/-!
# One linear map on the complete signed sum

Algebra for `app:ch_pairs:prop:pairs-lag-sum`. The source is the full matrix
product, with arbitrary amplitudes (including modulation and current corrections).
Only the difference diagonal is removed. No analytic solver is constructed here.
-/

@[expose] public noncomputable section

open Matrix

namespace JanetCartan.ProductSum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The coefficient mass `𝒲μ` of `app:ch_pairs:eq:pairs-weighted-U`. -/
def coefficientMass (μ : ι → ℝ) : ℝ := (∑ j, Real.sqrt (μ j)) ^ 2

/-- Both ordered signed sums in `app:ch_pairs:eq:pairs-exact-offself`, including
the plus diagonal and excluding precisely the minus diagonal. -/
def weightedSignedSum (b : ℝ) (μ : ι → ℝ) (plus minus : ι → ι → V) : V :=
  b ^ 2 • ((∑ j, ∑ k, Real.sqrt (μ j * μ k) • plus j k) +
    ∑ j, ∑ k ∈ Finset.univ.erase j, Real.sqrt (μ j * μ k) • minus j k)

/-- One fixed linear map commutes with the literal complete sum, as required in
Step 2 of `app:ch_pairs:prop:pairs-lag-sum`. -/
theorem map_weightedSignedSum (L : V →ₗ[ℝ] W) (b : ℝ) (μ : ι → ℝ)
    (plus minus : ι → ι → V) :
    L (weightedSignedSum b μ plus minus) =
      weightedSignedSum b μ (fun j k ↦ L (plus j k)) (fun j k ↦ L (minus j k)) := by
  simp [weightedSignedSum, map_sum]

omit [DecidableEq ι] in
/-- The sample count enters only as `𝒲μ ≤ M Cμ`
(`app:ch_pairs:prop:pairs-lag-sum`). Zero weights are allowed. -/
theorem coefficientMass_le_card_mul (μ : ι → ℝ) (hμ : ∀ j, 0 ≤ μ j)
    {Cμ : ℝ} (hmass : ∑ j, μ j ≤ Cμ) :
    coefficientMass μ ≤ Fintype.card ι * Cμ := by
  simpa [coefficientMass] using WeightedFamily.sum_sqrt_sq_le_card_mul_bound
    Finset.univ μ (fun j _ ↦ hμ j) hmass

variable {X m n : Type*} [Fintype m]

/-- The complete sum-phase source as a field, from
`app:ch_pairs:lem:pairs-ledger`. Angles include the unit-torus `2π` factor. -/
def plusSource (θ : ι → X → ℝ) (A : ι → X → Matrix m n ℂ) (j k : ι) :
    X → Matrix n n ℝ := fun x ↦ signedPairPlus (θ j x) (θ k x) (A j x) (A k x)

/-- The complete difference-phase source from `app:ch_pairs:lem:pairs-ledger`.
Its diagonal is defined but never used in the signed sum. -/
def minusSource (θ : ι → X → ℝ) (A : ι → X → Matrix m n ℂ) (j k : ι) :
    X → Matrix n n ℝ := fun x ↦ signedPairMinus (θ j x) (θ k x) (A j x) (A k x)

/-- The actual quadratic derivative tensor minus the complete Hermitian self
tensor, `Q_off` in `app:ch_pairs:eq:pairs-exact-offself`. -/
def offSelfSource (b : ℝ) (μ : ι → ℝ) (dW A : ι → X → Matrix m n ℂ) :
    X → Matrix n n ℝ := fun x ↦
  (realWaveMatrixSum b μ (fun j ↦ dW j x))ᵀ *
    realWaveMatrixSum b μ (fun j ↦ dW j x) - hermitianSelfSum b μ (fun j ↦ A j x)

/-- The signed expansion is derived from derivative factorization, not assumed
as a ledger (`app:ch_pairs:eq:pairs-exact-offself`). -/
theorem offSelfSource_eq_weightedSignedSum (b : ℝ) (μ : ι → ℝ)
    (hμ : ∀ j, 0 ≤ μ j) (θ : ι → X → ℝ) (dW A : ι → X → Matrix m n ℂ)
    (hdW : ∀ j x, dW j x = wavePhase (θ j x) • A j x) :
    offSelfSource b μ dW A = weightedSignedSum b μ (plusSource θ A) (minusSource θ A) := by
  have hd : dW = fun j x ↦ wavePhase (θ j x) • A j x := funext fun j ↦ funext (hdW j)
  subst dW
  funext x
  simpa [offSelfSource, weightedSignedSum, plusSource, minusSource,
    Finset.sum_apply] using realWaveMatrixSum_offSelf_eq_signedPairs b μ
      (fun j ↦ θ j x) hμ (fun j ↦ A j x)

/-- The correction from the complete tensor equals the weighted sum of the
individual corrections for the same solver (`app:ch_pairs:eq:pairs-weighted-U`).
The linear map includes the fixed source cutoff and all reconstruction terms. -/
theorem solve_offSelfSource (S : (X → Matrix n n ℝ) →ₗ[ℝ] V) (b : ℝ)
    (μ : ι → ℝ) (hμ : ∀ j, 0 ≤ μ j) (θ : ι → X → ℝ)
    (dW A : ι → X → Matrix m n ℂ)
    (hdW : ∀ j x, dW j x = wavePhase (θ j x) • A j x) :
    S (offSelfSource b μ dW A) = weightedSignedSum b μ
      (fun j k ↦ S (plusSource θ A j k)) (fun j k ↦ S (minusSource θ A j k)) := by
  rw [offSelfSource_eq_weightedSignedSum b μ hμ θ dW A hdW, map_weightedSignedSum]

end JanetCartan.ProductSum
