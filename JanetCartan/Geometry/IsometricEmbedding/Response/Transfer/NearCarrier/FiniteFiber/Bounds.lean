module

public import JanetCartan.Analysis.Microlocal.Pseudodifferential.Sobolev.MatrixBounds.Vector
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.DerivativeBounds.SpatialProfile

/-!
# Finite-fiber weighted envelope estimates

The finite-coordinate deduction in `app:ch_response:eq:direct-envelope-profile`.
The scalar premises are supplied by the parent's instantiation of
`AmplitudeExpression.exists_spatialSobolev_constant_of_zero`. This module proves
only their conversion to the existing vector Fourier Sobolev space. The constant
loses a fixed finite dimension factor; the weighted sum loses no powers of `L`.
-/

@[expose] public noncomputable section
open MeasureTheory
open JanetCartan.Pseudodifferential JanetCartan.AmplitudeBound
namespace JanetCartan.IsometricEmbedding.Response.NearCarrier.FiniteFiber

variable {d : ℕ} {I J : Type*} [Fintype I] [Fintype J]
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "L2" => Lp ℂ 2 (volume : Measure E)
local notation "V2" => Lp (EuclideanSpace ℂ J) 2 (volume : Measure E)
local notation "W2" => Lp (EuclideanSpace ℂ I) 2 (volume : Measure E)

/-- The exact weighted vector sum of `app:ch_response:eq:direct-envelope-profile`,
using the existing Hilbert Sobolev norms and Euclidean Lebesgue measure. -/
def vectorSpatialEnvelopeProfile (s : ℕ) (L : ℝ) (f : V2) : ℝ :=
  ∑ p ∈ Finset.range (s + 1), L ^ (s - p) * vectorFourierSobolevNorm (p : ℝ) f

/-- Every coordinate profile is bounded by the vector profile, term by term;
consumer: `vectorMatrix_weighted_bound` (`app:ch_response:eq:direct-envelope-profile`). -/
theorem spatialEnvelopeProfile_coordinate_le (s : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (f : V2) (j : J) :
    spatialEnvelopeSobolevProfile s L (finiteL2CoordinateIsometry volume f j) ≤
      vectorSpatialEnvelopeProfile s L f := by
  apply Finset.sum_le_sum
  intro p _
  exact mul_le_mul_of_nonneg_left
    (fourierSobolevNorm_coordinate_le (p : ℝ) (finiteL2CoordinateIsometry volume f) j)
    (pow_nonneg hL _)

/-- Finite rows of scalar outputs retain membership and their full triangle
bound. This is the common coordinate step for spatial and parameter profiles
in `app:ch_response:eq:direct-envelope-profile`. -/
theorem vectorSobolev_of_coordinate_sums (s : ℝ) (u : W2) (g : I → J → L2)
    (hu : ∀ i, finiteL2CoordinateIsometry volume u i = ∑ j, g i j)
    (hg : ∀ i j, MemFourierSobolev s (g i j)) :
    MemVectorFourierSobolev s u ∧
      vectorFourierSobolevNorm s u ≤ ∑ i, ∑ j, fourierSobolevNorm s (g i j) := by
  have hr (i : I) := fourierSobolev_finsetSum Finset.univ (g i) (fun j _ => hg i j)
  constructor
  · intro i
    rw [hu i]
    exact (hr i).1
  · apply (matrixFourierSobolevNorm_le_sum s (finiteL2CoordinateIsometry volume u)).trans
    exact Finset.sum_le_sum fun i _ => by rw [hu i]; exact (hr i).2

/-- The scalar weighted estimate gives the exact vector weighted estimate,
including Sobolev membership. The scalar premise is the output of the parent's
`DerivativeBounds` instantiation, not a claim that the selected graph has
already been estimated. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem vectorMatrix_weighted_bound
    (B : I → J → L2 →L[ℂ] L2) (s : ℕ) {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hB : ∀ i j f, MemFourierSobolev (s : ℝ) f →
      MemFourierSobolev (s : ℝ) (B i j f) ∧
        fourierSobolevNorm (s : ℝ) (B i j f) ≤ C * spatialEnvelopeSobolevProfile s L f)
    (f : V2) (hf : MemVectorFourierSobolev (s : ℝ) f) :
    MemVectorFourierSobolev (s : ℝ) (vectorMatrixL2Operator B f) ∧
      vectorFourierSobolevNorm (s : ℝ) (vectorMatrixL2Operator B f) ≤
        ((Fintype.card I : ℝ) * (Fintype.card J : ℝ) * C) *
          (∑ p ∈ Finset.range (s + 1), L ^ (s - p) * vectorFourierSobolevNorm (p : ℝ) f) := by
  have h := vectorSobolev_of_coordinate_sums (s : ℝ) (vectorMatrixL2Operator B f)
    (fun i j => B i j (finiteL2CoordinateIsometry volume f j))
    (fun i => by simp only [finiteL2CoordinateIsometry_vectorMatrixL2Operator,
      matrixOperator_apply]) (fun i j => (hB i j _ (hf j)).1)
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ ≤ ∑ _i : I, ∑ _j : J, C * vectorSpatialEnvelopeProfile s L f := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact (hB i j _ (hf j)).2.trans (mul_le_mul_of_nonneg_left
        (spatialEnvelopeProfile_coordinate_le s hL f j) hC)
    _ = _ := by simp [vectorSpatialEnvelopeProfile, mul_assoc]

/-- The literal Hilbert adjoint uses the transposed scalar adjoints; the same
weighted conversion applies to their reverse estimates. The complete reverse
amplitude, including any inverse weight, must be used by the scalar producer.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem vectorMatrix_adjoint_weighted_bound
    (B : I → J → L2 →L[ℂ] L2) (s : ℕ) {L C : ℝ} (hL : 0 ≤ L) (hC : 0 ≤ C)
    (hB : ∀ i j f, MemFourierSobolev (s : ℝ) f →
      MemFourierSobolev (s : ℝ) ((B i j).adjoint f) ∧
        fourierSobolevNorm (s : ℝ) ((B i j).adjoint f) ≤
          C * spatialEnvelopeSobolevProfile s L f)
    (f : W2) (hf : MemVectorFourierSobolev (s : ℝ) f) :
    MemVectorFourierSobolev (s : ℝ) ((vectorMatrixL2Operator B).adjoint f) ∧
      vectorFourierSobolevNorm (s : ℝ) ((vectorMatrixL2Operator B).adjoint f) ≤
        ((Fintype.card J : ℝ) * (Fintype.card I : ℝ) * C) *
          vectorSpatialEnvelopeProfile s L f := by
  rw [vectorMatrixL2Operator_adjoint]
  exact vectorMatrix_weighted_bound (fun j i => (B i j).adjoint) s hL hC
    (fun j i => hB i j) f hf

/-- Datum profiles convert the complete weighted sum to `K^s` without a
frequency loss (`app:ch_response:eq:direct-envelope-profile`). -/
theorem vectorSpatialEnvelopeProfile_le_K (s : ℕ) {L K A₀ : ℝ}
    (hL : 1 ≤ L) (hLK : L ≤ K) (D : ℕ → ℝ) (f : V2)
    (hf : ∀ p, p ≤ s → vectorFourierSobolevNorm (p : ℝ) f ≤ A₀ * D p * K ^ p) :
    vectorSpatialEnvelopeProfile s L f ≤
      A₀ * (∑ p ∈ Finset.range (s + 1), D p) * K ^ s := by
  have hL0 : 0 ≤ L := by linarith
  have hK0 : 0 ≤ K := hL0.trans hLK
  calc
    _ ≤ ∑ p ∈ Finset.range (s + 1), A₀ * D p * K ^ s := by
      apply Finset.sum_le_sum
      intro p hp
      have hps : p ≤ s := by have := Finset.mem_range.mp hp; omega
      calc
        _ ≤ K ^ (s - p) * (A₀ * D p * K ^ p) :=
          mul_le_mul (pow_le_pow_left₀ hL0 hLK _) (hf p hps)
            (norm_nonneg _) (pow_nonneg hK0 _)
        _ = _ := by rw [mul_left_comm, ← pow_add, Nat.sub_add_cancel hps]
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

end JanetCartan.IsometricEmbedding.Response.NearCarrier.FiniteFiber
