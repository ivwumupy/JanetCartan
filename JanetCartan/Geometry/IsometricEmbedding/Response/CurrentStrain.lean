module

public import JanetCartan.Geometry.IsometricEmbedding.Calculus

/-!
# Exact current strain cancellation

The algebraic identity in `main:lem:telescope` and `app:ch_lag:prop:lag-telescope`:
for `H = χ • linearizedMetric F W`, `Z = W - B H`, and
`E = linearizedMetric F (B H) - H`, the actual linearized metric of `Z` is `-E`
where `χ = 1`. This uses the real Euclidean fields and Frobenius tensor convention
of `Basic`.

The pointwise identity requires differentiability of `W` and `B H` at the
observation point. No derivative of the cutoff is taken. The finite synthesis
identities use one fixed real linear response and globally differentiable primary
fields, so that their sources agree globally before applying the response.
Differentiability of each response is required only on the observation set.

These results do not construct the response, bound its residual, or prove the
arbitrary-accuracy and measure-integration estimates in the cited statements.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace JanetCartan

variable {n N : ℕ} {F Y Z : Euclidean n → Euclidean N} {x : Euclidean n}

/-- `main:lem:telescope`: subtraction of differentiable variations commutes with
the actual linearized metric at the observation point. -/
theorem linearizedMetric_sub_apply (hY : DifferentiableAt ℝ Y x)
    (hZ : DifferentiableAt ℝ Z x) :
    linearizedMetric F (Y - Z) x = linearizedMetric F Y x - linearizedMetric F Z x := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    (linearizedMetric_add_apply (F := F) hY (hZ.const_smul (-1))).trans
      (congrArg (linearizedMetric F Y x + ·) (linearizedMetric_smul_apply hZ (-1)))

/-- `app:ch_lag:prop:lag-telescope`: the linearized metric commutes with finite sums
of variations differentiable at the observation point. -/
theorem linearizedMetric_sum_apply {ι : Type*} (t : Finset ι)
    (W : ι → Euclidean n → Euclidean N)
    (hW : ∀ i ∈ t, DifferentiableAt ℝ (W i) x) :
    linearizedMetric F (∑ i ∈ t, W i) x = ∑ i ∈ t, linearizedMetric F (W i) x := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      linearizedMetric_add_apply (hW i (Finset.mem_insert_self _ _))
        (DifferentiableAt.sum fun j hj ↦ hW j (Finset.mem_insert_of_mem hj))]
    rw [ih (fun j hj ↦ hW j (Finset.mem_insert_of_mem hj))]

/-- `app:ch_lag:prop:lag-telescope`: finite synthesis with constant real
coefficients commutes with the linearized metric. -/
theorem linearizedMetric_sum_smul_apply {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (W : ι → Euclidean n → Euclidean N)
    (hW : ∀ i ∈ t, DifferentiableAt ℝ (W i) x) :
    linearizedMetric F (∑ i ∈ t, a i • W i) x =
      ∑ i ∈ t, a i • linearizedMetric F (W i) x := by
  rw [linearizedMetric_sum_apply t _ (fun i hi ↦ (hW i hi).const_smul (a i))]
  exact Finset.sum_congr rfl fun i hi ↦ linearizedMetric_smul_apply (hW i hi) (a i)

/-- `main:eq:lag-recurrence`, `app:ch_lag:eq:lag-recurrence`: the complete source
`H = χ Dγ_F W` passed to the fixed response. -/
def currentStrainSource (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (W : Euclidean n → Euclidean N) : MetricField n :=
  fun x ↦ χ x • linearizedMetric F W x

/-- `main:eq:lag-recurrence`, `app:ch_lag:eq:lag-recurrence`: the corrected
variation `Z = W - B H`, using the complete cutoff source. -/
def currentStrainCorrected (F : Euclidean n → Euclidean N) (χ : Euclidean n → ℝ)
    (B : MetricField n → (Euclidean n → Euclidean N))
    (W : Euclidean n → Euclidean N) : Euclidean n → Euclidean N :=
  W - B (currentStrainSource F χ W)

/-- `main:lem:telescope`: the actual response residual `E = Dγ_F (B H) - H`.
Its smallness is a separate analytic input. -/
def currentStrainResidual (F : Euclidean n → Euclidean N)
    (B : MetricField n → (Euclidean n → Euclidean N)) (H : MetricField n) :
    MetricField n :=
  linearizedMetric F (B H) - H

/-- `main:eq:telescope`: on the source cutoff plateau, `Dγ_F Z = -E`.
Only the primary and response variations must be differentiable at this point;
linearity of the response is unnecessary for this single-source identity. -/
theorem currentStrain_cancellation_apply (χ : Euclidean n → ℝ)
    (B : MetricField n → (Euclidean n → Euclidean N))
    (W : Euclidean n → Euclidean N) (hχ : χ x = 1)
    (hW : DifferentiableAt ℝ W x)
    (hB : DifferentiableAt ℝ (B (currentStrainSource F χ W)) x) :
    linearizedMetric F (currentStrainCorrected F χ B W) x =
      -currentStrainResidual F B (currentStrainSource F χ W) x := by
  rw [currentStrainCorrected, linearizedMetric_sub_apply hW hB]
  simp only [currentStrainResidual, Pi.sub_apply, currentStrainSource, hχ, one_smul,
    neg_sub]

/-- `main:lem:telescope`, `app:ch_lag:prop:lag-telescope`: exact current strain
cancellation throughout a plateau set, with ordinary pointwise differentiability. -/
theorem currentStrain_cancellation (χ : Euclidean n → ℝ)
    (B : MetricField n → (Euclidean n → Euclidean N))
    (W : Euclidean n → Euclidean N) (s : Set (Euclidean n))
    (hχ : ∀ x ∈ s, χ x = 1)
    (hW : ∀ x ∈ s, DifferentiableAt ℝ W x)
    (hB : ∀ x ∈ s, DifferentiableAt ℝ (B (currentStrainSource F χ W)) x) :
    EqOn (linearizedMetric F (currentStrainCorrected F χ B W))
      (-currentStrainResidual F B (currentStrainSource F χ W)) s := by
  intro x hx
  exact currentStrain_cancellation_apply χ B W (hχ x hx) (hW x hx) (hB x hx)

/-- `app:ch_lag:defn:lag-recurrence`: the complete cutoff source commutes with
finite real synthesis. Global differentiability ensures global source equality. -/
theorem currentStrainSource_sum_smul {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (χ : Euclidean n → ℝ) (W : ι → Euclidean n → Euclidean N)
    (hW : ∀ i ∈ t, Differentiable ℝ (W i)) :
    currentStrainSource F χ (∑ i ∈ t, a i • W i) =
      ∑ i ∈ t, a i • currentStrainSource F χ (W i) := by
  funext x
  simp only [currentStrainSource, Finset.sum_apply, Pi.smul_apply]
  rw [linearizedMetric_sum_smul_apply t a W (fun i hi ↦ hW i hi x), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _

/-- `app:ch_lag:prop:lag-telescope`: correcting a finite synthesis with one fixed
linear response equals synthesizing the individually corrected fields. -/
theorem currentStrainCorrected_sum_smul {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (W : ι → Euclidean n → Euclidean N)
    (hW : ∀ i ∈ t, Differentiable ℝ (W i)) :
    currentStrainCorrected F χ B (∑ i ∈ t, a i • W i) =
      ∑ i ∈ t, a i • currentStrainCorrected F χ B (W i) := by
  simp only [currentStrainCorrected, currentStrainSource_sum_smul t a χ W hW,
    map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]

/-- `main:lem:telescope`, `app:ch_lag:prop:lag-telescope`: the strain of the
corrected finite synthesis is exactly the negative synthesis of the residuals
on the cutoff plateau. The same response is used for every summand. -/
theorem currentStrain_sum_cancellation_apply {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (W : ι → Euclidean n → Euclidean N) (hχ : χ x = 1)
    (hW : ∀ i ∈ t, Differentiable ℝ (W i))
    (hB : ∀ i ∈ t, DifferentiableAt ℝ (B (currentStrainSource F χ (W i))) x) :
    linearizedMetric F (currentStrainCorrected F χ B (∑ i ∈ t, a i • W i)) x =
      -(∑ i ∈ t, a i • currentStrainResidual F B (currentStrainSource F χ (W i)) x) := by
  have hd (i : ι) (hi : i ∈ t) :
      DifferentiableAt ℝ (currentStrainCorrected F χ B (W i)) x :=
    (hW i hi x).sub (hB i hi)
  rw [currentStrainCorrected_sum_smul t a χ B W hW,
    linearizedMetric_sum_smul_apply t a _ hd, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [currentStrain_cancellation_apply χ B (W i) hχ (hW i hi x) (hB i hi), smul_neg]

/-- `main:lem:telescope`, `app:ch_lag:prop:lag-telescope`: exact finite-synthesis
current strain cancellation on the common plateau set. -/
theorem currentStrain_sum_cancellation {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (W : ι → Euclidean n → Euclidean N) (s : Set (Euclidean n))
    (hχ : ∀ x ∈ s, χ x = 1)
    (hW : ∀ i ∈ t, Differentiable ℝ (W i))
    (hB : ∀ i ∈ t, ∀ x ∈ s,
      DifferentiableAt ℝ (B (currentStrainSource F χ (W i))) x) :
    EqOn (linearizedMetric F (currentStrainCorrected F χ B (∑ i ∈ t, a i • W i)))
      (-(∑ i ∈ t, a i • currentStrainResidual F B (currentStrainSource F χ (W i)))) s := by
  intro x hx
  simpa only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply] using
    currentStrain_sum_cancellation_apply t a χ B W (hχ x hx) hW (fun i hi ↦ hB i hi x hx)

end JanetCartan
