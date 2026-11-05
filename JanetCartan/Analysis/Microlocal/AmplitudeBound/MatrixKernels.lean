module

public import JanetCartan.Analysis.Microlocal.AmplitudeBound.SourceEstimates
public import JanetCartan.Analysis.Microlocal.AmplitudeBound.Matrices
public import Mathlib.Analysis.Matrix.Normed

/-!
# Fixed matrix amplitude kernels

The fixed-matrix assertion of `app:ch_osc:lem:osc-amplitude` in `paper.tex`.
Matrix derivative bounds use the Frobenius norm. The operators act on finite
Hilbert direct sums of scalar L² spaces, with their `ℓ²` norm. Their coordinate
kernels are the finite sums of the literal scalar oscillatory integrals.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.AmplitudeBound

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Every entry is bounded by the Frobenius norm, for the matrix step of
`app:ch_osc:lem:osc-amplitude`. -/
theorem norm_matrixEntry_le_frobenius (M : Matrix I J ℂ) (i : I) (j : J) :
    ‖M i j‖ ≤ ‖M‖ :=
  (PiLp.norm_apply_le (WithLp.toLp 2 (M i)) j).trans
    (PiLp.norm_apply_le (WithLp.toLp 2 (fun i ↦ WithLp.toLp 2 (M i))) i)

/-- Entry evaluation is continuous for the Frobenius norm, as used in
`app:ch_osc:lem:osc-amplitude`. -/
def matrixEntryEvaluation (i : I) (j : J) : Matrix I J ℂ →L[ℝ] ℂ :=
  ({ toFun := fun M ↦ M i j
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl } : Matrix I J ℂ →ₗ[ℝ] ℂ).mkContinuous 1
    (fun M ↦ by
      change ‖M i j‖ ≤ 1 * ‖M‖
      rw [one_mul]
      exact norm_matrixEntry_le_frobenius M i j)

/-- Ordered physical derivatives of a matrix amplitude, computed entrywise,
for the total-order hypothesis of `app:ch_osc:lem:osc-amplitude`. -/
def matrixAmplitudeCoordinateDerivList {n : ℕ} (is : List (Fin n))
    (b : EuclideanSpace ℝ (Fin n) → Matrix I J ℂ) (z : EuclideanSpace ℝ (Fin n)) :
    Matrix I J ℂ := fun i j ↦ euclideanCoordinateDerivList is (fun z ↦ b z i j) z

/-- Strong convergence of every scalar entry gives strong convergence of the
finite matrix operator (`app:ch_osc:lem:osc-amplitude`). -/
theorem tendsto_matrixOperator_apply {H K α : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    {l : Filter α} (B : α → I → J → H →L[ℂ] K) (C : I → J → H →L[ℂ] K)
    (h : ∀ i j f, Tendsto (fun a ↦ B a i j f) l (𝓝 (C i j f)))
    (f : PiLp 2 (fun _ : J ↦ H)) :
    Tendsto (fun a ↦ matrixOperator (B a) f) l (𝓝 (matrixOperator C f)) := by
  have hc : Tendsto (fun a i ↦ matrixOperator (B a) f i) l
      (𝓝 (fun i ↦ matrixOperator C f i)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    simp_rw [matrixOperator_apply]
    exact tendsto_finsetSum _ (fun j _ ↦ h i j (f j))
  exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp hc

/-- Kernel realization passes from scalar entries to their finite matrix
operator (`app:ch_osc:lem:osc-amplitude`). -/
theorem matrixOperator_ae_kernel {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (B : I → J → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (K : I → J → Lp ℂ 2 μ → X → ℂ)
    (h : ∀ i j f, B i j f =ᵐ[μ] K i j f)
    (f : PiLp 2 (fun _ : J ↦ Lp ℂ 2 μ)) (i : I) :
    (matrixOperator B f) i =ᵐ[μ] fun x ↦ ∑ j, K i j (f j) x := by
  rw [matrixOperator_apply]
  have hall : ∀ᵐ x ∂μ, ∀ j, B i j (f j) x = K i j (f j) x :=
    ae_all_iff.mpr (fun j ↦ h i j (f j))
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun j ↦ B i j (f j)), hall]
    with x hsum hx
  exact hsum.trans (Finset.sum_congr rfl (fun j _ ↦ hx j))

set_option maxHeartbeats 800000 in
/-- Fixed-matrix assertion of `app:ch_osc:lem:osc-amplitude`, from smoothness,
fixed physical support and the Frobenius derivative budget. The compact-frequency
kernels have uniform bounds and converge strongly to the unbounded-frequency
operator. The constant depends only on the box, dimension and matrix sizes. -/
theorem exists_matrixTwoPositionAmplitudeOperator {d : ℕ} (hd : 0 < d) (R : ℝ)
    (b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin (2 * d)) → Matrix I J ℂ)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hs : ∀ ξ i j, SupportedInCenteredBox R (fun z ↦ b ξ z i j)) (A : ℝ)
    (hbound : ∀ ξ is, is.length ≤ 2 * (d + 1) → ∀ z,
      ‖matrixAmplitudeCoordinateDerivList is (b ξ) z‖ ≤ A) :
    ∃ (B : PiLp 2 (fun _ : J ↦ Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) →L[ℂ]
          PiLp 2 (fun _ : I ↦ Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2))
      (Bρ : ℝ → PiLp 2 (fun _ : J ↦ Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) →L[ℂ]
          PiLp 2 (fun _ : I ↦ Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2)),
      ‖B‖ ≤ (Fintype.card I : ℝ) * (Fintype.card J : ℝ) *
        (fixedBoxAmplitudeConstant d R * A) ∧
      (∀ ρ, ‖Bρ ρ‖ ≤ (Fintype.card I : ℝ) * (Fintype.card J : ℝ) *
        (fixedBoxAmplitudeConstant d R * A)) ∧
      (∀ ρ f i, (Bρ ρ f) i =ᵐ[volume] fun x ↦
        ∑ j, boxScalarAmplitudeKernel (fun ξ z ↦ b ξ z i j) ρ (f j) x) ∧
      (∀ f, Tendsto (fun ρ ↦ Bρ ρ f) atTop (𝓝 (B f))) ∧
      (∀ f i, Tendsto (fun ρ ↦ Lp.toTemperedDistribution ((Bρ ρ f) i)) atTop
        (𝓝 (Lp.toTemperedDistribution ((B f) i)))) := by
  have he (i : I) (j : J) : ContDiff ℝ ∞
      (Function.uncurry (fun ξ z ↦ b ξ z i j)) :=
    (matrixEntryEvaluation i j).contDiff.comp hb
  have hbd (i : I) (j : J) : HasAmplitudeDerivativeBound
      (fun ξ z ↦ b ξ z i j) (2 * (d + 1)) A := by
    intro ξ is hi z
    exact (norm_matrixEntry_le_frobenius _ i j).trans (hbound ξ is hi z)
  choose C Cρ hC hCρ hker hlim hdist using fun i j ↦
    exists_twoPositionAmplitudeOperator hd R (fun ξ z ↦ b ξ z i j)
      (he i j) (fun ξ ↦ hs ξ i j) A (hbd i j)
  have hmlim (f) := tendsto_matrixOperator_apply (fun ρ i j ↦ Cρ i j ρ) C hlim f
  refine ⟨matrixOperator C, fun ρ ↦ matrixOperator (fun i j ↦ Cρ i j ρ),
    norm_matrixOperator_le_of_entry_bound C _ hC,
    fun ρ ↦ norm_matrixOperator_le_of_entry_bound _ _ (fun i j ↦ hCρ i j ρ),
    fun ρ f i ↦ matrixOperator_ae_kernel _ _ (fun i j ↦ hker i j ρ) f i,
    hmlim, ?_⟩
  intro f i
  exact (Lp.toTemperedDistributionCLM ℂ
    (volume : Measure (EuclideanSpace ℝ (Fin d))) 2).continuous.continuousAt.tendsto.comp
      ((PiLp.proj (𝕜 := ℂ) 2
        (fun _ : I ↦ Lp (α := EuclideanSpace ℝ (Fin d)) ℂ 2) i).continuous.continuousAt.tendsto.comp
          (hmlim f))

end JanetCartan.AmplitudeBound
