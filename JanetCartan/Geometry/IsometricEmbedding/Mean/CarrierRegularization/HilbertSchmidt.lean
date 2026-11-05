module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CarrierRegularization.BoundedKernel
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Squared-kernel identity on the carrier spaces

Parseval and dominated convergence prove the Hilbert–Schmidt identity for the
finite regularization of `app:ch_background:eq:bg-T`. The Hilbert–Schmidt and
compactness implications reuse `Analysis.Operator.HilbertSchmidt`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace JanetCartan.ContinuumRow.CarrierRegularization

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

variable {n : ℕ}
local notation "μ" => carrierMeasure n
local notation "ν" => (volume : Measure (Torus n))

variable {K : Torus n → CarrierVariable n → EuclideanSpace ℂ (Fin n)}
  {S : Set (CarrierVariable n)} {B : ℝ}
  (hK : StronglyMeasurable (Function.uncurry K))
  (hS : MeasurableSet S) (hfin : carrierMeasure n S ≠ ∞)
  (hs : ∀ x u, u ∉ S → K x u = 0)
  (hb : ∀ x u, ‖K x u‖ ≤ B)

include hK hb in
/-- Each kernel column defines an actual torus L² vector
(`app:ch_background:eq:bg-T`). -/
theorem memLp_column (u : CarrierVariable n) : MemLp (fun x ↦ K x u) 2 ν :=
  MemLp.of_bound hK.of_uncurry_right.aestronglyMeasurable B
    (Eventually.of_forall (fun x ↦ hb x u))

/-- Torus L² column of the literal kernel (`app:ch_background:eq:bg-T`). -/
def kernelColumn (u : CarrierVariable n) : ComplexOutputL2 n :=
  (memLp_column hK hb u).toLp _

include hK hb in
/-- The column squared norm is its literal integral
(`app:ch_background:eq:bg-T`). -/
theorem kernelColumn_norm_sq (u : CarrierVariable n) :
    ‖kernelColumn hK hb u‖ ^ 2 = ∫ x, ‖K x u‖ ^ 2 ∂ν := by
  rw [l2_vector_norm_sq_eq_integral (𝕜 := ℂ)]
  exact integral_congr_ae ((memLp_column hK hb u).coeFn_toLp.mono
    (fun _ hx ↦ congrArg (fun z ↦ ‖z‖ ^ 2) hx))

/-- A torus L² Hilbert basis is countable, as needed for kernel Parseval
in `app:ch_background:eq:bg-T`. -/
private theorem countable_output_basis {ι : Type*}
    (b : HilbertBasis ι ℂ (ComplexOutputL2 n)) : Countable ι := by
  have hd : Pairwise (fun i j ↦ Disjoint (Metric.ball (b i) (1/2))
      (Metric.ball (b j) (1/2))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have he : ‖b i - b j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq ℂ, b.orthonormal.norm_eq_one, b.orthonormal.norm_eq_one,
        b.orthonormal.inner_eq_zero hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (b i - b j)]
  exact hd.countable_of_isOpen_disjoint (fun _ ↦ Metric.isOpen_ball)
    (fun i ↦ ⟨b i, by simp⟩)

include hK hS hfin hs hb

/-- Integrability of the squared column norm follows from the finite input
support, with the output torus kept normalized (`app:ch_background:eq:bg-T`). -/
theorem integrable_column_norm_sq :
    Integrable (fun u ↦ ‖kernelColumn hK hb u‖ ^ 2) μ := by
  have hmeas : AEStronglyMeasurable (fun u ↦ ‖kernelColumn hK hb u‖ ^ 2) μ := by
    simp_rw [kernelColumn_norm_sq]
    exact (hK.prod_swap.norm.pow 2).integral_prod_right'.aestronglyMeasurable
  apply ((integrableOn_const (C := B ^ 2) hfin).integrable_indicator hS).mono' hmeas
  apply Eventually.of_forall
  intro u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), kernelColumn_norm_sq]
  by_cases hu : u ∈ S
  · rw [Set.indicator_of_mem hu]
    calc
      _ ≤ ∫ _x : Torus n, B ^ 2 ∂ν := integral_mono
        ((memLp_two_iff_integrable_sq_norm (memLp_column hK hb u).aestronglyMeasurable).mp
          (memLp_column hK hb u)) (integrable_const _)
        (fun x ↦ pow_le_pow_left₀ (norm_nonneg _) (hb x u) 2)
      _ = _ := by simp
  · simp [Set.indicator_of_notMem hu, hs _ _ hu]

/-- Kernel columns give the already constructed adjoint
(`app:ch_background:eq:bg-realification`). -/
theorem boundedKernelOperator_hasAdjointKernel :
    HasAdjointKernel (boundedKernelOperator hK hS hfin hs hb) (kernelColumn hK hb) := by
  intro w
  filter_upwards [boundedKernelOperator_adjoint_ae hK hS hfin hs hb w] with u hu
  rw [hu, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_column hK hb u).coeFn_toLp] with x hx
  rw [show kernelColumn hK hb u x = K x u from hx]

/-- Parseval identifies the convergent squared adjoint sum with the full
squared-kernel integral (`app:ch_background:eq:bg-T`). -/
theorem boundedKernelOperator_hasSum {ι : Type*} [Countable ι]
    (b : HilbertBasis ι ℂ (ComplexOutputL2 n)) :
    HasSum (fun i ↦ ‖(boundedKernelOperator hK hS hfin hs hb).adjoint (b i)‖ ^ 2)
      (∫ u, ∫ x, ‖K x u‖ ^ 2 ∂ν ∂μ) := by
  let k := kernelColumn hK hb
  have hT := boundedKernelOperator_hasAdjointKernel hK hS hfin hs hb
  have hm (w : ComplexOutputL2 n) :
      AEStronglyMeasurable (fun u ↦ inner ℂ (w) (k u)) μ := by
    have he : (fun u ↦ inner ℂ (k u) w) =ᵐ[μ]
        (boundedKernelOperator hK hS hfin hs hb).adjoint w := (hT w).symm
    exact (Complex.continuous_conj.comp_aestronglyMeasurable
      ((Lp.aestronglyMeasurable _).congr he.symm)).congr
      (Eventually.of_forall (fun u ↦ inner_conj_symm _ _))
  have hp (u : CarrierVariable n) := hilbertBasis_hasSum_sq_inner b (k u)
  have hsum : HasSum (fun i ↦ ∫ u, ‖inner ℂ (b i) (k u)‖ ^ 2 ∂μ)
      (∫ u, ‖k u‖ ^ 2 ∂μ) := by
    apply hasSum_integral_of_dominated_convergence
      (fun i u ↦ ‖inner ℂ (b i) (k u)‖ ^ 2)
    · exact fun i ↦ (hm (b i)).norm.pow 2
    · exact fun i ↦ Eventually.of_forall (fun u ↦ by simp)
    · exact Eventually.of_forall (fun u ↦ (hp u).summable)
    · simpa only [(hp _).tsum_eq] using integrable_column_norm_sq hK hS hfin hs hb
    · exact Eventually.of_forall hp
  convert hsum using 1
  · funext i
    rw [l2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [hT (b i)] with u hu
    rw [hu, norm_inner_symm]
  · exact integral_congr_ae (Eventually.of_forall
      (fun u ↦ (kernelColumn_norm_sq hK hb u).symm))

/-- Exact Hilbert–Schmidt identity, including convergence
(`app:ch_background:eq:bg-T`). -/
theorem boundedKernelOperator_hilbertSchmidt {κ : Type*}
    (c : HilbertBasis κ ℂ (CarrierL2 n)) :
    IsHilbertSchmidt c (boundedKernelOperator hK hS hfin hs hb) ∧
      hilbertSchmidtSq c (boundedKernelOperator hK hS hfin hs hb) =
        ∫ u, ∫ x, ‖K x u‖ ^ 2 ∂ν ∂μ := by
  obtain ⟨_, b, _⟩ := exists_hilbertBasis ℂ (ComplexOutputL2 n)
  let := countable_output_basis b
  have ht := boundedKernelOperator_hasSum hK hS hfin hs hb b
  obtain ⟨hh, he⟩ := isHilbertSchmidt_adjoint b c
    (boundedKernelOperator hK hS hfin hs hb).adjoint ht.summable
  rw [ContinuousLinearMap.adjoint_adjoint] at hh he
  exact ⟨hh, he.trans ht.tsum_eq⟩

/-- Finite regularizations are compact on the literal input and output
Hilbert spaces (`app:ch_background:eq:bg-T`). -/
theorem boundedKernelOperator_isCompact :
    IsCompactOperator (boundedKernelOperator hK hS hfin hs hb) := by
  obtain ⟨_, c, _⟩ := exists_hilbertBasis ℂ (CarrierL2 n)
  exact (boundedKernelOperator_hilbertSchmidt hK hS hfin hs hb c).1.isCompactOperator

/-- Rough squared-kernel bound by source volume. The normalized torus
contributes exactly one (`app:ch_background:eq:bg-T`). -/
theorem boundedKernelOperator_sq_integral_le :
    (∫ u, ∫ x, ‖K x u‖ ^ 2 ∂ν ∂μ) ≤ B ^ 2 * (carrierMeasure n).real S := by
  simp_rw [← kernelColumn_norm_sq hK hb]
  calc
    _ ≤ ∫ u, S.indicator (fun _ ↦ B ^ 2) u ∂μ := by
      apply integral_mono (integrable_column_norm_sq hK hS hfin hs hb)
        ((integrableOn_const (C := B ^ 2) hfin).integrable_indicator hS)
      intro u
      dsimp only
      rw [kernelColumn_norm_sq]
      by_cases hu : u ∈ S
      · rw [Set.indicator_of_mem hu]
        calc
          _ ≤ ∫ _x : Torus n, B ^ 2 ∂ν := integral_mono
            ((memLp_two_iff_integrable_sq_norm
              (memLp_column hK hb u).aestronglyMeasurable).mp (memLp_column hK hb u))
            (integrable_const _) (fun x ↦ pow_le_pow_left₀ (norm_nonneg _) (hb x u) 2)
          _ = _ := by simp
      · simp [Set.indicator_of_notMem hu, hs _ _ hu]
    _ = _ := by rw [integral_indicator_const _ hS]; simp [mul_comm]

end JanetCartan.ContinuumRow.CarrierRegularization
