module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.ReducedOperator

/-!
# The literal weak adjoint of the reduced periodic operator

For the image channel in `app:ch_background:defn:bg-row`, the formal adjoint of
`app:ch_waves:eq:reduced-symbol` differentiates the transposed principal
coefficients and retains the transposed zeroth-order connection coefficients.
The real L² pairing identity holds for every H¹ input and every smooth test.

The image-channel construction can apply this identity to `χ_meas g` before
composing with the Bessel inverse and source cutoff. Smooth periodic geometric
coefficient extensions and cutoffs are inputs to that parent construction.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace
namespace JanetCartan.ContinuumRow

variable {n : ℕ}

private theorem smooth_product {c : Torus n → ℝ} {g : Torus n → Euclidean n}
    (hc : IsSmoothPeriodic c) (hg : IsSmoothPeriodic g) (i : Fin n) :
    IsSmoothPeriodic (fun x ↦ c x * g x i) := by
  have hi := hg.comp_clm (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) i)
  exact ⟨hc.1.mul hi.1, hc.2.mul hi.2⟩

private theorem smooth_single {f : Torus n → ℝ} (hf : IsSmoothPeriodic f) (k : Fin n) :
    IsSmoothPeriodic (fun x ↦ f x • EuclideanSpace.single k (1 : ℝ)) := by
  exact hf.comp_clm ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single k (1 : ℝ)))

private theorem deriv_single {f : Torus n → ℝ} (hf : IsSmoothPeriodic f) (a k : Fin n) :
    periodicCoordinateDeriv a (fun x ↦ f x • EuclideanSpace.single k (1 : ℝ)) =
      fun x ↦ periodicCoordinateDeriv a f x • EuclideanSpace.single k (1 : ℝ) := by
  exact periodicCoordinateDeriv_comp_clm hf
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single k (1 : ℝ))) a

private theorem smooth_sum {ι : Type*} [Fintype ι] {f : ι → Torus n → Euclidean n}
    (hf : ∀ i, IsSmoothPeriodic (f i)) : IsSmoothPeriodic (fun x ↦ ∑ i, f i x) := by
  exact ⟨continuous_finsetSum _ (fun i _ ↦ (hf i).1),
    ContDiff.sum (fun i _ ↦ (hf i).2)⟩

/-- The literal formal adjoint of the reduced coefficient formula, including
all zeroth-order terms (`app:ch_waves:eq:reduced-symbol`). Its weak pairing
identity supplies the adjoint factor of `app:ch_background:defn:bg-row`. -/
def reducedFormalAdjoint
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (g : Torus n → Euclidean n) (x : Torus n) : Euclidean n :=
  -(∑ a, ∑ i, ∑ k,
    periodicCoordinateDeriv a (fun y ↦ c (.inl (a, i, k)) y * g y i) x •
      EuclideanSpace.single k (1 : ℝ)) +
    ∑ i, ∑ k, (c (.inr (i, k)) x * g x i) • EuclideanSpace.single k (1 : ℝ)

/-- The kth component is `-∑ₐ ∑ᵢ ∂ₐ(cₐᵢₖ gᵢ) + ∑ᵢ c₀ᵢₖ gᵢ`
(`app:ch_waves:eq:reduced-symbol`; `app:ch_background:defn:bg-row`). -/
theorem reducedFormalAdjoint_apply
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (g : Torus n → Euclidean n) (x : Torus n) (k : Fin n) :
    reducedFormalAdjoint c g x k =
      -(∑ a, ∑ i, periodicCoordinateDeriv a (fun y ↦ c (.inl (a, i, k)) y * g y i) x) +
        ∑ i, c (.inr (i, k)) x * g x i := by
  classical
  simp [reducedFormalAdjoint, EuclideanSpace.single, Pi.single_apply, mul_ite]

/-- Smooth coefficients and a smooth test give a smooth formal adjoint,
allowing its use as an actual L² representative in the image channel
(`app:ch_background:defn:bg-row`). -/
theorem isSmoothPeriodic_reducedFormalAdjoint
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j))
    (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) :
    IsSmoothPeriodic (reducedFormalAdjoint c g) := by
  have hfirst := smooth_sum (fun a ↦ smooth_sum (fun i ↦ smooth_sum (fun k ↦
    smooth_single ((smooth_product (hc (.inl (a, i, k))) hg i).coordinateDeriv a) k)))
  have hzero := smooth_sum (fun i ↦ smooth_sum (fun k ↦
    smooth_single (smooth_product (hc (.inr (i, k))) hg i) k))
  exact ⟨hfirst.1.neg.add hzero.1, hfirst.2.neg.add hzero.2⟩

/-- The full product-rule expansion retains the derivative of the principal
coefficient, the derivative of the test, and the transposed connection term
(`app:ch_waves:eq:reduced-symbol`; `app:ch_background:defn:bg-row`). -/
theorem reducedFormalAdjoint_apply_expanded
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j))
    (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) (x : Torus n) (k : Fin n) :
    reducedFormalAdjoint c g x k =
      -(∑ a, ∑ i, periodicCoordinateDeriv a (c (.inl (a, i, k))) x * g x i) -
      (∑ a, ∑ i, c (.inl (a, i, k)) x * periodicCoordinateDeriv a g x i) +
      ∑ i, c (.inr (i, k)) x * g x i := by
  have hprod (a i : Fin n) :
      periodicCoordinateDeriv a (fun y ↦ c (.inl (a, i, k)) y * g y i) x =
        periodicCoordinateDeriv a (c (.inl (a, i, k))) x * g x i +
          c (.inl (a, i, k)) x * periodicCoordinateDeriv a g x i := by
    have hi := hg.comp_clm (PiLp.proj 2 (fun _ : Fin n ↦ ℝ) i)
    have h := congr_fun (periodicCoordinateDeriv_inner (hc (.inl (a, i, k))) hi a) x
    rw [periodicCoordinateDeriv_comp_clm hg] at h
    simpa only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, mul_comm,
      PiLp.proj_apply] using h
  rw [reducedFormalAdjoint_apply]
  simp_rw [hprod, Finset.sum_add_distrib]
  ring

private theorem coefficient_inner_smooth (c : C(Torus n, ℝ)) (i k : Fin n)
    (u : OutputL2 n) (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) :
    ⟪reducedCoefficientMultiplier c i k u,
      PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 g hg)⟫ =
      ∫ x, ⟪u x, (c x * g x i) • EuclideanSpace.single k (1 : ℝ)⟫ := by
  rw [inner_periodicL2_ofSmooth]
  apply integral_congr_ae
  filter_upwards [reducedCoefficientMultiplier_coeFn c i k u] with x hx
  rw [hx]
  simp only [real_inner_smul_left, inner_smul_right, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, map_one, one_mul, conj_trivial]
  ring

private theorem derivative_coefficient_inner (c : C(Torus n, ℝ))
    (hc : IsSmoothPeriodic c) (a i k : Fin n)
    (u : PeriodicSobolevSpace n (Euclidean n) 1)
    (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) :
    ⟪reducedCoefficientMultiplier c i k (reducedCoordinateDerivative a u),
      PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 g hg)⟫ =
      -(∫ x, ⟪PeriodicSobolevSpace.toL2 1 u x,
        periodicCoordinateDeriv a (fun y ↦ c y * g y i) x •
          EuclideanSpace.single k (1 : ℝ)⟫) := by
  rw [coefficient_inner_smooth]
  have h := PeriodicSobolevSpace.hasPeriodicWeakDerivative_coordinateDerivative 0 a u
    (fun x ↦ (c x * g x i) • EuclideanSpace.single k (1 : ℝ))
    (smooth_single (smooth_product hc hg i) k)
  rw [deriv_single (smooth_product hc hg i)] at h
  exact h

private theorem integral_inner_sum {ι : Type*} [Fintype ι]
    (u : OutputL2 n) {f : ι → Torus n → Euclidean n}
    (hf : ∀ j, IsSmoothPeriodic (f j)) :
    (∫ x, ⟪u x, ∑ j, f j x⟫) = ∑ j, ∫ x, ⟪u x, f j x⟫ := by
  simp_rw [inner_sum]
  exact integral_finsetSum _ (fun j _ ↦ integrable_inner_periodicL2_smooth u (hf j))

private theorem integral_inner_neg_add (u : OutputL2 n)
    {f g : Torus n → Euclidean n} (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) :
    (∫ x, ⟪u x, -f x + g x⟫) = -(∫ x, ⟪u x, f x⟫) + ∫ x, ⟪u x, g x⟫ := by
  simp only [inner_add_right, inner_neg_right]
  rw [integral_add (f := fun x ↦ -⟪u x, f x⟫) (integrable_inner_periodicL2_smooth u hf).neg
    (integrable_inner_periodicL2_smooth u hg), integral_neg]

/-- Weak L² adjoint identity for every H¹ input and every smooth vector test.
This supplies the literal `P*` factor in the image-channel adjoint of
`app:ch_background:defn:bg-row`, including all terms of
`app:ch_waves:eq:reduced-symbol`. Integration by parts follows from the actual
weak derivative, tested against `(c gᵢ)eₖ`. -/
theorem reducedWeakOperator_inner_formalAdjoint
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j))
    (u : PeriodicSobolevSpace n (Euclidean n) 1)
    (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) :
    ⟪reducedWeakOperator c u,
      PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 g hg)⟫ =
    ⟪PeriodicSobolevSpace.toL2 1 u,
      PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0
        (reducedFormalAdjoint c g) (isSmoothPeriodic_reducedFormalAdjoint c hc g hg))⟫ := by
  have hfirst (a i k : Fin n) :=
    smooth_single ((smooth_product (hc (.inl (a, i, k))) hg i).coordinateDeriv a) k
  have hzero (i k : Fin n) := smooth_single (smooth_product (hc (.inr (i, k))) hg i) k
  simp only [reducedWeakOperator, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, sum_inner]
  simp_rw [derivative_coefficient_inner _ (hc _) _ _ _ u g hg,
    coefficient_inner_smooth _ _ _ _ g hg]
  rw [inner_periodicL2_ofSmooth]
  unfold reducedFormalAdjoint
  rw [integral_inner_neg_add _
    (smooth_sum fun a ↦ smooth_sum fun i ↦ smooth_sum (hfirst a i))
    (smooth_sum fun i ↦ smooth_sum (hzero i))]
  rw [integral_inner_sum _ (fun a ↦ smooth_sum fun i ↦ smooth_sum (hfirst a i)),
    integral_inner_sum _ (fun i ↦ smooth_sum (hzero i))]
  simp_rw [integral_inner_sum _ (fun i ↦ smooth_sum (hfirst _ i)),
    integral_inner_sum _ (hfirst _ _), integral_inner_sum _ (hzero _),
    Finset.sum_neg_distrib]

end JanetCartan.ContinuumRow
