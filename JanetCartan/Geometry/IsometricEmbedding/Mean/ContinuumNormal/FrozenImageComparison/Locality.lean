module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenImageComparison.Model

/-!
# Local coefficient agreement for the actual image adjoint

The frozen comparison in `paper-v2.tex`, `app:ch_background:prop:bg-frame`,
only requires constant coefficients on the measurement plateau. Testing the
bounded weak operator against a supported L² field shows that its adjoint is
unchanged by the coefficients away from that support. In particular the actual
periodic extension need not be globally constant. No regularity of the input
field, or unbounded differential operator on L², is used.
-/

@[expose] public noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
open JanetCartan.ContinuumRow JanetCartan.AmplitudeBound

namespace JanetCartan.ContinuumNormal.FrozenImageComparison

variable {n : ℕ} {r R : ℝ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem inner_coefficient_eq_of_supported
    (c d : C(Torus n, ℝ)) (i j : Fin n) (u f : OutputL2 n) (s : Set (Torus n))
    (hf : ∀ᵐ z ∂volume, z ∉ s → f z = 0)
    (hcd : ∀ z ∈ s, c z = d z) :
    ⟪reducedCoefficientMultiplier c i j u, f⟫ =
      ⟪reducedCoefficientMultiplier d i j u, f⟫ := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reducedCoefficientMultiplier_coeFn c i j u,
    reducedCoefficientMultiplier_coeFn d i j u, hf] with z hc hd hzf
  rw [hc, hd]
  by_cases hz : z ∈ s
  · rw [hcd z hz]
  · rw [hzf hz, inner_zero_right, inner_zero_right]

private theorem inner_reducedWeak_eq_of_supported
    (c d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (u : PeriodicSobolevSpace n E 1) (f : OutputL2 n) (s : Set (Torus n))
    (hf : ∀ᵐ z ∂volume, z ∉ s → f z = 0)
    (hcd : ∀ k z, z ∈ s → c k z = d k z) :
    ⟪reducedWeakOperator c u, f⟫ = ⟪reducedWeakOperator d u, f⟫ := by
  simp only [reducedWeakOperator, add_apply, sum_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, sum_inner]
  congr 1
  · apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact inner_coefficient_eq_of_supported _ _ i j _ f s hf (hcd (.inl (a, i, j)))
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact inner_coefficient_eq_of_supported _ _ i j _ f s hf (hcd (.inr (i, j)))

/-- Equality of coefficient arrays on the support of an L² test gives equality
of the actual bounded image adjoints there, with both original masks retained
(`app:ch_background:prop:bg-frame`, frozen image comparison). -/
theorem imageChannel_adjoint_eq_of_supported_coefficients
    (c d : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (f : OutputL2 n) (s : Set (Torus n))
    (hf : ∀ᵐ z ∂volume, z ∉ s → f z = 0)
    (hcd : ∀ k z, z ∈ s → c k z = d k z) :
    (imageChannel c χmeas χsrc).adjoint f =
      (imageChannel d χmeas χsrc).adjoint f := by
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_right,
    imageChannel_apply, imageChannel_apply]
  simp only [← (cutoffMultiplier χmeas).adjoint_inner_right, cutoffMultiplier_adjoint]
  apply inner_reducedWeak_eq_of_supported c d _ _ s _ hcd
  filter_upwards [cutoffMultiplier_coeFn χmeas f, hf] with z hz hzf hzs
  rw [hz, hzf hzs, smul_zero]

/-- Agreement on the fixed measurement plateau suffices to freeze the literal
adjoint on every smaller quotient ball. There is no assumption about the
coefficient extension away from the plateau
(`app:ch_background:prop:bg-frame`, the limit `σ = 0`). -/
theorem imageChannel_adjoint_eq_fixed_of_plateau
    (hR : 0 < R) (hcell : 4 * R < 1 / 2) (hrR : r ≤ R)
    (A : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ k z, FixedCutoffs.periodic hR hcell 1 z = 1 →
      c k z = constantImageCoefficients A k z)
    (f : OutputL2 n)
    (hf : ∀ᵐ z ∂volume, z ∉ torusQuotient '' Metric.ball (0 : E) r → f z = 0) :
    (imageChannel c (FixedCutoffs.periodic hR hcell 1)
      (FixedCutoffs.periodic hR hcell 2)).adjoint f =
        (fixedPeriodicChannel hR hcell A).adjoint f := by
  apply imageChannel_adjoint_eq_of_supported_coefficients _ _ _ _ _ _ hf
  intro k z hz
  exact hc k z (fixedCutoff_one_on_innerBall hR hcell hrR 1 hz)

end JanetCartan.ContinuumNormal.FrozenImageComparison
