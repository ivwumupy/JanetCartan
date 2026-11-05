module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.Bessel
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image.WeakAdjoint

/-!
# Construction of the continuum image channel

For `app:ch_background:defn:bg-row`, the reduced first-order factor is a
constructed bounded operator H¹ → L² with an explicit coefficient bound.
Its smooth formula agrees with the actual geometric reduced operator wherever
the coefficient arrays agree. Both principal and connection coefficients occur.

The Bessel inverse is constructed from the unit-torus Fourier basis and gains
one Sobolev order, including the L² endpoint. Composing its H¹ lift with the
weak reduced operator and fixed cutoffs gives an actual bounded image channel.
Its Hilbert adjoint on smooth tests is literally `χ_src J P* χ_meas`.

The input consists of continuous coefficient arrays and real continuous cutoffs;
the adjoint formula requires smooth coefficients and measurement cutoff. The
parent `jc-continuum-row` must instantiate the periodic geometric extension,
its agreement with the geometric arrays, and the fixed coefficient bounds.
This conditional construction does not assert the existence of those extensions
or identify the torus measure with Euclidean initial-data measures.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumRow

variable {n : ℕ}

/-- The actual image channel `χ_meas P ⟨D⟩⁻¹ χ_src` on the full real L²
space (`app:ch_background:defn:bg-row`). The reduced factor acts on the
constructed H¹ lift, so no image-channel boundedness is assumed. -/
def imageChannel
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) : OutputL2 n →L[ℝ] OutputL2 n :=
  cutoffMultiplier χmeas ∘L reducedWeakOperator c ∘L
    periodicBesselLift ∘L cutoffMultiplier χsrc

/-- Literal factorization of the image channel
(`app:ch_background:defn:bg-row`). -/
theorem imageChannel_apply
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (u : OutputL2 n) :
    imageChannel c χmeas χsrc u = cutoffMultiplier χmeas
      (reducedWeakOperator c (periodicBesselLift (cutoffMultiplier χsrc u))) := rfl

/-- Pointwise measurement cutoff on the weak reduced output
(`app:ch_background:defn:bg-row`). -/
theorem imageChannel_coeFn
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (u : OutputL2 n) :
    imageChannel c χmeas χsrc u =ᵐ[volume] fun x ↦ χmeas x •
      reducedWeakOperator c (periodicBesselLift (cutoffMultiplier χsrc u)) x :=
  cutoffMultiplier_coeFn _ _

/-- The fixed low coefficient norms control the full L² image operator
(`app:ch_background:prop:bg-frame`). -/
theorem imageChannel_norm_apply_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) (u : OutputL2 n) :
    ‖imageChannel c χmeas χsrc u‖ ≤
      (‖χmeas‖ * reducedCoefficientBound c * ‖χsrc‖) * ‖u‖ := by
  have hcut (χ : C(Torus n, ℝ)) (v : OutputL2 n) :
      ‖cutoffMultiplier χ v‖ ≤ ‖χ‖ * ‖v‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (cutoffMultiplier_norm_le χ) (norm_nonneg v))
  calc
    ‖imageChannel c χmeas χsrc u‖ ≤ ‖χmeas‖ *
        ‖reducedWeakOperator c (periodicBesselLift (cutoffMultiplier χsrc u))‖ :=
      hcut _ _
    _ ≤ ‖χmeas‖ * (reducedCoefficientBound c *
        ‖periodicBesselLift (cutoffMultiplier χsrc u)‖) :=
      mul_le_mul_of_nonneg_left (reducedWeakOperator_norm_apply_le _ _) (norm_nonneg _)
    _ = ‖χmeas‖ * (reducedCoefficientBound c * ‖cutoffMultiplier χsrc u‖) := by
      rw [norm_periodicBesselLift]
    _ ≤ ‖χmeas‖ * (reducedCoefficientBound c * (‖χsrc‖ * ‖u‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hcut _ _) (reducedCoefficientBound_nonneg c))
        (norm_nonneg _)
    _ = _ := by ring

/-- Operator-norm bound for the actual image channel
(`app:ch_background:prop:bg-frame`). -/
theorem imageChannel_norm_le
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) :
    ‖imageChannel c χmeas χsrc‖ ≤ ‖χmeas‖ * reducedCoefficientBound c * ‖χsrc‖ :=
  ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (norm_nonneg _) (reducedCoefficientBound_nonneg c))
      (norm_nonneg _)) (imageChannel_norm_apply_le c χmeas χsrc)

/-- Explicit bound from fixed entrywise sup bounds, including all zeroth-order
connection coefficients (`app:ch_background:prop:bg-frame`). -/
theorem imageChannel_norm_le_of_bounds
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) {C₁ C₀ : ℝ} (hC₁ : 0 ≤ C₁) (hC₀ : 0 ≤ C₀)
    (hfirst : ∀ a i k x, |c (.inl (a, i, k)) x| ≤ C₁)
    (hzero : ∀ i k x, |c (.inr (i, k)) x| ≤ C₀) :
    ‖imageChannel c χmeas χsrc‖ ≤
      ‖χmeas‖ * ((n : ℝ) ^ 3 * C₁ + (n : ℝ) ^ 2 * C₀) * ‖χsrc‖ :=
  (imageChannel_norm_le c χmeas χsrc).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (reducedCoefficientBound_le c hC₁ hC₀ hfirst hzero)
        (norm_nonneg _)) (norm_nonneg _))

/-- Smoothness of the measurement-cutoff test used in the weak image adjoint
(`app:ch_background:defn:bg-row`). -/
theorem isSmoothPeriodic_cutoff_smul (χ : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic χ) (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) :
    IsSmoothPeriodic (fun x ↦ χ x • g x) :=
  ⟨hχ.1.smul hg.1, hχ.2.smul hg.2⟩

/-- Multiplication of a smooth L² representative by a smooth cutoff is its
literal pointwise product (`app:ch_background:defn:bg-row`). -/
theorem cutoffMultiplier_ofSmooth (χ : C(Torus n, ℝ)) (hχ : IsSmoothPeriodic χ)
    (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) :
    cutoffMultiplier χ (PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 g hg)) =
      PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0
        (fun x ↦ χ x • g x) (isSmoothPeriodic_cutoff_smul χ hχ g hg)) := by
  apply Lp.ext
  filter_upwards [cutoffMultiplier_coeFn χ
    (PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 g hg)),
    PeriodicSobolevSpace.toL2_ofSmooth_ae 0 g hg,
    PeriodicSobolevSpace.toL2_ofSmooth_ae 0 _ (isSmoothPeriodic_cutoff_smul χ hχ g hg)]
    with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]

/-- The literal `χ_src J P* χ_meas` pairing for arbitrary L² input and smooth
tests (`app:ch_background:defn:bg-row`). The full coefficient derivative and
zeroth-order terms in `P*` are exposed by `reducedFormalAdjoint_apply_expanded`. -/
theorem imageChannel_inner_formalAdjoint
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j))
    (χmeas χsrc : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (u : OutputL2 n) (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) :
    ⟪imageChannel c χmeas χsrc u,
      PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 g hg)⟫ =
    ⟪u, cutoffMultiplier χsrc (periodicBesselInverse
      (PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0
        (reducedFormalAdjoint c (fun x ↦ χmeas x • g x))
        (isSmoothPeriodic_reducedFormalAdjoint c hc _
          (isSmoothPeriodic_cutoff_smul χmeas hχmeas g hg)))))⟫ := by
  rw [imageChannel_apply, ← ContinuousLinearMap.adjoint_inner_right,
    cutoffMultiplier_adjoint, cutoffMultiplier_ofSmooth χmeas hχmeas g hg,
    reducedWeakOperator_inner_formalAdjoint c hc,
    toL2_periodicBesselLift, periodicBesselInverse_inner,
    ← ContinuousLinearMap.adjoint_inner_right, cutoffMultiplier_adjoint]

/-- The bounded Hilbert adjoint agrees on every smooth test with the literal
weak adjoint `χ_src J P* χ_meas` (`app:ch_background:defn:bg-row`). -/
theorem imageChannel_adjoint_ofSmooth
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (hc : ∀ j, IsSmoothPeriodic (c j))
    (χmeas χsrc : C(Torus n, ℝ)) (hχmeas : IsSmoothPeriodic χmeas)
    (g : Torus n → Euclidean n) (hg : IsSmoothPeriodic g) :
    (imageChannel c χmeas χsrc).adjoint
      (PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0 g hg)) =
    cutoffMultiplier χsrc (periodicBesselInverse
      (PeriodicSobolevSpace.toL2 0 (PeriodicSobolevSpace.ofSmooth 0
        (reducedFormalAdjoint c (fun x ↦ χmeas x • g x))
        (isSmoothPeriodic_reducedFormalAdjoint c hc _
          (isSmoothPeriodic_cutoff_smul χmeas hχmeas g hg))))) := by
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact imageChannel_inner_formalAdjoint c hc χmeas χsrc hχmeas u g hg

end JanetCartan.ContinuumRow
