module

public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Differential.BesselAdjoint

/-!
# Finite factorization of the published image channel and its actual normal

For `app:ch_background:eq:bg-commutator`, the normal is literally
`imageChannel c χmeas χsrc ∘L (imageChannel c χmeas χsrc).adjoint`.
The identities below expose its coefficient multipliers, the constant `J`
and `Dᵢ J` factors, and both unchanged physical cutoffs. No new image operator
or normal representation is introduced. Principal and connection terms are
both retained. The consumer is the higher image-normal commutator.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace

namespace JanetCartan.ContinuumCommutator.ImageChannel.Differential

open ContinuumRow PeriodicSobolevSpace

variable {n : ℕ}

/-- The actual adjoint of a real matrix coefficient multiplier transposes
its matrix unit (`app:ch_background:eq:bg-commutator`). -/
theorem reducedCoefficientMultiplier_adjoint (c : C(Torus n, ℝ)) (i k : Fin n) :
    (reducedCoefficientMultiplier c i k).adjoint = reducedCoefficientMultiplier c k i := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reducedCoefficientMultiplier_coeFn c k i u,
    reducedCoefficientMultiplier_coeFn c i k v] with x hu hv
  rw [hu, hv, real_inner_smul_left, real_inner_smul_right,
    EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right]
  simp only [map_one, one_mul, starRingEnd_apply, star_trivial]
  ring

/-- Exact finite coefficient/Bessel factorization of the existing image
channel, with both masks and every connection coefficient
(`app:ch_background:eq:bg-commutator`). -/
theorem imageChannel_eq_finiteFactors
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) :
    imageChannel c χmeas χsrc = cutoffMultiplier χmeas ∘L
      ((∑ a, ∑ i, ∑ k,
        reducedCoefficientMultiplier (c (.inl (a, i, k))) i k ∘L derivativeBessel a) +
        ∑ i, ∑ k, reducedCoefficientMultiplier (c (.inr (i, k))) i k ∘L
          periodicBesselInverse) ∘L cutoffMultiplier χsrc := by
  have h : reducedWeakOperator c ∘L periodicBesselLift =
      ((∑ a, ∑ i, ∑ k,
        reducedCoefficientMultiplier (c (.inl (a, i, k))) i k ∘L derivativeBessel a) +
        ∑ i, ∑ k, reducedCoefficientMultiplier (c (.inr (i, k))) i k ∘L
          periodicBesselInverse) := by
    ext1 u
    simp only [reducedWeakOperator, derivativeBessel, ContinuousLinearMap.comp_apply,
      add_apply, sum_apply, toL2_periodicBesselLift]
  calc
    imageChannel c χmeas χsrc = cutoffMultiplier χmeas ∘L
        (reducedWeakOperator c ∘L periodicBesselLift) ∘L cutoffMultiplier χsrc := by
      simp only [imageChannel, ContinuousLinearMap.comp_assoc]
    _ = _ := by rw [h]

/-- The Hilbert adjoint of the same image channel reverses the literal
factors. The principal factors have their proved minus sign, while the
zeroth-order connection terms remain present
(`app:ch_background:eq:bg-commutator`). -/
theorem imageChannel_adjoint_eq_finiteFactors
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) :
    (imageChannel c χmeas χsrc).adjoint = cutoffMultiplier χsrc ∘L
      ((∑ a, ∑ i, ∑ k,
        (-derivativeBessel a) ∘L reducedCoefficientMultiplier (c (.inl (a, i, k))) k i) +
        ∑ i, ∑ k, periodicBesselInverse ∘L
          reducedCoefficientMultiplier (c (.inr (i, k))) k i) ∘L cutoffMultiplier χmeas := by
  rw [imageChannel_eq_finiteFactors]
  simp only [ContinuousLinearMap.adjoint_comp, map_add, map_sum,
    cutoffMultiplier_adjoint, derivativeBessel_adjoint,
    periodicBesselInverse_adjoint, reducedCoefficientMultiplier_adjoint,
    ← ContinuousLinearMap.comp_assoc]

private theorem sandwich_comp (M S P Q : OutputL2 n →L[ℝ] OutputL2 n) :
    (M ∘L P ∘L S) ∘L (S ∘L Q ∘L M) = M ∘L P ∘L S ∘L S ∘L Q ∘L M := by
  simp only [ContinuousLinearMap.comp_assoc]

/-- The actual image normal has two finite coefficient factors, with both
source multipliers between them and the original measurement multipliers
outside. This is the concrete factorization used by the image contribution
to `app:ch_background:eq:bg-commutator`; it assumes no normal estimate. -/
theorem imageNormal_eq_finiteFactors
    (c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ))
    (χmeas χsrc : C(Torus n, ℝ)) :
    (imageChannel c χmeas χsrc) ∘L (imageChannel c χmeas χsrc).adjoint =
      cutoffMultiplier χmeas ∘L
        ((∑ a, ∑ i, ∑ k,
          reducedCoefficientMultiplier (c (.inl (a, i, k))) i k ∘L derivativeBessel a) +
          ∑ i, ∑ k, reducedCoefficientMultiplier (c (.inr (i, k))) i k ∘L
            periodicBesselInverse) ∘L
        cutoffMultiplier χsrc ∘L cutoffMultiplier χsrc ∘L
        ((∑ a, ∑ i, ∑ k,
          (-derivativeBessel a) ∘L
            reducedCoefficientMultiplier (c (.inl (a, i, k))) k i) +
          ∑ i, ∑ k, periodicBesselInverse ∘L
            reducedCoefficientMultiplier (c (.inr (i, k))) k i) ∘L
        cutoffMultiplier χmeas := by
  calc
    _ = (cutoffMultiplier χmeas ∘L
        ((∑ a, ∑ i, ∑ k,
          reducedCoefficientMultiplier (c (.inl (a, i, k))) i k ∘L derivativeBessel a) +
          ∑ i, ∑ k, reducedCoefficientMultiplier (c (.inr (i, k))) i k ∘L
            periodicBesselInverse) ∘L cutoffMultiplier χsrc) ∘L
        (cutoffMultiplier χsrc ∘L
        ((∑ a, ∑ i, ∑ k,
          (-derivativeBessel a) ∘L
            reducedCoefficientMultiplier (c (.inl (a, i, k))) k i) +
          ∑ i, ∑ k, periodicBesselInverse ∘L
            reducedCoefficientMultiplier (c (.inr (i, k))) k i) ∘L
        cutoffMultiplier χmeas) := congrArg₂ ContinuousLinearMap.comp
      (imageChannel_eq_finiteFactors c χmeas χsrc)
      (imageChannel_adjoint_eq_finiteFactors c χmeas χsrc)
    _ = _ := sandwich_comp _ _ _ _

end JanetCartan.ContinuumCommutator.ImageChannel.Differential
