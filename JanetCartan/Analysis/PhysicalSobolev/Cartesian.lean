module

public import JanetCartan.Iteration.PhysicalPairs.FourierNorm
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.LocalDuality.WeakJetFourier
public import JanetCartan.Analysis.Sobolev.Local.Comparison.SmoothBounds.NormComparison

/-!
# Cartesian derivatives control the same physical Fourier Sobolev norm

For paper-v2 `main:prop:primary`, `main:prop:mean`, and `main:prop:pairs`,
actual compactly supported physical fields are estimated by their local jets.
The estimates below transfer those bounds to the radian Bessel norm consumed by
`RevisedStage.increment_estimates_of_physicalSobolev_profiles`. The real Schwartz
representative, physical Lebesgue measure, and derivative order are unchanged.
Only a dimension/order dependent constant is lost, never a frequency power.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Set MeasureTheory FourierTransform
open scoped SchwartzMap ContDiff

namespace JanetCartan.PhysicalSobolev

open LocalSobolev Pseudodifferential ArbitraryAccuracy

variable {n N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private theorem memLp_schwartz_iteratedFDeriv (u : 𝓢(E, V)) (r : ℕ) :
    MemLp (iteratedFDeriv ℝ r u) 2 volume := by
  have hc : Continuous (iteratedFDeriv ℝ r u) :=
    (u.smooth ⊤).continuous_iteratedFDeriv (by simp)
  have hi : Integrable (fun x ↦ ‖iteratedFDeriv ℝ r u x‖) volume := by
    simpa only [pow_zero, one_mul] using u.integrable_pow_mul_iteratedFDeriv volume 0 r
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
  apply (hi.const_mul (SchwartzMap.seminorm ℝ 0 r u)).mono'
    (hc.norm.pow 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x ↦ by
    change ‖‖iteratedFDeriv ℝ r u x‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
    exact mul_le_mul_of_nonneg_right (u.norm_iteratedFDeriv_le_seminorm ℝ r x) (norm_nonneg _)

/-- The actual Fourier Bessel norm at order `r` is bounded by the finite sum
of the SAME real Schwartz field's physical L² Fréchet jets. The constant precedes
all fields and all carrier parameters; this is the lossless-order norm transfer
for `main:prop:primary`, `main:prop:mean`, and `main:prop:pairs`. -/
theorem exists_physicalWeightedNorm_le_jetL2 (n N r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N)),
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight (r : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal ≤
        C * ∑ j ∈ Finset.range (r + 1),
          (eLpNorm (iteratedFDeriv ℝ j u) 2 volume).toReal := by
  obtain ⟨C, hC, hfourier⟩ := componentFourierSobolev_extension_bounds n r
    (EuclideanSpace.basisFun (Fin N) ℝ)
  refine ⟨(2 * Real.pi) ^ r * C, by positivity, ?_⟩
  intro u
  let v : LocalL2 univ (EuclideanSpace ℝ (Fin N)) :=
    ((u.memLp 2 volume).restrict univ).toLp u
  let e : SobolevExtension univ r v :=
    { toFun := u
      jet := fun j ↦ iteratedFDeriv ℝ j u
      weakJet := Mollification.hasWeakJetOn_of_contDiff volume (u.smooth r) univ
      memLp_fun := u.memLp 2 volume
      memLp_jet := fun j _ ↦ memLp_schwartz_iteratedFDeriv u j
      restrict_eq := (MemLp.coeFn_toLp _).symm }
  have he : e.toL2 = u.toLp 2 volume := by
    apply Lp.ext
    exact e.toL2_coeFn.trans (u.coeFn_toLp 2 volume).symm
  have hn := (hfourier univ v e).2
  rw [he] at hn
  calc
    _ ≤ (2 * Real.pi) ^ r * vectorFourierSobolevNorm r
        ((PhysicalCutoff.complexify u).toLp 2 volume) :=
      PhysicalPairs.physicalWeightedNorm_le_vectorFourierSobolevNorm r _
    _ = (2 * Real.pi) ^ r *
        componentFourierSobolevNorm (EuclideanSpace.basisFun (Fin N) ℝ) r
          (u.toLp 2 volume) := by
      rw [PhysicalPairs.vectorFourierSobolevNorm_complexify_eq]
    _ ≤ (2 * Real.pi) ^ r * (C * e.jetNorm) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = _ := (mul_assoc _ _ _).symm

/-- The manuscript's Cartesian jet norm also controls the physical radian
Bessel norm of the SAME real Schwartz field at the SAME order. This combines
the actual smooth-jet comparison with the previous physical transfer, and does
not identify the Cartesian and Fréchet norms (`app:not:fourier`). -/
theorem exists_physicalWeightedNorm_le_cartesianJetNorm (n N r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin N)),
      (eLpNorm (fun ξ ↦ euclideanSobolevWeight (r : ℝ) ((2 * Real.pi) • ξ) •
        𝓕 (PhysicalCutoff.complexify u) ξ) 2 volume).toReal ≤
        C * cartesianJetNorm univ r (fun j ↦ iteratedFDeriv ℝ j u) := by
  obtain ⟨C, hC, hphysical⟩ := exists_physicalWeightedNorm_le_jetL2 n N r
  let A : ℝ := Real.sqrt ((r + 1) * BallExtension.frechetEnergyComparisonConstant n r)
  have hA : 0 < A := Real.sqrt_pos.2 (mul_pos (by positivity)
    (BallExtension.frechetEnergyComparisonConstant_pos n r))
  refine ⟨C * A, mul_pos hC hA, fun u ↦ (hphysical u).trans ?_⟩
  have hJ : ∀ j ≤ r, MemLp (iteratedFDerivWithin ℝ j u univ) 2 (volume.restrict univ) := by
    intro j _
    simpa only [iteratedFDerivWithin_univ, Measure.restrict_univ] using
      memLp_schwartz_iteratedFDeriv u j
  have hcompare := jetL2Norm_iteratedFDerivWithin_le_mul_cartesianJetNorm
    isOpen_univ r (u.smooth ⊤).contDiffOn hJ
  simp only [jetL2Norm, iteratedFDerivWithin_univ, Measure.restrict_univ] at hcompare
  exact (mul_le_mul_of_nonneg_left hcompare hC.le).trans_eq (mul_assoc _ _ _).symm

end JanetCartan.PhysicalSobolev
