module

public import JanetCartan.Iteration.PhysicalMean.GroupedCross
public import JanetCartan.Iteration.PhysicalMean.IndividualSource
public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Iteration.PhysicalSamplingShells.Samples

/-!
# Exact native input and full-field identities for original grouped samples

The grouped sample fields are exactly the whole disjoint-shell forward
integrals, not diagonal approximations. Original square-root weighted
adjoints pack to the SAME native aggregate input under the original shell
isometry, including zero weights (`app:ch_mean_pairs:defn:mean-canonical`,
`app:ch_mean_pairs:eq:block-bilinear`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean
open PhysicalForwardMean PhysicalSamplingShells RawInputRealization RawInputPartition ContinuumRow

/-- Exact reassembly of each original sample's full matrix field. This
identifies the grouped lower-field jets with the WHOLE disjoint-shell
integral estimated in IndividualSource; no shellwise norm sum is used. -/
theorem groupedAnnularForwardField_eq_wholeIntegral {n N : ℕ} {ν β : Type*}
    [Fintype β] [MetricSpace β] [DiscreteTopology β] [MeasurableSpace β] [BorelSpace β]
    (radius : ν × β → ℝ)
    (φ : ((ν × β) × Euclidean (n-1)) → Euclidean n → ℝ)
    (m : ((ν × β) × Euclidean (n-1)) → ℝ)
    (A : Fin N → Fin n → ((ν × β) × Euclidean (n-1)) → Euclidean n → ℂ)
    (hφ : ∀ i, Continuous (fun z : (β × Euclidean (n-1)) × Euclidean n ↦ φ ((i,z.1.1),z.1.2) z.2))
    (hm : ∀ i, Continuous (fun z : β × Euclidean (n-1) ↦ m ((i,z.1),z.2)))
    (hms : ∀ i, HasCompactSupport (fun z : β × Euclidean (n-1) ↦ m ((i,z.1),z.2)))
    (hAc : ∀ a c i, Continuous (fun z : (β × Euclidean (n-1)) × Euclidean n ↦ A a c ((i,z.1.1),z.1.2) z.2))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hAK : ∀ a c z, tsupport (A a c z) ⊆ K)
    (v : ∀ i : ν, Lp ℂ 2 (annularShellMeasure (fun j ↦ radius (i,j)))) (i : ν) (x : Euclidean n) :
    groupedAnnularForwardField radius φ m A
      (fun ij ↦ annularShellEquiv (fun j ↦ radius (ij.1,j)) (v ij.1) ij.2) i x =
      (∫ z : β × Euclidean (n-1), ((fun a c ↦ physicalForwardKernel
        (fun z ↦ φ ((i,z.1),z.2)) (fun z ↦ m ((i,z.1),z.2))
        (fun z y ↦ A a c ((i,z.1),z.2) y) x z*v i z) : Matrix (Fin N) (Fin n) ℂ)
        ∂annularShellMeasure (fun j ↦ radius (i,j)) : Matrix (Fin N) (Fin n) ℂ) := by
  let F : (β × Euclidean (n-1)) → Matrix (Fin N) (Fin n) ℂ := fun z a c ↦
    physicalForwardKernel (fun z ↦ φ ((i,z.1),z.2)) (fun z ↦ m ((i,z.1),z.2))
      (fun z y ↦ A a c ((i,z.1),z.2) y) x z*v i z
  have hi : Integrable F (annularShellMeasure (fun j ↦ radius (i,j))) :=
    (physicalMatrixForwardIntegral_integrable_apply
      (fun z ↦ φ ((i,z.1),z.2)) (fun z ↦ m ((i,z.1),z.2))
      (fun a c z y ↦ A a c ((i,z.1),z.2) y) (hφ i) (hm i) (hms i) (fun a c ↦ hAc a c i)
      hK (fun a c z ↦ hAK a c ((i,z.1),z.2)) (v i) (Lp.memLp (v i)) x).1
  change _ = ∫ z, F z ∂annularShellMeasure (fun j ↦ radius (i,j))
  have he : (∫ z, F z ∂annularShellMeasure (fun j ↦ radius (i,j))) =
      ∑ j : β, ∫ z, F z ∂(annularMeasure n (radius (i,j))).map (Prod.mk j) := by
    simpa only [annularShellMeasure, tsum_fintype] using integral_sum_measure hi
  refine Eq.trans ?_ he.symm
  apply Finset.sum_congr rfl
  intro j _
  rw [(measurableEmbedding_prodMk_left j).integral_map]
  apply integral_congr_ae
  filter_upwards [annularShellEquiv_ae (fun j ↦ radius (i,j)) (v i) j] with η hη
  change ((fun a c ↦ physicalForwardKernel (fun η ↦ φ ((i,j),η))
      (fun η ↦ m ((i,j),η)) (fun η y ↦ A a c ((i,j),η) y) x η*
      annularShellEquiv (fun j ↦ radius (i,j)) (v i) j η) : Matrix (Fin N) (Fin n) ℂ) = _
  rw [hη]
  rfl

/-- The exact native weighted input is the original sampled-shell inverse
isometry of the actual weighted adjoint column. This is an equality, valid
also for zero weights; no weight division or norm comparison is a premise. -/
theorem weightedAnnularInput_eq_sampledAdjoint {n J : ℕ} {ν : Type*}
    [Fintype ν] [MetricSpace ν] [DiscreteTopology ν] [MeasurableSpace ν] [BorelSpace ν]
    [MetricSpace (RefinedIndex J)] [DiscreteTopology (RefinedIndex J)] [BorelSpace (RefinedIndex J)]
    (weight : ν → ℝ)
    (A : ν → Input n (refinedRadius (J := J)) →L[ℝ] OutputL2 n) (w : OutputL2 n) :
    weightedAnnularInput (fun ij : ν × RefinedIndex J ↦ refinedRadius ij.2)
      (fun ij ↦ weight ij.1) (fun ij ↦ ((A ij.1).adjoint w) ij.2) =
      (sampledShellEquiv (V := ℂ) (ι := ν) n J).symm ((CanonicalRow.weightedRow weight A).adjoint w) := by
  apply (annularShellEquiv (V := ℂ) (fun ij : ν × RefinedIndex J ↦ refinedRadius ij.2)).injective
  rw [weightedAnnularInput, LinearIsometryEquiv.apply_symm_apply]
  simp only [sampledShellEquiv, LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
  apply PiLp.ext
  intro ij
  change Real.sqrt (weight ij.1) • ((A ij.1).adjoint w) ij.2 =
    ((CanonicalRow.weightedRow weight A).adjoint w ij.1) ij.2
  rw [CanonicalRow.weightedRow_adjoint_apply_component]
  rfl

/-- The original shell isometry transfers a literal real sampled row to its
actual native adjoint. This exact identity is the only row-realization input
needed to consume AggregateSource with the SAME current inverse. -/
theorem weightedAnnularInput_eq_nativeAdjoint {n J : ℕ} {ν : Type*}
    [Fintype ν] [MetricSpace ν] [DiscreteTopology ν] [MeasurableSpace ν] [BorelSpace ν]
    [MetricSpace (RefinedIndex J)] [DiscreteTopology (RefinedIndex J)] [BorelSpace (RefinedIndex J)]
    (weight : ν → ℝ)
    (A : ν → Input n (refinedRadius (J := J)) →L[ℝ] OutputL2 n)
    (R : Lp ℂ 2 (sampledShellMeasure (ι := ν) n J) →L[ℝ] OutputL2 n)
    (hR : (CanonicalRow.weightedRow weight A).comp
      ((sampledShellEquiv (V := ℂ) (ι := ν) n J).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ) = R)
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n) (u : OutputL2 n) :
    weightedAnnularInput (fun ij : ν × RefinedIndex J ↦ refinedRadius ij.2)
      (fun ij ↦ weight ij.1) (fun ij ↦ ((A ij.1).adjoint (Q₀ u)) ij.2) = R.adjoint (Q₀ u) := by
  let e : Lp ℂ 2 (sampledShellMeasure (ι := ν) n J) ≃ₗᵢ[ℝ]
      PiLp 2 (fun _ : ν ↦ Input n (refinedRadius (J := J))) :=
    { toLinearEquiv := (sampledShellEquiv (V := ℂ) (ι := ν) n J).toLinearEquiv.restrictScalars ℝ
      norm_map' := (sampledShellEquiv (V := ℂ) (ι := ν) n J).norm_map }
  have he : (sampledShellEquiv (V := ℂ) (ι := ν) n J).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ =
      e.toContinuousLinearEquiv.toContinuousLinearMap := rfl
  rw [weightedAnnularInput_eq_sampledAdjoint, ← hR, he, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, e.adjoint_eq_symm]
  rfl

end JanetCartan.PhysicalMean
