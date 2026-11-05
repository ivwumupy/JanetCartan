module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.StressScaling
public import JanetCartan.Geometry.IsometricEmbedding.Mean.NormalizedBackground.SourceGeometry.Transport.Operator
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ReducedCoefficients

/-!
# Source dilation of the complete reduced-coefficient array

For `main:prop:seed` and `app:ch_regular:eq:coefficient-extension`, the actual
flat source dilation has zero connection terms. Its remaining coefficients
are the literal geometric projected stresses. Continuous linear row inclusions
transfer their Frobenius seminorm bounds to the full array's supremum norm.

The consumers are `ProtectedFlow.exists_extendedReducedCoefficients_low_neighborhood`,
the regular-sector coefficient class, and the fixed reference in `UniformStep`.
The neighborhood and source-scale interval precede every derivative order.
-/

open Set
open scoped ContDiff Topology Matrix.Norms.Frobenius

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace JanetCartan.ReferenceInitialization.FullCoefficientDilation
open GeometricProfile ProjectedStressFrame ProtectedFlow
variable {n : ℕ}

private def principalRowInclusion (i : Fin n) :
    MetricTensor n →L[ℝ] (ReducedCoefficientIndex n → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A c ↦ match c with
        | .inl (a, j, k) => if i = j then A a k else 0
        | .inr _ => 0
      map_add' := by
        intro A B
        funext c
        rcases c with ⟨a, j, k⟩ | ⟨j, k⟩
        · by_cases h : i = j <;> simp [h]
        · simp
      map_smul' := by
        intro a A
        funext c
        rcases c with ⟨b, j, k⟩ | ⟨j, k⟩
        · by_cases h : i = j <;> simp [h]
        · simp }

/-- The actual lower-order entries vanish for the flat source dilation in
`main:prop:seed`. This proves that the zero lower-order completion in
`app:ch_regular:eq:coefficient-extension` is the correct reference background. -/
theorem geometricReducedCoefficients_sourceDilation_lower_eq_zero
    (G : FlatReference n) {σ : ℝ} (hσ : 0 < σ) (x : Euclidean n) (i k : Fin n) :
    geometricReducedCoefficients (sourceDilation G.map σ) x (.inr (i, k)) = 0 := by
  have hΓ (a b c : Fin n) : christoffel (sourceDilation G.map σ) x a b c = 0 :=
    NormalizedBackground.SourceGeometry.christoffel_sourceDilation_eq_zero
      isOpen_univ G.contDiff.contDiffOn (fun y _ ↦ G.inducedMetric_eq_one y)
      hσ (mem_univ _) a b c
  simp [geometricReducedCoefficients, reducedZerothCoefficient, hΓ]

private theorem reducedDifference_eq_sum (G : FlatReference n)
    {σ : ℝ} (hσ : 0 < σ) {x : Euclidean n}
    (hr : Set.range (normalMap (sourceDilation G.map σ) x) =
      (normalSpace (sourceDilation G.map σ) x : Set (Euclidean (embeddingDimension n)))) :
    geometricReducedCoefficients (sourceDilation G.map σ) x -
        reducedCoefficientBackground (fun _ _ ↦ 0) x =
      ∑ i, principalRowInclusion i
        (projectedStress (sourceDilation G.map σ) x i - cubeStress n i) := by
  funext c
  rcases c with ⟨a, j, k⟩ | ⟨j, k⟩
  · simp only [Pi.sub_apply, geometricReducedCoefficients, reducedCoefficientBackground,
      NullTransport.principalCoefficient,
      ContinuumRow.ImageGeometry.geometricCubeStress_val_eq_projectedStress
        ((contDiff_sourceDilation G.contDiff).contDiffAt.of_le (by simp)) hr]
    simp [principalRowInclusion]
  · simp [geometricReducedCoefficients_sourceDilation_lower_eq_zero G hσ,
      reducedCoefficientBackground, principalRowInclusion]

private theorem cNorm_principalRowInclusion_le {K : Set (Euclidean n)}
    (hK : IsCompact K) (m : ℕ) (i : Fin n) {f : Euclidean n → MetricTensor n}
    (hf : ∀ x ∈ K, ContDiffAt ℝ m f x) :
    cNorm K m (principalRowInclusion i ∘ f) ≤
      (m + 1 : ℝ) * (‖principalRowInclusion i‖ * cNorm K m f) := by
  have hb := cNorm_le_sum_of_bounds (s := K) (r := m)
    (f := principalRowInclusion i ∘ f)
    (C := fun _ ↦ ‖principalRowInclusion i‖ * cNorm K m f)
    (fun _ _ ↦ mul_nonneg (norm_nonneg _) (cNorm_nonneg _ _ _))
    (fun j hj x hx ↦
      ((principalRowInclusion i).norm_iteratedFDeriv_comp_left (hf x hx)
        (by exact_mod_cast hj)).trans
        (mul_le_mul_of_nonneg_left
          (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK hf hx hj) (norm_nonneg _)))
  simpa using hb


/-- The full reduced array and literal principal frame are `O(σ)` for every
sufficiently small positive source scale (`main:prop:seed`,
`app:ch_regular:eq:coefficient-extension`). The fixed open neighborhood and
scale interval precede the derivative order, and each positive constant
precedes `σ`. Only the actual flat reference and compact physical set are inputs. -/
theorem exists_fullReducedCoefficients_dilation_bounds (G : FlatReference n)
    {K : Set (Euclidean n)} (hK : IsCompact K) :
    ∃ U : Set (Euclidean n), IsOpen U ∧ K ⊆ U ∧
      ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
        (∀ σ ∈ Icc (0 : ℝ) σ₀, ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U,
          t • (σ • x) ∈ G.domain.chart n) ∧
        (∀ σ ∈ Ioc (0 : ℝ) σ₀,
          ContDiff ℝ ∞ (sourceDilation G.map σ) ∧
          IsImmersionOn (sourceDilation G.map σ) U ∧
          HasFullNormalRankOn (sourceDilation G.map σ) U ∧
          ContDiffOn ℝ ∞ (geometricReducedCoefficients (sourceDilation G.map σ)) U) ∧
        ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ σ ∈ Ioc (0 : ℝ) σ₀,
          cNorm K m (geometricReducedCoefficients (sourceDilation G.map σ) -
            reducedCoefficientBackground (fun _ _ ↦ 0)) ≤ C * σ ∧
          ∀ i, cNorm K m (fun x ↦ projectedStress (sourceDilation G.map σ) x i -
            cubeStress n i) ≤ C * σ := by
  classical
  obtain ⟨U, hU, hKU, σ₀, hσ₀, hσ₁, hseg, hgeom, hb⟩ :=
    exists_projectedStress_dilation_bounds G hK
  refine ⟨U, hU, hKU, σ₀, hσ₀, hσ₁, hseg, ?_, ?_⟩
  · intro σ hσ
    obtain ⟨hi, hr, _⟩ := hgeom σ hσ
    exact ⟨contDiff_sourceDilation G.contDiff, hi, hr,
      ContinuumRow.ImageGeometry.contDiffOn_geometricReducedCoefficients
        (contDiff_sourceDilation G.contDiff) hU hi hr⟩
  · intro m
    obtain ⟨C, hC, hbound⟩ := hb m
    let A : ℝ := (m + 1 : ℝ) * ∑ i : Fin n, ‖principalRowInclusion i‖
    have hA : 0 ≤ A := mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
    refine ⟨(1 + A) * C, mul_pos (by positivity) hC, ?_⟩
    intro σ hσ
    obtain ⟨_, hr, hQ⟩ := hgeom σ hσ
    let f : Fin n → Euclidean n → MetricTensor n :=
      fun i x ↦ projectedStress (sourceDilation G.map σ) x i - cubeStress n i
    have hf (i : Fin n) (x : Euclidean n) (hx : x ∈ K) : ContDiffAt ℝ m (f i) x :=
      ((hQ i).contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const |>.of_le (by simp)
    have heq : cNorm K m (geometricReducedCoefficients (sourceDilation G.map σ) -
        reducedCoefficientBackground (fun _ _ ↦ 0)) =
        cNorm K m (fun x ↦ ∑ i, principalRowInclusion i (f i x)) := by
      apply cNorm_eq_of_eventuallyEq
      intro x hx
      filter_upwards [hU.mem_nhds (hKU hx)] with y hy
      exact reducedDifference_eq_sum G hσ.1 (hr y hy)
    constructor
    · rw [heq]
      calc
        _ ≤ ∑ i, cNorm K m (principalRowInclusion i ∘ f i) :=
          cNorm_sum_le_of_contDiffAt Finset.univ hK
            (fun i _ x hx ↦ (principalRowInclusion i).contDiff.contDiffAt.comp x (hf i x hx))
        _ ≤ ∑ i, (m + 1 : ℝ) * (‖principalRowInclusion i‖ * (C * σ)) := by
          apply Finset.sum_le_sum
          intro i _
          exact (cNorm_principalRowInclusion_le hK m i (hf i)).trans
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hbound σ hσ i) (norm_nonneg _)) (by positivity))
        _ = A * (C * σ) := by simp [A, Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ ≤ (1 + A) * C * σ := by nlinarith [mul_pos hC hσ.1]
    · intro i
      exact (hbound σ hσ i).trans (by nlinarith [mul_nonneg hA (mul_pos hC hσ.1).le])

end JanetCartan.ReferenceInitialization.FullCoefficientDilation
