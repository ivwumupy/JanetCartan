module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.Homogeneity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.ImageSymbol

/-!
# Regularity and the common geometric threshold for a finite frozen family

These are finite-family deductions from the exact local geometric outputs of
`exists_frozen_conic_inputs`. They close the continuity, boundedness and radial
comparison steps of `app:ch_background:prop:bg-frame` for the literal matrix
symbol. Selecting a finite incidence cover and instantiating these geometric
inputs at a common primitive frame threshold remain construction obligations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n N : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : ∀ j, PatchQuantitativeFamily (P j) U hU)
    (G : ι → (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))

/-- One common physical frequency threshold for the retained finite family,
derived from every actual inverse comparison. The extra one handles an empty
family without changing the image estimate (`app:ch_background:prop:bg-frame`). -/
def frozenFamilyHighFrequencyRadius : ℝ :=
  1 + ∑ j, frozenHighFrequencyRadius (T j) (G j)

/-- The common threshold is at least one, including an empty family
(`app:ch_background:prop:bg-frame`). -/
theorem one_le_frozenFamilyHighFrequencyRadius : 1 ≤ frozenFamilyHighFrequencyRadius T G := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun j _ ↦ (zero_le_one.trans (one_le_frozenHighFrequencyRadius (T j) (G j)))

/-- The common threshold dominates the comparison threshold of each retained
chart (`app:ch_background:prop:bg-frame`). -/
theorem frozenHighFrequencyRadius_le_family (j : ι) :
    frozenHighFrequencyRadius (T j) (G j) ≤ frozenFamilyHighFrequencyRadius T G := by
  have hj := Finset.single_le_sum (s := Finset.univ) (f := fun j ↦ frozenHighFrequencyRadius (T j) (G j))
    (fun i _ ↦ zero_le_one.trans (one_le_frozenHighFrequencyRadius (T i) (G i))) (Finset.mem_univ j)
  exact hj.trans (le_add_of_nonneg_left zero_le_one)

variable (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ j, cNorm (closedBall (0 : Euclidean n) (T j).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < (T j).family.threshold)
    (F : Euclidean n → Euclidean N) (row col : ι → Fin n)
    (Φ Y : ι → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1)) (r a : ι → ℝ)
    (hηb : ∀ j, ηb j ≠ 0) (hr : ∀ j, 0 < r j) (ha : ∀ j, 0 < a j)
    {b cJ : ι → ℝ} {V L : ι → Set (ℝ × Euclidean (n - 1))}
    {c C : ℝ} (hP : ∀ j, (P j).IsValid c C)
    (har : ∀ j, 6 * a j ≤ 3 * r j)
    (hcarrier : ∀ j, closedBall (spectatorCenter (z₀ j)) (3 * r j) ×ˢ
      closedBall (z₀ j 0) (3 * r j) ⊆
        carrierParameters ⁻¹' parameterInterior (3 * (P j).radius / 2))
    (hf : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩))
      (physicalParameterSet (z₀ j) (6 * a j) ×ˢ dataSet (z₀ j) (ηb j) (3 * r j)))
    (hInv : ∀ j, BufferedPhaseInverse (adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩)
      (physicalParameterSet (z₀ j) (6 * a j)) (dataBox (z₀ j) (ηb j) (r j))
      (dataSet (z₀ j) (ηb j) (2 * r j)) (dataBox (z₀ j) (ηb j) (2 * r j))
      (V j) (L j) (b j) (cJ j) (G j))
    (htrans : ∀ j, ∀ p ∈ physicalParameterSet (z₀ j) (6 * a j),
      ∀ u ∈ supportedCone (z₀ j) (NormedSpace.normalize (ηb j)) (r j) (angularWidth (ηb j) (r j)),
        ‖(adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩ p u).2 - u.2‖ ≤
          (angularWidth (ηb j) (r j) / 4) * ‖u.2‖)
    (hcJ : ∀ j, 0 < cJ j) (hV : ∀ j, IsOpen (V j)) (hLV : ∀ j, L j ⊆ V j)

local notation "e₀" => canonicalFrozenMatrixSymbol T Q hQ hlow F row col Φ Y
  (fun _ _ ↦ 1) z₀ ηb r a hηb hr ha

include hP har hcarrier hf hInv htrans hcJ hV hLV

/-- Continuity of the literal finite frozen matrix, with every carrier's
continuity proved from its actual geometric inputs. There is no assumed
continuity of an integrated symbol (`app:ch_background:prop:bg-frame`). -/
theorem canonicalFrozenMatrixSymbol_unit_continuous : Continuous e₀ := by
  apply (frozenImageSymbol_continuous (Q 0)).add
  apply continuous_finsetSum
  intro j _
  exact canonicalFrozenCarrierSymbol_unit_continuous (T j) ⟨Q, hQ, hlow j⟩ F
    (row j) (col j) (Φ j) (Y j) (hP j) (hηb j) (hr j) (ha j) (har j)
    (hcarrier j) (hf j) (hInv j) (htrans j) (hcJ j) (hV j) (hLV j)

omit hV hLV in
/-- Uniform frequency boundedness of the actual finite matrix expression,
using the literal integrals' proved bounds and the image pencil norm
(`app:ch_background:prop:bg-frame`). -/
theorem canonicalFrozenMatrixSymbol_unit_bounded :
    ∃ B ≥ (0 : ℝ), ∀ k, ‖e₀ k‖ ≤ B := by
  choose B hB hb using fun j ↦ canonicalFrozenCarrierSymbol_unit_bounded
    (T j) ⟨Q, hQ, hlow j⟩ F (row j) (col j) (Φ j) (Y j) (hP j)
    (hηb j) (hr j) (ha j) (har j) (hcarrier j) (hf j) (hInv j) (htrans j) (hcJ j)
  refine ⟨‖pencilContinuousLinearMap (Q 0)‖ ^ 2 + ∑ j, B j,
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ ↦ hB j), fun k ↦ ?_⟩
  rw [canonicalFrozenMatrixSymbol_eq]
  exact (norm_add_le _ _).trans (add_le_add (frozenImageSymbol_norm_le (Q 0) k)
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hb j k)))

variable (hgap : ∀ j, ∀ p ∈ physicalParameterSet (z₀ j) (6 * a j),
    ∀ u ∈ dataBox (z₀ j) (ηb j) (2 * r j),
      ‖((G j).symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩ p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)

omit hcJ hV hLV in
include hgap in
/-- Above the common geometric threshold, increasing the radius cannot
decrease the actual finite frozen quadratic form. The carrier contributions
are exactly unchanged and the literal image Bessel factor increases
(`app:ch_background:prop:bg-frame`, compact-sphere reduction). -/
theorem canonicalFrozenMatrixSymbol_unit_quadratic_smul_mono
    {t : ℝ} (ht : 1 ≤ t) {k : Euclidean n}
    (hk : frozenFamilyHighFrequencyRadius T G ≤ ‖k‖) (s : Euclidean n) :
    dotProduct (fun i ↦ s i) (e₀ k *ᵥ (fun i ↦ s i)) ≤
      dotProduct (fun i ↦ s i) (e₀ (t • k) *ᵥ (fun i ↦ s i)) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have htk : ‖k‖ ≤ ‖t • k‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact le_mul_of_one_le_left (norm_nonneg k) ht
  have he (j : ι) : canonicalFrozenCarrierSymbol (T j) ⟨Q, hQ, hlow j⟩ F
      (row j) (col j) (Φ j) (Y j) (fun _ ↦ 1) (z₀ j) (hηb j) (hr j) (ha j) (t • k) =
      canonicalFrozenCarrierSymbol (T j) ⟨Q, hQ, hlow j⟩ F
      (row j) (col j) (Φ j) (Y j) (fun _ ↦ 1) (z₀ j) (hηb j) (hr j) (ha j) k :=
    canonicalFrozenCarrierSymbol_highFrequency_smul (T j) ⟨Q, hQ, hlow j⟩ (hP j)
      (hηb j) (hr j) (ha j) (har j) (hcarrier j) (hf j) (hInv j) (htrans j)
      F (row j) (col j) (Φ j) (Y j) (fun _ ↦ 1) (hgap j) htpos
      ((frozenHighFrequencyRadius_le_family T G j).trans hk)
      (((frozenHighFrequencyRadius_le_family T G j).trans hk).trans htk)
  simp only [canonicalFrozenMatrixSymbol_eq, he, add_mulVec, dotProduct_add]
  exact add_le_add (frozenImageSymbol_quadratic_smul_mono (Q 0) ht k s) le_rfl

end JanetCartan.ContinuumNormal.FrozenModel
