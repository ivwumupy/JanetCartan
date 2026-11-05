module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Regularity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Homogeneity
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.FiniteFamily
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Spectral.ImageSymbol

/-!
# Finite spectral bounds on the retained masks

This leaf deduces continuity, boundedness, nonnegativity and radial comparison
for the literal ideal image plus finite reflected carrier sum. It reuses
`frozenFamilyHighFrequencyRadius` and the same outer geometry retained by
`jc-retained-frozen-unit-realization`. The consumer is
`retained_incidence_spectral_bounds` (`app:ch_background:prop:bg-frame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric MeasureTheory Matrix
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.RetainedFrozen
open FrozenModel ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts ActualComparison
open ContinuumRow CanonicalCarrier CanonicalConic
open ContinuumNormalReduction TransportSymbol ConicChart

variable {n N : ℕ} {ι : Type*} [Fintype ι]
    {P : ι → Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : ∀ j, PatchQuantitativeFamily (P j) U hU)
    (G : ι → (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1)))

variable (Q : Euclidean n → Fin n → MetricTensor n) (hQ : ContDiffOn ℝ ∞ Q U)
    (hlow : ∀ j, cNorm (closedBall (0 : Euclidean n) (T j).data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < (T j).family.threshold)
    (F : Euclidean n → Euclidean N) (row col : ι → Fin n)
    (Φ Y : ι → ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (z₀ : ι → Euclidean 3) (ηb : ι → Euclidean (n - 1)) (r a r' a' : ι → ℝ)
    (hηb : ∀ j, ηb j ≠ 0) (hr : ∀ j, 0 < r j) (ha : ∀ j, 0 < a j)
    (hr' : ∀ j, 0 < r' j) (ha' : ∀ j, 0 < a' j)
    (hrr : ∀ j, r' j ≤ r j) (haa : ∀ j, a' j ≤ a j)
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

/-- The ideal image plus the literal finite reflected retained-carrier sum.
This retains the image Bessel weight, reflection and factor four
(`app:ch_background:prop:bg-frame`, Step 2). -/
abbrev retainedFrozenMatrixSymbol (k : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  frozenImageSymbol (Q 0) k + ∑ j, retainedFrozenCarrierSymbol (T j) ⟨Q, hQ, hlow j⟩ F
    (row j) (col j) (Φ j) (Y j) (fun _ ↦ 1) (z₀ j) (r j) (a j) (hηb j) (hr' j) (ha' j) k

local notation "e₀" => retainedFrozenMatrixSymbol T Q hQ hlow F row col Φ Y
  z₀ ηb r a r' a' hηb hr' ha'

/-- Pointwise nonnegativity of the same finite frozen matrix (`bg-real-symbol`). -/
theorem retainedFrozenMatrixSymbol_posSemidef (k : Euclidean n) : (e₀ k).PosSemidef :=
  (frozenImageSymbol_posSemidef (Q 0) k).add (Matrix.posSemidef_sum _ (fun j _ ↦
    retainedFrozenCarrierSymbol_posSemidef (T j) ⟨Q, hQ, hlow j⟩ F
      (row j) (col j) (Φ j) (Y j) (fun _ ↦ 1) (z₀ j) (r j) (a j) (hηb j) (hr' j) (ha' j) k))

include hP hr ha hrr haa har hcarrier hf hInv htrans hcJ hV hLV

/-- Continuity of the literal finite frozen matrix, with every carrier's
continuity proved from its actual geometric inputs. There is no assumed
continuity of an integrated symbol (`app:ch_background:prop:bg-frame`). -/
theorem retainedFrozenMatrixSymbol_unit_continuous : Continuous e₀ := by
  apply (frozenImageSymbol_continuous (Q 0)).add
  apply continuous_finsetSum
  intro j _
  exact retainedFrozenCarrierSymbol_unit_continuous (T j) ⟨Q, hQ, hlow j⟩ F
    (row j) (col j) (Φ j) (Y j) (hP j) (hηb j) (hr j) (ha j) (hr' j) (ha' j) (hrr j) (haa j) (har j)
    (hcarrier j) (hf j) (hInv j) (htrans j) (hcJ j) (hV j) (hLV j)

omit ha hrr hV hLV in
/-- Uniform frequency boundedness of the actual finite matrix expression,
using the literal integrals' proved bounds and the image pencil norm
(`app:ch_background:prop:bg-frame`). -/
theorem retainedFrozenMatrixSymbol_unit_bounded :
    ∃ B ≥ (0 : ℝ), ∀ k, ‖e₀ k‖ ≤ B := by
  choose B hB hb using fun j ↦ retainedFrozenCarrierSymbol_unit_bounded
    (T j) ⟨Q, hQ, hlow j⟩ F (row j) (col j) (Φ j) (Y j) (hP j)
    (hηb j) (hr j) (hr' j) (ha' j) (haa j) (har j) (hcarrier j) (hf j) (hInv j) (htrans j) (hcJ j)
  refine ⟨‖pencilContinuousLinearMap (Q 0)‖ ^ 2 + ∑ j, B j,
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ ↦ hB j), fun k ↦ ?_⟩
  rw [retainedFrozenMatrixSymbol]
  exact (norm_add_le _ _).trans (add_le_add (frozenImageSymbol_norm_le (Q 0) k)
    ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ hb j k)))

variable (hgap : ∀ j, ∀ p ∈ physicalParameterSet (z₀ j) (6 * a j),
    ∀ u ∈ dataBox (z₀ j) (ηb j) (2 * r j),
      ‖((G j).symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩ p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)

omit ha hrr haa hcJ hV hLV in
include hgap in
/-- Above the common geometric threshold, increasing the radius cannot
decrease the actual finite frozen quadratic form. The carrier contributions
are exactly unchanged and the literal image Bessel factor increases
(`app:ch_background:prop:bg-frame`, compact-sphere reduction). -/
theorem retainedFrozenMatrixSymbol_unit_quadratic_smul_mono
    {t : ℝ} (ht : 1 ≤ t) {k : Euclidean n}
    (hk : frozenFamilyHighFrequencyRadius T G ≤ ‖k‖) (s : Euclidean n) :
    dotProduct (fun i ↦ s i) (e₀ k *ᵥ (fun i ↦ s i)) ≤
      dotProduct (fun i ↦ s i) (e₀ (t • k) *ᵥ (fun i ↦ s i)) := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have htk : ‖k‖ ≤ ‖t • k‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact le_mul_of_one_le_left (norm_nonneg k) ht
  have he (j : ι) : retainedFrozenCarrierSymbol (T j) ⟨Q, hQ, hlow j⟩ F
      (row j) (col j) (Φ j) (Y j) (fun _ ↦ 1) (z₀ j) (r j) (a j) (hηb j) (hr' j) (ha' j) (t • k) =
      retainedFrozenCarrierSymbol (T j) ⟨Q, hQ, hlow j⟩ F
      (row j) (col j) (Φ j) (Y j) (fun _ ↦ 1) (z₀ j) (r j) (a j) (hηb j) (hr' j) (ha' j) k :=
    retainedFrozenCarrierSymbol_highFrequency_smul (T j) ⟨Q, hQ, hlow j⟩ (hP j)
      (hηb j) (hr j) (hr' j) (ha' j) (har j) (hcarrier j) (hf j) (hInv j) (htrans j)
      F (row j) (col j) (Φ j) (Y j) (fun _ ↦ 1) (hgap j) htpos
      ((frozenHighFrequencyRadius_le_family T G j).trans hk)
      (((frozenHighFrequencyRadius_le_family T G j).trans hk).trans htk)
  simp only [retainedFrozenMatrixSymbol, he, add_mulVec, dotProduct_add]
  exact add_le_add (frozenImageSymbol_quadratic_smul_mono (Q 0) ht k s) le_rfl

end JanetCartan.ContinuumNormal.RetainedFrozen
