module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.FiniteFamily
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.RetainedFrozen.DetectorGap.Detection
public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Compact-sphere deduction for the retained frozen matrix

The local retained density proofs discharge integrability and regularity.
Zero energy annihilates each active detector, and `DetectorGram` compactness
gives a uniform sphere gap. The original geometric threshold and radial
comparison extend it to every larger Euclidean frequency.
`retained_incidence_spectral_bounds` supplies the root and detection inputs
from the SAME original cover and selected columns; these intermediate
implications alone do not instantiate the parent
(`app:ch_background:prop:bg-frame`, Step 2).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory Matrix
open scoped ContDiff InnerProductSpace Matrix.Norms.Frobenius
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

local notation "e₀" => retainedFrozenMatrixSymbol T Q hQ hlow F row col Φ Y
  z₀ ηb r a r' a' hηb hr' ha'

include hP hr ha hrr haa har hcarrier hf hInv htrans hcJ hV hLV

local notation "u₀" => fun j ↦ frozenSymbolInverse (T j) (Subtype.mk Q (And.intro hQ (hlow j))) (z₀ j) (ηb j) (r j) (6 * a j)
local notation "Ω₀" => fun j ↦ frozenSymbolDomain (T j) (Subtype.mk Q (And.intro hQ (hlow j))) (z₀ j) (ηb j) (r j) (6 * a j)
local notation "J₀" => fun j ↦ transportAbsoluteJacobian (adaptedSliceCoordinates (T j))
  (normalizedTransportPosition (T j) (Subtype.mk Q (And.intro hQ (hlow j))) 0)
local notation "a₀" => fun j ↦ uncutFrozenCoefficients (T j) (Subtype.mk Q (And.intro hQ (hlow j))) F (row j) (col j)
  (Φ j) (Y j) (fun _ ↦ 1)
  (angularMask (z₀ j) (NormedSpace.normalize (ηb j)) (ha' j) (And.left (angularWidth_spec (hηb j) (hr' j))))
  FixedCutoffs.highFrequency

omit ha hrr in
/-- The actual finite frozen energy is strictly positive when the selected
incidence roots are in its literal inverse domains, their actual weights are
positive, and their original image-plus-detector family detects. Density
integrability is supplied by the constructed regularity theorem, not assumed
(`app:ch_background:prop:bg-frame`, frozen limit). -/
theorem retainedFrozenMatrixSymbol_unit_pos_of_incidence
    (k : Euclidean n) (active : Finset ι) (z : ι → Euclidean 3)
    (hroot : ∀ j ∈ active,
      ((0, 0, k), spectatorCenter (z₀ j)) ∈ Ω₀ j ∧
      parameter (((u₀ j) ((0, 0, k), spectatorCenter (z₀ j))).1, spectatorCenter (z₀ j)) = z j ∧
      0 < inputWeight (a₀ j) (J₀ j)
        (inverseCoordinates (u₀ j) ((0, 0, k), spectatorCenter (z₀ j))))
    (hdetect : ∀ s : Euclidean n,
      ActualCarriers.imageChannel (pencil (Q 0) k) s = 0 →
      (∀ j ∈ active, ⟪quadratic (Q 0) ((T j).carrierGradient ⟨Q, hQ, hlow j⟩ 0 (z j)), s⟫_ℝ = 0) →
      s = 0) {s : Euclidean n} (hs : s ≠ 0) :
    0 < dotProduct (fun i ↦ s i) (e₀ k *ᵥ (fun i ↦ s i)) := by
  let E (j : ι) := dotProduct (fun i ↦ s i)
    (retainedFrozenCarrierSymbol (T j) ⟨Q, hQ, hlow j⟩ F (row j) (col j)
      (Φ j) (Y j) (fun _ ↦ 1) (z₀ j) (r j) (a j) (hηb j) (hr' j) (ha' j) k *ᵥ (fun i ↦ s i))
  have hE (j : ι) : 0 ≤ E j := by
    simpa only [star_trivial] using
      (retainedFrozenCarrierSymbol_posSemidef (T j) ⟨Q, hQ, hlow j⟩ F (row j) (col j)
        (Φ j) (Y j) (fun _ ↦ 1) (z₀ j) (r j) (a j) (hηb j) (hr' j) (ha' j) k).dotProduct_mulVec_nonneg
          (fun i ↦ s i)
  have hI : 0 ≤ dotProduct (fun i ↦ s i) (frozenImageSymbol (Q 0) k *ᵥ (fun i ↦ s i)) := by
    simpa only [star_trivial] using (frozenImageSymbol_posSemidef (Q 0) k).dotProduct_mulVec_nonneg
      (fun i ↦ s i)
  have hsum : 0 ≤ ∑ j, E j := Finset.sum_nonneg fun j _ ↦ hE j
  by_contra! hnot
  have hzero : dotProduct (fun i ↦ s i) (frozenImageSymbol (Q 0) k *ᵥ (fun i ↦ s i)) +
      ∑ j, E j = 0 := by
    apply le_antisymm _ (add_nonneg hI hsum)
    simpa only [retainedFrozenMatrixSymbol, add_mulVec, dotProduct_add,
      sum_mulVec, dotProduct_sum, E] using hnot
  have hiZero : dotProduct (fun i ↦ s i) (frozenImageSymbol (Q 0) k *ᵥ (fun i ↦ s i)) = 0 := by
    linarith
  have hsZero : ∑ j, E j = 0 := by linarith
  have heZero : ∀ j, E j = 0 := fun j ↦
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ hE i)).mp hsZero j (Finset.mem_univ j)
  apply hs (hdetect s ((frozenImageSymbol_quadratic_eq_zero_iff (Q 0) k s).mp hiZero) ?_)
  intro j hj
  obtain ⟨hp, hz, hw⟩ := hroot j hj
  exact retainedFrozenCarrierSymbol_detector_eq_zero_of_integrable
    (T j) ⟨Q, hQ, hlow j⟩ F (row j) (col j) (Φ j) (Y j) (fun _ ↦ 1)
    (z₀ j) (hηb j) (hr j) (hr' j) (ha' j) (hInv j) (htrans j) (hV j) (hLV j)
    (retainedFrozenPrimitiveRegularity_unit (T j) ⟨Q, hQ, hlow j⟩ F
      (row j) (col j) (Φ j) (Y j) (hP j) (hηb j) (hr j) (hr' j) (ha' j)
      (har j) (hcarrier j) (hf j) (hInv j) (htrans j) (hcJ j))
    (retainedFrozenExtendedDensity_unit_integrable (T j) ⟨Q, hQ, hlow j⟩ F
      (row j) (col j) (Φ j) (Y j) (hP j) (hηb j) (hr j) (hr' j) (ha' j) (haa j)
      (har j) (hcarrier j) (hf j) (hInv j) (htrans j) (hcJ j) (hV j) (hLV j) (0, 0, k))
    hp hz hw s (heZero j)


variable (hgap : ∀ j, ∀ p ∈ physicalParameterSet (z₀ j) (6 * a j),
    ∀ u ∈ dataBox (z₀ j) (ηb j) (2 * r j),
      ‖((G j).symm : (ℝ × Euclidean (n - 1)) →L[ℝ] (ℝ × Euclidean (n - 1))).comp
        (fderiv ℝ (adaptedTransportChart (T j) ⟨Q, hQ, hlow j⟩ p) u) -
          ContinuousLinearMap.id ℝ (ℝ × Euclidean (n - 1))‖ ≤ 1 / 2)

include hgap

/-- The literal finite frozen matrix has a uniform high-frequency gap once
the SAME selected roots and detection are instantiated on the sphere at the
common geometric threshold. No positive-symbol or coercivity estimate is a
hypothesis: strict positivity is deduced from those roots, and compactness and
the proved radial comparison give the uniform bound. This conditional deduction
still requires the parent's finite incidence construction
(`app:ch_background:prop:bg-frame`, frozen limit). -/
theorem exists_retainedFrozenMatrixSymbol_unit_gap_of_incidence
    (active : Euclidean n → Finset ι) (z : Euclidean n → ι → Euclidean 3)
    (hroot : ∀ k : Euclidean n, ‖k‖ = frozenFamilyHighFrequencyRadius T G → ∀ j ∈ active k,
      ((0, 0, k), spectatorCenter (z₀ j)) ∈ Ω₀ j ∧
      parameter (((u₀ j) ((0, 0, k), spectatorCenter (z₀ j))).1, spectatorCenter (z₀ j)) = z k j ∧
      0 < inputWeight (a₀ j) (J₀ j)
        (inverseCoordinates (u₀ j) ((0, 0, k), spectatorCenter (z₀ j))))
    (hdetect : ∀ k : Euclidean n, ‖k‖ = frozenFamilyHighFrequencyRadius T G → ∀ s : Euclidean n,
      ActualCarriers.imageChannel (pencil (Q 0) k) s = 0 →
      (∀ j ∈ active k, ⟪quadratic (Q 0) ((T j).carrierGradient ⟨Q, hQ, hlow j⟩ 0 (z k j)), s⟫_ℝ = 0) →
      s = 0) :
    ∃ c > (0 : ℝ), ∀ k : Euclidean n, frozenFamilyHighFrequencyRadius T G ≤ ‖k‖ →
      ∀ s : Euclidean n, c * ‖s‖ ^ 2 ≤ dotProduct (fun i ↦ s i) (e₀ k *ᵥ (fun i ↦ s i)) := by
  let R := frozenFamilyHighFrequencyRadius T G
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (one_le_frozenFamilyHighFrequencyRadius T G)
  let L : Matrix (Fin n) (Fin n) ℝ ≃L[ℝ] (Euclidean n →L[ℝ] Euclidean n) :=
    Matrix.toEuclideanCLM.toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv
  have hLtest (M : Matrix (Fin n) (Fin n) ℝ) (s : Euclidean n) :
      ⟪s, L M s⟫_ℝ = dotProduct (fun i ↦ s i) (M *ᵥ (fun i ↦ s i)) :=
    Matrix.inner_toEuclideanCLM M s s
  have hecont := retainedFrozenMatrixSymbol_unit_continuous T G Q hQ hlow F row col Φ Y
    z₀ ηb r a r' a' hηb hr ha hr' ha' hrr haa hP har hcarrier hf hInv htrans hcJ hV hLV
  have hpos : ∀ k ∈ sphere (0 : Euclidean n) R, ∀ s : Euclidean n,
      s ≠ 0 → 0 < ⟪s, L (e₀ k) s⟫_ℝ := by
    intro k hk s hs
    have hn : ‖k‖ = R := by simpa only [mem_sphere, dist_zero_right] using hk
    simpa only [hLtest] using
      retainedFrozenMatrixSymbol_unit_pos_of_incidence T G Q hQ hlow F row col Φ Y
        z₀ ηb r a r' a' hηb hr hr' ha' haa hP har hcarrier hf hInv htrans hcJ hV hLV k
        (active k) (z k) (hroot k hn) (hdetect k hn) hs
  obtain ⟨c, hc, hbound⟩ := DetectorGram.exists_uniform_lower_bound (isCompact_sphere _ _)
    (fun k ↦ L (e₀ k)) (L.continuous.comp hecont).continuousOn hpos
  refine ⟨c, hc, fun k hk s ↦ ?_⟩
  have hkn : 0 < ‖k‖ := hR.trans_le hk
  let w := (R / ‖k‖) • k
  let t := ‖k‖ / R
  have hw : ‖w‖ = R := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hkn), div_mul_cancel₀ _ hkn.ne']
  have ht : 1 ≤ t := (one_le_div hR).mpr hk
  have htw : t • w = k := by
    dsimp [t, w]
    rw [smul_smul]
    have he : ‖k‖ / R * (R / ‖k‖) = 1 := by field_simp [hR.ne', hkn.ne']
    rw [he, one_smul]
  have hb : c * ‖s‖ ^ 2 ≤ dotProduct (fun i ↦ s i) (e₀ w *ᵥ (fun i ↦ s i)) := by
    simpa only [hLtest] using
      hbound w (by simpa only [mem_sphere, dist_zero_right] using hw) s
  have hm := retainedFrozenMatrixSymbol_unit_quadratic_smul_mono T G Q hQ hlow F row col Φ Y
    z₀ ηb r a r' a' hηb hr hr' ha' hP har hcarrier hf hInv htrans hgap ht hw.ge s
  rw [htw] at hm
  exact hb.trans hm

end JanetCartan.ContinuumNormal.RetainedFrozen
