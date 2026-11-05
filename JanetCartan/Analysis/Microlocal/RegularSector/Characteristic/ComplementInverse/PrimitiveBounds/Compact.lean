module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.NormalizedMinor
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.Bordered

/-!
# A compact class of primitive characteristic matrices

For `app:ch_regular_base:lem:characteristic-kernel`, choose the displacement
interval before choosing a coefficient family. Only Frobenius bounds and the
original minor and transport gaps enter this class. Its common completion and
bordered determinant gaps feed the quantitative bounds for `W₁` and `Op(b₋₁ α)`.
-/

open scoped Matrix Matrix.Norms.Frobenius ContDiff
open Matrix Set
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bounded primitive coefficient class for
`app:ch_regular_base:eq:complement-inverse`. The gaps concern the original
adjugate minor and unnormalized transport coefficient. -/
def minorCoefficientClass (r c : ι) (M μ ν : ℝ) :
    Set (Matrix ι ι ℝ × Matrix ι ι ℝ) :=
  {p | ‖p.1‖ ≤ M ∧ ‖p.2‖ ≤ M ∧ p.1.det = 0 ∧
    μ ≤ |p.1.adjugate r c| ∧ ν ≤ |minorTransportCoefficient p.1 p.2 r c|}

/-- Polynomial smoothness of the original transport coefficient in the paired
primitive matrices (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem contDiff_minorTransportCoefficient_pair (r c : ι) {m : ℕ∞ω} :
    ContDiff ℝ m (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦
      minorTransportCoefficient p.1 p.2 r c) := by
  rw [← contDiffOn_univ]
  exact contDiffOn_minorTransportCoefficient r c
    (fun i j ↦ ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp
      contDiff_fst).contDiffOn)
    (fun i j ↦ ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp
      contDiff_snd).contDiffOn)

/-- Compactness comes from primitive matrix bounds and closed original gap
conditions (`app:ch_regular_base:lem:characteristic-kernel`). -/
theorem isCompact_minorCoefficientClass (r c : ι) (M μ ν : ℝ) :
    IsCompact (minorCoefficientClass r c M μ ν) := by
  have hm : Continuous (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦
      |p.1.adjugate r c|) := by
    exact ((continuous_apply c).comp
      ((continuous_apply r).comp continuous_fst.matrix_adjugate)).abs
  have ht : Continuous (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦
      |minorTransportCoefficient p.1 p.2 r c|) :=
    (contDiff_minorTransportCoefficient_pair r c (m := ∞)).continuous.abs
  have hc : IsClosed (minorCoefficientClass r c M μ ν) :=
    (isClosed_le continuous_fst.norm continuous_const).inter
      ((isClosed_le continuous_snd.norm continuous_const).inter
        ((isClosed_eq continuous_fst.matrix_det continuous_const).inter
          ((isClosed_le continuous_const hm).inter (isClosed_le continuous_const ht))))
  apply ((isCompact_closedBall (0 : Matrix ι ι ℝ) M).prod
    (isCompact_closedBall (0 : Matrix ι ι ℝ) M)).of_isClosed_subset hc
  intro p hp
  exact ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.1,
    by simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.1⟩

/-- One positive interval and positive gaps for both literal determinants,
uniform over all primitive matrices with the fixed bounds and original gaps
(`app:ch_regular_base:eq:complement-inverse`). No coefficient family, kernel
data, completion gap, or inverse estimate is an input. -/
theorem exists_minorCoefficientClass_determinant_gaps (r c : ι) (M : ℝ)
    {μ ν : ℝ} (hμ : 0 < μ) (hν : 0 < ν) :
    ∃ ε > 0, ∃ δ > 0, ∀ p ∈ minorCoefficientClass r c M μ ν,
      ∀ e : ℝ, |e| ≤ ε →
        δ ≤ |(pencilCompletion p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det| ∧
        δ ≤ |(borderedPencil p.1 p.2 (minorRightNullvector p.1 r c)
          (minorLeftNullvector p.1 p.2 r c) e).det| := by
  let K := minorCoefficientClass r c M μ ν
  let : CompactSpace K := isCompact_iff_compactSpace.mp
    (isCompact_minorCoefficientClass r c M μ ν)
  have hm (p) (hp : p ∈ K) : p.1.adjugate r c ≠ 0 :=
    abs_pos.mp (hμ.trans_le hp.2.2.2.1)
  have ht (p) (hp : p ∈ K) : minorTransportCoefficient p.1 p.2 r c ≠ 0 :=
    abs_pos.mp (hν.trans_le hp.2.2.2.2)
  have hH (i j : ι) : ContDiffOn ℝ ∞
      (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ p.1 i j) K :=
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp
      contDiff_fst).contDiffOn
  have hA (i j : ι) : ContDiffOn ℝ ∞
      (fun p : Matrix ι ι ℝ × Matrix ι ι ℝ ↦ p.2 i j) K :=
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp
      contDiff_snd).contDiffOn
  have hk : Continuous (fun p : K ↦ minorRightNullvector p.val.1 r c) :=
    continuousOn_iff_continuous_domRestrict.mp
      (contDiffOn_minorRightNullvector r c hH hm).continuousOn
  have hl : Continuous (fun p : K ↦ minorLeftNullvector p.val.1 p.val.2 r c) :=
    continuousOn_iff_continuous_domRestrict.mp
      (contDiffOn_minorLeftNullvector r c hH hA ht).continuousOn
  obtain ⟨ε, hε, δ, hδ, hgap⟩ := exists_uniform_bordered_completion_gap
    (fun p : K ↦ p.val.1) (fun p : K ↦ p.val.2)
    (fun p : K ↦ minorRightNullvector p.val.1 r c)
    (fun p : K ↦ minorLeftNullvector p.val.1 p.val.2 r c)
    (continuous_fst.comp continuous_subtype_val) (continuous_snd.comp continuous_subtype_val)
    hk hl isCompact_univ
    (fun p _ ↦ (minor_normalization p.property.2.2.1 (hm p p.property)
      (ht p p.property)).2.1)
    (fun p _ ↦ (minor_normalization p.property.2.2.1 (hm p p.property)
      (ht p p.property)).2.2.1)
    (fun p _ ↦ (minor_normalization p.property.2.2.1 (hm p p.property)
      (ht p p.property)).2.2.2)
  exact ⟨ε, hε, δ, hδ, fun p hp e he ↦ hgap ⟨p, hp⟩ (mem_univ _) e he⟩

end JanetCartan.RegularSector.Characteristic
