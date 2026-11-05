module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ComplementInverse.PrimitiveBounds.Compact

/-!
# Smoothness of the literal primitive coefficient map

The map `((H,A),e) ↦ minorComplementInverse H A r c e` is smooth on the open
set where its two original denominators and completion determinant are nonzero.
The compact primitive class lies in this open set for the interval constructed
from its original gaps. This is the coefficient map used to bound the same
inverse in `app:ch_regular_base:eq:complement-inverse`, for `W₁` and `Op(b₋₁ α)`.
-/

open scoped Matrix Matrix.Norms.Frobenius ContDiff
open Matrix Set
@[expose] public noncomputable section
namespace JanetCartan.RegularSector.Characteristic
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The open domain of the literal rational complement construction
(`app:ch_regular_base:eq:complement-inverse`). No characteristic equation is
required to evaluate this map in an ambient neighborhood. -/
def minorComplementDomain (r c : ι) :
    Set ((Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ) :=
  {p | p.1.1.adjugate r c ≠ 0 ∧ minorTransportCoefficient p.1.1 p.1.2 r c ≠ 0} ∩
    {p | (pencilCompletion p.1.1 p.1.2 (minorRightNullvector p.1.1 r c)
      (minorLeftNullvector p.1.1 p.1.2 r c) p.2).det ≠ 0}

omit [DecidableEq ι] in
private theorem smooth_primitive_H_entry (i j : ι) {m : ℕ∞ω} :
    ContDiff ℝ m (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦ p.1.1 i j) :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp
    (contDiff_fst.comp contDiff_fst)

omit [DecidableEq ι] in
private theorem smooth_primitive_A_entry (i j : ι) {m : ℕ∞ω} :
    ContDiff ℝ m (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦ p.1.2 i j) :=
  (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.comp
    (contDiff_snd.comp contDiff_fst)

/-- Joint ambient smoothness of the actual inverse on its open rational domain
(`app:ch_regular_base:eq:complement-inverse`). This supplies the outer map for
compact-range tame composition, including at the boundary of the compact class. -/
theorem minorComplementDomain_regular (r c : ι) {m : ℕ∞ω} :
    IsOpen (minorComplementDomain r c) ∧
      ContDiffOn ℝ m (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
        minorComplementInverse p.1.1 p.1.2 r c p.2) (minorComplementDomain r c) := by
  let S : Set ((Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ) :=
    {p | p.1.1.adjugate r c ≠ 0 ∧ minorTransportCoefficient p.1.1 p.1.2 r c ≠ 0}
  have hm : Continuous (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
      p.1.1.adjugate r c) :=
    (continuous_apply c).comp ((continuous_apply r).comp
      (continuous_fst.comp continuous_fst).matrix_adjugate)
  have ht : Continuous (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
      minorTransportCoefficient p.1.1 p.1.2 r c) :=
    (contDiff_minorTransportCoefficient_pair r c (m := ∞)).continuous.comp continuous_fst
  have hS : IsOpen S := (isClosed_eq hm continuous_const).isOpen_compl.inter
    (isClosed_eq ht continuous_const).isOpen_compl
  have hk : ContDiffOn ℝ m (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
      minorRightNullvector p.1.1 r c) S :=
    contDiffOn_minorRightNullvector r c
      (fun i j ↦ (smooth_primitive_H_entry i j).contDiffOn) (fun _ hp ↦ hp.1)
  have hl : ContDiffOn ℝ m (fun p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
      minorLeftNullvector p.1.1 p.1.2 r c) S :=
    contDiffOn_minorLeftNullvector r c
      (fun i j ↦ (smooth_primitive_H_entry i j).contDiffOn)
      (fun i j ↦ (smooth_primitive_A_entry i j).contDiffOn) (fun _ hp ↦ hp.2)
  have hcompletion := contDiffOn_pencilCompletion
    (fun i j ↦ (smooth_primitive_H_entry i j).contDiffOn)
    (fun i j ↦ (smooth_primitive_A_entry i j).contDiffOn) hk hl contDiffOn_snd
  have hd := continuous_id.matrix_det.comp_continuousOn hcompletion.continuousOn
  refine ⟨hd.isOpen_inter_preimage hS isOpen_compl_singleton, ?_⟩
  exact contDiffOn_minorComplementInverse r c
    (fun i j ↦ (smooth_primitive_H_entry i j).contDiffOn)
    (fun i j ↦ (smooth_primitive_A_entry i j).contDiffOn) contDiffOn_snd
    (fun _ hp ↦ hp.1.1) (fun _ hp ↦ hp.1.2) (fun _ hp ↦ hp.2)

/-- Pointwise ambient smoothness of the literal coefficient map for
`app:ch_regular_base:eq:complement-inverse`. The primitive compact gap theorem
supplies all three nonzero denominators on its common closed interval. -/
theorem contDiffAt_minorComplementInverse_coefficients (r c : ι)
    {p : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ} {m : ℕ∞ω}
    (hm : p.1.1.adjugate r c ≠ 0) (ht : minorTransportCoefficient p.1.1 p.1.2 r c ≠ 0)
    (hd : (pencilCompletion p.1.1 p.1.2 (minorRightNullvector p.1.1 r c)
      (minorLeftNullvector p.1.1 p.1.2 r c) p.2).det ≠ 0) :
    ContDiffAt ℝ m (fun q : (Matrix ι ι ℝ × Matrix ι ι ℝ) × ℝ ↦
      minorComplementInverse q.1.1 q.1.2 r c q.2) p :=
  (minorComplementDomain_regular r c).2.contDiffAt
    ((minorComplementDomain_regular r c (m := m)).1.mem_nhds ⟨⟨hm, ht⟩, hd⟩)

end JanetCartan.RegularSector.Characteristic
