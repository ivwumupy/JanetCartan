module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ConicChart.Inverse
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth extension of the annular inverse to the cone

The smoothness deduction in Step 1 of `app:ch_background:prop:bg-frame`.
The only inverse regularity assumed here is on the buffered annular output
chart, provided by the normal inverse APIs. The conic inverse is the one
already constructed in `Inverse`, and its smoothness is a conclusion.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ContinuumNormalReduction.ConicChart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Any actual annular inverse branch can replace the choice inverse in the
conic construction (`app:ch_background:prop:bg-frame`, Step 1). -/
theorem AnnularData.inverse_eq_annular_branch (A : AnnularData E)
    (g : (ℝ × E) → (ℝ × E))
    (hg : ∀ u ∈ A.annulus, g (A.map u) = u)
    {k : ℝ × E} (hk : k ∈ A.map '' A.cone) :
    A.inverse k = radialScale ‖k.2‖ (g (‖k.2‖⁻¹ • k)) := by
  obtain ⟨u, hu, rfl⟩ := hk
  rw [← A.homogeneous u hu _ (inv_pos.mpr (A.transverse_norm_pos hu)),
    hg _ (A.normalize_mem_annulus hu), A.inverse_map hu]
  simp [(A.transverse_norm_pos hu).ne']

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Joint smoothness of the conic inverse in physical positions, spectator,
and output, from a joint smooth annular inverse branch. This is the precise
conditional smoothness deduction in `app:ch_background:prop:bg-frame`, Step 1.

Take `P` to contain `(x,x',v)` (and any coefficient parameters). `D` is the
desired conic output set. `V` is the common buffered annular output chart.
The producer must supply `g`, its annular inverse identity, smoothness on `V`,
and the normalized-image containment. No conic inverse regularity is assumed.
The within-set conclusion also handles compact smaller supports and closed
parameter intervals without asserting that these are open sets. -/
theorem inverse_family_contDiffOn (A : P → AnnularData E)
    (D V : Set (P × (ℝ × E))) (g : P × (ℝ × E) → (ℝ × E))
    (hg : ContDiffOn ℝ ∞ g V)
    (hbranch : ∀ q ∈ D, ∀ u ∈ (A q.1).annulus, g (q.1, (A q.1).map u) = u)
    (himage : ∀ q ∈ D, q.2 ∈ (A q.1).map '' (A q.1).cone)
    (hV : ∀ q ∈ D, (q.1, ‖q.2.2‖⁻¹ • q.2) ∈ V) :
    ContDiffOn ℝ ∞ (fun q : P × (ℝ × E) ↦ (A q.1).inverse q.2) D := by
  have hne (q : P × (ℝ × E)) (hq : q ∈ D) : q.2.2 ≠ 0 := by
    obtain ⟨u, hu, he⟩ := himage q hq
    rw [← he]
    exact norm_pos_iff.mp ((A q.1).transverse_norm_pos hu)
  have hnorm : ContDiffOn ℝ ∞ (fun q : P × (ℝ × E) ↦ ‖q.2.2‖) D :=
    (contDiffOn_snd.snd).norm ℝ hne
  have hinv : ContDiffOn ℝ ∞ (fun q : P × (ℝ × E) ↦ ‖q.2.2‖⁻¹) D :=
    hnorm.inv (fun q hq ↦ norm_ne_zero_iff.mpr (hne q hq))
  have harg : ContDiffOn ℝ ∞
      (fun q : P × (ℝ × E) ↦ (q.1, ‖q.2.2‖⁻¹ • q.2)) D :=
    contDiffOn_fst.prodMk (hinv.smul contDiffOn_snd)
  have hcomp := hg.comp harg hV
  have hresult := hcomp.fst.prodMk (hnorm.smul hcomp.snd)
  apply hresult.congr
  intro q hq
  exact (A q.1).inverse_eq_annular_branch (fun k ↦ g (q.1, k))
    (hbranch q hq) (himage q hq)

/-- Joint annular inverse regularity alone supplies conic inverse regularity:
the normalized-image containment is discharged by `normalize_mem_annulus`.
This form is consumed by `app:ch_background:eq:bg-full-complex-amplitude`.
`Q` is the admissible physical/spectator parameter set. -/
theorem inverse_family_contDiffOn_of_annular (A : P → AnnularData E)
    (Q : Set P) (g : P × (ℝ × E) → (ℝ × E))
    (hg : ContDiffOn ℝ ∞ g {q | q.1 ∈ Q ∧ q.2 ∈ (A q.1).map '' (A q.1).annulus})
    (hbranch : ∀ p ∈ Q, ∀ u ∈ (A p).annulus, g (p, (A p).map u) = u) :
    ContDiffOn ℝ ∞ (fun q : P × (ℝ × E) ↦ (A q.1).inverse q.2)
      {q | q.1 ∈ Q ∧ q.2 ∈ (A q.1).map '' (A q.1).cone} := by
  apply inverse_family_contDiffOn A _ _ g hg
  · intro q hq
    exact hbranch q.1 hq.1
  · intro q hq
    exact hq.2
  · intro q hq
    refine ⟨hq.1, ?_⟩
    obtain ⟨u, hu, he⟩ := hq.2
    refine ⟨radialScale ‖q.2.2‖⁻¹ u, ?_, ?_⟩
    · simpa only [← he] using (A q.1).normalize_mem_annulus hu
    · rw [(A q.1).homogeneous u hu _ (by
        rw [← he]; exact inv_pos.mpr ((A q.1).transverse_norm_pos hu)), he]

end JanetCartan.ContinuumNormalReduction.ConicChart
