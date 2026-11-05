module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Retarded.Representation
public import JanetCartan.Analysis.Sobolev.Local.Comparison.WeakUniqueness

/-!
# The whole-chart grade of a retarded test field

Weak-jet uniqueness removes the infimum over extensions in the actual local
Sobolev scale. This is the restriction-norm part of the comparison consumed by
the envelope transfer in `app:ch_response:eq:fixed-factor-transfer`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.ResponseTransfer

open RetardedSobolev.Spaces LocalSobolev

/-- Every extension of the whole-chart class has exactly the classical jet norm.
This discharges the weak-extension issue in
`app:ch_response:eq:fixed-factor-transfer`. -/
theorem retardedTest_extension_jetNorm_eq {d s : ℕ} (f : Test d)
    (e : SobolevExtension univ s (retardedTestToLocalL2 f)) :
    e.jetNorm = jetL2Norm univ s (fun j ↦ iteratedFDeriv ℝ j (retardedTestFunction f)) := by
  have hw := Mollification.hasWeakJetOn_of_contDiff volume
    ((contDiff_retardedTestFunction f).of_le (by simp)) univ (m := s)
  have he := e.weakJet.ae_eq hw isOpen_univ
    (e.restrict_eq.trans (retardedTestToLocalL2_ae f))
  simp only [SobolevExtension.jetNorm, jetL2Norm, Measure.restrict_univ]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := he j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  simp only [Measure.restrict_univ] at hj'
  rw [eLpNorm_congr_ae hj']

/-- On the whole chart the actual grade norm is exactly the sum of classical
Fréchet L² jet norms. No comparison or profile bound is assumed
(`app:ch_response:eq:fixed-factor-transfer`). -/
theorem retardedTestToLocalL2_gradeNorm_eq_jetL2Norm {d : ℕ} (s : ℕ) (f : Test d) :
    (restrictionSobolevScale (univ : Set (Euclidean (d + 1))) ℂ MeasurableSet.univ).gradeNorm s (retardedTestToLocalL2 f) =
      jetL2Norm univ s (fun j ↦ iteratedFDeriv ℝ j (retardedTestFunction f)) := by
  rw [restrictionSobolevScale_gradeNorm MeasurableSet.univ (retardedTestToLocalL2_mem f s)]
  obtain ⟨e⟩ := retardedTestToLocalL2_mem f s
  apply le_antisymm
  · exact (restrictionSobolevNorm_le e).trans_eq (retardedTest_extension_jetNorm_eq f e)
  · apply le_csInf
    · exact ⟨e.jetNorm, e, rfl⟩
    · rintro _ ⟨e', rfl⟩
      exact (retardedTest_extension_jetNorm_eq f e').symm.le

end JanetCartan.ResponseTransfer
