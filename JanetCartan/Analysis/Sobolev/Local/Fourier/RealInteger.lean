module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.Integer
public import JanetCartan.Analysis.Sobolev.Local.Fourier.Representative
public import JanetCartan.Analysis.Microlocal.RegularSector.Realization.L2

/-!
# The real-fiber Fourier-to-restriction comparison at natural orders comparison

Project the complex weak extension by the actual real-part map from
`RegularSector.Realization`, retaining its L² classes and the very same
constant. This is the real-output comparison in
`app:ch_regular:thm:exact-correction`.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.LocalSobolev

open Pseudodifferential RegularSector.Realization

/-- Complex natural-order regularity of the literal inclusion of real data constructs a
real weak extension with exactly the chosen representative and the same norm
constant (`app:ch_regular:thm:exact-correction`). -/
theorem exists_real_sobolevExtension_nat (n r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℝ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))),
      MemVectorFourierSobolev (s : ℝ) (l2ComplexInclusion volume u) →
      ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 U (EuclideanSpace ℝ (Fin r))),
      (u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v →
      ∃ e : SobolevExtension U s v,
        e.toFun = u ∧ e.toL2 = u ∧
        e.jetNorm ≤ C * vectorFourierSobolevNorm (s : ℝ) (l2ComplexInclusion volume u) := by
  obtain ⟨C, hC, h⟩ := exists_vector_sobolevExtension_nat n r s
  refine ⟨C, hC, fun u hu U v huv ↦ ?_⟩
  have hinc : (l2ComplexInclusion volume u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U]
      l2ComplexInclusion (volume.restrict U) v := by
    filter_upwards [ae_restrict_of_ae (euclideanComplexInclusion.coeFn_compLpL u),
      euclideanComplexInclusion.coeFn_compLpL v, huv] with x hx hy hz
    exact hx.trans ((congrArg euclideanComplexInclusion hz).trans hy.symm)
  obtain ⟨e, _, he, hb⟩ := h (l2ComplexInclusion volume u) hu U
    (l2ComplexInclusion (volume.restrict U) v) hinc
  let eR := e.mapCLM (euclideanRealPart (ι := Fin r))
  have hR : eR.toL2 = u := by
    rw [SobolevExtension.toL2_mapCLM, he]
    exact realPart_inclusion u
  have hfun : eR.toFun =ᵐ[volume] u := by
    rw [← hR]
    exact eR.toL2_coeFn.symm
  let eN := eR.withRepresentative u hfun
  have hnorm : eN.jetNorm ≤ C * vectorFourierSobolevNorm (s : ℝ) (l2ComplexInclusion volume u) := by
    rw [SobolevExtension.jetNorm_withRepresentative]
    exact (e.jetNorm_mapCLM_le euclideanRealPart).trans
      ((mul_le_of_le_one_left e.jetNorm_nonneg euclideanRealPart_norm_le).trans hb)
  have hclass : eN.toL2 = u := by
    apply Lp.ext
    exact eN.toL2_coeFn
  have hout : ∃ e' : SobolevExtension U s
      (l2RealPart (volume.restrict U) (l2ComplexInclusion (volume.restrict U) v)),
      e'.toFun = u ∧ e'.toL2 = u ∧
        e'.jetNorm ≤ C * vectorFourierSobolevNorm (s : ℝ) (l2ComplexInclusion volume u) :=
    ⟨eN, rfl, hclass, hnorm⟩
  rw [realPart_inclusion v] at hout
  exact hout

/-- Whole-space real weak jets retain the literal real L² representative and
the complex-inclusion Fourier bound, for `app:not:fourier`. All derivatives
are taken over ℝ and the constant precedes the datum. -/
theorem exists_real_weakJet_nat (n r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℝ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))),
      MemVectorFourierSobolev (s : ℝ) (l2ComplexInclusion volume u) →
      ∃ J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
          (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] EuclideanSpace ℝ (Fin r),
        Mollification.HasWeakJetOn volume u J univ s ∧
        (∀ j ≤ s, MemLp (J j) 2 volume) ∧
        (∑ j ∈ Finset.range (s + 1), (eLpNorm (J j) 2 volume).toReal) ≤
          C * vectorFourierSobolevNorm (s : ℝ) (l2ComplexInclusion volume u) := by
  obtain ⟨C, hC, h⟩ := exists_real_sobolevExtension_nat n r s
  refine ⟨C, hC, fun u hu ↦ ?_⟩
  obtain ⟨e, he, _, hb⟩ := h u hu ∅ 0 (by
    simp only [Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot)
  refine ⟨e.jet, ?_, e.memLp_jet, hb⟩
  simpa only [he] using e.weakJet

/-- The real restriction Sobolev membership and norm bound follow from actual
complex Fourier regularity of the L² inclusion, for the fixed-domain inverse
in `app:ch_regular:thm:exact-correction`. -/
theorem real_restrictionSobolev_nat_bounds (n r s : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℝ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))),
      MemVectorFourierSobolev (s : ℝ) (l2ComplexInclusion volume u) →
      ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 U (EuclideanSpace ℝ (Fin r))),
      (u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v →
      MemRestrictionSobolev U s v ∧ restrictionSobolevNorm U s v ≤
        C * vectorFourierSobolevNorm (s : ℝ) (l2ComplexInclusion volume u) := by
  obtain ⟨C, hC, h⟩ := exists_real_sobolevExtension_nat n r s
  refine ⟨C, hC, fun u hu U v huv ↦ ?_⟩
  obtain ⟨e, _, _, hb⟩ := h u hu U v huv
  exact ⟨⟨e⟩, (restrictionSobolevNorm_le e).trans hb⟩

end JanetCartan.LocalSobolev
