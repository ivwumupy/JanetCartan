module

public import JanetCartan.Analysis.Sobolev.Local.Fourier.VectorFirstDerivative

/-!
# The Fourier-to-restriction H¹ endpoint

This independent leaf supplies the genuine output comparison for the fixed
inverse contraction in `app:ch_regular:thm:exact-correction`. Its only analytic
input is order-one vector Fourier membership. There is no additional derivative
loss, smoothness hypothesis, or assumed weak jet. The parent sector construction
must still supply the Fourier estimates for its actual operators and residuals.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace JanetCartan.LocalSobolev

open Pseudodifferential

/-- Order-one Fourier membership constructs a normalized whole-space weak jet
with an input-independent positive constant, for
`app:ch_regular_base:eq:sector-theorem-residual`. -/
theorem exists_vector_weakJet_one (n r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))), MemVectorFourierSobolev 1 u →
      ∃ J : (j : ℕ) → EuclideanSpace ℝ (Fin n) →
          (EuclideanSpace ℝ (Fin n)) [×j]→L[ℝ] EuclideanSpace ℂ (Fin r),
        Mollification.HasWeakJetOn volume u J univ 1 ∧
        (∀ j ≤ 1, MemLp (J j) 2 volume) ∧
        (∑ j ∈ Finset.range 2, (eLpNorm (J j) 2 volume).toReal) ≤
          C * vectorFourierSobolevNorm 1 u := by
  refine ⟨((r : ℝ) + 1) * (1 + 2 * Real.pi * n), by positivity, ?_⟩
  intro u hu
  obtain ⟨D, hD, hm, hb⟩ := exists_vector_firstWeakDerivative u hu
  exact ⟨firstWeakJet u D, hasWeakJetOn_firstWeakJet hD,
    memLp_firstWeakJet (Lp.memLp u) hm,
    (firstWeakJet_normSum (Lp.memLp u) hm).le.trans hb⟩

/-- Any local L² class agreeing with a whole-space Fourier H¹ datum has an
actual weak Sobolev extension with the same uniform bound. This is the output
comparison for `app:ch_regular:thm:exact-correction`; even measurability of the
domain is unnecessary once a local L² class and a.e. agreement are supplied. -/
theorem exists_vector_sobolevExtension_one (n r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))), MemVectorFourierSobolev 1 u →
      ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 U (EuclideanSpace ℂ (Fin r))),
      (u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v →
      ∃ e : SobolevExtension U 1 v,
        e.toFun = u ∧ e.toL2 = u ∧ e.jetNorm ≤ C * vectorFourierSobolevNorm 1 u := by
  obtain ⟨C, hC, h⟩ := exists_vector_weakJet_one n r
  refine ⟨C, hC, fun u hu U v huv ↦ ?_⟩
  obtain ⟨J, hw, hm, hb⟩ := h u hu
  let e : SobolevExtension U 1 v :=
    ⟨u, J, hw, Lp.memLp u, hm, huv⟩
  refine ⟨e, rfl, ?_, hb⟩
  apply Lp.ext
  exact e.toL2_coeFn

/-- The genuine restriction H¹ norm is controlled by the vector Fourier H¹
norm, with no extra order and with membership proved as a conclusion. The
sector residual in `app:ch_regular_base:eq:sector-theorem-residual` supplies
the Fourier premise when this comparison is instantiated. -/
theorem vector_restrictionSobolev_one_bounds (n r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n)))), MemVectorFourierSobolev 1 u →
      ∀ (U : Set (EuclideanSpace ℝ (Fin n))) (v : LocalL2 U (EuclideanSpace ℂ (Fin r))),
      (u : EuclideanSpace ℝ (Fin n) → _) =ᵐ[volume.restrict U] v →
      MemRestrictionSobolev U 1 v ∧
        restrictionSobolevNorm U 1 v ≤ C * vectorFourierSobolevNorm 1 u := by
  obtain ⟨C, hC, h⟩ := exists_vector_sobolevExtension_one n r
  refine ⟨C, hC, fun u hu U v huv ↦ ?_⟩
  obtain ⟨e, _, _, hb⟩ := h u hu U v huv
  exact ⟨⟨e⟩, (restrictionSobolevNorm_le e).trans hb⟩

end JanetCartan.LocalSobolev
