module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint.CompactKernel
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Fubini for the compact full graph

The finite sum and the physical and frequency integrals in
`app:ch_regular_base:eq:actual-adjoint-trade` commute by continuity and compact
support. This leaf supplies the integrability for the literal identification.
-/

@[expose] public noncomputable section
open MeasureTheory Filter Set
namespace JanetCartan.FourierIntegral.FullLowBounds
variable {n r : ℕ}
local notation "E" => Euclidean n

/-- Evaluation and Fubini for the compact matrix integrand. Consumer:
`compactFullGraph_adjoint_ae` (`app:ch_regular_base:eq:actual-adjoint-trade`). -/
theorem compactEntry_integral_sum
    (F : Fin r → Fin r → E × E → ℂ)
    (hc : ∀ i j, Continuous (F i j)) (hs : ∀ i j, HasCompactSupport (F i j))
    (u : E → Fin r → ℂ) (hu : Continuous u) (i : Fin r) :
    (∫ η, ∫ y, fun i ↦ ∑ j, F i j (η, y) * u y j) i =
      ∑ j, ∫ y, (∫ η, F i j (η, y)) * u y j := by
  have hi (i j : Fin r) : Integrable (fun p : E × E ↦ F i j p * u p.2 j)
      ((volume : Measure E).prod volume) :=
    ((hc i j).mul ((continuous_apply j).comp (hu.comp continuous_snd))).integrable_of_hasCompactSupport
      (hs i j).mul_right
  have hv : Integrable (fun p : E × E ↦ fun i ↦ ∑ j, F i j p * u p.2 j)
      ((volume : Measure E).prod volume) :=
    integrable_pi_iff.mpr (fun i ↦ integrable_finsetSum _ (fun j _ ↦ hi i j))
  rw [← integral_prod _ hv, eval_integral (fun i ↦ integrable_finsetSum _ (fun j _ ↦ hi i j)),
    integral_finsetSum _ (fun j _ ↦ hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_prod_symm _ (hi i j)]
  simp only [integral_mul_const]

/-- Integrating the frequency of a continuous compact full kernel gives a
continuous compact physical kernel. Consumer: the finite-cutoff full-graph
adjoint identification (`app:ch_regular_base:eq:actual-adjoint-trade`). -/
theorem compactEntry_integral_regular
    {F : (E × E) × E → ℂ} (hc : Continuous F) (hs : HasCompactSupport F) :
    Continuous (fun p : E × E ↦ ∫ η, F (p, η)) ∧
      HasCompactSupport (fun p : E × E ↦ ∫ η, F (p, η)) := by
  have hz (p : E × E) (η : E) (hη : η ∉ Prod.snd '' tsupport F) : F (p, η) = 0 := by
    by_contra h
    exact hη ⟨(p, η), subset_tsupport F h, rfl⟩
  constructor
  · have he : (fun p : E × E ↦ ∫ η, F (p, η)) =
        fun p ↦ ∫ η in Prod.snd '' tsupport F, F (p, η) := by
      funext p
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hz p)).symm
    rw [he]
    exact continuous_parametric_integral_of_continuous (f := fun p η ↦ F (p, η))
      hc (hs.image continuous_snd)
  · apply HasCompactSupport.of_support_subset_isCompact (hs.image continuous_fst)
    intro p hp
    by_contra hn
    apply hp
    apply integral_eq_zero_of_ae
    exact Eventually.of_forall fun η ↦ by
      by_contra h
      exact hn ⟨(p, η), subset_tsupport F h, rfl⟩

/-- The frequency/source section remains compactly supported. This supplies
Fubini in the forward literal graph (`app:ch_regular_base:thm:actual-calculus`, Step 1). -/
theorem compactEntry_forward_section
    {F : (E × E) × E → ℂ} (hs : HasCompactSupport F) (x : E) :
    HasCompactSupport (fun p : E × E ↦ F ((x, p.2), p.1)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hs.image (continuous_snd.prodMk continuous_fst.snd))
  intro p hp
  exact ⟨((x, p.2), p.1), subset_tsupport F hp, rfl⟩

/-- The frequency/output section remains compactly supported. This supplies
Fubini in the reverse literal graph (`app:ch_regular_base:eq:actual-adjoint-trade`). -/
theorem compactEntry_reverse_section
    {F : (E × E) × E → ℂ} (hs : HasCompactSupport F) (y : E) :
    HasCompactSupport (fun p : E × E ↦ star (F ((p.2, y), p.1))) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (hs.image (continuous_snd.prodMk continuous_fst.fst))
  intro p hp
  refine ⟨((p.2, y), p.1), subset_tsupport F ?_, rfl⟩
  simpa only [Function.mem_support, star_ne_zero] using hp

end JanetCartan.FourierIntegral.FullLowBounds
