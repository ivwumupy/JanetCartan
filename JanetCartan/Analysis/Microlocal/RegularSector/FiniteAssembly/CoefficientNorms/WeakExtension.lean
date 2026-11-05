module

public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.SmoothEstimate
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.Approximation
public import JanetCartan.Analysis.Sobolev.Local.Smooth.FiniteOrder.UniformLimit
public import JanetCartan.Analysis.Sobolev.Local.Basic
public import JanetCartan.Analysis.ContDiff.Norm.Basic
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Coefficient seminorm bounds from every weak extension

For `app:not:fourier` and the coefficient budgets in
`app:ch_regular_base:eq:sector-theorem-solution` and
`app:ch_regular_base:eq:sector-theorem-residual`, the smooth jet estimate passes
through weak-jet approximation. Keeping the uniform limits of the lower jets
retains the quantitative estimate. Almost-everywhere equality then identifies
the representative with the original smooth coefficient on the open norm ball.

The consumer is the coefficient-norm comparison for
`FiniteAssembly.exists_finite_direct_operator_bounds`. The bound applies to
every genuine weak extension and keeps the given Banach target norm, including
the Frobenius matrix norm and the supremum norm on arrays of those matrices.
The infimum over extensions belongs to the parent comparison.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace JanetCartan.RegularSector.FiniteAssembly.CoefficientNorms

open LocalSobolev LocalSobolev.FiniteOrder

/-- Retain the uniform convergence of every lower jet in the finite-order limit
argument of `app:not:fourier`. This supplies the quantitative limit evidence
used by `exists_cNorm_le_extension_jetNorm`. -/
private theorem exists_contDiff_tendstoUniformly_iteratedFDeriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {v : ℕ → E → F} {k : ℕ}
    (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hC : ∀ j ≤ k, UniformCauchySeqOn (fun i ↦ iteratedFDeriv ℝ j (v i)) atTop univ) :
    ∃ g : E → F, ContDiff ℝ k g ∧ TendstoUniformly v g atTop ∧
      ∀ j ≤ k, TendstoUniformly (fun i ↦ iteratedFDeriv ℝ j (v i))
        (iteratedFDeriv ℝ j g) atTop := by
  have hex : ∀ j : ℕ, ∃ G : E → E [×j]→L[ℝ] F,
      j ≤ k → TendstoUniformly (fun i ↦ iteratedFDeriv ℝ j (v i)) G atTop := by
    intro j
    by_cases hj : j ≤ k
    · have hp : ∀ x : E, ∃ w, Tendsto (fun i ↦ iteratedFDeriv ℝ j (v i) x)
          atTop (𝓝 w) := fun x ↦
        cauchySeq_tendsto_of_complete ((hC j hj).cauchySeq (mem_univ x))
      choose G hG using hp
      refine ⟨G, fun _ ↦ ?_⟩
      rw [← tendstoUniformlyOn_univ]
      exact (hC j hj).tendstoUniformlyOn_of_tendsto (fun x _ ↦ hG x)
    · exact ⟨0, fun h ↦ (hj h).elim⟩
  choose G hG using hex
  let g : E → F := fun x ↦ (G 0 x).curry0
  have ht : HasFTaylorSeriesUpTo (k : ℕ∞ω) g (fun x j ↦ G j x) := by
    refine ⟨fun _ ↦ rfl, ?_, ?_⟩
    · intro j hj x
      have hjk : j < k := by exact_mod_cast hj
      have hnext := (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (j + 1) ↦ E) F).isometry.uniformContinuous.comp_tendstoUniformly
          (hG (j + 1) (by omega))
      exact hasFDerivAt_of_tendstoUniformly hnext
        (fun i x ↦ (hv i).ftaylorSeries.fderiv j (by exact_mod_cast ENat.natCast_lt_top j) x)
        (fun x ↦ (hG j (by omega)).tendsto_at x) x
    · intro j hj
      exact (hG j (by exact_mod_cast hj)).continuous
        (Eventually.of_forall fun i ↦ (hv i).continuous_iteratedFDeriv (by simp)).frequently
  refine ⟨g, ht.contDiff, ?_, ?_⟩
  · have hzero := (continuousMultilinearCurryFin0 ℝ E F).isometry.uniformContinuous
      |>.comp_tendstoUniformly (hG 0 (Nat.zero_le k))
    simpa [Function.comp_def, g] using hzero
  · intro j hj
    have heq : G j = iteratedFDeriv ℝ j g :=
      funext fun x ↦ ht.eq_iteratedFDeriv (by exact_mod_cast hj) x
    exact heq ▸ hG j hj

/-- The original coefficient seminorm is bounded by every actual weak Sobolev
extension, with a constant chosen before the ball, coefficient, local class,
and extension (`app:not:fourier`,
`app:ch_regular_base:eq:sector-theorem-solution`,
`app:ch_regular_base:eq:sector-theorem-residual`). The derivative reserve is
`n + 1`; only the given Banach norm on the target is used. This is the input
to the infimum argument replacing the original coefficient budgets in
`FiniteAssembly.exists_finite_direct_operator_bounds`. -/
theorem exists_cNorm_le_extension_jetNorm (n m : ℕ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (x : EuclideanSpace ℝ (Fin n)) (RQ R : ℝ),
      0 < RQ → RQ < R → ∀ f : EuclideanSpace ℝ (Fin n) → F,
      ContDiffOn ℝ ∞ f (ball x R) → ∀ u : LocalL2 (ball x R) F,
      f =ᵐ[volume.restrict (ball x R)] u →
      ∀ e : SobolevExtension (ball x R) (m + n + 1) u,
      cNorm (closedBall x RQ) m f ≤ C * e.jetNorm := by
  obtain ⟨C, hC, hest⟩ := exists_smooth_jet_estimate (F := F) n m
  refine ⟨max 1 ((m + 1 : ℝ) * C), le_max_left _ _, ?_⟩
  intro x RQ R _hRQ hR f hf u hfu e
  obtain ⟨v, hv, _, hvJ, hvf, hvconv⟩ :=
    exists_smooth_approximation_weakJet volume e.weakJet e.memLp_fun e.memLp_jet
  have hCauchy := uniformCauchySeqOn_iteratedFDeriv_of_smooth_estimate
    hv hvJ hvconv C hest
  obtain ⟨g, hg, hvg, hvgJ⟩ := exists_contDiff_tendstoUniformly_iteratedFDeriv hv hCauchy
  have hsum : Tendsto (fun i ↦ C * ∑ l ∈ Finset.range (m + n + 1 + 1),
      (eLpNorm (iteratedFDeriv ℝ l (v i)) 2 volume).toReal)
      atTop (𝓝 (C * e.jetNorm)) := by
    apply Tendsto.const_mul
    unfold SobolevExtension.jetNorm
    apply tendsto_finsetSum
    intro l hl
    have hl' : l ≤ m + n + 1 := by simpa using Finset.mem_range.mp hl
    simpa only [Lp.norm_toLp] using
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun i ↦ hvJ i l hl') _
        (e.memLp_jet l hl')).mpr (hvconv l hl')).norm
  have hbound : ∀ j ≤ m, ∀ y, ‖iteratedFDeriv ℝ j g y‖ ≤ C * e.jetNorm := by
    intro j hj y
    exact le_of_tendsto_of_tendsto ((hvgJ j hj).tendsto_at y).norm hsum
      (Eventually.of_forall fun i ↦ hest (v i) (hv i) (hvJ i) j hj y)
  have hge : g =ᵐ[volume] e.toFun :=
    ae_eq_of_tendsto_eLpNorm_of_tendsto hvf hvg.tendsto_at
  have hge' : g =ᵐ[volume.restrict (ball x R)] e.toFun := ae_restrict_of_ae hge
  have hgf : g =ᵐ[volume.restrict (ball x R)] f :=
    hge'.trans (e.restrict_eq.trans hfu.symm)
  have heq : EqOn g f (ball x R) :=
    Measure.eqOn_open_of_ae_eq hgf isOpen_ball hg.continuous.continuousOn hf.continuousOn
  have hjet : ∀ j ≤ m, ∀ y ∈ closedBall x RQ,
      ‖iteratedFDeriv ℝ j f y‖ ≤ C * e.jetNorm := by
    intro j hj y hy
    have hnear : g =ᶠ[𝓝 y] f :=
      heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds (closedBall_subset_ball hR hy))
    rw [← (hnear.iteratedFDeriv ℝ j).eq_of_nhds]
    exact hbound j hj y
  calc
    cNorm (closedBall x RQ) m f ≤
        ∑ _j ∈ Finset.range (m + 1), C * e.jetNorm :=
      cNorm_le_sum_of_bounds (fun _ _ ↦ mul_nonneg hC e.jetNorm_nonneg) hjet
    _ = ((m + 1 : ℝ) * C) * e.jetNorm := by simp; ring
    _ ≤ max 1 ((m + 1 : ℝ) * C) * e.jetNorm :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) e.jetNorm_nonneg

end JanetCartan.RegularSector.FiniteAssembly.CoefficientNorms
