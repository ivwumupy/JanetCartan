module

public import JanetCartan.Analysis.Sobolev.Local.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition.SmoothExtension

/-!
# The fixed coefficient norm ball and its actual local classes

For `app:not:fourier` and `sector-theorem-solution` / `sector-theorem-residual`,
the coefficient norm domain is chosen before the coefficients. It contains the
unchanged compact coefficient measurement ball with a positive margin, and its
closure remains inside the original smoothness domain. A supported smooth
extension proves restriction Sobolev membership of the literal coefficients at
every finite order. No estimate for a near-minimal extension is asserted here.

The consumer is `FiniteAssembly.exists_finite_direct_operator_bounds`. The
coefficient-array norm and the Frobenius matrix norm are retained throughout.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.FiniteAssembly.CoefficientNorms

variable {n : ℕ} {Ω : Set (Euclidean n)} {x : Euclidean n} {R : ℝ}

/-- Choose the norm ball before varying coefficients, with a positive margin
around the original coefficient compact set and compact closure in the original
domain (`app:not:fourier`, `sector-theorem-solution`, `sector-theorem-residual`).
This does not change any coefficient compact set, family, mask, or radial threshold. -/
theorem exists_coefficient_norm_ball (hΩ : IsOpen Ω) {RQ : ℝ}
    (hRQ : 0 < RQ) (hQΩ : closedBall x RQ ⊆ Ω) :
    ∃ R : ℝ, RQ < R ∧ Bornology.IsBounded (ball x R) ∧
      IsCompact (closure (ball x R)) ∧ closure (ball x R) ⊆ Ω ∧
      ∃ ε : ℝ, 0 < ε ∧ closedBall x (RQ + ε) ⊆ ball x R := by
  obtain ⟨δ, hδ, hδΩ⟩ :=
    (isCompact_closedBall x RQ).exists_cthickening_subset_open hΩ hQΩ
  rw [cthickening_closedBall hδ.le hRQ.le] at hδΩ
  refine ⟨RQ + δ / 2, by linarith, isBounded_ball, ?_, ?_,
    δ / 4, by positivity, closedBall_subset_ball (by linarith)⟩
  · exact (isCompact_closedBall x (RQ + δ / 2)).of_isClosed_subset
      isClosed_closure closure_ball_subset_closedBall
  · exact closure_ball_subset_closedBall.trans
      ((closedBall_subset_closedBall (by linarith : RQ + δ / 2 ≤ δ + RQ)).trans hδΩ)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A coefficient smooth on the original domain is square integrable on the
fixed norm ball. The proof uses a genuine supported smooth extension
(`app:not:fourier`, `sector-theorem-solution`). -/
theorem memLp_smoothCoefficient (hΩ : IsOpen Ω) (hR : 0 < R)
    (hball : closedBall x R ⊆ Ω) {f : Euclidean n → F}
    (hf : ContDiffOn ℝ ∞ f Ω) :
    MemLp f 2 (volume.restrict (ball x R)) := by
  obtain ⟨g, hg, hgc, _, heq⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall x hR hΩ hball hf
  apply ((hg.continuous.memLp_of_hasCompactSupport hgc).restrict (ball x R)).ae_eq
  exact (ae_restrict_mem measurableSet_ball).mono fun y hy ↦
    (heq y (ball_subset_closedBall hy)).eq_of_nhds

/-- The actual local L² equivalence class of the original coefficient, using
the existing target norm (`app:not:fourier`, `sector-theorem-solution`). -/
def smoothCoefficientL2 (hΩ : IsOpen Ω) (hR : 0 < R)
    (hball : closedBall x R ⊆ Ω) (f : Euclidean n → F)
    (hf : ContDiffOn ℝ ∞ f Ω) : LocalSobolev.LocalL2 (ball x R) F :=
  (memLp_smoothCoefficient hΩ hR hball hf).toLp f

/-- The constructed local class represents the literal coefficient on the
whole norm ball (`app:not:fourier`). -/
theorem smoothCoefficientL2_coeFn (hΩ : IsOpen Ω) (hR : 0 < R)
    (hball : closedBall x R ⊆ Ω) (f : Euclidean n → F)
    (hf : ContDiffOn ℝ ∞ f Ω) :
    smoothCoefficientL2 hΩ hR hball f hf =ᵐ[volume.restrict (ball x R)] f :=
  MemLp.coeFn_toLp _

/-- The original coefficient class has a genuine whole-space weak extension
at every order. The supported smooth construction proves membership; the
restriction norm still takes the infimum over all weak extensions
(`app:not:fourier`, `sector-theorem-solution`, `sector-theorem-residual`). -/
theorem smoothCoefficientL2_memRestrictionSobolev (hΩ : IsOpen Ω) (hR : 0 < R)
    (hball : closedBall x R ⊆ Ω) (f : Euclidean n → F)
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    LocalSobolev.MemRestrictionSobolev (ball x R) m
      (smoothCoefficientL2 hΩ hR hball f hf) := by
  obtain ⟨g, hg, hgc, _, heq⟩ :=
    ProjectedStressFrame.exists_contDiff_extension_eq_near_closedBall x hR hΩ hball hf
  refine ⟨{
    toFun := g
    jet := fun j ↦ iteratedFDeriv ℝ j g
    weakJet := Mollification.hasWeakJetOn_of_contDiff volume (hg.of_le (by simp)) univ
    memLp_fun := hg.continuous.memLp_of_hasCompactSupport hgc
    memLp_jet := fun j _ ↦
      (hg.continuous_iteratedFDeriv (by simp)).memLp_of_hasCompactSupport
        (hgc.iteratedFDeriv j)
    restrict_eq := ?_ }⟩
  have hgf : g =ᵐ[volume.restrict (ball x R)] f :=
    (ae_restrict_mem measurableSet_ball).mono fun y hy ↦
      (heq y (ball_subset_closedBall hy)).eq_of_nhds
  exact hgf.trans (smoothCoefficientL2_coeFn hΩ hR hball f hf).symm

/-- Both literal sector coefficients, with the coefficient-array norm for `Q`
and the Frobenius norm for `B`, yield genuine restriction Sobolev elements on
the same fixed ball at every order (`app:not:fourier`,
`sector-theorem-solution`, `sector-theorem-residual`). -/
theorem coefficient_pair_memRestrictionSobolev {d : ℕ}
    {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {R : ℝ}
    (hΩ : IsOpen Ω) (hR : 0 < R) (hball : closedBall x R ⊆ Ω)
    (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
    (B : Euclidean (d + 1) → MetricTensor (d + 1))
    (hQ : ContDiffOn ℝ ∞ Q Ω) (hB : ContDiffOn ℝ ∞ B Ω) (m : ℕ) :
    LocalSobolev.MemRestrictionSobolev (ball x R) m
        (smoothCoefficientL2 hΩ hR hball Q hQ) ∧
      LocalSobolev.MemRestrictionSobolev (ball x R) m
        (smoothCoefficientL2 hΩ hR hball B hB) :=
  ⟨smoothCoefficientL2_memRestrictionSobolev hΩ hR hball Q hQ m,
    smoothCoefficientL2_memRestrictionSobolev hΩ hR hball B hB m⟩

end JanetCartan.RegularSector.FiniteAssembly.CoefficientNorms
