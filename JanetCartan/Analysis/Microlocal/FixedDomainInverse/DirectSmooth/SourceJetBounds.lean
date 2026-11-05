module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.DirectSmooth.TestSources
public import JanetCartan.Analysis.ContDiff.Norm.Basic

/-!
# Finite source-jet bounds for the same smooth solver

Apply the existing retarded-to-restriction norm comparison to every admitted
source. The additive tame bound of `DirectSmooth` gives the precise finite
source-jet estimate consumed by `Response.SmoothParameters` and by the
finite-band source superposition. The source map and solver are unchanged.
Sources: `app:ch_regular:eq:inverse-tame` and
`app:ch_response:thm:response-literal-transfer`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Metric
open scoped ContDiff
namespace JanetCartan.FixedDomainInverse
open LocalSobolev RetardedSobolev.Spaces

/-- The actual inverse's classical tame estimate controls every test source
in one finite retarded jet norm. The comparison constants precede the solver,
coefficient profile and all sources. `DirectSmooth` instantiates the sole
operator estimate on its SAME selected smooth solver; no bound restricted to
individual atoms is used (`app:ch_response:thm:response-literal-transfer`). -/
theorem exists_smoothSolver_source_jet_constants (d : ℕ) :
    ∃ D : ℕ → ℝ, (∀ s, 0 ≤ D s) ∧
      ∀ (W : Set (Euclidean (d+1))) (x : Euclidean (d+1)) (Rout : ℝ)
        (S : smoothSource W (Euclidean (d+1)) →ₗ[ℝ]
          (Euclidean (d+1) → Euclidean (d+1))) (C a : ℕ → ℝ) (ℓ β : ℕ),
      (∀ m, 0 ≤ C m) → (∀ s, 0 ≤ a s) →
      (∀ h, ContDiff ℝ ∞ (S h)) →
      (∀ (h : smoothSource W (Euclidean (d+1))) (m : ℕ),
        cNorm (closedBall x Rout) m (S h) ≤ C m *
          (restrictionSobolevNorm W (m+ℓ) (h : LocalL2 W (Euclidean (d+1))) +
            (1+a (m+ℓ+β))*‖(h : LocalL2 W (Euclidean (d+1)))‖)) →
      ∀ (L : ℂ →L[ℝ] Euclidean (d+1)) (m : ℕ) (f : Test d)
        (y : Euclidean (d+1)), y ∈ closedBall x Rout →
        ‖iteratedFDeriv ℝ m (S (retardedTestSmoothSource W L f)) y‖ ≤
          ((C m * (2+a (m+ℓ+β))) * (‖L‖ * D (m+ℓ))) * ‖ofTest (m+ℓ) volume f‖ := by
  obtain ⟨D, hD, hsource⟩ :=
    exists_retardedTestSourceL2_sobolev_constants (d := d) (F := Euclidean (d+1))
  refine ⟨D, hD, ?_⟩
  intro W x Rout S C a ℓ β hC ha hsmooth hbound L m f y hy
  let h := retardedTestSmoothSource W L f
  have hmem : MemRestrictionSobolev W (m+ℓ) (h : LocalL2 W (Euclidean (d+1))) :=
    h.property _
  have hn : restrictionSobolevNorm W (m+ℓ) (h : LocalL2 W (Euclidean (d+1))) ≤
      (‖L‖ * D (m+ℓ)) * ‖ofTest (m+ℓ) volume f‖ := (hsource W L (m+ℓ) f).2
  have hlow := norm_le_restrictionSobolevNorm hmem
  have hhi : 0 ≤ 1+a (m+ℓ+β) := add_nonneg zero_le_one (ha _)
  have hhi' : 0 ≤ 2+a (m+ℓ+β) := by linarith [ha (m+ℓ+β)]
  calc
    _ ≤ cNorm (closedBall x Rout) m (S h) :=
      norm_iteratedFDeriv_le_cNorm (isCompact_closedBall _ _)
        ((hsmooth h).of_le (by simp)) hy le_rfl
    _ ≤ C m * (restrictionSobolevNorm W (m+ℓ) (h : LocalL2 W (Euclidean (d+1))) +
        (1+a (m+ℓ+β))*‖(h : LocalL2 W (Euclidean (d+1)))‖) := hbound h m
    _ ≤ C m * ((2+a (m+ℓ+β)) *
        restrictionSobolevNorm W (m+ℓ) (h : LocalL2 W (Euclidean (d+1)))) := by
      apply mul_le_mul_of_nonneg_left _ (hC m)
      nlinarith [mul_le_mul_of_nonneg_left hlow hhi]
    _ ≤ C m * ((2+a (m+ℓ+β)) *
        ((‖L‖ * D (m+ℓ)) * ‖ofTest (m+ℓ) volume f‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hn hhi') (hC m)
    _ = _ := by ring

end JanetCartan.FixedDomainInverse
