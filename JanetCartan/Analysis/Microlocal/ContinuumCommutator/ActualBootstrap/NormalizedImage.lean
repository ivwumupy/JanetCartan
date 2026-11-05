module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RetainedAssembly.NormalizedImage
public import JanetCartan.Analysis.Microlocal.ContinuumCommutator.ImageChannel.Translation
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AuxiliaryAdjoints
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.FixedCutoffs

/-!
# Uniform image estimates before varying the normalized source scale

Apply the actual normalized geometric coefficient producer to a supplied fixed
measurement radius and coefficient cutoff. The image-normal translation bound
and the image/exterior adjoint bounds are then proved with constants before
every `σ ∈ (0, σ₀]`. No bound on the varying coefficients or operators is an
input. An array supplied by the common row is identified with the producer's
array by its exact centered formula, not by identifying existential choices.

Consumers: `PositiveBackground.SourceInverse` and the normalized-family
application of `exists_uniform_augmentedNormal_elliptic_estimates` in
`app:ch_background:prop:bg-inverse` and `app:ch_background:prop:bg-normalized`.
The common radius/cutoff, normalized carrier family, its uniform low and high
budgets, and positive total-normal gap still belong to the actual normalized
construction. Fixed-source history estimates alone do not supply them.
-/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace JanetCartan.ContinuumCommutator
open ContinuumRow AmplitudeBound
  ContinuumAdjoint.Canonical.AuxiliaryAdjoints ImageChannelTranslation

variable {n : ℕ}

/-- The fixed periodic cutoff's first jet has one global bound, as needed
by the translation step of `app:ch_background:prop:bg-inverse`. -/
private theorem fixed_periodic_cutoff_first_jet_le (χ : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic χ) (x : Euclidean n) :
    ‖iteratedFDeriv ℝ 1 (periodicLift χ) x‖ ≤
      cNorm (fundamentalCell n) 1 (periodicLift χ) := by
  apply norm_iteratedFDeriv_periodicLift_le χ 1 _ x
  intro y hy
  exact norm_iteratedFDeriv_le_cNorm (isCompact_fundamentalCell n)
    (hχ.2.of_le (by simp)) hy (le_refl 1)

/-- The literal normalized image has uniform translation and full auxiliary
adjoint estimates on the supplied SAME cutoffs
(`app:ch_background:eq:bg-uniform-normalized`,
`app:ch_background:eq:bg-commutator`, `app:ch_background:prop:bg-adjoint`).
The radius and cutoff precede the interval; every analytic constant precedes
the varying source scale. The exact geometric formula transfers these
estimates to any coefficient array retained by the common row. -/
theorem exists_normalized_image_analytic_bounds (H : FlatReference n)
    {r : ℝ} (hr : 0 < r) (hR : 6 * r < 1 / 2)
    {χcoeff : Euclidean n → ℝ} (hχcoeff : ContDiff ℝ ∞ χcoeff)
    (hs : tsupport χcoeff ⊆ Metric.ball 0 (5 * r))
    (hp : Metric.closedBall 0 (4 * r) ⊆ interior {x | χcoeff x = 1}) :
    let hcell : 4 * r < 1 / 2 := by linarith
    let χ := FixedCutoffs.periodic hr hcell 1
    let χsrc := FixedCutoffs.periodic hr hcell 2
    let ψ := FixedCutoffs.periodic hr hcell 0
    let S := periodicSobolevScale n (Euclidean n)
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      ∃ P C : ℕ → ℝ, (∀ m, 0 < P m) ∧ (∀ s, 0 < C s) ∧
      ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧
      ∀ σ ∈ Ioc (0 : ℝ) σ₀,
        (∃ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
          ∀ a z, c a z = χcoeff (centeredTorusRepresentative z) *
            GeometricProfile.geometricReducedCoefficients (sourceDilation H.map σ)
              (centeredTorusRepresentative z) a) ∧
        ∀ c : GeometricProfile.ReducedCoefficientIndex n → C(Torus n, ℝ),
        (∀ a z, c a z = χcoeff (centeredTorusRepresentative z) *
          GeometricProfile.geometricReducedCoefficients (sourceDilation H.map σ)
            (centeredTorusRepresentative z) a) →
        (∀ a, IsSmoothPeriodic (c a)) ∧
        (∀ a j, j ≤ 1 → ∀ x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ L) ∧
        (∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c a)) x‖ ≤ P j) ∧
        (∀ (i : Fin n) (h : ℝ),
          ‖periodicConjugationDifference
            ((imageChannel c χ χsrc).comp (imageChannel c χ χsrc).adjoint) i h‖ ≤ B) ∧
        ∀ (s : ℕ) (w : OutputL2 n), w ∈ S.level s →
          (imageChannel c χ χsrc).adjoint w ∈ S.level s ∧
          (exteriorChannel ψ).adjoint w ∈ S.level s ∧
          S.gradeNorm s ((imageChannel c χ χsrc).adjoint w) +
            S.gradeNorm s ((exteriorChannel ψ).adjoint w) ≤
              C s * (S.gradeNorm s w + ‖w‖) := by
  intro hcell χ χsrc ψ S
  obtain ⟨σ₀, hσ₀, hσ₁, c₀, c, _, _, _, hformula, hc, _, hjets, _⟩ :=
    RetainedAssembly.NormalizedImage.exists_normalized_image_coefficients H
      (by positivity : 0 < 4 * r) (by linarith : 4 * r < 5 * r)
      (by linarith : 5 * r < 6 * r) hR hχcoeff hs hp
  choose P hP _ hjet using hjets
  let L := P 0 + P 1
  have hL : 0 ≤ L := add_nonneg (hP 0).le (hP 1).le
  have hm := FixedCutoffs.periodic_smooth (n := n) hr hcell 1
  have hsrc := FixedCutoffs.periodic_smooth (n := n) hr hcell 2
  have hext := FixedCutoffs.periodic_smooth (n := n) hr hcell 0
  obtain ⟨B, hB, htranslation⟩ := exists_uniform_imageNormal_translation_bound
    n (P 0) (P 1) ‖χ‖ ‖χsrc‖
    (cNorm (fundamentalCell n) 1 (periodicLift χ))
    (cNorm (fundamentalCell n) 1 (periodicLift χsrc))
    (hP 0).le (hP 1).le (norm_nonneg _) (norm_nonneg _)
    (cNorm_nonneg ..) (cNorm_nonneg ..)
  obtain ⟨C, hC, hadjoint⟩ := exists_auxiliaryAdjoints_gradeNorm_profile
    χ χsrc ψ hm hsrc hext hL P (fun j ↦ (hP j).le)
  refine ⟨σ₀, hσ₀, hσ₁, P, C, hP, hC, L, B, hL, hB, ?_⟩
  intro σ hσ
  refine ⟨⟨c σ hσ, hformula σ hσ⟩, ?_⟩
  intro c' hc'
  have heq : c' = c σ hσ := by
    funext a
    ext z
    exact (hc' a z).trans (hformula σ hσ a z).symm
  subst c'
  have hhigh (a j x) : ‖iteratedFDeriv ℝ j (periodicLift (c σ hσ a)) x‖ ≤ P j :=
    (hjet j σ hσ a x).2
  have hlow : ∀ a j, j ≤ 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (periodicLift (c σ hσ a)) x‖ ≤ L := by
    intro a j hj x
    apply (hhigh a j x).trans
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · exact le_add_of_nonneg_right (hP 1).le
    · exact le_add_of_nonneg_left (hP 0).le
  have hvalue : ∀ a z, |c σ hσ a z| ≤ P 0 := by
    intro a z
    simpa only [norm_iteratedFDeriv_zero, periodicLift, Function.comp_apply,
      torusQuotient_centeredTorusRepresentative, Real.norm_eq_abs] using
      hhigh a 0 (centeredTorusRepresentative z)
  refine ⟨hc σ hσ, hlow, hhigh,
    htranslation _ (hc σ hσ) hvalue (fun a ↦ hhigh a 1) χ χsrc hm hsrc
      χ.norm_coe_le_norm χsrc.norm_coe_le_norm
      (fixed_periodic_cutoff_first_jet_le χ hm)
      (fixed_periodic_cutoff_first_jet_le χsrc hsrc), ?_⟩
  intro s w hw
  have hhigh' : ∀ a j x, ‖iteratedFDeriv ℝ j (periodicLift (c σ hσ a)) x‖ ≤
      P j * (1 + (fun _ : ℕ ↦ (0 : ℝ)) (j + 2)) := by
    simpa only [add_zero, mul_one] using hhigh
  simpa only [S, periodicSobolevScale, add_zero, one_mul] using
    hadjoint (c σ hσ) (hc σ hσ) (fun _ ↦ 0) (fun _ ↦ le_rfl) monotone_const
      hlow hhigh' s w hw

end JanetCartan.ContinuumCommutator
