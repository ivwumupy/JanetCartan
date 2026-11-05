module

public import JanetCartan.Analysis.Extension.Ball.ContinuousBounds
public import JanetCartan.Analysis.Extension.Ball.SobolevBounds

/-!
# One fixed smooth ball extension

For `app:ch_regular_base:lem:ball-extension`, the actual Seeley coefficients and
radial formula give a single linear operator. It extends smooth functions on the
closed ball, has support in one fixed compact collar, and is bounded at every
nonnegative integer `C^m` and derivative `H^m` order. The continuous input norm
uses intrinsic one-sided jets; the Sobolev norm counts each Cartesian multiindex
once. `exists_fixed_smooth_extension_with_bounds` chooses the operator and its
support before every order and input, and discharges all analytic prerequisites.

This proves the smooth-input construction and both estimates in the source
lemma. Extensions to completed finite-regularity spaces and comparison with
Bessel-potential restriction norms are separate results.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff

namespace JanetCartan.BallExtension

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace Parameters

variable (p : Parameters E)

/-- The single real linear operator in `app:ch_regular_base:lem:ball-extension`,
using the universal coefficients at all orders. -/
def seeleyExtension : (E → F) →ₗ[ℝ] (E → F) := p.linearMap Seeley.coeff

/-- Restriction of the fixed operator in `app:ch_regular_base:lem:ball-extension`. -/
theorem seeleyExtension_eq_on_closedBall (f : E → F) :
    EqOn (p.seeleyExtension f) f (closedBall p.center p.radius) :=
  p.extend_eq_on_closedBall Seeley.coeff f

/-- The fixed extension depends only on the input's restriction to the ball
(`app:ch_regular_base:lem:ball-extension`). -/
theorem seeleyExtension_congr {f g : E → F} (hfg : EqOn f g (closedBall p.center p.radius)) :
    p.seeleyExtension f = p.seeleyExtension g :=
  p.extend_congr Seeley.coeff hfg

/-- One fixed support for every input and order in
`app:ch_regular_base:lem:ball-extension`. -/
theorem tsupport_seeleyExtension_subset (f : E → F) :
    tsupport (p.seeleyExtension f) ⊆ closedBall p.center (p.radius + p.width / 2) :=
  p.tsupport_extend_subset Seeley.coeff f

/-- Compact support in `app:ch_regular_base:lem:ball-extension`. -/
theorem hasCompactSupport_seeleyExtension [FiniteDimensional ℝ E] (f : E → F) :
    HasCompactSupport (p.seeleyExtension f) :=
  p.hasCompactSupport_extend Seeley.coeff f

/-- Smoothness of the fixed operator in `app:ch_regular_base:lem:ball-extension`;
the moment and summability assumptions have been discharged. -/
theorem contDiff_seeleyExtension [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) :
    ContDiff ℝ ∞ (p.seeleyExtension f) :=
  p.contDiff_extend_finiteDimensional Seeley.coeff Seeley.summable_abs_coeff_moment
    Seeley.infinite_moment hf

/-- The extension commutes with real linear maps, including coordinate maps,
as asserted in `app:ch_regular_base:lem:ball-extension`. -/
theorem seeleyExtension_map {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : F →ₗ[ℝ] G) (f : E → F) :
    p.seeleyExtension (L ∘ f) = L ∘ p.seeleyExtension f :=
  p.extend_map Seeley.coeff L f

/-- Scalar compatibility in `app:ch_regular_base:lem:ball-extension`. In
particular the same real-coefficient formula is complex linear. -/
theorem seeleyExtension_smul {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] (r : 𝕜) (f : E → F) :
    p.seeleyExtension (r • f) = r • p.seeleyExtension f := by
  exact p.seeleyExtension_map (ContinuousLinearMap.lsmul ℝ 𝕜 r).toLinearMap f

/-- The single operator over a real normed scalar algebra; specializing to `ℂ`
gives the complex linear operator in `app:ch_regular_base:lem:ball-extension`. -/
def seeleyExtensionOver (𝕜 : Type*) [NormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedSpace 𝕜 F] [IsScalarTower ℝ 𝕜 F] : (E → F) →ₗ[𝕜] (E → F) where
  toFun := p.seeleyExtension
  map_add' := p.seeleyExtension.map_add
  map_smul' := p.seeleyExtension_smul

/-- All intrinsic `C^m` estimates for the same operator, as in
`app:ch_regular_base:eq:ball-extension-continuous`. -/
theorem exists_cNorm_seeleyExtension_le [FiniteDimensional ℝ E] (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : E → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      cNorm univ m (p.seeleyExtension f) ≤ C * p.closedBallCNorm m f :=
  p.exists_cNorm_extend_le m

end Parameters

/-- The derivative `H^m` bound for the same operator as the `C^m` estimate,
as in `app:ch_regular_base:eq:ball-extension-sobolev`. -/
theorem Parameters.exists_cartesianSobolevNorm_seeleyExtension_le {n : ℕ}
    (p : Parameters (EuclideanSpace ℝ (Fin n))) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      cartesianSobolevNorm univ m (p.seeleyExtension f) ≤
        C * cartesianSobolevNorm (ball p.center p.radius) m f :=
  p.exists_cartesianSobolevNorm_extend_bound m

/-- Every Cartesian derivative of the fixed extension lies in `L²`, so the
integrals defining the norm in `app:ch_regular_base:eq:ball-extension-sobolev`
are finite. -/
theorem Parameters.memLp_cartesianDerivativeWithin_seeleyExtension {n : ℕ}
    (p : Parameters (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (α : Fin n → ℕ) :
    MeasureTheory.MemLp (cartesianDerivativeWithin α (p.seeleyExtension f) univ)
      2 MeasureTheory.volume :=
  p.memLp_cartesianDerivativeWithin_extend hf α

/-- Restriction decreases the derivative norm of the fixed extension in
`app:ch_regular_base:lem:ball-extension`. -/
theorem Parameters.cartesianSobolevNorm_ball_le_seeleyExtension {n : ℕ}
    (p : Parameters (EuclideanSpace ℝ (Fin n)))
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (closedBall p.center p.radius)) (m : ℕ) :
    cartesianSobolevNorm (ball p.center p.radius) m f ≤
      cartesianSobolevNorm univ m (p.seeleyExtension f) :=
  p.cartesianSobolevNorm_ball_le_extend hf m

/-- Both estimates of `app:ch_regular_base:lem:ball-extension` hold for the
single fixed operator, with one positive constant at each order and only
closed-ball smoothness of the input. All dimensions, including zero and one,
are covered. -/
theorem Parameters.exists_seeleyExtension_bounds {n : ℕ}
    (p : Parameters (EuclideanSpace ℝ (Fin n))) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ ∞ f (closedBall p.center p.radius) →
      cNorm univ m (p.seeleyExtension f) ≤ C * p.closedBallCNorm m f ∧
      cartesianSobolevNorm univ m (p.seeleyExtension f) ≤
        C * cartesianSobolevNorm (ball p.center p.radius) m f := by
  obtain ⟨A, hA, hcont⟩ := p.exists_cNorm_seeleyExtension_le m
  obtain ⟨B, _, hsob⟩ := p.exists_cartesianSobolevNorm_seeleyExtension_le m
  refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
  intro f hf
  exact ⟨(hcont f hf).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (p.closedBallCNorm_nonneg m f)),
    (hsob f hf).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (cartesianSobolevNorm_nonneg _ _ _))⟩

/-- The smooth-input assertion of `app:ch_regular_base:lem:ball-extension`:
one real linear operator, with one compact support inside the prescribed open
neighborhood, satisfies both estimates at every order. It depends only on the
closed-ball restriction of the input, whose `C^m` norm is expressed using its
intrinsic jets. No ambient smooth extension or analytic estimate is assumed. -/
theorem exists_fixed_smooth_extension_with_bounds {n : ℕ}
    (c : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R)
    {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
    (hRV : closedBall c R ⊆ V) :
    ∃ L : (EuclideanSpace ℝ (Fin n) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ),
      ∃ K : Set (EuclideanSpace ℝ (Fin n)),
      IsCompact K ∧ K ⊆ V ∧
      (∀ f, EqOn (L f) f (closedBall c R)) ∧
      (∀ f, tsupport (L f) ⊆ K) ∧
      (∀ f, ContDiffOn ℝ ∞ f (closedBall c R) → ContDiff ℝ ∞ (L f)) ∧
      (∀ f g, EqOn f g (closedBall c R) → L f = L g) ∧
      (∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
        ContDiffOn ℝ ∞ f (closedBall c R) →
        cNorm univ m (L f) ≤ C *
          ∑ i ∈ Finset.range (m + 1),
            sSup ((fun x ↦ ‖iteratedFDerivWithin ℝ i f (closedBall c R) x‖) ''
              closedBall c R) ∧
        cartesianSobolevNorm univ m (L f) ≤
          C * cartesianSobolevNorm (ball c R) m f) := by
  obtain ⟨p, hc, hr, hpV⟩ := exists_parameters c hR hV hRV
  refine ⟨p.seeleyExtension, closedBall p.center (p.radius + p.width / 2),
    isCompact_closedBall _ _, ?_, ?_, p.tsupport_seeleyExtension_subset, ?_, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (by linarith [p.width_pos])).trans hpV
  · intro f
    simpa only [hc, hr] using p.seeleyExtension_eq_on_closedBall f
  · intro f hf
    exact p.contDiff_seeleyExtension (by simpa only [hc, hr] using hf)
  · intro f g hfg
    exact p.seeleyExtension_congr (by simpa only [hc, hr] using hfg)
  · intro m
    simpa only [Parameters.closedBallCNorm, hc, hr] using p.exists_seeleyExtension_bounds m

/-- The smooth, compactly supported operator and all continuous norm bounds in
`app:ch_regular_base:lem:ball-extension`. The operator and its support are chosen
before the order. The stronger intrinsic input estimate is
`Parameters.exists_cNorm_seeleyExtension_le`; for both estimates on Euclidean
space use `exists_fixed_smooth_extension_with_bounds`. -/
theorem exists_fixed_smooth_extension_with_continuous_bounds [FiniteDimensional ℝ E]
    (c : E) {R : ℝ} (hR : 0 < R) {V : Set E} (hV : IsOpen V)
    (hRV : closedBall c R ⊆ V) :
    ∃ L : (E → ℝ) →ₗ[ℝ] (E → ℝ), ∃ K : Set E,
      IsCompact K ∧ K ⊆ V ∧
      (∀ f, EqOn (L f) f (closedBall c R)) ∧
      (∀ f, tsupport (L f) ⊆ K) ∧
      (∀ f, ContDiffOn ℝ ∞ f (closedBall c R) → ContDiff ℝ ∞ (L f)) ∧
      (∀ f g, EqOn f g (closedBall c R) → L f = L g) ∧
      (∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (f : E → ℝ), ContDiff ℝ ∞ f →
        cNorm univ m (L f) ≤ C * cNorm (closedBall c R) m f) := by
  obtain ⟨p, hc, hr, hpV⟩ := exists_parameters c hR hV hRV
  refine ⟨p.seeleyExtension, closedBall p.center (p.radius + p.width / 2),
    isCompact_closedBall _ _, ?_, ?_, p.tsupport_seeleyExtension_subset, ?_, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (by linarith [p.width_pos])).trans hpV
  · intro f
    simpa only [hc, hr] using p.seeleyExtension_eq_on_closedBall f
  · intro f hf
    exact p.contDiff_seeleyExtension (by simpa only [hc, hr] using hf)
  · intro f g hfg
    exact p.seeleyExtension_congr (by simpa only [hc, hr] using hfg)
  · intro m
    obtain ⟨C, hC, hb⟩ := p.exists_cNorm_seeleyExtension_le m
    refine ⟨C, hC, ?_⟩
    intro f hf
    simpa only [p.closedBallCNorm_eq_cNorm hf m, hc, hr] using hb f hf.contDiffOn

end JanetCartan.BallExtension
