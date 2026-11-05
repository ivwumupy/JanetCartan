module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.FullCoefficientDilation.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Periodization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Operator

/-!
# Uniform normalized image coefficients on a supplied fixed cutoff

For `app:ch_background:prop:bg-normalized`, periodize the complete geometric
reduced coefficients of the source dilations of the supplied flat reference.
The background uses the frozen principal coefficients and zero lower-order
completion, with the SAME supplied cutoff. The interval is chosen before all
derivative orders; neither the radii nor the cutoff vary with the source scale.

`FullCoefficientDilation.exists_fullReducedCoefficients_dilation_bounds`
produces the actual coefficient estimates and local smoothness on a neighborhood
of the fixed closed ball. `ImageGeometry.Periodization` transfers them to the
literal centered arrays. The image inputs of
`exists_augmentedNormal_tame_commutators` and
`Canonical.exists_measured_retained_augmented_bounds` consume the resulting
absolute jet bounds. The plateau identifies the physical operator, its weak
torus-volume representative and its full formal adjoint on these same arrays.

This supplies the image part of `app:ch_background:eq:bg-uniform-normalized`.
The normalized-background parent still has to instantiate its common row cutoff
and prove the carrier gap and the inverse estimates for that same family.
-/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace JanetCartan.RetainedAssembly.NormalizedImage

open GeometricProfile ProtectedFlow ContinuumRow ImageGeometry Periodization
open ReferenceInitialization.FullCoefficientDilation

variable {n : ℕ}

/-- The actual fixed-cutoff image arrays for
`app:ch_background:prop:bg-normalized`. All full physical jets of their
difference from the algebraic zero-scale background are `O_m(σ)`; their
absolute jets are uniformly bounded. One positive scale interval precedes
every order and constant. The formulas, plateau and physical/formal-adjoint
identities all use the supplied reference and cutoff, including every
zeroth-order coefficient (`app:ch_waves:eq:reduced-symbol`). -/
theorem exists_normalized_image_coefficients (H : FlatReference n)
    {r₀ r₁ R : ℝ} (_hr₀ : 0 < r₀) (h₀₁ : r₀ < r₁) (h₁R : r₁ < R)
    (hR : R < 1 / 2) {χ : Euclidean n → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hs : tsupport χ ⊆ Metric.ball 0 r₁)
    (hp : Metric.closedBall 0 r₀ ⊆ interior {x | χ x = 1}) :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ σ₀ ≤ 1 ∧
      ∃ (c₀ : ReducedCoefficientIndex n → C(Torus n, ℝ))
        (c : (σ : ℝ) → σ ∈ Ioc (0 : ℝ) σ₀ →
          ReducedCoefficientIndex n → C(Torus n, ℝ)),
        (∀ j z, c₀ j z = χ (AmplitudeBound.centeredTorusRepresentative z) *
          reducedCoefficientBackground (fun _ _ ↦ 0)
            (AmplitudeBound.centeredTorusRepresentative z) j) ∧
        (∀ j, IsSmoothPeriodic (c₀ j)) ∧
        (∀ j x, x ∈ Metric.closedBall 0 r₀ → periodicLift (c₀ j) =ᶠ[𝓝 x]
          (fun y ↦ reducedCoefficientBackground (fun _ _ ↦ 0) y j)) ∧
        (∀ σ hσ j z, c σ hσ j z = χ (AmplitudeBound.centeredTorusRepresentative z) *
          geometricReducedCoefficients (sourceDilation H.map σ)
            (AmplitudeBound.centeredTorusRepresentative z) j) ∧
        (∀ σ hσ j, IsSmoothPeriodic (c σ hσ j)) ∧
        (∀ σ hσ j x, x ∈ Metric.closedBall 0 r₀ → periodicLift (c σ hσ j) =ᶠ[𝓝 x]
          (fun y ↦ geometricReducedCoefficients (sourceDilation H.map σ) y j)) ∧
        (∀ m : ℕ, ∃ C : ℝ, 0 < C ∧
          (∀ j x, ‖iteratedFDeriv ℝ m (periodicLift (c₀ j)) x‖ ≤ C) ∧
          ∀ σ hσ j x,
            ‖iteratedFDeriv ℝ m (periodicLift (c σ hσ j - c₀ j)) x‖ ≤ C * σ ∧
            ‖iteratedFDeriv ℝ m (periodicLift (c σ hσ j)) x‖ ≤ C) ∧
        (∀ σ hσ (f : Torus n → Euclidean n), IsSmoothPeriodic f →
          ∀ x ∈ Metric.closedBall 0 r₀,
            reducedPeriodicFormula (c σ hσ) f (torusQuotient x) =
              WithLp.toLp 2 (NullTransport.reducedOperator (sourceDilation H.map σ)
                (fun y i ↦ (StressFrame.geometricCubeStress (sourceDilation H.map σ) y i).val)
                (periodicLift f) x)) ∧
        (∀ σ hσ (ψ : Euclidean n → ℝ) (hψ : ContDiff ℝ ∞ ψ)
          (hψs : tsupport ψ ⊆ Metric.closedBall 0 r₀)
          (f : Torus n → Euclidean n) (hf : IsSmoothPeriodic f),
          cutoffMultiplier (periodizedImageCutoff (h₀₁.trans (h₁R.trans hR)) ψ hψ hψs)
            (reducedWeakOperator (c σ hσ) (PeriodicSobolevSpace.ofSmooth 1 f hf)) =ᵐ[volume]
            fun z ↦ ψ (AmplitudeBound.centeredTorusRepresentative z) •
              WithLp.toLp 2 (NullTransport.reducedOperator (sourceDilation H.map σ)
                (fun y i ↦ (StressFrame.geometricCubeStress (sourceDilation H.map σ) y i).val)
                (periodicLift f) (AmplitudeBound.centeredTorusRepresentative z))) ∧
        (∀ σ hσ (g : Torus n → Euclidean n), IsSmoothPeriodic g →
          ∀ x ∈ Metric.closedBall 0 r₀, ∀ k : Fin n,
            reducedFormalAdjoint (c σ hσ) g (torusQuotient x) k =
              -(∑ a, ∑ i, fderiv ℝ (fun y ↦
                geometricReducedCoefficients (sourceDilation H.map σ) y (.inl (a, i, k))) x
                  (EuclideanSpace.single a 1) * periodicLift g x i) -
              (∑ a, ∑ i, geometricReducedCoefficients (sourceDilation H.map σ) x
                (.inl (a, i, k)) *
                  (fderiv ℝ (periodicLift g) x (EuclideanSpace.single a 1)) i) +
              ∑ i, geometricReducedCoefficients (sourceDilation H.map σ) x (.inr (i, k)) *
                periodicLift g x i) := by
  obtain ⟨U, hU, hKU, σ₀, hσ₀, hσ₁, _hseg, hgeom, hb⟩ :=
    exists_fullReducedCoefficients_dilation_bounds H
      (isCompact_closedBall (0 : Euclidean n) R)
  let q₀ : Euclidean n → ReducedCoefficientIndex n → ℝ :=
    reducedCoefficientBackground (fun _ _ ↦ 0)
  let q : ℝ → Euclidean n → ReducedCoefficientIndex n → ℝ :=
    fun σ ↦ geometricReducedCoefficients (sourceDilation H.map σ)
  have hq₀ : ContDiff ℝ ∞ q₀ := contDiff_reducedCoefficientBackground contDiff_const
  have hq (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) :
      ContDiffOn ℝ ∞ (q σ) (Metric.ball 0 R) :=
    (hgeom σ hσ).2.2.2.mono (Metric.ball_subset_closedBall.trans hKU)
  have hqa (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) (m : ℕ)
      (x : Euclidean n) (hx : x ∈ Metric.closedBall 0 R) :
      ContDiffAt ℝ m (q σ) x :=
    ((hgeom σ hσ).2.2.2.contDiffAt (hU.mem_nhds (hKU hx))).of_le (by simp)
  let c₀ := periodicReducedCoefficients h₁R (h₁R.trans hR) hχ hs q₀ hq₀.contDiffOn
  let c := fun σ hσ ↦
    periodicReducedCoefficients h₁R (h₁R.trans hR) hχ hs (q σ) (hq σ hσ)
  have hc (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) (j : ReducedCoefficientIndex n) :
      IsSmoothPeriodic (c σ hσ j) :=
    isSmoothPeriodic_cutCoefficient h₁R (h₁R.trans hR) hχ hs (hq σ hσ) j
  have heq (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) (j : ReducedCoefficientIndex n)
      (x : Euclidean n) (hx : x ∈ Metric.closedBall 0 r₀) :
      periodicLift (c σ hσ j) =ᶠ[𝓝 x] (fun y ↦ q σ y j) :=
    periodicReducedCoefficients_eventuallyEq h₀₁ h₁R (h₁R.trans hR) hχ hs hp
      (q σ) (hq σ hσ) j hx
  refine ⟨σ₀, hσ₀, hσ₁, c₀, c, ?_, ?_, ?_, ?_, hc, heq, ?_, ?_, ?_, ?_⟩
  · exact periodicReducedCoefficients_apply h₁R (h₁R.trans hR) hχ hs q₀ hq₀.contDiffOn
  · exact isSmoothPeriodic_cutCoefficient h₁R (h₁R.trans hR) hχ hs hq₀.contDiffOn
  · intro j x hx
    exact periodicReducedCoefficients_eventuallyEq h₀₁ h₁R (h₁R.trans hR) hχ hs hp
      q₀ hq₀.contDiffOn j hx
  · intro σ hσ
    exact periodicReducedCoefficients_apply h₁R (h₁R.trans hR) hχ hs (q σ) (hq σ hσ)
  · intro m
    obtain ⟨B, hB, hbound⟩ := hb m
    let D := cutoffDerivativeBound χ r₁ m
    let B₀ := cNorm (Metric.closedBall 0 r₁) m q₀
    have hD : 0 < D := cutoffDerivativeBound_pos χ r₁ m
    have hB₀ : 0 ≤ B₀ := cNorm_nonneg _ _ _
    have hdiff (σ : ℝ) (hσ : σ ∈ Ioc (0 : ℝ) σ₀) :
        cNorm (Metric.closedBall 0 r₁) m (q σ - q₀) ≤ B * σ :=
      (cNorm_mono_set_of_contDiffAt (Metric.closedBall_subset_closedBall h₁R.le)
        (isCompact_closedBall 0 R)
        (fun x hx ↦ (hqa σ hσ m x hx).sub (hq₀.contDiffAt.of_le (by simp)))).trans
          (hbound σ hσ).1
    refine ⟨D * (B + B₀ + 1), mul_pos hD (by positivity), ?_, ?_⟩
    · intro j x
      exact (norm_iteratedFDeriv_periodicReducedCoefficients_le h₁R (h₁R.trans hR)
        hχ hs q₀ hq₀.contDiffOn m j x).trans
          (mul_le_mul_of_nonneg_left (by dsimp [B₀]; linarith) hD.le)
    · intro σ hσ j x
      have hdiffq : ContDiffOn ℝ ∞ (q σ - q₀) (Metric.ball 0 R) :=
        (hq σ hσ).sub hq₀.contDiffOn
      have hsub : c σ hσ j - c₀ j =
          periodicReducedCoefficients h₁R (h₁R.trans hR) hχ hs (q σ - q₀) hdiffq j := by
        ext z
        change χ (AmplitudeBound.centeredTorusRepresentative z) *
            q σ (AmplitudeBound.centeredTorusRepresentative z) j -
          χ (AmplitudeBound.centeredTorusRepresentative z) *
            q₀ (AmplitudeBound.centeredTorusRepresentative z) j =
          χ (AmplitudeBound.centeredTorusRepresentative z) *
            (q σ (AmplitudeBound.centeredTorusRepresentative z) j -
              q₀ (AmplitudeBound.centeredTorusRepresentative z) j)
        exact (mul_sub ..).symm
      have hqnorm : cNorm (Metric.closedBall 0 r₁) m (q σ) ≤ B * σ + B₀ := by
        have hadd := cNorm_add_le_of_contDiffAt (isCompact_closedBall 0 r₁)
          (fun y hy ↦ (hqa σ hσ m y (Metric.closedBall_subset_closedBall h₁R.le hy)).sub
            (hq₀.contDiffAt.of_le (by simp)))
          (fun _ _ ↦ hq₀.contDiffAt.of_le (show (m : ℕ∞ω) ≤ ∞ by simp))
        change cNorm (Metric.closedBall 0 r₁) m ((q σ - q₀) + q₀) ≤ _ at hadd
        simpa only [sub_add_cancel] using hadd.trans (add_le_add (hdiff σ hσ) (le_refl B₀))
      constructor
      · rw [hsub]
        calc
          _ ≤ D * cNorm (Metric.closedBall 0 r₁) m (q σ - q₀) :=
            norm_iteratedFDeriv_periodicReducedCoefficients_le h₁R (h₁R.trans hR)
              hχ hs (q σ - q₀) hdiffq m j x
          _ ≤ D * (B * σ) := mul_le_mul_of_nonneg_left (hdiff σ hσ) hD.le
          _ ≤ D * (B + B₀ + 1) * σ := by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by linarith) hD.le) hσ.1.le
      · calc
          _ ≤ D * cNorm (Metric.closedBall 0 r₁) m (q σ) :=
            norm_iteratedFDeriv_periodicReducedCoefficients_le h₁R (h₁R.trans hR)
              hχ hs (q σ) (hq σ hσ) m j x
          _ ≤ D * (B * σ + B₀) := mul_le_mul_of_nonneg_left hqnorm hD.le
          _ ≤ D * (B + B₀ + 1) := mul_le_mul_of_nonneg_left
            (by nlinarith [hσ.2.trans hσ₁]) hD.le
  · intro σ hσ f hf x hx
    exact reducedPeriodicFormula_eq_geometric_of_eventuallyEq
      (sourceDilation H.map σ) (c σ hσ) f hf (fun j ↦ heq σ hσ j x hx)
  · intro σ hσ ψ hψ hψs f hf
    exact cutoff_reducedWeakOperator_ofSmooth_ae (sourceDilation H.map σ) (c σ hσ)
      (h₀₁.trans (h₁R.trans hR)) (heq σ hσ) ψ hψ hψs f hf
  · intro σ hσ g hg x hx k
    exact reducedFormalAdjoint_eq_geometric_jets (sourceDilation H.map σ) (c σ hσ)
      (hc σ hσ) g hg (fun j ↦ heq σ hσ j x hx) k

end JanetCartan.RetainedAssembly.NormalizedImage
