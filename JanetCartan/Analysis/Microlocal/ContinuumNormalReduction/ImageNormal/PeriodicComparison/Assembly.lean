module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Normal
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.Endpoint

/-!
# Comparison of the actual periodic and Euclidean image normals

For `app:ch_background:prop:bg-frame`, Step 1, instantiate the bounded
Euclidean channel and the differentiated one-factor lattice comparison.
Expanding both normal factors retains `B D*`, `D B*`, and `D D*`. The
one-factor construction derives its identity from
`periodicBesselInverse_localized_eq_add_remainder`; its output plateau is
one near the measurement support, so every plateau derivative defect
vanishes under the original measurement mask.

The final theorem assumes only the original smooth fixed data, their chart
support, and local coefficient agreement. ImageGeometry produces that
agreement. All channel actions and analytic bounds are instantiated here.
The parent image-normal reduction retains the splitting of `euclideanNormal`
into the leading full amplitude, coefficient remainder, and source commutator,
and the final geometric instantiation.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff
open JanetCartan.PeriodicLocalL2 JanetCartan.Pseudodifferential
open JanetCartan.Pseudodifferential.DifferentialChart

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "R²" => EuclideanL2 d E

set_option maxHeartbeats 800000 in
/-- The actual periodized image normal equals the bounded literal Euclidean
normal plus a gain-one error, with its literal adjoint, original measurement
support, and transferred negative endpoint
(`app:ch_background:prop:bg-frame`, Step 1, image-normal paragraph).

Here `pullback` is exactly `toEuclidean ∘ T ∘ toTorus`, using torus volume
and Lebesgue measure. `euclideanNormal_schwartz_action` identifies the same
Euclidean term with `coefficientSourceSquaredImageSchwartz`. The error is
constructed as all three cross terms of the proved one-factor comparison;
no smoothing estimate or channel identity remains as an input. -/
theorem exists_periodicImageNormal_comparison (hd : 0 < d)
    {r : ℝ} (hr : r < 1 / 2)
    (c : GeometricProfile.ReducedCoefficientIndex d → C(Torus d, ℝ))
    (hc : ∀ k, IsSmoothPeriodic (c k))
    (χ μ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hμ : ContDiff ℝ ∞ μ)
    (hχs : tsupport χ ⊆ chartBox r) (hμs : tsupport μ ⊆ chartBox r)
    (A : E → Fin d → Matrix (Fin d) (Fin d) ℝ)
    (Z : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ a i j, ContDiff ℝ ∞ (fun x ↦ A x a i j))
    (hZ : ∀ i j, ContDiff ℝ ∞ (fun x ↦ Z x i j))
    (hcA : ∀ x ∈ tsupport μ, ∀ a i j,
      periodicLift (c (.inl (a, i, j))) =ᶠ[nhds x] (fun y ↦ A y a i j))
    (hcZ : ∀ x ∈ tsupport μ, ∀ i j,
      periodicLift (c (.inr (i, j))) =ᶠ[nhds x] (fun y ↦ Z y i j)) :
    let hχc := hasCompactSupport_of_imageBessel_cube_support χ
      (fun _x hx ↦ hχs (subset_tsupport χ hx))
    let hμc := hasCompactSupport_of_imageBessel_cube_support μ
      (fun _x hx ↦ hμs (subset_tsupport μ hx))
    let T := ContinuumRow.imageChannel c (periodizedCutoff hr μ hμ hμs)
      (periodizedCutoff hr χ hχ hχs)
    ∃ S : R² →L[ℝ] R²,
      pullback (T.comp T.adjoint) = euclideanNormal A Z χ μ hA hZ hχ hχc hμ hμc + S ∧
      S.adjoint = S ∧
      (∀ f, (∀ᵐ x ∂volume, x ∉ tsupport μ → S f x = 0) ∧
        (∀ᵐ x ∂volume, x ∉ tsupport μ → S.adjoint f x = 0)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ f,
        MemVectorFourierSobolev 1 (l2ComplexInclusion volume (S f)) ∧
        vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (S f)) ≤ C * ‖f‖ ∧
        MemVectorFourierSobolev 1 (l2ComplexInclusion volume (S.adjoint f)) ∧
        vectorFourierSobolevNorm 1 (l2ComplexInclusion volume (S.adjoint f)) ≤ C * ‖f‖) ∧
      (∃ C : ℝ, 0 ≤ C ∧
        (∃ H : PeriodicL2 d E →L[ℝ] PeriodicSobolevSpace d E 1,
          (PeriodicSobolevSpace.toL2 1).comp H = (transferOperator S).adjoint ∧ ‖H‖ ≤ C) ∧
        ∀ f : PeriodicL2 d E,
          ‖transferOperator S f‖ ≤ C * ‖PeriodicSobolevNegativeOne.ofL2 f‖) := by
  let hχc := hasCompactSupport_of_imageBessel_cube_support χ
    (fun _x hx ↦ hχs (subset_tsupport χ hx))
  let hμc := hasCompactSupport_of_imageBessel_cube_support μ
    (fun _x hx ↦ hμs (subset_tsupport μ hx))
  let B := euclideanChannel A Z χ μ hA hZ hχ hχc hμ hμc
  obtain ⟨D, hcomparison, hDs, CD, hCD, hD⟩ :=
    exists_periodicChannel_oneFactorRemainder hd hr c hc χ μ hχ hμ hχs hμs
      A Z hA hZ hcA hcZ B
      (euclideanChannel_schwartz_action A Z χ μ hA hZ hχ hχc hμ hμc)
  obtain ⟨CB, hCB, hB⟩ :=
    euclideanChannel_sobolev_one_bound A Z χ μ hA hZ hχ hχc hμ hμc
  have hBs := euclideanChannel_support A Z χ μ hA hZ hχ hχc hμ hμc
  refine ⟨normalCrossTerms B D, ?_, normalCrossTerms_adjoint B D,
    normalCrossTerms_support B D μ hBs hDs,
    normalCrossTerms_sobolev_one_bounds B D hCB hCD hB hD,
    normalCrossTerms_periodic_endpoints hr B D μ hμs hBs hDs hCB hCD hB hD⟩
  exact pullback_normal_eq_of_channel_eq _ B D hcomparison

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison
