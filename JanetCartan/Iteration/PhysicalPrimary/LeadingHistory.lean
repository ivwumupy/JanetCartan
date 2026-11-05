module

public import JanetCartan.Iteration.PhysicalSeed.GenericLeading
public import JanetCartan.Iteration.PhysicalPrimary.LeadingAdmission
public meta import JanetCartan.Iteration.PhysicalPrimary.LeadingTemplates

/-!
# Same retained leading data on actual physical histories

Instantiate the original generic leading continuation on the SAME revised
physical prefix, with no new row/cell selector. Both full/carrier flow systems,
their compatibility, and scalar transport conclusions are retained literally.
-/

set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false

declare_physical_primary_retained_leading_data

@[expose] public noncomputable section
set_option maxHeartbeats 1200000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPrimary

open FrozenMenu ActualCarriers.CurrentFullPhase ProjectedStressFrame

/-- The retained original callback, instantiated on actual revised physical
histories. This is a real all-cell leading construction: its conclusion is
LITERALLY the full original carrier/full-ODE, compatibility, nonvanishing,
transport and shift-13/14 scalar data, not a replacement success record. The
single original tuple and all its row/column choices are unchanged; every
current-map hypothesis is discharged by physical admissibility.

The `GenericLeading` premise is the checked `PhysicalSeed` retained finite
selector's arbitrary-map continuation. At the final constructor it is the
SAME `PhysicalSeed.OriginalBoundary.generic_leading` field, not a new selector.
Consumers: the actual `Chart`, `Compatibility`, and `Solution` inputs of
`PhysicalNormalInverse.exists_capped_source_history_inverse_from_original_leading`
and the complete primary's `fullCorrectionCovector` (`main:prop:current-waves`). -/
theorem exists_history_retained_leading_data {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {P : Patch n} (T : PatchQuantitativeFamily P (ball (0 : Euclidean n) R) isOpen_ball)
    {η : ℝ} (hη : 0 < η) (centers : Finset (parameterCube P.radius))
    (row col : centers → Fin n) (ρ L τ Rc τc Mc rcomp δcomp σcover : centers → ℝ)
    (Ωc : centers → Set (Euclidean n × Euclidean 3)) (ρc Bc gc Bfull : centers → ℝ)
    (hgeneric : PhysicalSeed.GenericLeading T (K := closedBall (0 : Euclidean n) r)
      η centers row col ρ L τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull)
    {Bband : ℝ} (hBband : 1 ≤ Bband) {rStar kMin : ℕ} (hStar : 14 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    (hreference : ∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
      (fun x ↦ projectedStress G.map x i - cubeStress n i) < (η / (2 * (6 + 1 : ℝ))) / 2)
    {Mscalar mscalar : ℝ} (hMscalar : 0 ≤ Mscalar) (hmscalar : 0 < mscalar) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧
      ∃ Amap : ℕ → ℝ, (∀ q, 0 ≤ Amap q) ∧
      ∃ c : ℝ, ∃ E : ℕ → ℝ, ∃ A H B : centers → ℕ → ℝ,
      0 < c ∧ (∀ q, 0 < E q) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Bband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap G.map u
      ∃ hF : ContDiff ℝ ∞ F, ∃ hi : IsImmersionOn F (ball 0 R),
      ∃ hrank : HasFullNormalRankOn F (ball 0 R),
        RetainedLeadingData T (K := closedBall (0 : Euclidean n) r) centers row col
          ρ L τ Rc τc Mc rcomp δcomp σcover Ωc ρc Bc gc Bfull
          Mscalar mscalar c E A H B F hF.contDiffOn hi hrank ∧
        HasDerivativeProfile (closedBall 0 r) F rStar (currentCoefficientScale R₀ j) Amap := by
  obtain ⟨threshold, hthreshold, κ, hκ, Amap, hAmap, hadmit⟩ :=
    exists_history_leading_admission G hr hrR hR hBband hStar horder hη hreference
  obtain ⟨c, E, A, H, B, hc, hE, hactual⟩ := hgeneric
    (cNorm (closedBall 0 r) 14 G.map + 1) Mscalar (1/4) κ mscalar
    (add_nonneg (cNorm_nonneg _ _ _) zero_le_one) hMscalar (by norm_num) hκ hmscalar
  refine ⟨threshold, hthreshold, Amap, hAmap, c, E, A, H, B, hc, hE, ?_⟩
  intro R₀ hR₀ j u ell hu F
  obtain ⟨hF, hi, hrank, hFM, hmet, hnormal, hframe, hprofile⟩ := hadmit R₀ hR₀ j u ell hu
  exact ⟨hF, hi, hrank, hactual F hF.contDiffOn hi hrank hFM hmet hnormal hframe, hprofile⟩

end JanetCartan.PhysicalPrimary
