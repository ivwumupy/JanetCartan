module

public import JanetCartan.Iteration.PhysicalInitialization.OriginalReference
public import JanetCartan.Iteration.PhysicalPrimary.LeadingHistory

/-!
# One original all-patch leading construction on physical histories

Instantiate the genuine retained callback on the concrete contracted reference.
The reference margin, original rows, phase domains, geometry, and all source
parameters are actual outputs of the SAME strengthened initializer. A finite
maximum selects one history threshold before histories; every leading constant
is fixed once. The global history is never periodized.

Consumers: the same-current chart/ODE extraction, current inverse and positive
background (`main:prop:current-waves`, `new:sec:order-of-choices`).
-/

@[expose] public noncomputable section
set_option warningAsError true
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalInitialization
open PhysicalSeed PhysicalPrimary
variable {n : ℕ}

/-- Deterministic wide-chart packaging of the SAME final reference map. -/
def originalWideContractedReference (hn : 5 ≤ n) {extra : ℝ} (hextra : 0 < extra)
    {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1) : FlatReference n :=
  sourceDilationReference (originalSourceReference hn hextra) hσ hσone

/-- No map, source scale or reference is reselected by wide-chart packaging. -/
theorem originalWideContractedReference_map (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1) :
    (originalWideContractedReference hn hextra hσ hσone).map =
      (originalContractedReference hn hextra hσ hσone).map :=
  (originalContractedReference_map hn hextra hσ hσone).symm

/-- The wide-chart radius is the original analytic radius. -/
theorem originalWideContractedReference_radius (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1) :
    OriginalBoundary.R hn <
      (originalWideContractedReference hn hextra hσ hσone).domain.chartRadius :=
  originalSourceReference_radius hn hextra

/-- The actual original callback supplies the complete leading data on ALL
original patches with one pre-history threshold. No leading-data premise, frame
closeness hypothesis, new row selection, or successful current inverse occurs.
The full covector, ODE, scalar transport, shift-13/14 and compatibility fields
are retained literally through `RetainedLeadingData` (`main:prop:current-waves`). -/
theorem exists_original_retained_physical_leading (hn : 5 ≤ n) {extra : ℝ}
    (hextra : 0 < extra) {σ : ℝ} (hσ : 0 < σ) (hσone : σ ≤ 1)
    {Cband : ℝ} (hband : 1 ≤ Cband) {rStar kMin : ℕ} (hStar : 14 ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ))
    {Mscalar mscalar : ℝ} (hMscalar : 0 ≤ Mscalar) (hmscalar : 0 < mscalar) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧
      ∃ Amap : OriginalPatchIndex hn → ℕ → ℝ,
      ∃ c : OriginalPatchIndex hn → ℝ,
      ∃ E : OriginalPatchIndex hn → ℕ → ℝ,
      ∃ A H B : (a : OriginalPatchIndex hn) → OriginalBoundary.centers hn a → ℕ → ℝ,
      (∀ a q, 0 ≤ Amap a q) ∧ (∀ a, 0 < c a) ∧ (∀ a q, 0 < E a q) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
        (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      let F := RevisedGlobal.finiteMap (originalContractedReference hn hextra hσ hσone).map u
      ∀ a : OriginalPatchIndex hn,
        ∃ hF : ContDiff ℝ ∞ F,
        ∃ hi : IsImmersionOn F (ball 0 (OriginalBoundary.R hn)),
        ∃ hrank : HasFullNormalRankOn F (ball 0 (OriginalBoundary.R hn)),
        RetainedLeadingData (OriginalBoundary.T hn a)
          (K := closedBall (0 : Euclidean n) (OriginalBoundary.b hn))
          (OriginalBoundary.centers hn a) (OriginalBoundary.row hn a) (OriginalBoundary.col hn a)
          (OriginalBoundary.ρlead hn a) (OriginalBoundary.L hn a) (OriginalBoundary.τ hn a)
          (OriginalBoundary.Rc hn a) (OriginalBoundary.τc hn a) (OriginalBoundary.Mc hn a)
          (OriginalBoundary.rcomp hn a) (OriginalBoundary.δcomp hn a) (OriginalBoundary.σcover hn a)
          (OriginalBoundary.Ωc hn a) (OriginalBoundary.ρc hn a) (OriginalBoundary.Bc hn a)
          (OriginalBoundary.gc hn a) (OriginalBoundary.Bfull hn a)
          Mscalar mscalar (c a) (E a) (A a) (H a) (B a) F hF.contDiffOn hi hrank ∧
        HasDerivativeProfile (closedBall 0 (OriginalBoundary.b hn)) F rStar
          (currentCoefficientScale R₀ j) (Amap a) := by
  classical
  let G := originalWideContractedReference hn hextra hσ hσone
  have hsame : G.map = (originalContractedReference hn hextra hσ hσone).map :=
    originalWideContractedReference_map hn hextra hσ hσone
  have hreference (a : OriginalPatchIndex hn) (i : Fin n) :
      cNorm (closedBall (0 : Euclidean n) (OriginalBoundary.b hn)) 6
        (fun x ↦ ProjectedStressFrame.projectedStress G.map x i - cubeStress n i) <
          (OriginalBoundary.η hn a / (2 * (6 + 1 : ℝ))) / 2 := by
    rw [hsame]
    exact originalContractedReference_leading_margin hn hextra hσ hσone a i
  have hconstruct (a : OriginalPatchIndex hn) :=
    exists_history_retained_leading_data G (OriginalBoundary.b_pos hn)
      (OriginalBoundary.b_lt_R hn) (originalWideContractedReference_radius hn hextra hσ hσone)
      (T := OriginalBoundary.T hn a) (OriginalBoundary.η_pos hn a)
      (OriginalBoundary.centers hn a) (OriginalBoundary.row hn a) (OriginalBoundary.col hn a)
      (OriginalBoundary.ρlead hn a) (OriginalBoundary.L hn a) (OriginalBoundary.τ hn a)
      (OriginalBoundary.Rc hn a) (OriginalBoundary.τc hn a) (OriginalBoundary.Mc hn a)
      (OriginalBoundary.rcomp hn a) (OriginalBoundary.δcomp hn a) (OriginalBoundary.σcover hn a)
      (OriginalBoundary.Ωc hn a) (OriginalBoundary.ρc hn a) (OriginalBoundary.Bc hn a)
      (OriginalBoundary.gc hn a) (OriginalBoundary.Bfull hn a)
      (OriginalBoundary.generic_leading hn a) hband hStar horder (hreference a) hMscalar hmscalar
  choose Sa hSa Amap hAmap c E A H B hc hE hdata using hconstruct
  let threshold := 2 + ∑ a, Sa a
  have hnonneg a : 0 ≤ Sa a := (by norm_num : (0 : ℝ) ≤ 2).trans (hSa a)
  have hthreshold : 2 ≤ threshold := le_add_of_nonneg_right (Finset.sum_nonneg fun a _ ↦ hnonneg a)
  have hle a : Sa a ≤ threshold := by
    exact (Finset.single_le_sum (fun b _ ↦ hnonneg b) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2))
  refine ⟨threshold, hthreshold, Amap, c, E, A, H, B, hAmap, hc, hE, ?_⟩
  intro R₀ hR₀ j u ell hu F a
  simpa only [hsame] using hdata a R₀ ((hle a).trans hR₀) j u ell hu

end JanetCartan.PhysicalInitialization
