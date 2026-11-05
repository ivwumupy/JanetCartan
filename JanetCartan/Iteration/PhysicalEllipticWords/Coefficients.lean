module

public import JanetCartan.Iteration.PhysicalGeometry.Retained
public import JanetCartan.Iteration.PhysicalInitialization.AdmissionRange

/-!
# Actual admitted Q and full B for the elliptic letters

One fixed original-reference tolerance supplies both global coefficient
admission and every reserved coefficient profile of every physical history.
Consumers: the algebraic/endpoint letters in
`app:ch_response:eq:response-graded-reduced` and their exact finite-word join.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalEllipticWords
open ProtectedFlow ProjectedStressFrame GeometricProfile
open ResponseTransfer.RetainedFactors

/-- The range, smoothness and high-order profiles are conclusions for the
literal same extended Q and FULL zeroth coefficient B. The reference tolerance
is chosen before the reference, reserves, minimum accuracy and all histories. -/
theorem exists_admitted_history_coefficient_profiles {n : ℕ}
    (ext : BallExtension.Parameters (Euclidean n)) {r : ℝ}
    (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference n, ∀ R : ℝ,
      0 < r → r < R → R < G.domain.chartRadius →
      (∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
        (fun x ↦ projectedStress G.map x i - cubeStress n i) < η) →
      ∀ {Cband : ℝ}, 1 ≤ Cband →
      ∀ rStar reserve kMin : ℕ, 8 ≤ rStar → 2 + reserve ≤ rStar →
      RevisedScales.displacementLoss n +
        bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ) →
      ∃ S : ℝ, 2 ≤ S ∧ ∃ AQ AB : ℕ → ℝ,
        (∀ k, 0 ≤ AQ k) ∧ (∀ k, 0 ≤ AB k) ∧
        ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
        let F := RevisedGlobal.finiteMap G.map u
        let Q := extendedProjectedStress ext F
        let B := reducedZerothProjection n ∘ extendedReducedCoefficients ext (fun _ _ ↦ 0) F
        ContDiff ℝ ∞ Q ∧ ContDiff ℝ ∞ B ∧
          MapsTo Q univ (closedBall (cubeStress n) ε) ∧
          (∀ K : Set (Euclidean n), cNorm K 6 (Q - fun _ ↦ cubeStress n) < δ) ∧
          ∀ K : Set (Euclidean n), IsCompact K →
            HasDerivativeProfile K Q reserve (currentCoefficientScale R₀ j) AQ ∧
            HasDerivativeProfile K B reserve (currentCoefficientScale R₀ j) AB := by
  obtain ⟨η, hη, hadmit⟩ :=
    PhysicalInitialization.exists_reference_tolerance_for_physical_frame_admission
      ext hextcenter hextradius hε hδ
  refine ⟨η, hη, ?_⟩
  intro G R hr hrR hR href Cband hband rStar reserve kMin hStar hreserve horder
  obtain ⟨Sa, hSa, ha⟩ := hadmit G R hr hrR hR href hband rStar kMin hStar horder
  obtain ⟨Sp, hSp, AQ, AB, hAQ, hAB, hp⟩ :=
    PhysicalGeometry.exists_retained_coefficient_profiles G hr hrR hR ext
      hextcenter hextradius hband hStar hreserve horder
  refine ⟨max Sa Sp, hSa.trans (le_max_left _ _), AQ, AB, hAQ, hAB, ?_⟩
  intro R₀ hR₀ j u ell hu F Q B
  obtain ⟨hQ, hmap, hclose⟩ := ha R₀ ((le_max_left _ _).trans hR₀) j u ell hu
  obtain ⟨_, hB, hprofile⟩ := hp R₀ ((le_max_right _ _).trans hR₀) j u ell hu
  exact ⟨hQ, hB, hmap, hclose, hprofile⟩

end JanetCartan.PhysicalEllipticWords
