module

public import JanetCartan.Iteration.PhysicalGeometry.Neighborhood
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Neighborhood
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ReducedCoefficients

/-!
# Full reduced coefficients of the same physical current map

The reserve-two part of `main:prop:current-scale` in `paper-v2.tex`.  The
current map is the actual Schwartz prefix of the prescribed reference.
Its low geometric neighborhood and its all-order map profile are produced
from the physical band and revised L² history budgets, then the existing
finite-jet estimate produces the full reduced array, including the connection
term.  The reference, source dilation and coefficient extension remain fixed.

The consumers are the same-field regular-sector estimates and retained
response coefficients used by the analytic producer of
`RevisedGlobal.UniformHistoryCorrection`.  No inverse, modulation estimate,
or finite-stage correction is asserted here.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalGeometry

open GeometricProfile ProtectedFlow ContinuumRow.ImageGeometry

/-- `main:prop:current-scale`: the actual full reduced coefficient array has a
reserve-two profile on the fixed coefficient ball for every physical history.
Its smoothness and every high-order estimate are conclusions of the physical
history bounds; no compact-range or coefficient estimate is assumed. -/
theorem exists_reduced_coefficient_profiles {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    {B : ℝ} (hB : 1 ≤ B) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧
      ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
        let F := RevisedGlobal.finiteMap G.map u
        ContDiffOn ℝ ∞ (geometricReducedCoefficients F) (ball 0 R) ∧
        HasDerivativeProfile (closedBall 0 r) (geometricReducedCoefficients F) reserve
          (currentCoefficientScale R₀ j) A := by
  obtain ⟨δ, hδ, _, _, C, hC, hcoeff⟩ :=
    exists_reference_reduced_coefficient_estimates G hr hrR hR
  obtain ⟨S, hS, hnear⟩ := exists_initialScale_for_c8_neighborhood
    G.map R hB hStar horder hδ
  obtain ⟨A, hA, hprofile⟩ := PhysicalHistory.exists_prefix_derivative_profile
    (isCompact_closedBall (0 : Euclidean n) R) (fun _ _ ↦ G.contDiff.contDiffAt) hB horder
  refine ⟨S, hS, (fun m ↦ C m * (1 + A (m + 2))),
    (fun m ↦ mul_nonneg (hC m).le (by linarith [hA (m + 2)])), ?_⟩
  intro R₀ hR₀ j u ell hu
  have hF : ContDiff ℝ ∞ (RevisedGlobal.finiteMap G.map u) :=
    G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨hsmooth, _, hc⟩ := hcoeff _ hF (hnear R₀ hR₀ j u ell hu)
  have hp := hprofile R₀ (hS.trans hR₀) j u ell hu _ Subset.rfl
  refine ⟨hsmooth, fun m ↦ ?_⟩
  exact JointBudget.fixed_profile_transfer_bound
    (one_le_currentCoefficientScale (by linarith [hS.trans hR₀]) j)
    (hA (m + 2)) (hC m).le hreserve (hp (m + 2)) (hc m)

-- The prescribed affine background is constant, so the global coefficient
-- bound is uniform in every later compact measurement set.  The unbundled
-- Seeley bound is reused; no history or extension is changed.
private theorem exists_global_affine_array_bound {n N : ℕ}
    (p : BallExtension.Parameters (Euclidean n)) (m : ℕ) :
    ∃ C > 0, ∀ F : Euclidean n → Euclidean N, ContDiff ℝ ∞ F →
      ∀ U : Set (Euclidean n), IsOpen U → closedBall p.center p.radius ⊆ U →
      IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm univ m (extendedReducedCoefficients p (fun _ _ ↦ 0) F) ≤
        C * (1 + cNorm (closedBall p.center p.radius) m (geometricReducedCoefficients F)) := by
  obtain ⟨A, hA, hbound⟩ := exists_cNorm_vector_seeleyExtension_le
    (F := ReducedCoefficientIndex n → ℝ) p m
  let a₀ : Euclidean n → ReducedCoefficientIndex n → ℝ :=
    reducedCoefficientBackground (fun _ _ ↦ 0)
  have ha₀ : a₀ = fun _ ↦ a₀ 0 := rfl
  have hs₀ : ContDiff ℝ ∞ a₀ := contDiff_reducedCoefficientBackground contDiff_const
  let B := ‖a₀ 0‖ + A * cNorm (closedBall p.center p.radius) m a₀
  have hB : 0 ≤ B := add_nonneg (norm_nonneg _) (mul_nonneg hA.le (cNorm_nonneg _ _ _))
  refine ⟨(m + 1 : ℝ) * (B + A + 1), by positivity, ?_⟩
  intro F hF U hU hpU hi hrank
  let a := geometricReducedCoefficients F
  have ha : ∀ x ∈ closedBall p.center p.radius, ContDiffAt ℝ ∞ a x := fun x hx ↦
    (contDiffOn_geometricReducedCoefficients hF hU hi hrank).contDiffAt (hU.mem_nhds (hpU hx))
  let g := p.seeleyExtension (a - a₀)
  have hg : ContDiff ℝ ∞ g := p.contDiff_seeleyExtension
    (fun x hx ↦ ((ha x hx).sub hs₀.contDiffAt).contDiffWithinAt)
  have he := hbound (a - a₀) (fun x hx ↦ (ha x hx).sub hs₀.contDiffAt)
  have hsub : cNorm (closedBall p.center p.radius) m (a - a₀) ≤
      cNorm (closedBall p.center p.radius) m a + cNorm (closedBall p.center p.radius) m a₀ := by
    simpa only [sub_eq_add_neg, cNorm_neg] using
      cNorm_add_le_of_contDiffAt (f := a) (g := -a₀) (isCompact_closedBall p.center p.radius)
        (fun x hx ↦ (ha x hx).of_le (by simp))
        (fun _ _ ↦ hs₀.contDiffAt.neg.of_le (by simp))
  have he' : cNorm univ m g ≤ A *
      (cNorm (closedBall p.center p.radius) m a + cNorm (closedBall p.center p.radius) m a₀) :=
    he.trans (mul_le_mul_of_nonneg_left hsub hA.le)
  obtain ⟨M, _, hM⟩ := (p.hasCompactSupport_seeleyExtension (a - a₀)).exists_bound_iteratedFDeriv hg m
  have hjet (j : ℕ) (hj : j ≤ m) (x : Euclidean n) :
      ‖iteratedFDeriv ℝ j (a₀ + g) x‖ ≤ ‖a₀ 0‖ + cNorm univ m g := by
    rw [iteratedFDeriv_add_apply (hs₀.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
    apply (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [ha₀]
      cases j with
      | zero => simp
      | succ j => simp [iteratedFDeriv_succ_const]
    · exact norm_iteratedFDeriv_le_cNorm_of_bddAbove
        (show BddAbove ((fun y ↦ ‖iteratedFDeriv ℝ j g y‖) '' univ) from
          ⟨M, by rintro _ ⟨y, _, rfl⟩; exact hM j hj y⟩) (mem_univ x) hj
  have htotal := cNorm_le_sum_of_bounds (s := univ) (r := m) (f := a₀ + g)
    (C := fun _ ↦ ‖a₀ 0‖ + cNorm univ m g)
    (fun _ _ ↦ add_nonneg (norm_nonneg _) (cNorm_nonneg _ _ _))
    (fun j hj x _ ↦ hjet j hj x)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at htotal
  apply htotal.trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : (0 : ℝ) ≤ m + 1)
  have hnorm := cNorm_nonneg (closedBall p.center p.radius) m a
  dsimp only [B] at hB ⊢
  nlinarith

/-- `main:prop:current-scale` and `app:ch_regular:eq:coefficient-extension`:
the prescribed affine Seeley extension of the FULL actual reduced array has
one global reserve-two profile for every physical prefix.  The constants
precede all histories and all compact measurement sets.  Smoothness, exact
agreement on the original coefficient ball and the fixed support are produced,
not supplied as success hypotheses. -/
theorem exists_extended_reduced_profiles {n : ℕ} (G : FlatReference n)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0)
    (hpradius : p.radius = r) {B : ℝ} (hB : 1 ≤ B) {rStar reserve kMin : ℕ}
    (hStar : 8 ≤ rStar) (hreserve : 2 + reserve ≤ rStar)
    (horder : RevisedScales.displacementLoss n +
      bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < (kMin : ℝ)) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A E : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ E m) ∧
      ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
          (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
        let F := RevisedGlobal.finiteMap G.map u
        ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) ∧
        EqOn (extendedReducedCoefficients p (fun _ _ ↦ 0) F) (geometricReducedCoefficients F)
          (closedBall 0 r) ∧
        tsupport (extendedReducedCoefficients p (fun _ _ ↦ 0) F -
            reducedCoefficientBackground (fun _ _ ↦ 0)) ⊆ closedBall 0 (r + p.width / 2) ∧
        HasDerivativeProfile (closedBall 0 r) (geometricReducedCoefficients F) reserve
          (currentCoefficientScale R₀ j) A ∧
        HasDerivativeProfile univ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) reserve
          (currentCoefficientScale R₀ j) E := by
  obtain ⟨Sr, hSr, A, hA, hraw⟩ :=
    exists_reduced_coefficient_profiles G hr hrR hR hB hStar hreserve horder
  obtain ⟨Sg, hSg, _, _, _, _, hgeom⟩ :=
    exists_geometric_neighborhood G hr hrR hR hB hStar horder (by norm_num : (0 : ℝ) < 1)
  choose D hD hext using exists_global_affine_array_bound (N := embeddingDimension n) p
  refine ⟨max Sr Sg, hSr.trans (le_max_left _ _), A, (fun m ↦ D m * (1 + A m)), hA,
    (fun m ↦ mul_nonneg (hD m).le (by linarith [hA m])), ?_⟩
  intro R₀ hR₀ j u ell hu
  have hRR := (le_max_left Sr Sg).trans hR₀
  have hRG := (le_max_right Sr Sg).trans hR₀
  have hscale := one_le_currentCoefficientScale (by linarith [hSr.trans hRR]) j
  let F := RevisedGlobal.finiteMap G.map u
  have hF : ContDiff ℝ ∞ F := G.contDiff.add (ContDiff.sum (fun i _ ↦ (u i).smooth'))
  obtain ⟨hi, hrank, _⟩ := hgeom R₀ hRG j u ell hu
  have hp := (hraw R₀ hRR j u ell hu).2
  have hpU : closedBall p.center p.radius ⊆ ball (0 : Euclidean n) R := by
    simpa only [hpcenter, hpradius] using closedBall_subset_ball hrR
  refine ⟨contDiff_extendedReducedCoefficients p _ contDiff_const hF isOpen_ball hi hrank hpU,
    ?_, ?_, hp, ?_⟩
  · simpa only [hpcenter, hpradius] using extendedReducedCoefficients_eqOn p (fun _ _ ↦ 0) F
  · simpa only [hpcenter, hpradius] using tsupport_extendedReducedCoefficients_sub p (fun _ _ ↦ 0) F
  · intro m
    have he := hext m F hF (ball 0 R) isOpen_ball hpU hi hrank
    simp only [hpcenter, hpradius] at he
    exact JointBudget.fixed_profile_transfer_bound (c := 0) (R := reserve)
      hscale (hA m) (hD m).le (by omega) (by simpa using hp m) he

end JanetCartan.PhysicalGeometry
