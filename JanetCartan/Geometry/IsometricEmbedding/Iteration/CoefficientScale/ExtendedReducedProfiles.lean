module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ActualHistory
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.ImageGeometry.Neighborhood
public import JanetCartan.Analysis.Microlocal.ProtectedFlow.ReducedCoefficients

/-!
# The fixed affine extension of the actual history's reduced coefficients

The complete array of `P_F`, including its zeroth-order connection terms, has
`app:eq:uniform-high-coeff` for every admissible prefix of the SAME reference.
One prescribed Seeley operator is used at every order and stage. The affine
background is the frozen principal frame with zero lower-order completion.
The global estimate includes that background, and the perturbation has one
fixed compact support. The consumer is the regular response coefficient array
in `main:prop:current-scale`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CurrentCoefficientProfiles

open ProtectedFlow GeometricProfile ContinuumRow.ImageGeometry

private theorem exists_global_extendedReducedCoefficients_bound {n N : ℕ}
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

/-- The full affine extended reduced-operator array has the paper profile for
all admissible histories. Its smoothness, fixed support and agreement with the
literal array are proved as well. No current low bound, coefficient estimate or
extension estimate is an input; the selected reference and Seeley operator are
preserved. The reserve is exactly two (`main:prop:current-scale`,
`app:eq:uniform-high-coeff`, `app:ch_regular:eq:coefficient-extension`). -/
theorem exists_admissible_history_extended_reduced_profiles {n : ℕ}
    (G : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G.domain.chartRadius)
    (p : BallExtension.Parameters (Euclidean n)) (hpcenter : p.center = 0) (hpradius : p.radius = r)
    {rStar r₀ kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 2 + r₀ ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ S : ℝ, 2 ≤ S ∧ ∃ A E : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ E m) ∧
      ∀ R₀, S ≤ R₀ →
      ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let F := finiteHistoryMap G.map u
      ContDiff ℝ ∞ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) ∧
      EqOn (extendedReducedCoefficients p (fun _ _ ↦ 0) F) (geometricReducedCoefficients F)
        (closedBall 0 r) ∧
      tsupport (extendedReducedCoefficients p (fun _ _ ↦ 0) F -
          reducedCoefficientBackground (fun _ _ ↦ 0)) ⊆ closedBall 0 (r + p.width / 2) ∧
      HasDerivativeProfile (closedBall 0 r) (geometricReducedCoefficients F) r₀
        (currentCoefficientScale R₀ j) A ∧
      HasDerivativeProfile univ (extendedReducedCoefficients p (fun _ _ ↦ 0) F) r₀
        (currentCoefficientScale R₀ j) E := by
  have h8 : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    have hs : (8 : ℝ) ≤ rStar := by exact_mod_cast hStar
    exact lt_of_le_of_lt (by
      have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
      nlinarith) horder
  obtain ⟨δ, hδ, _, _, C, hC, hcoeff⟩ :=
    exists_reference_reduced_coefficient_estimates G hr hrR hR
  obtain ⟨Sr, hSr, hnear⟩ :=
    HistoryGeometry.exists_initialScale_for_c8_neighborhood G.map R h8 hδ
  obtain ⟨Sg, hSg, _, _, _, _, hgeom⟩ :=
    HistoryGeometry.exists_geometric_neighborhood G hr hrR hR h8 (by norm_num : (0 : ℝ) < 1)
  obtain ⟨A, hA, hprofile⟩ := exists_admissible_history_profile G.map G.contDiff
    (isCompact_closedBall (0 : Euclidean n) R) rStar kMin horder
  choose D hD hext using exists_global_extendedReducedCoefficients_bound
    (N := embeddingDimension n) p
  let B := fun m ↦ C m * (1 + A (m + 2))
  have hB (m) : 0 ≤ B m := mul_nonneg (hC m).le (by linarith [hA (m + 2)])
  refine ⟨max Sr Sg, hSr.trans (le_max_left _ _), B, (fun m ↦ D m * (1 + B m)), hB,
    (fun m ↦ mul_nonneg (hD m).le (by linarith [hB m])), ?_⟩
  intro R₀ hR₀ j u ell hu
  have hRR := (le_max_left Sr Sg).trans hR₀
  have hRG := (le_max_right Sr Sg).trans hR₀
  have hscale := one_le_currentCoefficientScale (by linarith [hSr.trans hRR]) j
  let F := finiteHistoryMap G.map u
  have hF : ContDiff ℝ ∞ F := hu.contDiff_finiteHistoryMap G.contDiff
  obtain ⟨hi, hrank, _⟩ := hgeom R₀ hRG j u ell hu
  obtain ⟨_, _, hc⟩ := hcoeff F hF (hnear R₀ hRR j u ell hu)
  have hp := hprofile R₀ (hSr.trans hRR) j u ell hu _ Subset.rfl
  have hpU : closedBall p.center p.radius ⊆ ball (0 : Euclidean n) R := by
    simpa only [hpcenter, hpradius] using closedBall_subset_ball hrR
  have hraw : HasDerivativeProfile (closedBall 0 r) (geometricReducedCoefficients F) r₀
      (currentCoefficientScale R₀ j) B := fun m ↦
    JointBudget.fixed_profile_transfer_bound hscale (hA (m + 2)) (hC m).le hreserve
      (hp (m + 2)) (hc m)
  refine ⟨contDiff_extendedReducedCoefficients p _ contDiff_const hF isOpen_ball hi hrank hpU,
    ?_, ?_, hraw, ?_⟩
  · simpa only [hpcenter, hpradius] using extendedReducedCoefficients_eqOn p (fun _ _ ↦ 0) F
  · simpa only [hpcenter, hpradius] using tsupport_extendedReducedCoefficients_sub p (fun _ _ ↦ 0) F
  · intro m
    have he := hext m F hF (ball 0 R) isOpen_ball hpU hi hrank
    simp only [hpcenter, hpradius] at he
    exact JointBudget.fixed_profile_transfer_bound (c := 0) (R := r₀)
      hscale (hB m) (hD m).le (by omega) (by simpa using hraw m) he

end JanetCartan.CurrentCoefficientProfiles
