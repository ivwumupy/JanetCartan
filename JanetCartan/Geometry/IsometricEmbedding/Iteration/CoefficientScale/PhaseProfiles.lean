module

public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.GeometricProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.SharpPhaseBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.Initialization.ScaledReference

/-!
# Constructed Hamilton phase profiles for the source-scaled history

For `main:prop:current-scale`, choose the finite Hamilton family first and then
choose one source dilation satisfying its frame threshold. The actual history
geometry and sharp immersion-order `m+3` phase estimate give the paper profile
for every member of that same family. No current frame, phase or high-norm
estimate is assumed. Quotient inverses and transport remain separate obligations.
-/

@[expose] public noncomputable section

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.NormalRankStability

namespace JanetCartan.CurrentCoefficientProfiles

open ActualCarriers CurrentFullPhase FrozenMenu ProjectedStressFrame HamiltonPhase

/-- The Hamilton phase part of `app:eq:uniform-high-coeff` for the actual
source-scaled reference and all its admissible prefixes. The finite family,
source scale, physical domains and initial-scale threshold precede the stage,
history, all high derivatives and every later accuracy. The sharp derivative
reserve is three. The SAME reference is retained for later geometric, quotient
and transport assembly; its low frame bound is produced, not assumed. -/
theorem exists_scaled_history_geometric_and_phase_profiles {n : ℕ} (hn : 5 ≤ n)
    (G₀ : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G₀.domain.chartRadius)
    {rStar r₀ kMin : ℕ} (hStar : 8 ≤ rStar) (hreserve : 3 + r₀ ≤ rStar)
    (horder : displacementLoss n + bandExponent * ((rStar : ℝ) + (n : ℝ) / 2) + 2 < kMin) :
    ∃ (D : CoverData n) (c C : ℝ), D.IsValid c C ∧
      ∃ family : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
          PatchQuantitativeFamily (D.patches i.1 i.2) (ball 0 R) isOpen_ball,
        (∀ i, closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius ⊆
          closedBall 0 r) ∧
      ∃ (σ : ℝ) (hσ : 0 < σ) (hσ₁ : σ ≤ 1),
      let G := sourceDilationReference G₀ hσ hσ₁
      ∃ S : ℝ, 2 ≤ S ∧ ∃ C₀ > 0, ∃ κ > 0,
      ∃ A B E : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧ (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ E m) ∧
        ∀ R₀, S ≤ R₀ →
        ∀ (j : ℕ) (u : Fin j → Torus n → Euclidean (embeddingDimension n))
          (ell : Fin j → ℕ), IsAdmissibleHistory R₀ kMin u ell →
        let F := finiteHistoryMap G.map u
        ∃ (hF : ContDiffOn ℝ ∞ F (ball 0 R))
          (hi : IsImmersionOn F (ball 0 R)) (hrank : HasFullNormalRankOn F (ball 0 R)),
          cNorm (closedBall 0 r) 4 F ≤ C₀ ∧
          (∀ x ∈ ball 0 R, ∀ v,
            (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) ∧
          (∀ x ∈ ball 0 R, ∀ w ∈ normalSpace F x,
            κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) ∧
          HasDerivativeProfile (closedBall 0 r) F rStar (currentCoefficientScale R₀ j) A ∧
          (∀ m, currentGeometricCoefficientNorm (closedBall 0 r) m F ≤
            E m * currentCoefficientScale R₀ j ^ (m - r₀)) ∧
          ∃ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
              (family i).data.localReference.stateRadius) 6
              (projectedStress F - fun _ ↦ cubeStress n) < (family i).family.threshold,
          ∀ i,
            let T := family i
            let Q := ⟨projectedStress F,
              contDiffOn_pi.mpr (contDiffOn_projectedStress isOpen_ball hF hi hrank), hlow i⟩
            HasDerivativeProfile
              (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
                T.data.adapted.baseData.2) T.family.radius)
              (phase (T.currentChart Q).coordinates) r₀ (currentCoefficientScale R₀ j) B := by
  classical
  have hK : IsCompact (closedBall (0 : Euclidean n) r) := isCompact_closedBall _ _
  have hKU : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  obtain ⟨D, c, C, hD, family, hphysical, rc, Kc, εmax, hrc, hrcb, hKc,
    hεmax, hεmax1, hεmaxc, hradius, hproduce⟩ :=
    exists_constructed_carrier_phases hn isOpen_ball hr hKU
  have hball (i) : closedBall (0 : Euclidean n) (family i).data.localReference.stateRadius ⊆
      closedBall 0 r :=
    (frameBall_subset_of_stateDomain (family i).data.localReference (hphysical i)).trans
      ball_subset_closedBall
  obtain ⟨δ, hδ, hinputs⟩ := hproduce εmax hεmax le_rfl
  obtain ⟨σ, hσ, hσ₁, V, hV, hKV, _, _, _, _, hreference, _⟩ :=
    exists_source_scale_projectedStress_lt G₀ hK (half_pos hδ)
  let G := sourceDilationReference G₀ hσ hσ₁
  have h8 : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    have hs : (8 : ℝ) ≤ rStar := by exact_mod_cast hStar
    exact lt_of_le_of_lt (by
      have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
      nlinarith) horder
  obtain ⟨S, hS, C₀, hC₀, κ, hκ, hgeom⟩ :=
    HistoryGeometry.exists_cube_frame_neighborhood G hr hrR hR h8 hδ hreference
  obtain ⟨Sg, hSg, _, _, _, _, A, E, hA, hE, hgeometric⟩ :=
    exists_admissible_history_geometric_profiles G hr hrR hR
      (r₀ := r₀) hStar (by omega) horder
  choose H hH hbound using fun i ↦ (family i).exists_projected_phase_sharp_bound
    (N := embeddingDimension n) hK hKU (hball i) C₀
      (by norm_num : (0 : ℝ) < 1 / 4) hκ
  let B : ℕ → ℝ := fun m ↦ (1 + ∑ i, H i m) * (1 + A (m + 3))
  have hB (m) : 0 ≤ B m := by
    exact mul_nonneg (add_nonneg zero_le_one (Finset.sum_nonneg fun i _ ↦ (hH i m).le))
      (add_nonneg zero_le_one (hA (m + 3)))
  refine ⟨D, c, C, hD, family, hball, σ, hσ, hσ₁,
    max S Sg, hS.trans (le_max_left _ _), C₀, hC₀, κ, hκ, A, B, E, hA, hB, hE, ?_⟩
  intro R₀ hR₀ j u ell hu
  have hRS := (le_max_left S Sg).trans hR₀
  have hRSg := (le_max_right S Sg).trans hR₀
  let F := finiteHistoryMap G.map u
  have hF : ContDiffOn ℝ ∞ F (ball 0 R) :=
    (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn
  obtain ⟨hi, hrank, hlowF, hmet, hnormal, hQ, hclose⟩ := hgeom R₀ hRS j u ell hu
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) :=
    contDiffOn_pi.mpr hQ
  obtain ⟨hlow, _⟩ := hinputs (projectedStress F) hframe hclose
  obtain ⟨_, _, _, _, _, hp, hcoefficients⟩ := hgeometric R₀ hRSg j u ell hu
  refine ⟨hF, hi, hrank, hlowF, hmet, hnormal, hp, hcoefficients, hlow, ?_⟩
  intro i
  dsimp only
  intro m
  have hb := hbound i F hF hi hrank hlowF (fun x hx ↦ hmet x (hKU hx))
    (fun x hx ↦ hnormal x (hKU hx)) (hlow i) m
  have hh := JointBudget.fixed_profile_transfer_bound
    (one_le_currentCoefficientScale (by linarith [hS.trans hRS]) j)
    (hA (m + 3)) (hH i m).le hreserve (hp (m + 3)) hb
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _
    (pow_nonneg (zero_le_one.trans (one_le_currentCoefficientScale
      (by linarith [hS.trans hRS]) j)) _)
  apply mul_le_mul_of_nonneg_right _ (add_nonneg zero_le_one (hA (m + 3)))
  have hsum := Finset.single_le_sum (s := Finset.univ) (f := fun k ↦ H k m)
    (fun k _ ↦ (hH k m).le) (Finset.mem_univ i)
  linarith

end JanetCartan.CurrentCoefficientProfiles
