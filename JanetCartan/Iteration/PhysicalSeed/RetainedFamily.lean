module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.RetainedCover.History
public import JanetCartan.Iteration.PhysicalSeed.GenericLeading
public meta import JanetCartan.Iteration.PhysicalSeed.Templates

/-!
# First retention point for the actual generic leading family

Replay the genuine finite selection exactly once, before its arbitrary-map
callback is specialized to the legacy history. The latter is retained solely
as an existing source/empty-history construction tool; physical histories use
the unrestricted callback instead (`app:ch_waves:thm:leading`).
-/

set_option warningAsError true
set_option maxRecDepth 4000
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalSeed
open CurrentCoefficientProfiles
open NullTransport ActualFlow ActualCarriers FrozenMenu CurrentFullPhase FlowAmplitude
open ProjectedStressFrame AmbientResponse ResponseTransfer
open LeadingWave LeadingWave.FullModulation LeadingWave.FullModulation.CarrierCompatibility
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.LeadingPrimitive
open FullPhaseCharts.ActualComparison

/-- Strengthen the actual first discard point without changing any cell or row.
All geometric and scalar budgets precede the arbitrary smooth current map. -/
theorem exists_retained_family_with_generic_leading {n : ℕ} (hn : 5 ≤ n)
    {I : Type*} [Fintype I] (G₀ : FlatReference n) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < G₀.domain.chartRadius)
    (P : I → Patch n) {c₀ C₁ : ℝ} (hP : ∀ i, (P i).IsValid c₀ C₁)
    (family : (i : I) → PatchQuantitativeFamily (P i) (ball 0 R) isOpen_ball)
    (hball : ∀ i, closedBall (0 : Euclidean n)
      (family i).data.localReference.stateRadius ⊆ closedBall 0 r) :
    retain_physical_seed%
      (CurrentCoefficientProfiles.exists_source_scale_cap_for_history_retained_full_modulation_with_source_geometry
        hn G₀ hr hrR hR P hP family hball)
      before cap retaining
      (∃ η : I → ℝ, (∀ i, 0 < η i) ∧ ∀ i,
        GenericLeading (family i) (K := closedBall (0 : Euclidean n) r)
          (η i) (centers i) (row i) (col i) (ρ i) (L i) (τ i)
          (Rc i) (τc i) (Mc i) (rcomp i) (δcomp i) (σcover i)
          (Ωc i) (ρc i) (Bc i) (gc i) (Bfull i)) := by
  classical
  have hK : IsCompact (closedBall (0 : Euclidean n) r) := isCompact_closedBall _ _
  have hKU : closedBall (0 : Euclidean n) r ⊆ ball 0 R := closedBall_subset_ball hrR
  choose η ε hη hε centers row col ρ L τ Rc τc Mc rcomp δcomp σcover
    hrc hpositive Ωc ρc Bc gc μc Bfull hsource hfull hgeometryc hworking εcarrier ρdet hcell hcarrierCover
    V hV hgraph hcover hproduce using
    fun i ↦ exists_finite_retained_leading_family_before_geometry_with_source_geometry hn (hP i)
      (family i) hK hKU (hball i)
  obtain ⟨_, d, _, _, _, hd, _, hcommon⟩ := exists_common_phase_buffers
    (fun _ : I ↦ (1 : ℝ)) η (fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_lt_one) hη
  have heps : 0 < d / (2 * (6 + 1 : ℝ)) := by positivity
  obtain ⟨cap, hcap, hcap₁, hsmall⟩ :=
    FixedReferenceProfiles.exists_source_scale_interval_projectedStress_lt G₀ hK (half_pos heps)
  refine ⟨ε, hε, centers, row, col, ρ, L, τ, Rc, τc, Mc, rcomp, δcomp, σcover,
    hrc, hpositive, Ωc, ρc, Bc, gc, μc, Bfull, hsource, hfull,
    hgeometryc, hworking, εcarrier, ρdet, hcell, hcarrierCover,
    V, (fun i ↦ ⟨hV i, hgraph i, hcover i⟩), ⟨η, hη, hproduce⟩, cap, hcap, hcap₁, ?_⟩
  intro σ hσ hσcap Gfixed hmap rStar r₀ kMin hStar hreserve horder Mᵣ m₀ hMᵣ hm₀
  rw [hmap]
  let G := sourceDilationReference G₀ hσ (hσcap.trans hcap₁)
  have h14 : displacementLoss n + bandExponent * (14 + (n : ℝ) / 2) + 2 < kMin := by
    have hs : (14 : ℝ) ≤ rStar := by exact_mod_cast hStar
    have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
    exact lt_of_le_of_lt (by nlinarith) horder
  have h8 : displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin := by
    have hb : 0 ≤ bandExponent := by norm_num [bandExponent]
    exact lt_of_le_of_lt (by nlinarith) h14
  obtain ⟨Sg, hSg, C₀, _, κ, hκ, hgeom⟩ :=
    HistoryGeometry.exists_cube_frame_neighborhood G hr hrR hR h8 heps (hsmall σ hσ hσcap)
  obtain ⟨St, hSt, hbudget⟩ := HistoryGeometry.exists_initialScale_for_fixed_immersion_bound
    14 G.map G.contDiff (closedBall 0 r) hK h14
  obtain ⟨Amap, hAmap, hprofile⟩ := exists_admissible_history_profile G.map G.contDiff hK
    rStar kMin horder
  choose c E A H B hc hE hactual using fun i ↦ hproduce i
    (cNorm (closedBall 0 r) 14 G.map + 1) Mᵣ (1 / 4) κ m₀
    (by linarith [cNorm_nonneg (closedBall 0 r) 14 G.map]) hMᵣ (by norm_num) hκ hm₀
  refine ⟨max Sg St, hSg.trans (le_max_left _ _), κ, hκ, c, Amap, E, A, H, B,
    hc, hAmap, hE, ?_⟩
  intro R₀ hR₀ stage u ell hu
  have hRg := (le_max_left Sg St).trans hR₀
  have hRt := (le_max_right Sg St).trans hR₀
  have hRtwo : 2 ≤ R₀ := hSg.trans hRg
  have hscale := one_le_currentCoefficientScale (show 1 ≤ R₀ by linarith) stage
  let F := finiteHistoryMap G.map u
  have hF : ContDiffOn ℝ ∞ F (ball 0 R) :=
    (hu.contDiff_finiteHistoryMap G.contDiff).contDiffOn
  obtain ⟨hi, hrank, _, hmet, hnormal, hQ, hclose⟩ := hgeom R₀ hRg stage u ell hu
  have hframe : ContDiffOn ℝ ∞ (projectedStress F) (ball 0 R) := contDiffOn_pi.mpr hQ
  have hframeK : cNorm (closedBall 0 r) 6
      (projectedStress F - fun _ ↦ cubeStress n) < d :=
    frame_cNorm_lt_of_componentwise hK
      (fun x hx ↦ ((hframe.contDiffAt (isOpen_ball.mem_nhds (hKU hx))).sub
        contDiffAt_const).of_le (by simp)) hd hclose
  have hlowF := hbudget R₀ hRt stage u ell hu
  have hp := hprofile R₀ hRtwo stage u ell hu (closedBall 0 r) (Subset.refl _)
  choose hlow hspec using fun i ↦ hactual i F hF hi hrank hlowF
    (fun x hx ↦ hmet x (hKU hx)) (fun x hx ↦ hnormal x (hKU hx))
    (hframeK.trans_le (hcommon i).2.1)
  refine ⟨hF, hi, hrank, hlowF, hmet, hnormal, hp, hlow, ?_⟩
  intro i
  dsimp only
  intro j
  obtain ⟨hdom, hx, hdirLow, Dc, φ, y, hcarrierData, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, hsolution⟩ := hspec i j
  refine ⟨hdom, hx, hdirLow, Dc, φ, y, hcarrierData, hDc, hcoverc, hbigc, hφDc, hyL, hφ₀, hyφ, hφy,
    hvelocityc, hφbuffer, hflowcLow, D, Φ, Y, hD, hcover, hbig, hphys, hballD, hphaseInitial,
    hΦ, hY, hΦD, hYL, hΦ₀, hYΦ, hΦY, hΦz, hYz, hvelocity,
    hΦbuffer, hYbuffer, hflow, hgaps, hcoeff, hcompat, ?_⟩
  intro initial hsmooth hlowInitial hpos
  obtain ⟨hα, hb₀, hinit, hpositive, hpde, hsymbol, hreduce, habound, hidentity, hjoint⟩ :=
    hsolution initial hsmooth hlowInitial hpos
  have hmapBound (m d : ℕ) (hd : d + r₀ ≤ rStar) :
      1 + cNorm (closedBall 0 r) (m + d) F ≤
        (1 + Amap (m + d)) * currentCoefficientScale R₀ stage ^ (m - r₀) := by
    simpa only [one_mul] using JointBudget.fixed_profile_transfer_bound hscale
      (hAmap (m + d)) (by norm_num : (0 : ℝ) ≤ 1) hd (hp (m + d))
      (le_refl (1 * (1 + cNorm (closedBall 0 r) (m + d) F)))
  refine ⟨hα, hb₀, hinit, hpositive, hpde, hsymbol, hreduce, ?_, hidentity, ?_⟩
  · intro m
    refine ⟨habound m, ?_⟩
    have habs := (habound m).trans (mul_le_mul_of_nonneg_right (le_abs_self (B i j m))
      (by linarith [cNorm_nonneg (closedBall (0 : Euclidean n) r) (m + 13) F,
        (cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), j.1.1) (L i j / 8))
          (m + 13) initial)]))
    exact habs.trans (mul_le_mul_of_nonneg_left
      (add_le_add (hmapBound m 13 (by omega)) le_rfl) (abs_nonneg _))
  · intro m
    have hmixed := (hjoint m).trans (mul_le_mul_of_nonneg_left
      (add_le_add (hmapBound m 14 hreserve) le_rfl) (hE i m).le)
    refine ⟨hjoint m, hmixed, ?_⟩
    have hinitBound := mul_le_mul_of_nonneg_left (one_le_pow₀ hscale (n := m - r₀))
      (cNorm_nonneg (closedBall ((0 : Euclidean (n - 1)), j.1.1) (L i j / 8))
        (m + 14) initial)
    have hh := hmixed.trans (mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (by simpa only [mul_one] using hinitBound)) (hE i m).le)
    simpa only [← add_mul, mul_assoc, F, G, sourceDilationReference] using hh

end JanetCartan.PhysicalSeed
