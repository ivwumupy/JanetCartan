module

public import JanetCartan.Iteration.PhysicalSmoothing.Profiles

/-!
# Actual same-history physical smoothing and revised normalized source

`main:lem:smoothing` in `paper-v2.tex` is instantiated on the actual physical
Schwartz prefix and the original normalized local target. One support carrier
and one target interval precede the finite accuracy, all histories and the
finally chosen target dilation. Both tails and all source norms are proved for
the SAME finite-moment output. No periodic representative or legacy forcing
exponent occurs in this handoff to the revised primary/mean/stage construction.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalSmoothing

open BallSmoothing LocalSobolev

private theorem normalized_power_le_source_profile (n r : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    R ^ ((r : ℝ) - 2 * RevisedScales.forcingExponent n) ≤
      R ^ (-separationExponent) * R ^ (r - RevisedScales.sourceOrder n) := by
  have hRp : 0 < R := zero_lt_one.trans_le hR
  rw [← Real.rpow_natCast R (r - RevisedScales.sourceOrder n), ← Real.rpow_add hRp]
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hr : (r : ℝ) ≤ (RevisedScales.sourceOrder n : ℝ) +
      ((r - RevisedScales.sourceOrder n : ℕ) : ℝ) := by
    exact_mod_cast (show r ≤ RevisedScales.sourceOrder n + (r - RevisedScales.sourceOrder n) by omega)
  have hgap := (RevisedScales.source_order_and_forcing_gap n).2.2.1
  have hβ : separationExponent < 1 := by norm_num [separationExponent]
  linarith

/-- `main:lem:smoothing`, `main:eq:smoothing-low`, and the normalized source in
`app:prop:ordered-scale-selection`, for the actual original target and physical
history. The fixed support and target interval precede the order `m`. Only the
current metric-defect budget is assumed; all smoothness, physical Sobolev norms,
symmetry and the two independent approximation tails are constructed. -/
theorem exists_original_target_history_smoothing {n : ℕ}
    (D : LocalDomain) (G : FlatReference n) {ρ : ℝ} (hρ : 0 < ρ)
    {g : MetricField n} {U : Set (Euclidean n)} (hU : IsOpen U)
    (h0 : (0 : Euclidean n) ∈ U) (hg : IsRiemannianMetricOn g U) (hg0 : g 0 = 1)
    {B : ℝ} (hB : 1 ≤ B) {kMin : ℕ}
    (horder : RevisedScales.displacementLoss n + bandExponent * (1 + (n : ℝ) / 2) + 2 < kMin) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 ∧
      (∀ s ∈ Icc (0 : ℝ) s₀, ∀ x ∈ D.closureChart n, (s * ρ) • x ∈ U) ∧
      ∃ K : Set (Euclidean n), IsCompact K ∧ K ⊆ D.chart n ∧
        ∀ m : ℕ, 1 ≤ m → ∃ (Rmin : ℝ) (L Ln : ℕ → ℝ) (Cs Ch : ℝ),
          2 ≤ Rmin ∧ (2 : ℝ) * m ≤ Rmin ∧
          (∀ r, 0 ≤ L r) ∧ (∀ r, 0 ≤ Ln r) ∧ 0 ≤ Cs ∧ 0 ≤ Ch ∧
          ∀ s ∈ Icc (0 : ℝ) s₀, ∀ R₀ : ℝ, 2 ≤ R₀ →
            ∀ (j : ℕ) (u : Fin j → SchwartzMap (Euclidean n) (Euclidean (embeddingDimension n)))
              (ell : Fin j → ℕ), RevisedGlobal.IsAdmissibleHistory B R₀ kMin u ell →
            let R := iterationScale R₀ growthExponent j
            Rmin ≤ R → ∀ δ : ℝ, 0 < δ →
            cNorm (D.core n) 0
              (inducedMetric (RevisedGlobal.finiteMap G.map u) - scaledMetric g (s * ρ)) ≤ δ ^ 2 →
            let gs := scaledMetric g (s * ρ)
            let e := historyDefect gs G.map u
            let eR := smoothedDefect D R m gs G.map u
            let source := normalizedSource D R m δ gs G.map u
            ContDiff ℝ ∞ eR ∧ tsupport eR ⊆ K ∧ HasCompactSupport eR ∧
            (∀ x, (eR x).IsSymm) ∧
            (∀ r, MemLp (iteratedFDeriv ℝ r eR) 2 volume) ∧
            (∀ r, cNorm univ r eR + cartesianJetNorm univ r
              (fun a ↦ iteratedFDeriv ℝ a eR) ≤ L r * δ ^ 2 * R ^ r) ∧
            (∀ x ∈ D.core n, ‖eR x - e x‖ ≤ Cs * δ ^ 2) ∧
            (∀ x ∈ D.core n, ‖eR x - e x‖ ≤ Ch * (R ^ coefficientExponent / R) ^ m) ∧
            ContDiff ℝ ∞ source ∧ tsupport source ⊆ K ∧ HasCompactSupport source ∧
            (∀ x, (source x).IsSymm) ∧
            (∀ r, MemLp (iteratedFDeriv ℝ r source) 2 volume) ∧
            (∀ r, cNorm univ r source + cartesianJetNorm univ r
              (fun a ↦ iteratedFDeriv ℝ a source) ≤
                Ln r * R ^ ((r : ℝ) - 2 * RevisedScales.forcingExponent n)) ∧
            (cNorm univ (RevisedScales.sourceOrder n) source +
              cartesianJetNorm univ (RevisedScales.sourceOrder n)
                (fun a ↦ iteratedFDeriv ℝ a source) ≤
                  Ln (RevisedScales.sourceOrder n) * R ^ (-1 : ℝ)) ∧
            (cNorm univ (RevisedScales.sourceOrder n) source +
              cartesianJetNorm univ (RevisedScales.sourceOrder n)
                (fun a ↦ iteratedFDeriv ℝ a source) ≤
                  Ln (RevisedScales.sourceOrder n) * R ^ (-separationExponent)) ∧
            (∀ r, cNorm univ r source + cartesianJetNorm univ r
              (fun a ↦ iteratedFDeriv ℝ a source) ≤
                Ln r * R ^ (-separationExponent) * R ^ (r - RevisedScales.sourceOrder n)) := by
  obtain ⟨s₀, hs₀, hs₁, hmaps, P, hP, hprofile⟩ :=
    exists_historyDefect_derivative_profile D G hρ hU h0 hg.1 hg0 hB horder
  obtain ⟨K, Rgeom, hK, hKD, hRg, hsupp⟩ :=
    exists_affineSmoothing_fixed_support (F := MetricTensor n) (0 : Euclidean n)
      D.coreRadius_pos isOpen_ball (closedBall_subset_ball D.coreRadius_lt_chartRadius)
  refine ⟨s₀, hs₀, hs₁, hmaps, K, hK, hKD, ?_⟩
  intro m hm
  obtain ⟨_, Rcut, L, Cs, Ch, _, _, hRc, hRm, hL, hCs, hCh, hraw⟩ :=
    DefectSmoothing.exists_finiteMoment_source_bounds D m hm P hP
  obtain ⟨_, Rnorm, Ln, _, _, _, hRmn, hLn, _, hnormalized⟩ :=
    DefectSmoothing.exists_revisedFiniteMomentSource_bounds (n := n) D m hm
  let Rmin := max 2 (max Rgeom (max Rcut Rnorm))
  refine ⟨Rmin, L, Ln, Cs, Ch, le_max_left _ _,
    hRm.trans ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
    hL, hLn, hCs, hCh, ?_⟩
  intro s hs R₀ hR₀ j u ell hu R hR δ hδ hsmall gs e eR source
  have hRgeom : Rgeom ≤ R :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRcut : Rcut ≤ R :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hRnorm : Rnorm ≤ R :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hRone : 1 ≤ R := hRc.trans hRcut
  have hRorder : (2 : ℝ) * m ≤ R := hRm.trans hRcut
  have htarget : ContDiffOn ℝ ∞ gs (D.chart n) :=
    hg.1.comp (contDiff_id.const_smul (s * ρ)).contDiffOn
      (fun x hx ↦ hmaps s hs x (ball_subset_closedBall hx))
  have he : ContDiffOn ℝ ∞ e (D.chart n) := contDiffOn_historyDefect htarget G.contDiff u
  have hecore : ContinuousOn e (D.core n) :=
    he.continuousOn.mono (closedBall_subset_ball D.coreRadius_lt_chartRadius)
  have hesym (x : Euclidean n) (hx : x ∈ D.core n) : (e x).IsSymm :=
    historyDefect_isSymm (g := gs) (x := x) ((hg.2 _ (hmaps s hs x
      (closedBall_subset_closedBall D.coreRadius_lt_chartRadius.le hx))).isHermitian.isSymm) G.map u
  have hsmall' : cNorm (D.core n) 0 e ≤ δ ^ 2 := by
    change cNorm (D.core n) 0
      (scaledMetric g (s * ρ) - inducedMetric (RevisedGlobal.finiteMap G.map u)) ≤ _
    rw [← neg_sub (inducedMetric (RevisedGlobal.finiteMap G.map u)) (scaledMetric g (s * ρ)), cNorm_neg]
    exact hsmall
  have hT : 1 ≤ R ^ coefficientExponent :=
    Real.one_le_rpow hRone (by norm_num [coefficientExponent])
  obtain ⟨heR, _, hmem, hlow, hsmallTail, hhighTail⟩ :=
    hraw R hRcut e he (R ^ coefficientExponent) δ hT
      (hprofile s hs R₀ hR₀ j u ell hu) hsmall'
  have heRsupp : tsupport eR ⊆ K := hsupp R hRgeom m e
  have heRcompact : HasCompactSupport eR := hK.of_isClosed_subset (isClosed_tsupport _) heRsupp
  have hsourceSupp : tsupport source ⊆ K :=
    (tsupport_smul_subset_right
      (fun _ : Euclidean n ↦ ((δ * R ^ RevisedScales.forcingExponent n) ^ 2)⁻¹) eR).trans heRsupp
  obtain ⟨hsource, _, hsourceCompact, hsourceSym, hsourceMem, hsourceProfile, hsourceLow, hsourceSmall⟩ :=
    hnormalized R hRnorm e he δ hδ hsmall'
  have hpoint (x : Euclidean n) (hx : x ∈ D.core n) :
      ‖eR x - e x‖ ≤ cNorm (D.core n) 0 (e - eR) := by
    rw [norm_sub_rev]
    simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using
      norm_iteratedFDeriv_le_cNorm_of_contDiffAt (s := D.core n) (r := 0) (j := 0)
        (f := e - eR) (isCompact_closedBall _ _)
        (fun y hy ↦ ((he.contDiffAt (isOpen_ball.mem_nhds
          (closedBall_subset_ball D.coreRadius_lt_chartRadius hy))).sub heR.contDiffAt).of_le (by simp))
        hx le_rfl
  refine ⟨heR, heRsupp, heRcompact, DefectSmoothing.finiteMomentTensor_isSymm D hm hRorder hecore hesym,
    hmem, hlow, fun x hx ↦ (hpoint x hx).trans hsmallTail,
    fun x hx ↦ (hpoint x hx).trans hhighTail, hsource, hsourceSupp, hsourceCompact,
    hsourceSym hesym, hsourceMem, hsourceProfile, hsourceLow, hsourceSmall, ?_⟩
  intro r
  rw [mul_assoc]
  exact (hsourceProfile r).trans
    (mul_le_mul_of_nonneg_left (normalized_power_le_source_profile n r hRone) (hLn r))

end JanetCartan.PhysicalSmoothing
