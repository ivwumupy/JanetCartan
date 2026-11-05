module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryAdmission

/-!
# A coefficient cap fixed before the common reference

The original history-admission producer chooses its reference tolerance before
the reference. Requesting a C6 error at most one also supplies one numerical C4
coefficient cap, independent of that reference and every compact set. This cap
pays for the low phase jets used to select stationary radii in
`app:ch_response:eq:direct-envelope-profile`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.FullSourceStationary
open ResponseTransfer.RetainedFactors ProtectedFlow GeometricProfile CurrentCoefficientProfiles
open ProjectedStressFrame

/-- The order-four coefficient cap depends only on the fixed cube frame,
before the common reference, histories, source masks and operators
(`app:ch_response:eq:direct-envelope-profile`). -/
def stationaryCoefficientCap (n : ℕ) : ℝ := 1 + ‖cubeStress n‖

/-- Positivity of the fixed low coefficient cap used to choose the stationary
interval (`app:ch_response:eq:direct-envelope-profile`). -/
theorem stationaryCoefficientCap_pos (n : ℕ) : 0 < stationaryCoefficientCap n := by
  dsimp [stationaryCoefficientCap]
  positivity

private theorem cNorm_constant_le {n : ℕ} (K : Set (Euclidean n)) (m : ℕ)
    (v : Fin n → MetricTensor n) : cNorm K m (fun _ ↦ v) ≤ ‖v‖ := by
  induction m with
  | zero =>
    rw [cNorm_order_zero]
    exact Real.sSup_le (by rintro _ ⟨x, _, rfl⟩; exact le_rfl) (norm_nonneg _)
  | succ m ih =>
    rw [cNorm_succ]
    have hz : sSup ((fun x : Euclidean n ↦
        ‖iteratedFDeriv ℝ (m + 1) (fun _ : Euclidean n ↦ v) x‖) '' K) ≤ 0 := by
      apply Real.sSup_le _ le_rfl
      rintro _ ⟨x, _, rfl⟩
      simp [iteratedFDeriv_succ_const]
    linarith

/-- The actual C6 cube-frame admission with error at most one bounds the
coefficient C4 norm by a constant chosen before the reference. This is the
elementary input to both source and joint low phase budgets
(`app:ch_seed:setup:seed-current`, `app:ch_response:eq:direct-envelope-profile`). -/
theorem cNorm_four_le_stationaryCoefficientCap {n : ℕ}
    {Q : Euclidean n → Fin n → MetricTensor n} {K : Set (Euclidean n)}
    (hK : IsCompact K) (hQ : ∀ x ∈ K, ContDiffAt ℝ 4 Q x)
    (hclose : cNorm K 6 (Q - fun _ ↦ cubeStress n) ≤ 1) :
    cNorm K 4 Q ≤ stationaryCoefficientCap n := by
  have hh := cNorm_add_le_of_contDiffAt
    (f := Q - fun _ ↦ cubeStress n) (g := fun _ ↦ cubeStress n) hK
    (fun x hx ↦ (hQ x hx).sub contDiffAt_const) (fun _ _ ↦ contDiffAt_const)
  rw [sub_add_cancel] at hh
  exact hh.trans (add_le_add
    ((cNorm_mono_order (by omega : 4 ≤ 6)).trans hclose) (cNorm_constant_le K 4 _))

/-- The original admission producer supplies the SAME later reference's
actual extended history field, its original range and C6 tolerance, and the
fixed stationary C4 cap on every compact set. The tolerance is chosen BEFORE
`G`; the parent must invoke its common initializer at that tolerance. No
reference is selected or identified here
(`app:ch_regular:eq:coefficient-extension`,
`app:ch_response:eq:direct-envelope-profile`). -/
theorem exists_reference_tolerance_for_stationary_coefficient_cap {n : ℕ}
    (ext : BallExtension.Parameters (Euclidean n)) {r : ℝ}
    (hextcenter : ext.center = 0) (hextradius : ext.radius = r)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ η > (0 : ℝ), ∀ G : FlatReference n, ∀ R : ℝ,
      0 < r → r < R → R < G.domain.chartRadius →
      (∀ i, cNorm (closedBall (0 : Euclidean n) r) 6
        (fun x ↦ projectedStress G.map x i - cubeStress n i) < η) →
      ∀ kMin : ℕ,
      displacementLoss n + bandExponent * (8 + (n : ℝ) / 2) + 2 < kMin →
      ∃ S : ℝ, 2 ≤ S ∧ ∀ R₀, S ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus n → Euclidean (embeddingDimension n))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      let Q := extendedProjectedStress ext (finiteHistoryMap G.map u)
      ContDiff ℝ ∞ Q ∧ MapsTo Q univ (closedBall (cubeStress n) ε) ∧
      (∀ K : Set (Euclidean n), cNorm K 6 (Q - fun _ ↦ cubeStress n) < δ) ∧
      ∀ K : Set (Euclidean n), IsCompact K → cNorm K 4 Q ≤ stationaryCoefficientCap n := by
  obtain ⟨η, hη, hadmit⟩ := exists_reference_tolerance_for_retained_history_admission
    ext hextcenter hextradius hε (lt_min hδ zero_lt_one)
  refine ⟨η, hη, ?_⟩
  intro G R hr hrR hR href kMin horder
  obtain ⟨S, hS, hh⟩ := hadmit G R hr hrR hR href kMin horder
  refine ⟨S, hS, ?_⟩
  intro R₀ hR₀ s u ell hu Q
  obtain ⟨hQ, hrange, hclose⟩ := hh R₀ hR₀ s u ell hu
  refine ⟨hQ, hrange, fun K ↦ (hclose K).trans_le (min_le_left _ _), ?_⟩
  intro K hK
  exact cNorm_four_le_stationaryCoefficientCap hK
    (fun _ _ ↦ hQ.contDiffAt.of_le (by simp))
    ((hclose K).le.trans (min_le_right _ _))

end JanetCartan.FullSourceStationary
