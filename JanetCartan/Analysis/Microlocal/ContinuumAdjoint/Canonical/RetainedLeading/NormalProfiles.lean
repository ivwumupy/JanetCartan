module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.LeadingPrimitive.NormalBounds

/-!
# Profiles of the retained complete normal

The full leading producer bounds its complete normal with reserve fourteen.
`LeadingPrimitive.exists_normalField_pullback_bounds` transfers that bound to
the SAME carrier normal on a fixed chart. Cut it off there and interpolate
its actual component norms. In the scalar endpoint the initial and flow
multipliers can both be one: the original initial scalar remains in the
complete normal and in its original norm domain. The literal carrier data
are unchanged, as the kernel agreement below proves.

Consumer: the uniform scalar endpoint for `app:ch_background:prop:bg-adjoint`;
source estimate: `app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumAdjoint.Canonical.RetainedLeading
open ContinuumRow PhaseExtension AmplitudeProfiles ActualCarriers FrozenMenu CurrentFullPhase
open DerivativeKernels ProjectedStressFrame

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- Compact extension of the retained normal, including its ORIGINAL scalar.
The same fixed chart bump equals one on the complete original support
(`app:ch_background:eq:bg-T`). -/
def extendedRetainedNormal (F : Euclidean n → Euclidean N) (row col : Fin n)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) {a : ℝ} (ha : 0 < a) (p : CarrierParameter × Euclidean n) : Euclidean N :=
  chartBump z ha (p.2, p.1) • CanonicalCarrier.normalField T Q F row col φ y initial p.2 p.1

/-- The unit-multiplier factorization retains the ORIGINAL scalar inside the
complete normal and gives exactly the literal carrier kernel, on unchanged
masks and measures (`app:ch_background:eq:bg-T`). -/
theorem carrierKernel_extendedRetainedNormal_eq
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
    (initial : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (z : Euclidean 3) {a b : ℝ} (ha : 0 < a) (hcell : 4 * a < 1 / 2)
    (θ₀ : Euclidean (n - 1)) (hb : 0 < b) (high : ℝ → ℝ)
    (Yext : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (hYext : EqOn Yext (CanonicalCarrier.transportPosition T Q) (supportedChart z a)) :
    let d := CanonicalCarrier.data T Q F row col φ y initial ha hcell
      (CanonicalConic.angularMask z θ₀ ha hb) high
    carrierKernel (scalarTransportData d Yext (fun _ ↦ 1) (fun _ ↦ 1)
      (extendedRetainedNormal T Q F row col φ y initial z ha)) = carrierKernel d := by
  apply canonical_scalarTransportData_kernel_eq T Q F row col φ y initial ha hcell
    z θ₀ hb high Yext (fun _ ↦ 1) (fun _ ↦ 1)
    (extendedRetainedNormal T Q F row col φ y initial z ha) hYext
  intro p hp
  have he := (chartBump_eventuallyEq_one z ha hp).eq_of_nhds
  change (1 * 1 : ℝ) • (chartBump z ha p • _) = _
  rw [show chartBump z ha p = 1 from he, one_mul, one_smul, one_smul]

omit Q in
/-- Construct the global component profiles from the actual complete-normal
jet bound transferred by `LeadingPrimitive.exists_normalField_pullback_bounds`.
The derivative reserve is `2*(n+1)+14`, independent of the requested order,
including zero. The original scalar norm set `Kinitial` is unchanged.
The detector estimate is instantiated from primitive immersion data; no
operator or composite-amplitude estimate is assumed (`bg-adjoint`, `joint-tame`). -/
theorem exists_extendedRetainedNormal_profiles {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3))
    (z : Euclidean 3) {ρ σ a : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (ha : 0 < a)
    (haσ : 12 * a ≤ σ)
    (hx : MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hc : closedBall ((0 : Euclidean n), z) ρ ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    (hmap : MapsTo (fun p : Euclidean n × CarrierParameter ↦ (p.1, CanonicalCarrier.parameter p.2))
      (ball (chartCenter z) (2 * σ)) (closedBall ((0 : Euclidean n), z) ρ))
    (E : ℕ → ℝ) (hE : ∀ j, 0 < E j)
    {MF Mr κmet κ : ℝ} (_hMF : 0 ≤ MF) (_hMr : 0 ≤ Mr)
    (hκmet : 0 < κmet) (hκ : 0 < κ) (s : ℕ) :
    ∃ C₀ : Fin n → ℕ → ℝ, (∀ j i, 0 ≤ C₀ j i) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N) (row col : Fin n)
        (φ y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ),
      Q.1 = projectedStress F → ContDiffOn ℝ ∞ F U → IsImmersionOn F U →
      HasFullNormalRankOn F U → cNorm K (2*(n+1)+14) F ≤ MF →
      cNorm Kinitial (2*(n+1)+14) initial ≤ Mr →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖^2 ≤ ‖fderiv ℝ F x v‖^2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x, κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ContDiffOn ℝ ∞ (Function.uncurry (CanonicalCarrier.normalField T Q F row col φ y initial))
        (ball (chartCenter z) (2 * σ)) →
      (∀ j, cNorm (closedBall (chartCenter z) σ) j
        (Function.uncurry (CanonicalCarrier.normalField T Q F row col φ y initial)) ≤
        E j * (1 + cNorm K (j+14) F + cNorm Kinitial (j+14) initial)) →
      let ν := extendedRetainedNormal T Q F row col φ y initial z ha
      ContDiff ℝ ∞ ν ∧
      ∀ (hcell : 4 * a < 1 / 2) (angular : CarrierParameter → Euclidean (n - 1) → ℝ)
        (high : ℝ → ℝ),
      let d := CanonicalCarrier.data T Q F row col φ y initial ha hcell angular high
      (∀ j, ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j)) ∧
      ∀ H : ℝ, 1 + cNorm K (s+2*(n+1)+14) F + cNorm Kinitial (s+2*(n+1)+14) initial ≤ H →
      ∀ j p, ∀ i ≤ s+2*(n+1),
        ‖iteratedFDeriv ℝ i (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j) p‖ ≤
          C₀ j i * H ^ (((i-2*(n+1) : ℕ) : ℝ) / (max s 1 : ℕ)) := by
  let L := closedBall (chartCenter (n := n) z) σ
  let O := ball (chartCenter (n := n) z) (2 * σ)
  have hLO : L ⊆ O := closedBall_subset_ball (by linarith)
  have hsupp : tsupport (chartBump (n := n) z ha) ⊆ L := by
    rw [(chartBump z ha).tsupport_eq]
    exact closedBall_subset_closedBall haσ
  obtain ⟨Bq, hBq, hbq⟩ := exists_geometricDetector_bounds T (N := N) hP z hρ hx hc
    (isCompact_closedBall _ _) (hmap.mono_left hLO) hK hKU hball MF hκmet hκ
  choose D hD hd using fun j ↦ exists_cNorm_geometricPolynomial_le (N := N) z ha hσ
    (E 0 * (1 + MF + Mr)) (Bq 0 * (1 + MF)) j
  let B := fun j m ↦ D j m * (1 + E m + Bq m)
  have hB j m : 0 < B j m := mul_pos (hD j m) (by linarith [hE m, hBq m])
  let b := 2 * (n + 1)
  choose C₀ hC₀ hprofile using fun j ↦ exists_closedBall_reserve_profile (F := ℂ)
    (chartCenter (n := n) z) hσ b s (B j b * (1 + MF + Mr)) (B j (b+s))
  refine ⟨C₀, hC₀, ?_⟩
  intro Q F row col φ y initial hQ hF hi hrank hFM hIM hmet hnormal hν hνB
  let g := Function.uncurry (CanonicalCarrier.normalField T Q F row col φ y initial)
  let q := fun p : Euclidean n × CarrierParameter ↦
    quadratic (Q.1 p.1) (T.carrierGradient Q p.1 (CanonicalCarrier.parameter p.2))
  have hdomain : O ⊆ (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ
      (CanonicalCarrier.parameter ⁻¹' parameterInterior (2 * P.radius)) := by
    intro p hp
    have hm : (p.1, CanonicalCarrier.parameter p.2) ∈ closedBall ((0 : Euclidean n), z) ρ := hmap (x := p) hp
    have hxc : p.1 ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius := hx (x := (p.1, CanonicalCarrier.parameter p.2)) hm
    have hpc := hc hm
    exact ⟨⟨hKU (hball hxc), hpc.1⟩, hpc.2⟩
  have hq : ContDiffOn ℝ ∞ q O :=
    (CanonicalCarrier.quadratic_canonical_smooth T hP Q).mono hdomain
  have hqB := hbq Q F hQ hF hi hrank ((cNorm_mono_order (by omega)).trans hFM) hmet hnormal
  have hg0 : cNorm L 0 g ≤ E 0 * (1 + MF + Mr) :=
    (hνB 0).trans (mul_le_mul_of_nonneg_left
      (add_le_add (add_le_add (le_refl 1) ((cNorm_mono_order (by omega)).trans hFM))
        ((cNorm_mono_order (by omega)).trans hIM)) (hE 0).le)
  have hq0 : cNorm L 0 q ≤ Bq 0 * (1 + MF) :=
    (hqB 0).trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) ((cNorm_mono_order (by omega)).trans hFM)) (hBq 0).le)
  let f : Fin n → (Euclidean n × CarrierParameter) → ℂ := fun j p ↦
    ((FixedCutoffs.physical ha 1) p.1 * ‖chartBump z ha p • g p‖^2 * q p j : ℝ)
  have hext : ContDiff ℝ ∞ (fun p ↦ chartBump z ha p • g p) :=
    Localization.contDiff_of_contDiffOn_support_neighborhood isOpen_ball
      ((chartBump z ha).contDiff.contDiffOn.smul hν)
      ((tsupport_smul_subset_left _ _).trans (hsupp.trans hLO))
  have hfsupp j : tsupport (f j) ⊆ tsupport (chartBump z ha) := by
    apply (isClosed_tsupport _).closure_subset_iff.mpr
    intro p hp
    by_contra hn
    have hz := image_eq_zero_of_notMem_tsupport hn
    exact hp (by simp [f, hz])
  have hf j : ContDiff ℝ ∞ (f j) := by
    apply Localization.contDiff_of_contDiffOn_support_neighborhood isOpen_ball
    · exact Complex.ofRealCLM.contDiff.comp_contDiffOn
        ((((FixedCutoffs.physical ha 1).contDiff.comp contDiff_fst).contDiffOn.mul
          (hext.norm_sq ℝ).contDiffOn).mul (contDiffOn_pi.mp (PiLp.contDiff_ofLp.comp_contDiffOn hq) j))
    · exact (hfsupp j).trans (hsupp.trans hLO)
  have hb j m : cNorm L m (f j) ≤
      B j m * (1 + cNorm K (m+14) F + cNorm Kinitial (m+14) initial) := by
    have hh := hd j O isOpen_ball hLO g q hν hq hg0 hq0 m
    have hqh : cNorm L m q ≤ Bq m *
        (1 + cNorm K (m+14) F + cNorm Kinitial (m+14) initial) :=
      (hqB m).trans (mul_le_mul_of_nonneg_left
        (by linarith [cNorm_mono_order (s := K) (f := F) (by omega : m+4 ≤ m+14),
          cNorm_nonneg Kinitial (m+14) initial]) (hBq m).le)
    apply hh.trans
    dsimp [B]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (hD j m).le
    have hg := hνB m
    nlinarith [cNorm_nonneg K (m+14) F, cNorm_nonneg Kinitial (m+14) initial]
  refine ⟨hext.comp (contDiff_snd.prodMk contDiff_fst), ?_⟩
  intro hcell angular high
  dsimp only
  have he j : carrierChartGeometryComponent
      (CanonicalCarrier.data T Q F row col φ y initial ha hcell angular high)
      (FixedCutoffs.physical ha 1) (extendedRetainedNormal T Q F row col φ y initial z ha) j =
      fun p ↦ f j (p.2, p.1) := by
    funext p
    simp only [carrierChartGeometryComponent, CanonicalCarrier.reducedCovector_data]
    rfl
  refine ⟨fun j ↦ by rw [he]; exact (hf j).comp (contDiff_snd.prodMk contDiff_fst), ?_⟩
  intro H hH j p i hi
  have hH1 : 1 ≤ H := by
    linarith [cNorm_nonneg K (s+2*(n+1)+14) F,
      cNorm_nonneg Kinitial (s+2*(n+1)+14) initial]
  rw [he]
  apply ((LinearIsometryEquiv.prodComm ℝ CarrierParameter (Euclidean n)).norm_iteratedFDeriv_comp_right
    (f j) p i).trans_le
  change ‖iteratedFDeriv ℝ i (f j) (p.2, p.1)‖ ≤ _
  by_cases hp : (p.2, p.1) ∈ L
  · have hlo : cNorm L b (f j) ≤ B j b * (1+MF+Mr) :=
      (hb j b).trans (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (le_refl 1) hFM) hIM) (hB j b).le)
    have hhi : cNorm L (b+s) (f j) ≤ B j (b+s) * H :=
      (hb j (b+s)).trans (mul_le_mul_of_nonneg_left
        (by simpa only [b, Nat.add_comm (2*(n+1)) s] using hH) (hB j (b+s)).le)
    exact hprofile j (f j) (hf j) hlo H hH1 hhi i (by dsimp [b]; omega) _ hp
  · have hz : iteratedFDeriv ℝ i (f j) (p.2, p.1) = 0 := by
      by_contra hn
      exact hp (hsupp (hfsupp j (support_iteratedFDeriv_subset i hn)))
    rw [hz, norm_zero]
    exact mul_nonneg (hC₀ j i) (Real.rpow_nonneg (zero_le_one.trans hH1) _)

end JanetCartan.ContinuumAdjoint.Canonical.RetainedLeading
