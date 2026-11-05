module

public import JanetCartan.Iteration.PhysicalGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.FamilyPhases

/-!
# Original Hamilton phase representatives on physical histories

For paper-v2 `main:prop:pairs`, the actual current projected stress profile pays
the sharp frame derivative shift. The fixed cutoffs preserve the original
Hamilton germs, and the profile precedes every real physical history, sample,
signed pair and localization accuracy. No periodic history is substituted.
The consumer is the original complete signed first-mask source construction
`InitialSignedChainSource.exists_sampled_source_before_firstMask`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPairs

open ActualCarriers CurrentFullPhase FrozenMenu HamiltonPhase ConstructedCarrierJets
open ResponseTransfer.RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles

private theorem carrier_joint_frame_constants
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} (hK : IsCompact K)
    (hKU : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)) :
    ∃ A : ℕ → ℝ, (∀ m, 0 ≤ A m) ∧ ∀ Q m,
      cNorm K m (fun q ↦ T.carrier Q q.1 q.2) ≤ A m *
        (1 + cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m + 1) Q.1) := by
  let J := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  have hψ : ∀ q ∈ K, ContDiffAt ℝ ∞ T.carrierRestriction q := fun q hq ↦
    (T.carrierRestriction_smooth hP).contDiffAt
      ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds (hKU hq))
  have hψJ : MapsTo T.carrierRestriction K J := fun q hq ↦
    ball_subset_closedBall (T.reference.target_contains _ (hKU hq).1 _ (hKU hq).2)
  obtain ⟨B, hB, hb⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK
    (isCompact_closedBall _ _) hψ hψJ
  refine ⟨fun m ↦ B m * T.family.coefficient m,
    fun m ↦ (mul_pos (hB m) (T.family.coefficient_pos m)).le, ?_⟩
  intro Q m
  let f := phase (T.currentChart Q).coordinates
  have hf : ∀ q ∈ J, ContDiffAt ℝ ∞ f q := fun q hq ↦
    (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius < 2 * T.family.radius) hq))
  change cNorm K m (f ∘ T.carrierRestriction) ≤ _
  exact (hb f hf m).trans ((mul_le_mul_of_nonneg_left (T.current_phase_bound Q m)
    (hB m).le).trans_eq (by ring))

private theorem supported_carrier_representative
    {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} (hK : IsCompact K)
    (hKU : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)) :
    ∃ ψ : Euclidean n × Euclidean 3 → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ Q, let f := fun q : Euclidean n × Euclidean 3 ↦ ψ q * T.carrier Q q.1 q.2
      ContDiff ℝ ∞ f ∧ ∀ q ∈ K, f =ᶠ[𝓝 q] (fun q ↦ T.carrier Q q.1 q.2) := by
  let Ω := ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)
  have hΩ : IsOpen Ω := isOpen_ball.prod (isOpen_parameterInterior _)
  obtain ⟨ψ, hψ, hcψ, hsψ, _, heψ⟩ := NormalComparison.exists_contDiff_localization
    hΩ hK hKU (contDiff_const (c := (1 : ℝ))).contDiffOn
  refine ⟨ψ, hψ, hcψ, ?_⟩
  intro Q f
  constructor
  · apply contDiff_iff_contDiffAt.mpr
    intro q
    by_cases hq : q ∈ tsupport ψ
    · exact hψ.contDiffAt.mul ((T.carrier_smooth hP Q).contDiffAt
        (hΩ.mem_nhds (hsψ hq)))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hq] with p hp
      change ψ p = 0 at hp
      simp only [f, hp, zero_mul]
  · intro q hq
    filter_upwards [heψ q hq] with p hp
    simp only [f, hp, one_mul]

/-- Actual revised physical histories supply the SAME original Hamilton
representatives and sharp joint jets `L^(m−2)`. Fixed cutoffs and constants
precede histories and samples; original radial labels remain unchanged
(`app:ch_seed:eq:seed-phase-tame`, `main:prop:pairs`). -/
theorem exists_physical_history_signed_family_representatives
    {d : ℕ} {G : Type*} [Fintype G]
    (P : G → Patch (d + 1)) {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : (g : G) → PatchQuantitativeFamily (P g) U hU)
    {c C₀ : ℝ} (hP : ∀ g, (P g).IsValid c C₀) (radial : G → ℝ)
    {S : Set (Euclidean (d + 1))} (hS : IsCompact S)
    (hSball : ∀ g, S ⊆ ball (0 : Euclidean (d + 1)) (T g).physicalRadius)
    (Gref : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters (Euclidean (d + 1))) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {Cband : ℝ} (hband : 1 ≤ Cband)
    {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : RevisedScales.displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    ∃ ψ : G → Euclidean (d + 1) × Euclidean 3 → ℝ,
      (∀ g, ContDiff ℝ ∞ (ψ g) ∧ HasCompactSupport (ψ g)) ∧
      ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ jointProfile : ℕ → ℝ,
      (∀ j, 0 ≤ jointProfile j) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → SchwartzMap (Euclidean (d + 1))
          (Euclidean (embeddingDimension (d + 1))))
        (ell : Fin s → ℕ), RevisedGlobal.IsAdmissibleHistory Cband R₀ kMin u ell →
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiffOn ℝ ∞ Q U)
        (hlow : ∀ g, cNorm (closedBall (0 : Euclidean (d + 1)) (T g).data.localReference.stateRadius)
          6 (Q - fun _ ↦ cubeStress (d + 1)) < (T g).family.threshold),
      Q = extendedProjectedStress ext (RevisedGlobal.finiteMap Gref.map u) →
      let φ₀ := fun g z x ↦ radial g * (T g).carrier ⟨Q, hQ, hlow g⟩ x z
      let φ := fun g z x ↦ radial g * (ψ g (x, z) * (T g).carrier ⟨Q, hQ, hlow g⟩ x z)
      (∀ g, ContDiff ℝ ∞ (fun p : Euclidean (d + 1) × Euclidean 3 ↦ φ g p.2 p.1)) ∧
      (∀ g x, x ∈ S → ∀ z ∈ parameterCube (P g).radius, φ g z =ᶠ[𝓝 x] φ₀ g z) ∧
      ∀ g x, x ∈ S → ∀ z ∈ parameterCube (P g).radius, ∀ m,
        ‖iteratedFDeriv ℝ m (fun p : Euclidean (d + 1) × Euclidean 3 ↦ φ g p.2 p.1) (x,z)‖ ≤
          jointProfile m * currentCoefficientScale R₀ s ^ (m-2) := by
  classical
  let Z := fun g ↦ parameterCube (P g).radius
  have hK g : IsCompact (S ×ˢ Z g) := hS.prod (isCompact_parameterCube _)
  have hKU g : S ×ˢ Z g ⊆ ball (0 : Euclidean (d + 1)) (T g).physicalRadius ×ˢ
      parameterInterior (2 * (P g).radius) := fun _ hq ↦
    ⟨hSball g hq.1, parameterCube_subset_doubledInterior (hP g).1 hq.2⟩
  choose ψ hψ hcψ hrep using fun g ↦ supported_carrier_representative (T g) (hP g) (hK g) (hKU g)
  choose B hB hframe using fun g ↦ carrier_joint_frame_constants (T g) (hP g) (hK g) (hKU g)
  obtain ⟨threshold, hthreshold, AQ, AB, hAQ, _, hcoeff⟩ :=
    PhysicalGeometry.exists_retained_coefficient_profiles Gref hr hrR hR ext hextcenter hextradius
      hband hStar (reserve := 3) (by omega) horder
  let J := fun g m ↦ B g m * (1 + AQ (m + 1))
  have hJ g m : 0 ≤ J g m := mul_nonneg (hB g m) (by linarith [hAQ (m + 1)])
  let A := fun m ↦ ∑ g, |radial g| * J g m
  have hA m : 0 ≤ A m := Finset.sum_nonneg (fun g _ ↦ mul_nonneg (abs_nonneg _) (hJ g m))
  refine ⟨ψ, fun g ↦ ⟨hψ g, hcψ g⟩, threshold, hthreshold, A, hA, ?_⟩
  intro R₀ hR₀ s u ell hu Q hQ hlow hQeq φ₀ φ
  let L := currentCoefficientScale R₀ s
  have hL : 1 ≤ L := one_le_currentCoefficientScale (by linarith) s
  let Qg g := (⟨Q, hQ, hlow g⟩ : {Q // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (d + 1)) (T g).data.localReference.stateRadius)
      6 (Q - fun _ ↦ cubeStress (d + 1)) < (T g).family.threshold})
  let f g := fun p : Euclidean (d + 1) × Euclidean 3 ↦ φ g p.2 p.1
  have hf g : ContDiff ℝ ∞ (f g) := by
    have h₀ : ContDiff ℝ ∞ (fun p : Euclidean (d + 1) × Euclidean 3 ↦
        ψ g p * (T g).carrier (Qg g) p.1 p.2) := (hrep g (Qg g)).1
    exact contDiff_const.mul h₀
  have he g x (hx : x ∈ S) z (hz : z ∈ Z g) : φ g z =ᶠ[𝓝 x] φ₀ g z := by
    have hh := ((hrep g (Qg g)).2 (x, z) ⟨hx, hz⟩).comp_tendsto
      (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [hh] with y hy
    exact congrArg (radial g * ·) hy
  have hjoint g j x (hx : x ∈ S) z (hz : z ∈ Z g) :
      ‖iteratedFDeriv ℝ j (f g) (x, z)‖ ≤ |radial g| * J g j * L ^ (j - 2) := by
    let f₀ := fun p : Euclidean (d + 1) × Euclidean 3 ↦ ψ g p * (T g).carrier (Qg g) p.1 p.2
    have h₀ : ContDiff ℝ ∞ f₀ := (hrep g (Qg g)).1
    have hQj : cNorm (closedBall (0 : Euclidean (d + 1)) (T g).data.localReference.stateRadius)
        (j + 1) Q ≤ AQ (j + 1) * L ^ (j - 2) := by
      rw [hQeq]
      simpa only [L, show j + 1 - 3 = j - 2 by omega] using
        (((hcoeff R₀ hR₀ s u ell hu).2.2 _ (isCompact_closedBall _ _)).1 (j + 1))
    have hc₀ : cNorm (S ×ˢ Z g) j f₀ ≤ J g j * L ^ (j - 2) := by
      rw [cNorm_eq_of_eventuallyEq ((hrep g (Qg g)).2) j]
      apply (hframe g (Qg g) j).trans
      dsimp only [J]
      have hone := one_le_pow₀ hL (n := j - 2)
      have hb := hB g j
      change B g j * (1 + cNorm _ (j + 1) Q) ≤ _
      nlinarith [mul_le_mul_of_nonneg_left (add_le_add hone hQj) hb]
    have hjet₀ := (norm_iteratedFDeriv_le_cNorm (x := (x, z)) (hK g) (h₀.of_le (by simp))
      ⟨hx, hz⟩ le_rfl).trans hc₀
    change ‖iteratedFDeriv ℝ j ((radial g) • f₀) (x, z)‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply (h₀.contDiffAt.of_le (by simp)), norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left hjet₀ (abs_nonneg _)).trans_eq (by ring)
  refine ⟨hf, he, ?_⟩
  intro g x hx z hz m
  apply (hjoint g m x hx z hz).trans
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun i _ ↦ mul_nonneg (abs_nonneg _) (hJ i m)) (Finset.mem_univ g))
    (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.PhysicalPairs
