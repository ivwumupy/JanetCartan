module
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.HistoryPhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryProfiles

/-!
# One history-uniform source geometry for the finite signed family

Construct globally smooth representatives for the supplied Hamilton carriers
on their original physical support and parameter cubes. Their cutoffs are
chosen before histories and signed pairs. The actual extended stress profile
pays the sharp frame shift and the mixed parameter derivative. Finite sums
retain every original radial label and give one profile for all signed pairs,
including doubled carriers and arbitrarily short nonzero differences.

The primitive gradient band comes from the same signed geometry constructed
by `ConstructedSignedGeometry`, via `currentGroup_eq_gradient_radial_carrier`.
All higher phase and cutoff grades are conclusions. The normalized phase
agrees with the original on the entire source support, so the existing
`modulatedSource_eq_of_support_agreement` preserves the complete tensor or
reduced-vector source (`app:ch_pairs:setup:pairs-lag`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.SignedProductEstimates
open ActualCarriers CurrentFullPhase FrozenMenu HamiltonPhase ConstructedCarrierJets
open ResponseTransfer.RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles

/-- The literal scalar Hamilton carrier has frame shift one, on its original
physical coordinates (`app:ch_seed:eq:seed-phase-tame`). This supplies the
history profile for the finite-family source geometry below. -/
private theorem exists_carrier_joint_frame_constants
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

/-- One cutoff extends the supplied carrier for every allowed coefficient
field while preserving its joint germ on the whole source carrier
(`app:ch_pairs:setup:pairs-lag`). It is chosen before histories and samples. -/
private theorem exists_supported_carrier_representative
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


open SignedPairs ResponseTransfer.SourceNegative

/-- Pointwise agreement on each original parameter patch preserves the SAME
signed-pair witness (`app:rem:exhaustive-signed-pairs`). -/
private theorem signed_pair_vector_congr_on
    {G E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : G → Set (Euclidean 3)} (q : Pair G (Euclidean 3) Z)
    {f g : G → Euclidean 3 → E} (hfg : ∀ i z, z ∈ Z i → f i z = g i z) :
    q.vector f = q.vector g := by
  cases q with
  | difference i z w hne => simp only [Pair.vector, hfg i z z.property, hfg i w w.property]
  | sum i z w => simp only [Pair.vector, hfg i z z.property, hfg i w w.property]
  | cross i j hne z w s t hs ht =>
      simp only [Pair.vector, hfg i z z.property, hfg j w w.property]

/-- Construct the same finite family's smooth Hamilton representatives and
sharp joint jets directly from the original admissible history. The cutoff
and all profile constants precede histories and samples, and each original
radial label is retained. Germ agreement holds at every source point and
parameter. This supplies the joint phase input of
`exists_normalized_sampled_source_discrepancy_constants` and the original
`SourceGeometry` constructor below (`app:ch_seed:eq:seed-phase-tame`,
`app:ch_pairs:setup:pairs-lag`). -/
theorem exists_admissible_history_signed_family_representatives
    {d : ℕ} {G : Type*} [Fintype G]
    (P : G → Patch (d + 1)) {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : (g : G) → PatchQuantitativeFamily (P g) U hU)
    {c C₀ : ℝ} (hP : ∀ g, (P g).IsValid c C₀) (radial : G → ℝ)
    {S : Set (Euclidean (d + 1))} (hS : IsCompact S)
    (hSball : ∀ g, S ⊆ ball (0 : Euclidean (d + 1)) (T g).physicalRadius)
    (Gref : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters (Euclidean (d + 1))) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    ∃ ψ : G → Euclidean (d + 1) × Euclidean 3 → ℝ,
      (∀ g, ContDiff ℝ ∞ (ψ g) ∧ HasCompactSupport (ψ g)) ∧
      ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ jointProfile : ℕ → ℝ,
      (∀ j, 0 ≤ jointProfile j) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiffOn ℝ ∞ Q U)
        (hlow : ∀ g, cNorm (closedBall (0 : Euclidean (d + 1)) (T g).data.localReference.stateRadius)
          6 (Q - fun _ ↦ cubeStress (d + 1)) < (T g).family.threshold),
      Q = extendedProjectedStress ext (finiteHistoryMap Gref.map u) →
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
  choose ψ hψ hcψ hrep using fun g ↦ exists_supported_carrier_representative (T g) (hP g) (hK g) (hKU g)
  choose B hB hframe using fun g ↦ exists_carrier_joint_frame_constants (T g) (hP g) (hK g) (hKU g)
  obtain ⟨threshold, hthreshold, AQ, AB, hAQ, _, hcoeff⟩ :=
    exists_admissible_history_retained_coefficient_profiles Gref hr hrR hR ext hextcenter hextradius
      hStar (reserve := 3) (by omega) horder
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

/-- Construct the original `SourceGeometry` for every normalized signed
pair of the supplied finite Hamilton family (`app:ch_pairs:setup:pairs-lag`).
The prescribed history extension supplies the row; the original signed
covector band is the sole remaining geometric input for each pair. No phase
profile or normalized-source estimate is assumed. Representatives, threshold
and both profiles precede histories and pair choices; fixed radial labels
remain in the constants. Agreement on the entire fixed source set preserves
the literal source through `modulatedSource_eq_of_support_agreement`.
Consumers: the negative-source and complete complementary-mask estimates. -/
theorem exists_admissible_history_signed_family_source_geometry
    {d : ℕ} {G : Type*} [Fintype G]
    (P : G → Patch (d + 1)) {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : (g : G) → PatchQuantitativeFamily (P g) U hU)
    {c C₀ : ℝ} (hP : ∀ g, (P g).IsValid c C₀) (radial : G → ℝ)
    {S : Set (Euclidean (d + 1))} (hS : IsCompact S)
    (hSball : ∀ g, S ⊆ ball (0 : Euclidean (d + 1)) (T g).physicalRadius)
    (χ : Euclidean (d + 1) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχS : tsupport χ ⊆ S)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (Gref : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters (Euclidean (d + 1))) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    ∃ ψ : G → Euclidean (d + 1) × Euclidean 3 → ℝ,
      (∀ g, ContDiff ℝ ∞ (ψ g) ∧ HasCompactSupport (ψ g)) ∧
      ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ phaseProfile cutoffProfile : ℕ → ℝ,
      (∀ j, 0 ≤ phaseProfile j) ∧ (∀ j, 0 ≤ cutoffProfile j) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ (Q : Euclidean (d + 1) → Fin (d + 1) → MetricTensor (d + 1))
        (hQ : ContDiffOn ℝ ∞ Q U)
        (hlow : ∀ g, cNorm (closedBall (0 : Euclidean (d + 1)) (T g).data.localReference.stateRadius)
          6 (Q - fun _ ↦ cubeStress (d + 1)) < (T g).family.threshold),
      Q = extendedProjectedStress ext (finiteHistoryMap Gref.map u) →
      let φ₀ := fun g z x ↦ radial g * (T g).carrier ⟨Q, hQ, hlow g⟩ x z
      let φ := fun g z x ↦ radial g * (ψ g (x, z) * (T g).carrier ⟨Q, hQ, hlow g⟩ x z)
      (∀ g, ContDiff ℝ ∞ (fun p : Euclidean (d + 1) × Euclidean 3 ↦ φ g p.2 p.1)) ∧
      ∀ q : Pair G (Euclidean 3) (fun g ↦ parameterCube (P g).radius),
        EqOn (fun x ↦ q.vector (fun g z ↦ φ g z x) / q.beat)
          (fun x ↦ q.vector (fun g z ↦ φ₀ g z x) / q.beat) S ∧
        ((∀ x ∈ S,
          a * q.beat ≤ ‖q.vector (fun g z ↦ gradient (φ₀ g z) x)‖ ∧
          ‖q.vector (fun g z ↦ gradient (φ₀ g z) x)‖ ≤ b * q.beat) →
          SourceGeometry χ (fun x ↦ q.vector (fun g z ↦ φ g z x) / q.beat)
            S a b (currentCoefficientScale R₀ s) phaseProfile cutoffProfile) := by
  obtain ⟨ψ, hψ, threshold, hthreshold, A, hA, hrepresentatives⟩ :=
    exists_admissible_history_signed_family_representatives P T hP radial hS hSball
      Gref hr hrR hR ext hextcenter hextradius hStar horder
  let C := fun m ↦ A m + A (m+1)
  have hC m : 0 ≤ C m := add_nonneg (hA m) (hA (m+1))
  let X := fun j ↦ cNorm S j χ
  have hX j : 0 ≤ X j := cNorm_nonneg ..
  refine ⟨ψ, hψ, threshold, hthreshold,
    (fun j ↦ 2 * C (j + 1)), X, (fun j ↦ mul_nonneg (by norm_num) (hC _)), hX, ?_⟩
  intro R₀ hR₀ s u ell hu Q hQ hlow hQeq φ₀ φ
  let L := currentCoefficientScale R₀ s
  have hL : 1 ≤ L := one_le_currentCoefficientScale (by linarith) s
  let Z := fun g ↦ parameterCube (P g).radius
  let f g := fun p : Euclidean (d + 1) × Euclidean 3 ↦ φ g p.2 p.1
  obtain ⟨hf, he, hjoint⟩ := hrepresentatives R₀ hR₀ s u ell hu Q hQ hlow hQeq
  have hjets x (hx : x ∈ S) m g z (hz : z ∈ Z g) :
      ‖iteratedFDeriv ℝ m (φ g z) x‖ ≤ C m * L ^ (m - 1) ∧
      ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ m (φ g w) x) z‖ ≤ C m * L ^ (m - 1) := by
    constructor
    · apply (primary_phase_spatial_jet_le_joint (f g) (hf g) x z m).trans ((hjoint g x hx z hz m).trans ?_)
      exact mul_le_mul (le_add_of_nonneg_right (hA (m+1))) (pow_le_pow_right₀ hL (by omega))
        (pow_nonneg (zero_le_one.trans hL) _) (hC m)
    · apply (norm_parameter_spatial_phase_jet_le_joint (f g) (hf g) m x z).trans
        ((hjoint g x hx z hz (m+1)).trans ?_)
      rw [show m + 1 - 2 = m - 1 by omega]
      exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hA m)) (pow_nonneg (zero_le_one.trans hL) _)
  refine ⟨hf, fun q ↦ ⟨?_, ?_⟩⟩
  · intro x hx
    exact congrArg (· / q.beat) (signed_pair_vector_congr_on q (fun g z hz ↦ (he g x hx z hz).eq_of_nhds))
  · intro hband
    apply sourceGeometry_normalized_signed_pair (fun g ↦ convex_parameterCube _) q χ φ hS hχS hχ
      (fun g z _ ↦ (hf g).comp (contDiff_id.prodMk contDiff_const)) ha hab hL
      (fun j ↦ C (j + 1)) X (fun j ↦ hC _) hX
    · intro x hx
      have hegrad : q.vector (fun g z ↦ gradient (φ g z) x) =
          q.vector (fun g z ↦ gradient (φ₀ g z) x) := signed_pair_vector_congr_on q
        (fun g z hz ↦ by unfold gradient; rw [(he g x hx z hz).fderiv_eq])
      rw [hegrad]
      exact hband x hx
    · intro x hx j _ g z hz
      simpa only [Nat.add_sub_cancel] using (hjets x hx (j + 1) g z hz).1
    · intro x _ j _ g z _
      exact ((contDiff_parameter_spatial_phase_jet (f g) (hf g) (j + 1) x).differentiable
        (by simp)).differentiableAt
    · intro x hx j _ g z hz
      simpa only [Nat.add_sub_cancel] using (hjets x hx (j + 1) g z hz).2
    · intro x j
      have hχjet : ‖iteratedFDeriv ℝ j χ x‖ ≤ X j := by
        by_cases hx : x ∈ S
        · exact norm_iteratedFDeriv_le_cNorm hS (hχ.of_le (by simp)) hx le_rfl
        · have hz : iteratedFDeriv ℝ j χ x = 0 := image_eq_zero_of_notMem_tsupport
            (fun hj ↦ hx (hχS ((tsupport_iteratedFDeriv_subset j) hj)))
          simpa only [hz, norm_zero] using hX j
      exact hχjet.trans (le_mul_of_one_le_right (hX j) (one_le_pow₀ hL))

end JanetCartan.SignedProductEstimates
