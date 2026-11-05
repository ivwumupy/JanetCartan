module
public import JanetCartan.Iteration.PhysicalPairs.Phases
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.PhysicalFrameAdmission

/-! # Sharp scalar jets from the SAME raw current's retained coefficient budget

The signed first mask needs joint spatial/outer-parameter jets of the original
radially labeled Hamilton scalar, not the different primary doubled-carrier
phase. Work with the raw projected stress itself: its coefficients have the
same jets as the actual extension on the original state balls. This form
receives the already selected `OriginalOperatorProfiles` budget, without an
extra start scale or an equality between Hamilton charts for different frames.
`main:prop:pairs`, `app:ch_seed:eq:seed-phase-tame`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.PhysicalPairs.NativeFramePhase
open ActualCarriers CurrentFullPhase FrozenMenu HamiltonPhase ConstructedCarrierJets
open ResponseTransfer.RetainedFactors GeometricProfile ProtectedFlow CurrentCoefficientProfiles ProjectedStressFrame

/-- Original state-domain buffer, without subtracting a frozen frame: the
complete frame jets used for the scalar phase really are the physical ones. -/
theorem raw_frame_on_state {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) (ext : BallExtension.Parameters (Euclidean n))
    (h0 : ext.center = 0) (hphysical : ∀ z ∈ T.data.localReference.stateDomain, z.1 ∈ ball 0 ext.radius)
    (F : Euclidean n → Euclidean N) (m : ℕ) :
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m (projectedStress F) =
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) m (extendedProjectedStress ext F) := by
  apply cNorm_eq_of_eventuallyEq
  intro x hx
  have hb := frameBall_subset_of_stateDomain T.data.localReference hphysical hx
  exact eventuallyEq_of_mem (isOpen_ball.mem_nhds hb)
    (fun y hy ↦ (affineFrameExtension_eqOn ext (projectedStress F) (by rw [h0];exact ball_subset_closedBall hy)).symm)

/-- Uniform POINTWISE joint jets of the literal radial carrier on one original
compact product; the only input is the previously retained coefficient price.
No phase envelope or control of an independently selected chart is assumed. -/
private theorem patch_jet_cost {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU) {c C : ℝ} (hp : P.IsValid c C) (radial : ℝ)
    {K : Set (Euclidean n × Euclidean 3)} (hK : IsCompact K)
    (hKU : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2*P.radius))
    (AQ : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ Q (L : ℝ), 1 ≤ L →
      (∀ m, cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m+1) Q.1 ≤ AQ (m+1)*L^(m-2)) →
      ∀ (v : Euclidean n × Euclidean 3), v ∈ K → ∀ m,
      ‖iteratedFDeriv ℝ m (fun p : Euclidean n × Euclidean 3 ↦ radial * T.carrier Q p.1 p.2) v‖ ≤ D m*L^(m-2) := by
  let J := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,T.data.adapted.baseData.2) T.family.radius
  have hd : ∀ z ∈ K, ContDiffAt ℝ ∞ T.carrierRestriction z := fun z hz ↦
    (T.carrierRestriction_smooth hp).contDiffAt ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds (hKU hz))
  have hJ : MapsTo T.carrierRestriction K J := fun _ hz ↦
    ball_subset_closedBall (T.reference.target_contains _ (hKU hz).1 _ (hKU hz).2)
  obtain ⟨B,hB,hBbound⟩ := exists_cNorm_fixed_pullback_le (G := ℝ) hK (isCompact_closedBall _ _) hd hJ
  let A := fun m ↦ |radial| * (B m*T.family.coefficient m)
  have hA m : 0 ≤ A m := mul_nonneg (abs_nonneg _) (mul_nonneg (hB m).le (T.family.coefficient_pos _).le)
  refine ⟨fun m ↦ A m*(1+AQ (m+1)), fun m ↦ mul_nonneg (hA m) (by linarith [hAQ (m+1)]),?_⟩
  intro Q L hL hframe v hv m
  let f := phase (T.currentChart Q).coordinates
  let a : Euclidean n × Euclidean 3 → ℝ := fun p ↦ T.carrier Q p.1 p.2
  have ha (w) (hw : w ∈ K) : ContDiffAt ℝ m a w :=
    ((T.carrier_smooth hp Q).contDiffAt ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds (hKU hw))).of_le (by simp)
  have hf : ∀ z ∈ J, ContDiffAt ℝ ∞ f z := fun z hz ↦ (T.family.phase_smooth Q).contDiffAt
    (isOpen_ball.mem_nhds (closedBall_subset_ball (by linarith [T.family.radius_pos] :
      T.family.radius < 2*T.family.radius) hz))
  have hC : cNorm K m a ≤ (B m*T.family.coefficient m) *
      (1+cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m+1) Q.1) :=
    (hBbound f hf m).trans ((mul_le_mul_of_nonneg_left (T.current_phase_bound Q m) (hB m).le).trans_eq (by ring))
  change ‖iteratedFDeriv ℝ m (radial • a) v‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply (ha v hv),norm_smul,Real.norm_eq_abs]
  have hj := (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hK ha hv le_rfl).trans hC
  have hparent := mul_le_mul_of_nonneg_left (add_le_add (one_le_pow₀ hL (n := m-2)) (hframe m)) (hA m)
  calc |radial| * ‖iteratedFDeriv ℝ m a v‖ ≤ |radial| * _ := mul_le_mul_of_nonneg_left hj (abs_nonneg _)
       _ = A m*(1+cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) (m+1) Q.1) := by simp only [A]; ring
       _ ≤ _ := hparent.trans_eq (by ring)

/-- A single classical profile precedes ALL actual raw frames and labels.
Only an auxiliary smooth representative is extended; it equals the very same
radial scalar germ on the entire compact × outer parameter cube. -/
theorem representatives {n : ℕ} {G : Type} [Fintype G] (P : G → Patch n)
    {U : Set (Euclidean n)} {hU : IsOpen U} (T : ∀ g, PatchQuantitativeFamily (P g) U hU)
    {c C : ℝ} (hp : ∀ g, (P g).IsValid c C) (radial : G → ℝ) {S : Set (Euclidean n)}
    (hS : IsCompact S) (hball : ∀ g, S ⊆ ball (0 : Euclidean n) (T g).physicalRadius)
    (AQ : ℕ → ℝ) (hAQ : ∀ m, 0 ≤ AQ m) :
    ∃ D : ℕ → ℝ, (∀ m, 0 ≤ D m) ∧ ∀ (Q : Euclidean n → Fin n → MetricTensor n)
      (hQ : ContDiffOn ℝ ∞ Q U)
      (hlow : ∀ g, cNorm (closedBall (0 : Euclidean n) (T g).data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < (T g).family.threshold)
      (L : ℝ), 1 ≤ L →
      (∀ g m, cNorm (closedBall (0 : Euclidean n) (T g).data.localReference.stateRadius) (m+1) Q ≤ AQ (m+1)*L^(m-2)) →
      ∃ φ : G → Euclidean n × Euclidean 3 → ℝ,
        (∀ g, ContDiff ℝ ∞ (φ g) ∧ HasCompactSupport (φ g)) ∧
        (∀ g v, v ∈ S ×ˢ parameterCube (P g).radius → φ g =ᶠ[𝓝 v]
          (fun p ↦ radial g*(T g).carrier ⟨Q,hQ,hlow g⟩ p.1 p.2)) ∧
        ∀ g v, v ∈ S ×ˢ parameterCube (P g).radius → ∀ m, ‖iteratedFDeriv ℝ m (φ g) v‖ ≤ D m*L^(m-2) := by
  classical
  let K := fun g ↦ S ×ˢ parameterCube (P g).radius
  let V := fun g ↦ ball (0 : Euclidean n) (T g).physicalRadius ×ˢ parameterInterior (2*(P g).radius)
  have hk g : IsCompact (K g) := hS.prod (isCompact_parameterCube _)
  have hv g : IsOpen (V g) := isOpen_ball.prod (isOpen_parameterInterior _)
  have hKV g : K g ⊆ V g := fun _ h ↦ ⟨hball g h.1,parameterCube_subset_doubledInterior (hp g).1 h.2⟩
  choose B hB hcost using fun g ↦ patch_jet_cost (T g) (hp g) (radial g) (hk g) (hKV g) AQ hAQ
  refine ⟨fun k ↦ ∑ g, B g k, fun k ↦ Finset.sum_nonneg (fun g _ ↦ hB g k),?_⟩
  intro Q hQ hlow L hL hframe
  let a := fun g (p : Euclidean n × Euclidean 3) ↦ radial g*(T g).carrier ⟨Q,hQ,hlow g⟩ p.1 p.2
  have ha g : ContDiffOn ℝ ∞ (a g) (V g) := contDiffOn_const.mul ((T g).carrier_smooth (hp g) _)
  choose φ hφ hc _ _ he using fun g ↦ NormalComparison.exists_contDiff_localization (hv g) (hk g) (hKV g) (ha g)
  refine ⟨φ,fun g ↦ ⟨hφ g,hc g⟩,he,?_⟩
  intro g v h m
  rw [((he g v h).iteratedFDeriv ℝ m).eq_of_nhds]
  exact (hcost g ⟨Q,hQ,hlow g⟩ L hL (hframe g) v h m).trans
    (mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun k _ ↦ hB k m) (Finset.mem_univ g))
      (pow_nonneg (zero_le_one.trans hL) _))
end JanetCartan.PhysicalPairs.NativeFramePhase
end
