module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.RootQuantitative.Local

/-!
# Fixed finite covers of the actual incidence graphs

The compact cylinder contains every continued root graph, before the immersion
is chosen. Local primitive budgets and root estimates therefore have one
positive frame threshold and common constants (`app:ch_seed:eq:seed-phase-tame`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
open HamiltonPhase FrozenMenu ProjectedStressFrame
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The literal incidence roots on a fixed physical/covector buffer satisfy
the reserve-six estimate. The finite cover and threshold are chosen before
all high orders and immersions. Only the root equation, smoothness, interval
location and scalar gap from the actual low construction are used
(`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_projected_cylinder_root_bound {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    (r : ℝ) (hrT : 2 * r < T.physicalRadius)
    (k : Euclidean n) (b a : ℝ) (z : Euclidean 3)
    (hz : ∀ t ∈ Icc (-a) a, incidenceParameter z t ∈ parameterInterior P.radius)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ cr : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) (hcr : 0 < cr) :
    ∃ δ > (0 : ℝ), ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < δ →
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        let s := closedBall (0 : Euclidean n) (2 * r) ×ˢ closedBall k b
        ∀ V : Set (Euclidean n × Euclidean n), IsOpen V → s ⊆ V →
        ∀ (g : Euclidean n × Euclidean n → ℝ), ContDiffOn ℝ ∞ g V →
        (∀ p ∈ V, currentIncidence (projectedStress F) (T.carrier Q) z (p, g p) = 0) →
        (∀ p ∈ s, g p ∈ Icc (-a) a) →
        (∀ p ∈ s, cr ≤ |CharacteristicRoot.scalarDerivative
          (currentIncidence (projectedStress F) (T.carrier Q) z) (p, g p)|) →
        ∀ m, cNorm s m g ≤ A m * (1 + cNorm K (m + 6) F) := by
  classical
  let R := (2 * r + T.physicalRadius) / 2
  have hrR : 2 * r < R := by dsimp [R]; linarith
  have hRT : R < T.physicalRadius := by dsimp [R]; linarith
  let s := closedBall (0 : Euclidean n) (2 * r) ×ˢ closedBall k b
  let Z := s ×ˢ Icc (-a) a
  have hZ : IsCompact Z := ((isCompact_closedBall _ _).prod
    (isCompact_closedBall _ _)).prod isCompact_Icc
  let O : Set ((Euclidean n × Euclidean n) × ℝ) :=
    {q | q.1.1 ∈ ball (0 : Euclidean n) R ∧
      incidenceParameter z q.2 ∈ parameterInterior P.radius}
  have hO : IsOpen O :=
    (isOpen_ball.preimage continuous_fst.fst).inter
      ((isOpen_parameterInterior _).preimage
        (continuous_const.add (continuous_snd.smul continuous_const)))
  have hZO : Z ⊆ O := fun q hq ↦
    ⟨closedBall_subset_ball hrR hq.1.1, hz _ hq.2⟩
  have hlocal (q : Z) : ∃ ρ > (0 : ℝ),
      closedBall q.1.1.1 ρ ⊆ closedBall (0 : Euclidean n) R ∧
      ∀ t ∈ Icc (q.1.2 - ρ) (q.1.2 + ρ), incidenceParameter z t ∈ parameterCube P.radius := by
    obtain ⟨ρ, hρ, hρO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (hO.mem_nhds (hZO q.2))
    refine ⟨ρ, hρ, ?_, ?_⟩
    · intro x hx
      have hm : ((x, q.1.1.2), q.1.2) ∈ closedBall q.1 ρ := by
        simpa only [mem_closedBall, Prod.dist_eq, dist_self,
          max_eq_left (dist_nonneg)] using hx
      exact ball_subset_closedBall (hρO hm).1
    · intro t ht
      have hd : dist t q.1.2 ≤ ρ := by
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith [ht.1, ht.2]
      have hm : (q.1.1, t) ∈ closedBall q.1 ρ := by
        simpa only [mem_closedBall, Prod.dist_eq, dist_self,
          max_eq_right (dist_nonneg)] using hd
      exact fun i ↦ ((hρO hm).2 i).le
  choose ρ hρ hxρ hzρ using hlocal
  choose d hd A hA hbound using fun q : Z ↦ T.exists_projected_local_root_bound
    (N := N) hP q.1 (hρ q) z (isCompact_closedBall _ _) (isCompact_parameterCube _)
    (closedBall_subset_ball hRT) (parameterCube_subset_doubledInterior hP.1)
    (hxρ q) (hzρ q) hK hKU hball C₀ hκmet hκ hcr
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun q : Z ↦ ball q.1 (ρ q))
    (fun _ ↦ isOpen_ball) (fun q hq ↦ mem_iUnion.mpr ⟨⟨q, hq⟩, mem_ball_self (hρ _)⟩)
  obtain ⟨δ, hδ, hδd⟩ := Pi.exists_forall_pos_add_lt (fun q : t ↦ hd q.1)
  let B (m : ℕ) := 1 + ∑ q : t, A q.1 m
  have hB (m : ℕ) : 0 < B m := by
    have hs := Finset.sum_nonneg (s := (Finset.univ : Finset t)) (fun q (_ : q ∈ Finset.univ) ↦ (hA q.1 m).le)
    change 0 < 1 + ∑ q : t, A q.1 m
    linarith
  have hAB (q : t) (m : ℕ) : A q.1 m ≤ B m := by
    have hs := Finset.single_le_sum (s := Finset.univ)
      (fun q (_ : q ∈ Finset.univ) ↦ (hA q.1 m).le) (Finset.mem_univ q)
    change A q.1 m ≤ 1 + ∑ x : t, A x.1 m
    linarith
  refine ⟨δ, hδ, fun m ↦ (m + 1) * B m, fun m ↦ mul_pos (by positivity) (hB m), ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow hclose
  dsimp only
  intro V hV hsV g hg heq hinterval hgap m
  have hpoint (p : Euclidean n × Euclidean n) (hp : p ∈ s) :
      cNorm {p} m g ≤ B m * (1 + cNorm K (m + 6) F) := by
    have hpZ : (p, g p) ∈ Z := ⟨hp, hinterval p hp⟩
    obtain ⟨q, hqt, hpq⟩ := mem_iUnion₂.mp (ht hpZ)
    have hqd : δ < d q := by simpa using hδd ⟨q, hqt⟩
    have hb := hbound q F hF hi hrank hlowF hmet hnormal hlow
      (hclose.trans hqd) {p} V hV (by simpa using hsV hp) g hg heq
      (by intro y hy; have hy' := mem_singleton_iff.mp hy; subst y; exact ball_subset_closedBall hpq)
      (by intro y hy; have hy' := mem_singleton_iff.mp hy; subst y; exact hgap p hp) m
    exact hb.trans (mul_le_mul_of_nonneg_right (hAB ⟨q, hqt⟩ m)
      (by linarith [cNorm_nonneg K (m + 6) F]))
  have hb := cNorm_le_sum_of_bounds (r := m)
    (C := fun _ ↦ B m * (1 + cNorm K (m + 6) F))
    (fun _ _ ↦ mul_nonneg (hB m).le (by linarith [cNorm_nonneg K (m + 6) F]))
    (fun j hj p hp ↦ (norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_singleton : IsCompact {p})
      (by intro y hy; have hy' := mem_singleton_iff.mp hy; subst y
          exact (hg.contDiffAt (hV.mem_nhds (hsV hp))).of_le (by simp))
      (mem_singleton p) hj).trans (hpoint p hp))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one, mul_assoc] using hb

end JanetCartan.ActualCarriers.CurrentFullPhase.PatchQuantitativeFamily
