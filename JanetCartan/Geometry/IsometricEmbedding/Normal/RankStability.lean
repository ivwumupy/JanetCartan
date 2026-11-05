module

public import JanetCartan.Geometry.IsometricEmbedding.Normal.RankStability.Geometry
public import JanetCartan.Geometry.IsometricEmbedding.Normal.SmoothProjection

/-!
# Local full normal rank and quantitative normal gaps

Operator-norm stability for `main:prop:seed` and
`app:ch_seed:setup:seed-current`, using the actual normal spaces. The leaf
modules prove the finite-dimensional estimates and the identification of
nearby normal spaces by restricted orthogonal projection.

The geometric corollaries derive continuity of the actual projection and second
fundamental form from C² immersion regularity using `Normal.SmoothProjection`.
Full normal rank at a single immersion point gives a ball with uniform positive
normal Gram gap. This proves the local rank and gap component of the cited
source results; the other reference and carrier gaps are separate components.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Frobenius Topology ContDiff

namespace JanetCartan.NormalRankStability

/-- `main:prop:seed`: coefficient continuity of the actual second form
gives operator-norm continuity of its Frobenius normal map. -/
theorem continuousAt_ambientNormalMap {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (hII : ∀ i j, ContinuousAt (fun y ↦ secondFundamentalForm F y i j) x) :
    ContinuousAt (ambientNormalMap F) x := by
  apply continuousAt_clm_apply.mpr
  intro H
  change ContinuousAt (fun y ↦ ∑ i, ∑ j, H i j • secondFundamentalForm F y i j) x
  exact tendsto_finsetSum _ fun i _ ↦ tendsto_finsetSum _ fun j _ ↦
    (hII i j).const_smul (H i j)

/-- `main:prop:seed`: the actual normal map becomes continuous on a
fixed output space by projection to the reference normal space. -/
theorem continuousAt_fixedNormalMap {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (hII : ∀ i j, ContinuousAt (fun y ↦ secondFundamentalForm F y i j) x) :
    ContinuousAt (fun y ↦ fixedNormalMap F x F y) x :=
  continuousAt_const.clm_comp (continuousAt_ambientNormalMap F x hII)

/-- `main:prop:seed` and `app:ch_seed:setup:seed-current`: full rank
and a uniform positive normal Gram gap persist locally for the actual
geometric normal map. Continuity of the actual projection and second form
is required explicitly here; the output normal spaces are allowed to vary. -/
theorem eventually_geometric_normal_rank_and_gap_of_continuousAt {n N : ℕ}
    (F : Euclidean n → Euclidean N) (x : Euclidean n)
    (hP : ContinuousAt (normalProjection F) x)
    (hII : ∀ i j, ContinuousAt (fun y ↦ secondFundamentalForm F y i j) x)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ y in 𝓝 x,
      Set.range (normalMap F y) = (normalSpace F y : Set (Euclidean N)) ∧
        ∀ w : normalSpace F y, (κ ^ 2 / 4) * ‖w‖ ^ 2 ≤
          inner ℝ (NormalPerturbation.normal (geometricNormalMap F y) w) w := by
  obtain ⟨κ, hκ, hstable⟩ := exists_geometric_normal_rank_gap_neighborhood F x hrank
  have hp : ∀ᶠ y in 𝓝 x, ‖normalProjection F x - normalProjection F y‖ < 1 :=
    (continuousAt_const.sub hP).norm.eventually (gt_mem_nhds (by simp))
  have hc' : ContinuousAt
      (fun y ↦ ‖fixedNormalMap F x F y - geometricNormalMap F x‖) x :=
    ContinuousAt.norm (E := MetricTensor n →L[ℝ] normalSpace F x)
      ((continuousAt_fixedNormalMap F x hII).sub continuousAt_const)
  have hc : ∀ᶠ y in 𝓝 x,
      ‖fixedNormalMap F x F y - geometricNormalMap F x‖ < κ / 2 :=
    hc'.eventually (gt_mem_nhds (by
      change ‖fixedNormalMap F x F x - geometricNormalMap F x‖ < κ / 2
      rw [fixedNormalMap_self F x, sub_self]
      rw [norm_zero (E := MetricTensor n →L[ℝ] normalSpace F x)]
      exact half_pos hκ))
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hp, hc] with y hpy hcy
  exact hstable F y hpy hcy.le

/-- `main:prop:seed` and `app:ch_seed:setup:seed-current`: full normal rank
of a C² immersion persists locally, with the explicit positive Gram gap
`κ² / 4`. Continuity of the projection and second form is proved from the
immersion hypotheses, and the gap is on each actual varying normal space. -/
theorem eventually_geometric_normal_rank_and_gap {n N : ℕ}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ 2 F s) (himm : IsImmersionOn F s)
    {x : Euclidean n} (hx : x ∈ s)
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ y in 𝓝 x,
      Set.range (normalMap F y) = (normalSpace F y : Set (Euclidean N)) ∧
        ∀ w : normalSpace F y, (κ ^ 2 / 4) * ‖w‖ ^ 2 ≤
          inner ℝ (NormalPerturbation.normal (geometricNormalMap F y) w) w := by
  apply eventually_geometric_normal_rank_and_gap_of_continuousAt F x _ _ hrank
  · exact (contDiffOn_normalProjection hs hF (r := 0) (by norm_num) himm).continuousOn
      |>.continuousAt (hs.mem_nhds hx)
  · intro i j
    exact (contDiffOn_secondFundamentalForm hs hF (r := 0) (by norm_num) himm i j).continuousOn
      |>.continuousAt (hs.mem_nhds hx)

/-- `main:prop:seed`: a full-rank immersion point of a C² map has a ball
inside the original domain on which immersion, full normal rank, and one
positive normal Gram gap all hold. Only immersion and rank at the center
are assumed. In particular, this applies to the smooth reference map. -/
theorem exists_ball_geometric_normal_rank_and_gap {n N : ℕ}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ 2 F s) {x : Euclidean n} (hx : x ∈ s)
    (himm : Function.Injective (fderiv ℝ F x))
    (hrank : Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ κ : ℝ, 0 < κ ∧
      Metric.ball x ε ⊆ s ∧ IsImmersionOn F (Metric.ball x ε) ∧
      HasFullNormalRankOn F (Metric.ball x ε) ∧
      ∀ y ∈ Metric.ball x ε, ∀ w : normalSpace F y,
        (κ ^ 2 / 4) * ‖w‖ ^ 2 ≤
          inner ℝ (NormalPerturbation.normal (geometricNormalMap F y) w) w := by
  have ht := isOpen_immersionDomain hs (hF.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
  have hxt : x ∈ immersionDomain F s := ⟨hx, himm⟩
  obtain ⟨κ, hκ, hstable⟩ := eventually_geometric_normal_rank_and_gap ht
    (hF.mono (fun _ hy ↦ hy.1)) (isImmersionOn_immersionDomain F s) hxt hrank
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp
    (Filter.Eventually.and (ht.mem_nhds hxt) hstable)
  exact ⟨ε, hε, κ, hκ, fun _ hy ↦ (hball hy).1.1,
    fun _ hy ↦ (hball hy).1.2, fun _ hy ↦ (hball hy).2.1,
    fun _ hy ↦ (hball hy).2.2⟩

/-- `main:prop:seed`: the points where a C² map is an immersion of full
normal rank form an open set. No common normal subspace is postulated. -/
theorem isOpen_fullNormalRank_immersionDomain {n N : ℕ}
    {F : Euclidean n → Euclidean N} {s : Set (Euclidean n)}
    (hs : IsOpen s) (hF : ContDiffOn ℝ 2 F s) :
    IsOpen {x | x ∈ immersionDomain F s ∧
      Set.range (normalMap F x) = (normalSpace F x : Set (Euclidean N))} := by
  rw [isOpen_iff_mem_nhds]
  rintro x ⟨⟨hx, himm⟩, hrank⟩
  obtain ⟨ε, hε, _, _, hsub, hi, hr, _⟩ :=
    exists_ball_geometric_normal_rank_and_gap hs hF hx himm hrank
  exact Metric.mem_nhds_iff.mpr ⟨ε, hε, fun y hy ↦ ⟨⟨hsub hy, hi y hy⟩, hr y hy⟩⟩

end JanetCartan.NormalRankStability
