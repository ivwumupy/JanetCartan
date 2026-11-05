module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.RootQuantitative.Cylinder

/-!
# Common bounds for the continued incidence family

The actual low root predicate supplies every equation, scalar gap and graph
containment needed by the finite-cylinder estimate. The full three-parameter
roots are the same affine lifts used in the detector.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers
open HamiltonPhase FrozenMenu ProjectedStressFrame CurrentFullPhase

/-- The fixed first-parameter direction used in the actual root lift
(`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
def incidenceParameterLinearMap : ℝ →L[ℝ] Euclidean 3 :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single 0 1)

/-- The distinguished parameter direction has unit operator norm
(`app:ch_seed:eq:seed-phase-tame`). -/
theorem norm_incidenceParameterLinearMap_le : ‖incidenceParameterLinearMap‖ ≤ 1 := by
  simp [incidenceParameterLinearMap, EuclideanSpace.single, PiLp.norm_single]

private theorem cNorm_incidence_linearMap_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} (hs : IsCompact s)
    (L : ℝ →L[ℝ] Euclidean 3) (g : E → ℝ) (m : ℕ)
    (hg : ∀ p ∈ s, ContDiffAt ℝ m g p) :
    cNorm s m (L ∘ g) ≤ ‖L‖ * cNorm s m g := by
  simp only [cNorm, Finset.mul_sum]
  apply cNorm_le_sum_of_bounds
    (fun j _ ↦ mul_nonneg (norm_nonneg _) (sSup_norm_iteratedFDeriv_nonneg s j g))
  intro j hj p hp
  apply (L.norm_iteratedFDeriv_comp_left (hg p hp) (by exact_mod_cast hj)).trans
  exact mul_le_mul_of_nonneg_left
    (le_csSup (bddAbove_norm_iteratedFDeriv_of_contDiffAt hs hg hj)
      (mem_image_of_mem _ hp)) (norm_nonneg _)

/-- The full incidence parameter vector inherits the scalar root bound via
its literal fixed affine lift (`app:ch_seed:eq:seed-phase-tame`). -/
theorem cNorm_incidenceParameter_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} (hs : IsCompact s) (z : Euclidean 3) (g : E → ℝ) (m : ℕ)
    (hg : ∀ p ∈ s, ContDiffAt ℝ m g p) :
    cNorm s m (fun p ↦ incidenceParameter z (g p)) ≤
      cNorm s m (fun _ : E ↦ z) + (m + 1) * cNorm s m g := by
  have hLg : ∀ p ∈ s, ContDiffAt ℝ m (incidenceParameterLinearMap ∘ g) p :=
    fun p hp ↦ incidenceParameterLinearMap.contDiff.contDiffAt.comp p (hg p hp)
  have heq : (fun p ↦ incidenceParameter z (g p)) =
      (fun _ : E ↦ z) + incidenceParameterLinearMap ∘ g := by funext p; rfl
  rw [heq]
  apply (cNorm_add_le_of_contDiffAt hs (fun _ _ ↦ contDiffAt_const) hLg).trans
  apply add_le_add le_rfl
  apply (cNorm_incidence_linearMap_le hs incidenceParameterLinearMap g m hg).trans
  apply mul_le_mul_of_nonneg_right _ (cNorm_nonneg s m g)
  exact norm_incidenceParameterLinearMap_le.trans (by linarith [Nat.cast_nonneg (α := ℝ) m])

/-- One common positive frame threshold and all-order constants for the
SAME continued roots. Graph containment and scalar gaps are extracted from
the proved low root family; all coefficient budgets come from the projected
immersion (`app:ch_seed:eq:seed-phase-tame`). -/
theorem exists_projected_rootFamily_bound {n N : ℕ} {D : CoverData n}
    {c C : ℝ} (hD : D.IsValid c C)
    {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : (i : (j : Fin D.chartCount) × Fin (D.patchCount j)) →
      PatchQuantitativeFamily (D.patches i.1 i.2) U hU)
    {R : IncidenceRefinement D} (hR : R.IsValid)
    {r : ℝ} (hr : 0 < r) (hradius : ∀ i, 3 * r < (T i).physicalRadius)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : ∀ i, closedBall (0 : Euclidean n) (T i).data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ cr : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) (hcr : 0 < cr) :
    ∃ δ > (0 : ℝ), ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) < δ) →
        ∀ hlow : ∀ i, cNorm (closedBall (0 : Euclidean n)
          (T i).data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < (T i).family.threshold,
        let hQ := contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
        ∀ (g : (j : Fin R.chartCount) → Fin (D.patchCount (R.sourceChart j)) →
          Euclidean n × Euclidean n → ℝ) (B ε : ℝ),
        IsConstructedIncidenceRootFamily D R r cr B ε (projectedStress F)
          (fun j a ↦ (T ⟨j, a⟩).carrier ⟨projectedStress F, hQ, hlow ⟨j, a⟩⟩) g →
        ∀ m j a,
          cNorm (closedBall (0 : Euclidean n) (2 * r) ×ˢ closedBall (R.center j) (R.radius j))
            m (g j a) ≤ A m * (1 + cNorm K (m + 6) F) ∧
          cNorm (closedBall (0 : Euclidean n) (2 * r) ×ˢ closedBall (R.center j) (R.radius j))
            m (fun p ↦ incidenceParameter (D.roots (R.sourceChart j) a (R.center j)) (g j a p)) ≤
              A m * (1 + cNorm K (m + 6) F) := by
  classical
  let I := (j : Fin R.chartCount) × Fin (D.patchCount (R.sourceChart j))
  let s (j : Fin R.chartCount) :=
    closedBall (0 : Euclidean n) (2 * r) ×ˢ closedBall (R.center j) (R.radius j)
  let V (j : Fin R.chartCount) :=
    ball (0 : Euclidean n) (3 * r) ×ˢ ball (R.center j) (2 * R.radius j)
  have hV (j) : IsOpen (V j) := isOpen_ball.prod isOpen_ball
  have hsV (j) : s j ⊆ V j := Set.prod_mono
    (closedBall_subset_ball (by linarith)) (closedBall_subset_ball (by linarith [hR.1 j]))
  choose d hd A hA hb using fun i : I ↦
    (T ⟨R.sourceChart i.1, i.2⟩).exists_projected_cylinder_root_bound (N := N)
      (hD.2.2.2.2.1 _ _).1 r (by linarith [hradius ⟨R.sourceChart i.1, i.2⟩])
      (R.center i.1) (R.radius i.1) (R.halfWidth i.1 i.2)
      (D.roots (R.sourceChart i.1) i.2 (R.center i.1))
      (hR.2.2.2 i.1 i.2).2.2.2.1 hK hKU (hball _) C₀ hκmet hκ hcr
  obtain ⟨d₀, hd₀, hd₀i⟩ := Pi.exists_forall_pos_add_lt hd
  let Z (i : I) (m : ℕ) := cNorm (s i.1) m
    (fun _ : Euclidean n × Euclidean n ↦ D.roots (R.sourceChart i.1) i.2 (R.center i.1))
  let E (i : I) (m : ℕ) := 1 + Z i m + (m + 2) * A i m
  have hE (i : I) (m : ℕ) : 0 < E i m := by
    have hz := cNorm_nonneg (s i.1) m
      (fun _ : Euclidean n × Euclidean n ↦ D.roots (R.sourceChart i.1) i.2 (R.center i.1))
    have ha := hA i m
    dsimp only [E, Z]
    positivity
  let H (m : ℕ) := 1 + ∑ i : I, E i m
  have hH (m) : 0 < H m := by
    have hs := Finset.sum_nonneg (s := (Finset.univ : Finset I)) (fun i _ ↦ (hE i m).le)
    change 0 < 1 + ∑ i : I, E i m
    linarith
  have hEH (i : I) (m) : E i m ≤ H m := by
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset I))
      (fun i _ ↦ (hE i m).le) (Finset.mem_univ i)
    change E i m ≤ 1 + ∑ i : I, E i m
    linarith
  refine ⟨d₀ / 14, by positivity, H, hH, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hclose hlow
  dsimp only
  intro g B ε hg m j a
  have hs : ContDiffOn ℝ ∞ (projectedStress F) U :=
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank)
  have hreg : ∀ x ∈ K, ContDiffAt ℝ 6 (projectedStress F - fun _ ↦ cubeStress n) x :=
    fun x hx ↦ ((hs.contDiffAt (hU.mem_nhds (hKU hx))).sub contDiffAt_const).of_le (by simp)
  have hglobal : cNorm K 6 (projectedStress F - fun _ ↦ cubeStress n) < d₀ := by
    apply frame_cNorm_lt_of_componentwise hK hreg hd₀
    convert hclose using 1; norm_num
  have hlocal : cNorm (closedBall (0 : Euclidean n)
      (T ⟨R.sourceChart j, a⟩).data.localReference.stateRadius) 6
      (projectedStress F - fun _ ↦ cubeStress n) < d ⟨j, a⟩ :=
    (cNorm_mono_set_of_contDiffAt (hball _) hK hreg).trans_lt
      (hglobal.trans (by simpa using hd₀i ⟨j, a⟩))
  have hb' := hb ⟨j, a⟩ F hF hi hrank hlowF hmet hnormal (hlow _) hlocal
    (V j) (hV j) (hsV j) (g j a) (hg j a).1
    (fun p hp ↦ ((hg j a).2.2.1 p hp).2.2.2.2.1)
    (fun p hp ↦ ⟨((hg j a).2.2.1 p (hsV j hp)).1.1.le,
      ((hg j a).2.2.1 p (hsV j hp)).1.2.le⟩)
    (fun p hp ↦ ((hg j a).2.2.1 p (hsV j hp)).2.2.2.2.2.1) m
  have hZ := cNorm_nonneg (s j) m
    (fun _ : Euclidean n × Euclidean n ↦ D.roots (R.sourceChart j) a (R.center j))
  have hAF := hA ⟨j, a⟩ m
  have hFnonneg := cNorm_nonneg K (m + 6) F
  have hAE : A ⟨j, a⟩ m ≤ E ⟨j, a⟩ m := by
    dsimp only [E, Z]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith only [hZ, hAF, hm]
  refine ⟨hb'.trans (mul_le_mul_of_nonneg_right
    (hAE.trans (hEH ⟨j, a⟩ m)) (by positivity)), ?_⟩
  have hp := cNorm_incidenceParameter_le ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
    (D.roots (R.sourceChart j) a (R.center j)) (g j a) m
    (fun p hp ↦ ((hg j a).1.contDiffAt ((hV j).mem_nhds (hsV j hp))).of_le (by simp))
  apply hp.trans
  apply le_trans _ (mul_le_mul_of_nonneg_right (hEH ⟨j, a⟩ m) (by positivity))
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  change _ ≤ (1 + Z ⟨j, a⟩ m + (m + 2) * A ⟨j, a⟩ m) * _
  dsimp only [Z, s] at *
  have hmul := mul_le_mul_of_nonneg_left hb' (show (0 : ℝ) ≤ m + 1 by positivity)
  nlinarith only [hmul, hZ, hAF, hFnonneg, mul_nonneg hZ hFnonneg]

end JanetCartan.ActualCarriers
