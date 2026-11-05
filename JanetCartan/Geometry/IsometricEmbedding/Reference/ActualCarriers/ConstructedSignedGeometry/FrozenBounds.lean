module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Assembly
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PhaseAssembly.Buffers
public import JanetCartan.Geometry.IsometricEmbedding.Reference.SignedPairs

/-!
# Quantitative frozen bounds for every literal signed pair

The normalized radial separation in `app:ch_seed:prop:seed-frozen-menu`
is converted to unnormalized bounds by compactness. These are the frozen
inputs to the constructed-carrier application of `signed_family_stability`
in Step 2 of `app:ch_seed:prop:seed-actual-menu`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff
namespace JanetCartan.ActualCarriers.ConstructedSignedGeometry
open FrozenMenu SignedPairs

/-- The literal parameter cube assigned to a full group. Assignments need not
be injective (`app:rem:exhaustive-signed-pairs`). -/
def groupCube {n : ℕ} (D : CoverData n) {G : Type*}
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (g : G) : Set (Euclidean 3) :=
  parameterCube (D.patches (assign g).1 (assign g).2).radius

/-- The frozen gradient with its fixed radial label; duplicate patch
specifications retain distinct group indices (`app:rem:exhaustive-signed-pairs`). -/
def frozenGroup {n : ℕ} (D : CoverData n) {G : Type*}
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b))
    (R : G → ℝ) (g : G) (z : Euclidean 3) : Euclidean n :=
  R g • (D.patches (assign g).1 (assign g).2).toFun z

private theorem projected_lower_of_gap {n : ℕ} {v : Euclidean n} {a d : ℝ}
    (ha : a ≤ ‖v‖) (hd : 0 ≤ d) (hg : BadDirectionGap d v)
    {L : Submodule ℝ (Euclidean n)} (hL : L ∈ cubeBadSubspaces n) :
    a * d ≤ ‖projectAway L v‖ := by
  rw [norm_project_eq_mul_normalize]
  apply mul_le_mul ha _ hd (norm_nonneg _)
  exact hg L hL

/-- Fixed radial labels and positive quantitative bounds for every `Pair`
constructor, derived from the frozen menu. Compactness supplies the missing
unnormalized sum and cross-pair bounds. The difference estimate retains its
exact parameter distance, and empty group families are allowed
(`app:ch_seed:prop:seed-actual-menu`, Step 2;
`app:rem:exhaustive-signed-pairs`). -/
theorem exists_frozen_signed_pair_bounds {n : ℕ} {D : CoverData n} {c C : ℝ}
    (hD : D.IsValid c C) (G : Type*) [Finite G]
    (assign : G → (b : Fin D.chartCount) × Fin (D.patchCount b)) :
    ∃ R : G → ℝ, (∀ g, 1 ≤ R g) ∧ Function.Injective R ∧
      ∃ a A : ℝ, 0 < a ∧ 0 < A ∧
        (∀ q : Pair G (Euclidean 3) (groupCube D assign),
          ∀ L ∈ cubeBadSubspaces n,
            a * q.beat ≤ ‖projectAway L (q.vector (frozenGroup D assign R))‖) ∧
        (∀ q : Pair G (Euclidean 3) (groupCube D assign),
          ‖q.vector (frozenGroup D assign R)‖ ≤ A * q.beat) := by
  classical
  let := Fintype.ofFinite G
  have hc := hD.1
  have hC := hD.2.1
  obtain ⟨R, hR, hinj, hsep⟩ := hD.hasRadialSeparation G
  let P (i : G) := D.patches (assign i).1 (assign i).2
  let f := frozenGroup D assign R
  have hP (i : G) : (P i).IsValid c C := (hD.2.2.2.2.1 _ _).1
  have hRp (i : G) : 0 < R i := zero_lt_one.trans_le (hR i)
  have hs (i : G) : ContinuousOn (f i) (groupCube D assign i) := by
    exact ((hP i).2.2.2.1.continuousOn.mono
      (parameterCube_subset_doubledInterior (hP i).1)).const_smul (R i)
  have hplus (i j : G) (z w : Euclidean 3)
      (hz : z ∈ groupCube D assign i) (hw : w ∈ groupCube D assign j) :
      f i z + f j w ≠ 0 ∧ BadDirectionGap (c / 2) (f i z + f j w) := by
    by_cases hij : i = j
    · subst j
      obtain ⟨_, _, hn, hg⟩ := (hP i).2.2.2.2.2 z hz w hw
      refine ⟨?_, ?_⟩
      · simpa only [f, frozenGroup, P, smul_add] using smul_ne_zero (hRp i).ne' hn
      · have hh := hg.smul_pos (hRp i)
        intro L hL
        exact (by linarith [hD.1] : c / 2 ≤ c).trans
          (by simpa only [f, frozenGroup, P, smul_add] using hh L hL)
    · exact (hsep i j hij _ _ _ _ z hz w hw).2.2
  have hminus (i j : G) (hij : i ≠ j) (z w : Euclidean 3)
      (hz : z ∈ groupCube D assign i) (hw : w ∈ groupCube D assign j) :
      f i z - f j w ≠ 0 ∧ BadDirectionGap (c / 2) (f i z - f j w) :=
    (hsep i j hij _ _ _ _ z hz w hw).imp_right And.left
  have hlocal (p : G × G) : ∃ d > (0 : ℝ),
      ∀ z ∈ groupCube D assign p.1, ∀ w ∈ groupCube D assign p.2,
        d ≤ ‖f p.1 z + f p.2 w‖ ∧
          (p.1 ≠ p.2 → d ≤ ‖f p.1 z - f p.2 w‖) := by
    have hk := (isCompact_parameterCube (P p.1).radius).prod
      (isCompact_parameterCube (P p.2).radius)
    have hcont₁ : ContinuousOn (fun v : Euclidean 3 × Euclidean 3 ↦ f p.1 v.1)
        (groupCube D assign p.1 ×ˢ groupCube D assign p.2) :=
      (hs p.1).comp continuousOn_fst (fun _ h ↦ h.1)
    have hcont₂ : ContinuousOn (fun v : Euclidean 3 × Euclidean 3 ↦ f p.2 v.2)
        (groupCube D assign p.1 ×ˢ groupCube D assign p.2) :=
      (hs p.2).comp continuousOn_snd (fun _ h ↦ h.2)
    obtain ⟨a, ha, hb⟩ := hk.exists_forall_le' (hcont₁.add hcont₂).norm
      (fun v hv ↦ norm_pos_iff.mpr (hplus _ _ _ _ hv.1 hv.2).1)
    by_cases hij : p.1 = p.2
    · exact ⟨a, ha, fun z hz w hw ↦ ⟨hb (z, w) ⟨hz, hw⟩, fun h ↦ (h hij).elim⟩⟩
    · obtain ⟨b, hbpos, hbound⟩ := hk.exists_forall_le' (hcont₁.sub hcont₂).norm
        (fun v hv ↦ norm_pos_iff.mpr (hminus _ _ hij _ _ hv.1 hv.2).1)
      exact ⟨min a b, lt_min ha hbpos, fun z hz w hw ↦
        ⟨(min_le_left _ _).trans (hb (z, w) ⟨hz, hw⟩),
          fun _ ↦ (min_le_right _ _).trans (hbound (z, w) ⟨hz, hw⟩)⟩⟩
  choose d hd hbound using hlocal
  obtain ⟨_, m, _, _, _, hm, _, hmin⟩ := exists_common_phase_buffers
    (fun _ : G × G ↦ (1 : ℝ)) d (fun _ ↦ (1 : ℝ)) (fun _ ↦ zero_lt_one) hd
  obtain ⟨_, _, B, _, _, _, hB, hmax⟩ := exists_common_phase_buffers
    (fun _ : G ↦ (1 : ℝ)) (fun _ ↦ (1 : ℝ)) R
    (fun _ ↦ zero_lt_one) (fun _ ↦ zero_lt_one)
  have hsum (i j : G) (z w : Euclidean 3)
      (hz : z ∈ groupCube D assign i) (hw : w ∈ groupCube D assign j)
      (L : Submodule ℝ (Euclidean n)) (hL : L ∈ cubeBadSubspaces n) :
      m * (c / 2) ≤ ‖projectAway L (f i z + f j w)‖ :=
    projected_lower_of_gap ((hmin (i, j)).2.1.trans (hbound (i, j) z hz w hw).1)
      (by positivity) (hplus i j z w hz hw).2 hL
  have hsub (i j : G) (hij : i ≠ j) (z w : Euclidean 3)
      (hz : z ∈ groupCube D assign i) (hw : w ∈ groupCube D assign j)
      (L : Submodule ℝ (Euclidean n)) (hL : L ∈ cubeBadSubspaces n) :
      m * (c / 2) ≤ ‖projectAway L (f i z - f j w)‖ :=
    projected_lower_of_gap ((hmin (i, j)).2.1.trans ((hbound (i, j) z hz w hw).2 hij))
      (by positivity) (hminus i j hij z w hz hw).2 hL
  have hnorm (i : G) (z : Euclidean 3) (hz : z ∈ groupCube D assign i) :
      ‖f i z‖ ≤ B * C := by
    change ‖R i • (P i).toFun z‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hRp i)]
    exact mul_le_mul ((hmax i).2.2) ((hP i).2.2.2.2.1 z hz).2.2.2.2.2.1
      (norm_nonneg _) hB.le
  refine ⟨R, hR, hinj, min c (m * (c / 2)), 2 * B * C,
    lt_min hD.1 (mul_pos hm (half_pos hD.1)), by positivity, ?_, ?_⟩
  · intro q L hL
    cases q with
    | difference i z w hne =>
      change min c (m * (c / 2)) * ‖(z : Euclidean 3) - w‖ ≤
        ‖projectAway L (R i • (P i).toFun z - R i • (P i).toFun w)‖
      rw [← smul_sub, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (hRp i)]
      have hh := ((hP i).2.2.2.2.2 z z.property w w.property).1 L hL
      calc
        _ ≤ c * ‖(z : Euclidean 3) - w‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
        _ ≤ ‖projectAway L ((P i).toFun z - (P i).toFun w)‖ := hh
        _ ≤ _ := le_mul_of_one_le_left (norm_nonneg _) (hR i)
    | sum i z w =>
      simpa only [Pair.beat, Pair.vector, mul_one] using
        (min_le_right c (m * (c / 2))).trans (hsum i i z w z.property w.property L hL)
    | cross i j hij z w s t hs ht =>
      have hp := (min_le_right c (m * (c / 2))).trans
        (hsum i j z w z.property w.property L hL)
      have hm' := (min_le_right c (m * (c / 2))).trans
        (hsub i j hij z w z.property w.property L hL)
      rcases (abs_eq zero_le_one).mp hs with rfl | rfl <;>
        rcases (abs_eq zero_le_one).mp ht with rfl | rfl
      · simpa only [Pair.vector, Pair.beat, mul_one, one_smul] using hp
      · simpa only [Pair.vector, Pair.beat, mul_one, one_smul, neg_smul,
          ← sub_eq_add_neg] using hm'
      · simpa only [Pair.vector, Pair.beat, mul_one, one_smul, neg_smul,
          neg_add_eq_sub] using (min_le_right c (m * (c / 2))).trans
            (hsub j i hij.symm w z w.property z.property L hL)
      · simpa only [Pair.vector, Pair.beat, mul_one, one_smul, neg_smul,
          ← neg_add, map_neg, norm_neg] using hp
  · intro q
    cases q with
    | difference i z w hne =>
      change ‖R i • (P i).toFun z - R i • (P i).toFun w‖ ≤
        2 * B * C * ‖(z : Euclidean 3) - w‖
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (hRp i)]
      have hh := ((hP i).2.2.2.2.2 z z.property w w.property).2.1
      calc
        _ ≤ B * (C * ‖(z : Euclidean 3) - w‖) :=
          mul_le_mul (hmax i).2.2 hh (norm_nonneg _) hB.le
        _ ≤ _ := by
          nlinarith [mul_nonneg (mul_nonneg hB.le hD.2.1.le)
            (norm_nonneg ((z : Euclidean 3) - w))]
    | sum i z w =>
      change ‖f i z + f i w‖ ≤ 2 * B * C * 1
      have hh := (norm_add_le (f i z) (f i w)).trans
        (add_le_add (hnorm i z z.property) (hnorm i w w.property))
      nlinarith
    | cross i j hij z w s t hs ht =>
      change ‖s • f i z + t • f j w‖ ≤ 2 * B * C * 1
      have hh := norm_add_le (s • f i z) (t • f j w)
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hs, ht,
        one_mul, one_mul] at hh
      have hh' := hh.trans (add_le_add (hnorm i z z.property) (hnorm j w w.property))
      nlinarith

end JanetCartan.ActualCarriers.ConstructedSignedGeometry
