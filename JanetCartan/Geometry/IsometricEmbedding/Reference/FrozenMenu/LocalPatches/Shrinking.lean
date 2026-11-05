module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.Basic
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.ChordEstimates
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.CubeGeometry
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.UniformBounds
public import JanetCartan.Geometry.IsometricEmbedding.Reference.FrozenMenu.LocalPatches.Shrinking.Regularity

/-!
# Quantitative shrinking of a characteristic chart

Step 3 of `app:ch_seed:prop:seed-frozen-menu`, including the projected chord
estimate `app:ch_seed:eq:seed-frozen-chord`. Continuity and finiteness allow one
cube to satisfy all geometric and analytic estimates simultaneously.
-/

@[expose] public noncomputable section

open Filter Set
open scoped ContDiff Topology
namespace JanetCartan.FrozenMenu
open CubeCarrier

/-- Shrinking any smooth characteristic chart with the prescribed admissible
first derivative gives every frozen-patch estimate and a positive incidence
first-parameter derivative bound (`app:ch_seed:prop:seed-frozen-menu`, Step 3,
and `app:ch_seed:eq:seed-frozen-chord`). -/
theorem exists_valid_patch_of_characteristic_chart {n : ℕ} (hn : 5 ≤ n)
    {k s ξ : Euclidean n} (h : CarrierSeed k s ξ)
    {A : Euclidean 3 →L[ℝ] Euclidean n} (hA : IsAdmissibleFrame k ξ A)
    {f : Euclidean 3 → Euclidean n} {U : Set (Euclidean 3)}
    (hU : IsOpen U) (h0 : (0 : Euclidean 3) ∈ U)
    (hf : ContDiffOn ℝ ∞ f U) (hf0 : f 0 = ξ) (hdf0 : fderiv ℝ f 0 = A)
    (hchar : ∀ z ∈ U, cubeDeterminant (f z) = 0) :
    ∃ ρ c C : ℝ, (Patch.mk ρ f).IsValid c C ∧
      (∀ z ∈ parameterCube ρ,
        c ≤ |fderiv ℝ (fun w ↦ incidence k (f w)) z (EuclideanSpace.single 0 1)|) ∧
      parameterInterior (2 * ρ) ⊆ U := by
  classical
  have hξ : ξ ≠ 0 := by
    intro hz
    exact h.coordinates_ne_zero ⟨0, by omega⟩ (by simp [hz])
  have hξpos : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  obtain ⟨γ, hγ, hgap⟩ := h.exists_pos_badDirectionGap hn
  obtain ⟨a, ha, hlinear⟩ := hA.exists_uniform_lower_bound
  let δ := min (‖ξ‖ / 2) (‖ξ‖ * γ / 4)
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδnorm : δ < ‖ξ‖ := (min_le_left _ _).trans_lt (by linarith)
  have hδgap : 2 * δ ≤ ‖ξ‖ * (γ / 2) := by
    have := min_le_right (‖ξ‖ / 2) (‖ξ‖ * γ / 4)
    dsimp [δ]
    linarith
  have hf_at : ContDiffAt ℝ ∞ f 0 := hf.contDiffAt (hU.mem_nhds h0)
  have hfc : ContinuousAt f 0 := hf_at.continuousAt
  have hdc : ContinuousAt (fderiv ℝ f) 0 := hf_at.continuousAt_fderiv (by simp)
  have hnormal := contDiffAt_normal_of_coordinates_ne_zero h.coordinates_ne_zero
  have hinc := contDiffAt_incidence_of_coordinates_ne_zero k h.coordinates_ne_zero
  let g := fun w ↦ incidence k (f w)
  have hg_at : ContDiffAt ℝ ∞ g 0 := by
    have hi : ContDiffAt ℝ ∞ (incidence k) (f 0) := by
      simpa only [hf0] using hinc
    simpa only [g, Function.comp_def] using hi.comp 0 hf_at
  have hdg0 : fderiv ℝ g 0 = (fderiv ℝ (incidence k) ξ).comp A := by
    have hi : DifferentiableAt ℝ (incidence k) (f 0) := by
      simpa only [hf0] using hinc.differentiableAt (by simp)
    simpa only [g, Function.comp_def, hf0, hdf0] using fderiv_comp 0 hi (hf_at.differentiableAt (by simp))
  let b := |fderiv ℝ g 0 (EuclideanSpace.single 0 1)|
  have hb : 0 < b := by
    dsimp [b]
    rw [hdg0]
    exact abs_pos.mpr hA.2.1
  have hcoord_event : ∀ᶠ z in 𝓝 (0 : Euclidean 3), ∀ i, f z i ≠ 0 := by
    apply eventually_all.mpr
    intro i
    exact ((PiLp.continuous_apply 2 _ i).continuousAt.comp hfc).eventually_ne
      (by simpa only [Function.comp_apply, hf0] using h.coordinates_ne_zero i)
  have hnormal_event : ∀ᶠ z in 𝓝 (0 : Euclidean 3), normal (f z) ≠ 0 := by
    have hc : ContinuousAt (fun z ↦ normal (f z)) 0 := by
      have hc : ContinuousAt normal (f 0) := by
        simpa only [hf0] using hnormal.continuousAt
      simpa only [Function.comp_def] using hc.comp hfc
    exact hc.eventually_ne (by simpa only [hf0] using h.normal_ne_zero)
  have hclose_event : ∀ᶠ z in 𝓝 (0 : Euclidean 3), ‖f z - ξ‖ < δ := by
    apply ((hfc.sub continuousAt_const).norm).eventually_lt continuousAt_const
    simpa only [Pi.sub_apply, hf0, sub_self, norm_zero] using hδpos
  have hsize_event : ∀ᶠ z in 𝓝 (0 : Euclidean 3),
      ‖ξ‖ / 2 < ‖f z‖ ∧ ‖f z‖ < ‖ξ‖ + 1 := by
    apply Filter.Eventually.and
    · exact continuousAt_const.eventually_lt hfc.norm (by rw [hf0]; linarith)
    · exact hfc.norm.eventually_lt continuousAt_const (by rw [hf0]; linarith)
  have hderiv_event : ∀ᶠ z in 𝓝 (0 : Euclidean 3), ‖fderiv ℝ f z‖ < ‖A‖ + 1 :=
    hdc.norm.eventually_lt continuousAt_const (by rw [hdf0]; linarith)
  have hproj_event : ∀ᶠ z in 𝓝 (0 : Euclidean 3), ∀ L ∈ cubeBadSubspaces n,
      ‖Lᗮ.orthogonalProjectionOnto.comp (fderiv ℝ f z) -
        Lᗮ.orthogonalProjectionOnto.comp A‖ < a / 2 := by
    have hev (L : ↥(cubeBadSubspaces n)) : ∀ᶠ z in 𝓝 (0 : Euclidean 3),
        ‖L.valᗮ.orthogonalProjectionOnto.comp (fderiv ℝ f z) -
          L.valᗮ.orthogonalProjectionOnto.comp A‖ < a / 2 := by
      apply ((continuousAt_const.clm_comp hdc).sub continuousAt_const).norm.eventually_lt
        continuousAt_const
      simpa only [Pi.sub_apply, hdf0, sub_self, norm_zero] using half_pos ha
    filter_upwards [eventually_all.mpr hev] with z hz L hL
    exact hz ⟨L, hL⟩
  have hinc_event : ∀ᶠ z in 𝓝 (0 : Euclidean 3),
      b / 2 < |fderiv ℝ g z (EuclideanSpace.single 0 1)| := by
    apply continuousAt_const.eventually_lt
      (((hg_at.continuousAt_fderiv (by simp)).clm_apply continuousAt_const).abs)
    exact half_lt_self hb
  obtain ⟨ρ, hρ, hshrink⟩ := exists_parameterCube_subset_nhds
    (show {z | z ∈ U ∧ (∀ i, f z i ≠ 0) ∧ normal (f z) ≠ 0 ∧
      ‖f z - ξ‖ < δ ∧ (‖ξ‖ / 2 < ‖f z‖ ∧ ‖f z‖ < ‖ξ‖ + 1) ∧
      ‖fderiv ℝ f z‖ < ‖A‖ + 1 ∧
      (∀ L ∈ cubeBadSubspaces n, ‖Lᗮ.orthogonalProjectionOnto.comp (fderiv ℝ f z) -
        Lᗮ.orthogonalProjectionOnto.comp A‖ < a / 2) ∧
      b / 2 < |fderiv ℝ g z (EuclideanSpace.single 0 1)|} ∈ 𝓝 0 from
      Filter.inter_mem (hU.mem_nhds h0) (hcoord_event.and (hnormal_event.and
        (hclose_event.and (hsize_event.and (hderiv_event.and (hproj_event.and hinc_event)))))))
  have hcube {z : Euclidean 3} (hz : z ∈ parameterCube ρ) :
      z ∈ parameterCube (2 * ρ) := fun i ↦ (hz i).trans (by linarith)
  have hinterior : parameterInterior (2 * ρ) ⊆ U := by
    intro z hz
    exact (hshrink (fun i ↦ (hz i).le)).1
  have hsub : parameterCube ρ ⊆ U := fun _ hz ↦ (hshrink (hcube hz)).1
  have hdiff (z : Euclidean 3) (hz : z ∈ parameterCube ρ) :
      HasFDerivAt f (fderiv ℝ f z) z :=
    ((hf.contDiffAt (hU.mem_nhds (hsub hz))).differentiableAt (by simp)).hasFDerivAt
  let c := min (min (‖ξ‖ / 2) (γ / 2)) (min (a / 2) (b / 2))
  let C := max (‖ξ‖ + 1) (‖A‖ + 1)
  have hc : 0 < c := lt_min (lt_min (half_pos hξpos) (half_pos hγ))
    (lt_min (half_pos ha) (half_pos hb))
  have hc_norm : c ≤ ‖ξ‖ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hc_gap : c ≤ γ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hc_chord : c ≤ a / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hc_inc : c ≤ b / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hC_norm : ‖ξ‖ + 1 ≤ C := le_max_left _ _
  have hC_chord : ‖A‖ + 1 ≤ C := le_max_right _ _
  have hC : 0 < C := (by positivity : 0 < ‖ξ‖ + 1).trans_le hC_norm
  have hsums {z w : Euclidean 3} (hz : z ∈ parameterCube ρ)
      (hw : w ∈ parameterCube ρ) :
      f z + f w ≠ 0 ∧ BadDirectionGap (γ / 2) (f z + f w) :=
    same_patch_sum_gap hξ hgap hδnorm hδgap
      (hshrink (hcube hz)).2.2.2.1.le (hshrink (hcube hw)).2.2.2.1.le
  refine ⟨ρ, c, C, ?_, ?_, hinterior⟩
  · refine ⟨hρ, hc, hC, hf.mono hinterior, ?_, ?_⟩
    · intro z hz
      obtain ⟨hzU, hzcoord, hznormal, _, hzsize, _, _, _⟩ := hshrink (hcube hz)
      refine ⟨hzcoord, hchar z hzU, pencil_rank_of_characteristic hn hzcoord (hchar z hzU),
        hznormal, hc_norm.trans hzsize.1.le, hzsize.2.le.trans hC_norm, ?_⟩
      have hgz := (hsums hz hz).2
      have heq : NormedSpace.normalize (f z + f z) = NormedSpace.normalize (f z) := by
        rw [← two_smul ℝ (f z), NormedSpace.normalize_smul_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (show BadDirectionGap (γ / 2) (f z) from fun L hL ↦ by
        simpa only [heq] using hgz L hL).mono hc_gap
    · intro z hz w hw
      refine ⟨?_, ?_, (hsums hz hw).1, ((hsums hz hw).2).mono hc_gap⟩
      · intro L hL
        have hp (x : Euclidean 3) (hx : x ∈ parameterCube ρ) :
            HasFDerivWithinAt (fun t ↦ Lᗮ.orthogonalProjectionOnto (f t))
              (Lᗮ.orthogonalProjectionOnto.comp (fderiv ℝ f x)) (parameterCube ρ) x :=
          (Lᗮ.orthogonalProjectionOnto.hasFDerivAt.comp x (hdiff x hx)).hasFDerivWithinAt
        have he := half_lower_chord_bound (convex_parameterCube ρ) hp
          (Lᗮ.orthogonalProjectionOnto.comp A) (hlinear L hL)
          (fun x hx ↦ ((hshrink (hcube hx)).2.2.2.2.2.2.1 L hL).le) hw hz
        rw [← map_sub] at he
        exact (mul_le_mul_of_nonneg_right hc_chord (norm_nonneg _)).trans he
      · have he := (convex_parameterCube ρ).norm_image_sub_le_of_norm_hasFDerivWithin_le
          (fun x hx ↦ (hdiff x hx).hasFDerivWithinAt)
          (fun x hx ↦ (hshrink (hcube hx)).2.2.2.2.2.1.le) hw hz
        exact he.trans (mul_le_mul_of_nonneg_right hC_chord (norm_nonneg _))
  · intro z hz
    exact hc_inc.trans (hshrink (hcube hz)).2.2.2.2.2.2.2.le

end JanetCartan.FrozenMenu
