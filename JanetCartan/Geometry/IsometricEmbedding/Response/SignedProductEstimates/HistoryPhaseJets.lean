module
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.NormalizedPhases
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.HistoryPrimaryPhaseJets
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.RetainedFactors.PrimaryRepresentative

/-!
# Mixed phase jets from the original admissible history

The divided-difference estimate in `app:ch_pairs:setup:pairs-lag` needs one
parameter derivative of every spatial phase jet. Restriction of the original
joint jet costs only one additional derivative. The existing primary-phase
history producer has reserve two, which pays this derivative while preserving
`L^(m-1)`. The SAME retained representative and extended projected stress are
used, with constants before the initial scale and finite history.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.SignedProductEstimates
open Pseudodifferential
variable {n : ℕ}

/-- The physical jet is the original joint jet restricted to spatial
vectors (`app:ch_pairs:setup:pairs-lag`). No parameter or phase is changed. -/
private theorem spatial_phase_jet_eq_joint_restriction
    (f : Euclidean n × Euclidean 3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (r : ℕ) (x : Euclidean n) (z : Euclidean 3) :
    iteratedFDeriv ℝ r (fun y ↦ f (y, z)) x =
      (iteratedFDeriv ℝ r f (x, z)).compContinuousLinearMap
        (fun _ ↦ (ContinuousLinearMap.id ℝ (Euclidean n)).prod (0 : Euclidean n →L[ℝ] Euclidean 3)) := by
  let L : Euclidean n →L[ℝ] Euclidean n × Euclidean 3 := (ContinuousLinearMap.id ℝ _).prod 0
  have h := L.iteratedFDeriv_comp_right (f := fun q ↦ f ((0, z) + q)) (hf.comp (contDiff_const.add contDiff_id)) x
    (i := r) (by simp : (r : ℕ∞ω) ≤ ∞)
  simpa only [Function.comp_def, iteratedFDeriv_comp_add_left', L,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    zero_apply, Prod.mk_add_mk, zero_add, add_zero] using h

/-- The spatial phase jet is smooth in the original parameter
(`app:ch_pairs:setup:pairs-lag`). This supplies the differentiability premise
of `sourceGeometry_normalized_signed_pair` for the retained representative. -/
theorem contDiff_parameter_spatial_phase_jet
    (f : Euclidean n × Euclidean 3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (r : ℕ) (x : Euclidean n) :
    ContDiff ℝ ∞ (fun z ↦ iteratedFDeriv ℝ r (fun y ↦ f (y, z)) x) := by
  let L : Euclidean n →L[ℝ] Euclidean n × Euclidean 3 := (ContinuousLinearMap.id ℝ _).prod 0
  let A := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin r ↦ L)
  have hs : ContDiff ℝ ∞ (fun z : Euclidean 3 ↦ (x, z)) := contDiff_const.prodMk contDiff_id
  have hj : ContDiff ℝ ∞ (iteratedFDeriv ℝ r f) := hf.iteratedFDeriv_right (by simp)
  have he : (fun z ↦ iteratedFDeriv ℝ r (fun y ↦ f (y, z)) x) =
      A ∘ ((iteratedFDeriv ℝ r f) ∘ fun z : Euclidean 3 ↦ (x, z)) := by
    funext z
    exact spatial_phase_jet_eq_joint_restriction f hf r x z
  rw [he]
  exact A.contDiff.comp (hj.comp hs)

/-- The mixed parameter/spatial phase jet costs one joint derivative and
no norm factor (`app:ch_pairs:setup:pairs-lag`). This is the mixed input for
the convex-segment estimate, before cancellation of the difference beat. -/
theorem norm_parameter_spatial_phase_jet_le_joint
    (f : Euclidean n × Euclidean 3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (r : ℕ) (x : Euclidean n) (z : Euclidean 3) :
    ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ r (fun y ↦ f (y, w)) x) z‖ ≤
      ‖iteratedFDeriv ℝ (r + 1) f (x, z)‖ := by
  let L : Euclidean n →L[ℝ] Euclidean n × Euclidean 3 := (ContinuousLinearMap.id ℝ _).prod 0
  let R : Euclidean 3 →L[ℝ] Euclidean n × Euclidean 3 := (0 : Euclidean 3 →L[ℝ] Euclidean n).prod (ContinuousLinearMap.id ℝ _)
  let A := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℝ) (fun _ : Fin r ↦ L)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp [L]
  have hR : ‖R‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp [R]
  have hA : ‖A‖ ≤ 1 := (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le ℝ (fun _ : Fin r ↦ L)).trans
    (by simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      pow_le_one₀ (norm_nonneg L) hL (n := r))
  have hj : ContDiff ℝ ∞ (iteratedFDeriv ℝ r f) := hf.iteratedFDeriv_right (by simp)
  have hs : ContDiff ℝ ∞ (fun w : Euclidean 3 ↦ iteratedFDeriv ℝ r f (x, w)) :=
    hj.comp (contDiff_const.prodMk contDiff_id)
  have he : (fun w ↦ iteratedFDeriv ℝ r (fun y ↦ f (y, w)) x) =
      A ∘ (fun w : Euclidean 3 ↦ iteratedFDeriv ℝ r f (x, w)) := by
    funext w
    exact spatial_phase_jet_eq_joint_restriction f hf r x w
  rw [he, ← norm_iteratedFDeriv_one]
  apply (A.norm_iteratedFDeriv_comp_left hs.contDiffAt (by simp : (1 : ℕ∞ω) ≤ ∞)).trans
  apply (mul_le_of_le_one_left (norm_nonneg _) hA).trans
  have hr := norm_iteratedFDeriv_comp_linear_le R
    (fun q ↦ iteratedFDeriv ℝ r f ((x, 0) + q)) (hj.comp (contDiff_const.add contDiff_id)) 1 z
  have hr' := hr.trans (mul_le_of_le_one_right (norm_nonneg _)
    (by simpa only [pow_one] using hR))
  simpa only [Function.comp_def, iteratedFDeriv_comp_add_left', R,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply,
    Prod.mk_add_mk, zero_add, add_zero, norm_iteratedFDeriv_one,
    norm_fderiv_iteratedFDeriv] using hr'


open ActualCarriers CurrentFullPhase FrozenMenu CompatibleResponse
open ResponseTransfer.RetainedFactors CurrentCoefficientProfiles GeometricProfile ProtectedFlow

/-- Derive the spatial and mixed phase inputs for normalized signed pairs
from the ORIGINAL admissible history (`app:ch_pairs:setup:pairs-lag`). The
fixed reserve two pays the parameter derivative; both bounds retain `L^(m-1)`.
The supplied representative is the SAME one produced by
`exists_primaryPhaseInCoordinates_representative`, and `Q` is identified with
the prescribed extended projected stress. No phase-grade premise is added.
Constants precede histories and parameters. The finite chart/radial assembly
must still use these inputs on its retained original source family. -/
theorem exists_admissible_history_signed_phase_jet_inputs
    {d : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    {c C₀ : ℝ} (hP : P.IsValid c C₀) (i : Fin (d + 1))
    {S : Set (Euclidean (d + 1))} {Z : Set (Euclidean 3)} (hS : IsCompact S) (hZ : IsCompact Z)
    (hSZ : ∀ q ∈ S ×ˢ Z,
      (primaryCoordinateChange i).symm q.1 ∈ ball 0 T.physicalRadius ∧
        q.2 ∈ parameterInterior (2 * P.radius))
    (χprimary : Euclidean (d + 1) × Euclidean 3 → ℝ)
    (hrep : ∀ Q,
      let f := fun q : Euclidean (d + 1) × Euclidean 3 ↦
        χprimary q * T.primaryPhaseInCoordinates i Q q.1 q.2
      ContDiff ℝ ∞ f ∧ ∀ q ∈ S ×ˢ Z,
        f =ᶠ[𝓝 q] (fun q ↦ T.primaryPhaseInCoordinates i Q q.1 q.2))
    (Gref : FlatReference (d + 1)) {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hR : R < Gref.domain.chartRadius)
    (ext : BallExtension.Parameters (Euclidean (d + 1))) (hextcenter : ext.center = 0)
    (hextradius : ext.radius = r) {rStar kMin : ℕ} (hStar : 8 ≤ rStar)
    (horder : displacementLoss (d + 1) +
      bandExponent * ((rStar : ℝ) + ((d + 1 : ℕ) : ℝ) / 2) + 2 < kMin) :
    ∃ threshold : ℝ, 2 ≤ threshold ∧ ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ R₀, threshold ≤ R₀ →
      ∀ (s : ℕ) (u : Fin s → Torus (d + 1) → Euclidean (embeddingDimension (d + 1)))
        (ell : Fin s → ℕ), IsAdmissibleHistory R₀ kMin u ell →
      ∀ Q, Q.1 = extendedProjectedStress ext (finiteHistoryMap Gref.map u) →
      let φ := fun z x ↦ χprimary (x, z) * T.primaryPhaseInCoordinates i Q x z
      ∀ x ∈ S, ∀ m : ℕ,
        ContDiff ℝ ∞ (fun z ↦ iteratedFDeriv ℝ m (φ z) x) ∧
        ∀ z ∈ Z, 1 ≤ m →
          ‖iteratedFDeriv ℝ m (φ z) x‖ ≤ C m * currentCoefficientScale R₀ s ^ (m - 1) ∧
          ‖fderiv ℝ (fun w ↦ iteratedFDeriv ℝ m (φ w) x) z‖ ≤
            C m * currentCoefficientScale R₀ s ^ (m - 1) := by
  obtain ⟨threshold, hthreshold, A, hA, hphase⟩ :=
    T.exists_admissible_history_primary_phase_profiles hP i (hS.prod hZ) hSZ
      Gref hr hrR hR ext hextcenter hextradius hStar (Rstar := 2) (by omega) horder
  refine ⟨threshold, hthreshold, fun m ↦ A m + A (m + 1),
    fun m ↦ add_nonneg (hA m) (hA (m + 1)), ?_⟩
  intro R₀ hR₀ s u ell hu Q hQ φ x hx m
  let f := fun q : Euclidean (d + 1) × Euclidean 3 ↦
    χprimary q * T.primaryPhaseInCoordinates i Q q.1 q.2
  have hf : ContDiff ℝ ∞ f := (hrep Q).1
  have hL : 1 ≤ currentCoefficientScale R₀ s :=
    one_le_currentCoefficientScale (by linarith) s
  refine ⟨contDiff_parameter_spatial_phase_jet f hf m x, ?_⟩
  intro z hz hm
  have hb (j : ℕ) : ‖iteratedFDeriv ℝ j f (x, z)‖ ≤
      A j * currentCoefficientScale R₀ s ^ (j - 2) := by
    have hfnorm : cNorm (S ×ˢ Z) j f ≤ A j * currentCoefficientScale R₀ s ^ (j - 2) := by
      rw [cNorm_eq_of_eventuallyEq ((hrep Q).2) j]
      exact hphase R₀ hR₀ s u ell hu Q hQ j
    exact (norm_iteratedFDeriv_le_cNorm (hS.prod hZ) (hf.of_le (by simp))
      ⟨hx, hz⟩ le_rfl).trans hfnorm
  constructor
  · apply (primary_phase_spatial_jet_le_joint f hf x z m).trans ((hb m).trans ?_)
    exact mul_le_mul (le_add_of_nonneg_right (hA (m + 1)))
      (pow_le_pow_right₀ hL (by omega))
      (pow_nonneg (zero_le_one.trans hL) _) (add_nonneg (hA m) (hA (m + 1)))
  · apply (norm_parameter_spatial_phase_jet_le_joint f hf m x z).trans ((hb (m + 1)).trans ?_)
    have he : m + 1 - 2 = m - 1 := by omega
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hA m))
      (pow_nonneg (zero_le_one.trans hL) _)

end JanetCartan.SignedProductEstimates
