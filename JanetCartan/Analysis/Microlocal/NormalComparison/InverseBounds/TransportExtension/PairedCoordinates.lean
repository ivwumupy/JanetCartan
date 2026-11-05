module

public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.CoordinateDerivatives

/-!
# Native and paired physical coordinates

The coordinate conversion for both amplitudes of `app:ch_osc:prop:osc-normal`.
The pairing is the existing `AmplitudeBound.pairedPosition`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NormalComparison
open AmplitudeBound
variable {n r : ℕ}

local instance transportPairedMatrixTopology (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- First position of the existing paired-position chart, for the normal
amplitude bounds in `app:ch_osc:prop:osc-normal`. -/
def normalLeftPosition (n : ℕ) :
    EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ WithLp.toLp 2 (fun i ↦ z ⟨i.val, by omega⟩)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- Second position of the existing paired-position chart, for the normal
amplitude bounds in `app:ch_osc:prop:osc-normal`. -/
def normalRightPosition (n : ℕ) :
    EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z ↦ WithLp.toLp 2 (fun i ↦ z ⟨n + i.val, by omega⟩)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- Recovery of the first position in `app:ch_osc:prop:osc-normal`. -/
@[simp] theorem normalLeftPosition_pairedPosition
    (x y : EuclideanSpace ℝ (Fin n)) :
    normalLeftPosition n (pairedPosition x y) = x := by
  ext i
  change pairedPosition x y ⟨i.val, by omega⟩ = x i
  simp [pairedPosition]

/-- Recovery of the second position in `app:ch_osc:prop:osc-normal`. -/
@[simp] theorem normalRightPosition_pairedPosition
    (x y : EuclideanSpace ℝ (Fin n)) :
    normalRightPosition n (pairedPosition x y) = y := by
  ext i
  change pairedPosition x y ⟨n + i.val, by omega⟩ = y i
  simp [pairedPosition, show ¬n + i.val < n by omega]

/-- The paired-position coordinates are exhausted by the two recovered
positions (`app:ch_osc:prop:osc-normal`). -/
theorem pairedPosition_normalPositions (z : EuclideanSpace ℝ (Fin (2 * n))) :
    pairedPosition (normalLeftPosition n z) (normalRightPosition n z) = z := by
  ext i
  by_cases hi : i.val < n
  · simp only [pairedPosition, PiLp.toLp_apply, dite_eq_left hi]
    rfl
  · simp only [pairedPosition, PiLp.toLp_apply, dite_eq_right hi]
    change z ⟨n + (i.val - n), _⟩ = z i
    exact congrArg (fun a : Fin (2 * n) ↦ z a) (Fin.ext (by
      change n + (i.val - n) = i.val
      omega))

/-- Linear physical-position insertion into the three native coordinates of
`app:ch_osc:prop:osc-normal`. -/
def normalPositionInsertion (n : ℕ) : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
    (EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :=
  (normalLeftPosition n).prod ((normalRightPosition n).prod 0)

/-- A native three-variable matrix amplitude in the two-position API of
`app:ch_osc:lem:osc-amplitude`. -/
def pairedNormalAmplitude
    (f : (EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n))) → Matrix (Fin r) (Fin r) ℂ)
    (u : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin (2 * n))) :=
  f (normalLeftPosition n z, (normalRightPosition n z, u))

/-- Exact identification of the two positions, used for both literal kernels
in `app:ch_osc:prop:osc-normal`. -/
@[simp] theorem pairedNormalAmplitude_pairedPosition
    (f : (EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n))) → Matrix (Fin r) (Fin r) ℂ) (u x y) :
    pairedNormalAmplitude f u (pairedPosition x y) = f (x, (y, u)) := by
  simp [pairedNormalAmplitude]

/-- Global joint smoothness survives the paired-position conversion in
`app:ch_osc:prop:osc-normal`. -/
theorem contDiff_pairedNormalAmplitude
    {f : (EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n))) → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Function.uncurry (pairedNormalAmplitude f)) :=
  hf.comp (((normalLeftPosition n).contDiff.comp contDiff_snd).prodMk
    (((normalRightPosition n).contDiff.comp contDiff_snd).prodMk contDiff_fst))

/-- The fixed coordinate loss for native-to-paired Frobenius jets, depending
only on dimension (`app:ch_osc:prop:osc-normal`). -/
def normalPositionJetFactor (n N : ℕ) : ℝ := max 1 ‖normalPositionInsertion n‖ ^ N

/-- Positivity of the fixed coordinate loss in the normal amplitude estimates
of `app:ch_osc:prop:osc-normal`. -/
theorem normalPositionJetFactor_pos (n N : ℕ) : 0 < normalPositionJetFactor n N :=
  pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _

/-- Reusable conversion from global native-coordinate Frobenius jets to the
matrix coordinate-derivative bounds required in `app:ch_osc:lem:osc-amplitude`.
It applies unchanged to the transport and inverse amplitudes. -/
theorem pairedNormalAmplitude_derivative_bound
    {f : (EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n))) → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ f) {N : ℕ} {K : ℝ}
    (hb : ∀ q k, k ≤ N → ‖iteratedFDeriv ℝ k f q‖ ≤ K)
    (u : EuclideanSpace ℝ (Fin n)) (is : List (Fin (2 * n))) (hi : is.length ≤ N) (z) :
    ‖matrixAmplitudeCoordinateDerivList is (pairedNormalAmplitude f u) z‖ ≤
      K * normalPositionJetFactor n N := by
  let a : EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    (0, (0, u))
  let g := fun q ↦ f (q + a)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have he : pairedNormalAmplitude f u = g ∘ normalPositionInsertion n := by
    funext w
    simp [pairedNormalAmplitude, g, a, normalPositionInsertion]
  have hs : ContDiff ℝ ∞ (pairedNormalAmplitude f u) := by
    rw [he]
    exact hg.comp (normalPositionInsertion n).contDiff
  apply (norm_matrixAmplitudeCoordinateDerivList_le_jet hs is z).trans
  rw [he, (normalPositionInsertion n).iteratedFDeriv_comp_right hg z (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hj : ‖iteratedFDeriv ℝ is.length g (normalPositionInsertion n z)‖ ≤ K := by
    rw [iteratedFDeriv_comp_add_right]
    exact hb _ _ hi
  have hp : ‖normalPositionInsertion n‖ ^ is.length ≤ normalPositionJetFactor n N := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
      (pow_le_pow_right₀ (le_max_left _ _) hi)
  exact mul_le_mul hj hp (by positivity) ((norm_nonneg _).trans hj)

/-- A fixed physical support gives the same centered box for every matrix
entry after pairing (`app:ch_osc:lem:osc-amplitude`). -/
theorem pairedNormalAmplitude_supportedInCenteredBox
    {f : (EuclideanSpace ℝ (Fin n) × (EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n))) → Matrix (Fin r) (Fin r) ℂ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {R : ℝ}
    (hR : ∀ x ∈ S, ‖x‖ ≤ R)
    (hs : ∀ q, f q ≠ 0 → q.1 ∈ S ∧ q.2.1 ∈ S)
    (u : EuclideanSpace ℝ (Fin n)) (i j : Fin r) :
    SupportedInCenteredBox R (fun z ↦ pairedNormalAmplitude f u z i j) := by
  intro z hz k
  have hn : f (normalLeftPosition n z, (normalRightPosition n z, u)) ≠ 0 := by
    intro h
    exact hz (by simp [pairedNormalAmplitude, h])
  have hmem := hs _ hn
  have he := congrArg (fun w : EuclideanSpace ℝ (Fin (2 * n)) ↦ w k)
    (pairedPosition_normalPositions z)
  rw [← he]
  by_cases hk : k.val < n
  · simp only [pairedPosition, PiLp.toLp_apply, dite_eq_left hk]
    have hb := (PiLp.norm_apply_le (normalLeftPosition n z) ⟨k.val, hk⟩).trans (hR _ hmem.1)
    simpa only [Real.norm_eq_abs] using hb
  · simp only [pairedPosition, PiLp.toLp_apply, dite_eq_right hk]
    have hb := (PiLp.norm_apply_le (normalRightPosition n z) ⟨k.val - n, by omega⟩).trans (hR _ hmem.2)
    simpa only [Real.norm_eq_abs] using hb

end JanetCartan.NormalComparison
