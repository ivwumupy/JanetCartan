module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PencilContinuity
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.SignedRegularity.Angular
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame

/-!
# Actual angular gaps from the current-frame neighborhood

Step 2 of `app:ch_seed:prop:seed-actual-menu`. The polynomial comparison and
angular stability lemmas are instantiated here: the only perturbation input is
the primitive frame closeness of `app:ch_seed:setup:seed-current`. In particular,
no adjugate, determinant or determinant-differential comparison is assumed.
The final specialization uses the literal projected stresses of the immersion.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers
open SignedPairs ProjectedStressFrame

/-- A single frame neighborhood preserves all angular gaps, and supplies a
uniform matrix upper bound, before any current frame is chosen. This closes
the coefficient-error inputs of `exists_angular_pencil_regularity` for
`app:ch_seed:prop:seed-actual-menu`, Step 2. -/
theorem exists_angular_frame_neighborhood {n : ℕ} (hn : 5 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ δ a d M : ℝ, 0 < δ ∧ 0 < a ∧ 0 < d ∧ 0 < M ∧
      ∀ Q : Fin n → MetricTensor n, ‖Q - cubeStress n‖ < δ →
      ∀ v ∈ angularSet n γ,
        a ≤ ‖(pencil Q v).adjugate‖ ∧ n - 1 ≤ (pencil Q v).rank ∧
        ‖pencil Q v‖ ≤ M ∧
        (determinant Q v = 0 → d ≤ ‖fderiv ℝ (determinant Q) v‖) := by
  obtain ⟨a, ha, d, hd, _, hreg⟩ := exists_angular_pencil_regularity hn hγ
  obtain ⟨δ, hδ, hclose⟩ := exists_uniform_pencil_data_radius (cubeStress n)
    (isCompact_angularSet n γ) (lt_min ha (lt_min hd zero_lt_one))
  obtain ⟨B, hB⟩ := (isCompact_angularSet n γ).exists_bound_of_continuousOn
    ((cubePencilContinuousLinearMap n).continuous.continuousOn)
  refine ⟨δ, a, d, max B 0 + 1, hδ, ha, hd, by positivity, ?_⟩
  intro Q hQ
  have he (v) (hv : v ∈ angularSet n γ) := hclose Q hQ v hv
  have hdet : determinant (cubeStress n) = cubeDeterminant :=
    funext determinant_cubeStress
  have hA (v) (hv : v ∈ angularSet n γ) :
      ‖(pencil Q v).adjugate - (cubePencil v).adjugate‖ ≤ a := by
    simpa only [pencil_cubeStress] using
      ((he v hv).2.2.2.1.le.trans (min_le_left a (min d 1)))
  have hp (v) (hv : v ∈ angularSet n γ) :
      ‖determinant Q v - cubeDeterminant v‖ ≤ d := by
    simpa only [hdet] using
      ((he v hv).2.1.le.trans ((min_le_right a (min d 1)).trans (min_le_left d 1)))
  have hD (v) (hv : v ∈ angularSet n γ) :
      ‖fderiv ℝ (determinant Q) v - fderiv ℝ cubeDeterminant v‖ ≤ d := by
    simpa only [hdet] using
      ((he v hv).2.2.1.le.trans ((min_le_right a (min d 1)).trans (min_le_left d 1)))
  intro v hv
  have hr := hreg Q hA hp hD v hv
  refine ⟨hr.1, hr.2.1, ?_, hr.2.2⟩
  have hc : ‖pencil Q v - cubePencil v‖ ≤ 1 := by
    simpa only [pencil_cubeStress] using
      ((he v hv).1.le.trans ((min_le_right a (min d 1)).trans (min_le_right d 1)))
  have hb := (hB v hv).trans (le_max_left B 0)
  have ht := norm_le_norm_sub_add (pencil Q v) (cubePencil v)
  change ‖cubePencil v‖ ≤ max B 0 at hb
  linarith

/-- The paper's componentwise `C⁶` frame neighborhood gives pointwise frame
closeness in the finite supremum of Frobenius norms. Local smoothness on an
open neighborhood of the compact set justifies the seminorm evaluation
(`app:ch_seed:setup:seed-current`). -/
theorem projectedStress_norm_sub_cube_lt_of_cNorm {n N : ℕ}
    {F : Euclidean n → Euclidean N} {U K : Set (Euclidean n)}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hr : HasFullNormalRankOn F U) {δ : ℝ} (hδ : 0 < δ)
    (hclose : ∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) < δ)
    {x : Euclidean n} (hx : x ∈ K) :
    ‖projectedStress F x - cubeStress n‖ < δ := by
  apply (pi_norm_lt_iff hδ).mpr
  intro i
  have hs := (contDiffOn_projectedStress hU hF hi hr i).sub
    (contDiffOn_const (c := cubeStress n i))
  have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (r := 6) hK
    (fun y hy ↦ (hs.contDiffAt (hU.mem_nhds (hKU hy))).of_le (by simp))
    hx (Nat.zero_le 6)
  have hb' : ‖projectedStress F x i - cubeStress n i‖ ≤
      cNorm K 6 (fun y ↦ projectedStress F y i - cubeStress n i) := by
    simpa only [norm_iteratedFDeriv_zero] using hb
  exact hb'.trans_lt (hclose i)

/-- Actual projected pencils have uniform adjugate, rank, matrix and simple-zero
gaps on the protected angular set under precisely the componentwise `C⁶`
closeness in `app:ch_seed:setup:seed-current`. All constants precede the
immersion and its higher norms. No pencil comparison is an extra premise.
The signed-direction inclusion and the numbered singular-value bound are
separate parts of `app:ch_seed:prop:seed-actual-menu`. -/
theorem exists_projectedStress_angular_neighborhood {n : ℕ} (hn : 5 ≤ n)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ δ a d M : ℝ, 0 < δ ∧ 0 < a ∧ 0 < d ∧ 0 < M ∧
      ∀ (N : ℕ) (F : Euclidean n → Euclidean N) (U K : Set (Euclidean n)),
        IsOpen U → IsCompact K → K ⊆ U →
        ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
        (∀ i, cNorm K 6 (fun x ↦ projectedStress F x i - cubeStress n i) < δ) →
        ∀ x ∈ K, ∀ v ∈ angularSet n γ,
          a ≤ ‖(pencil (projectedStress F x) v).adjugate‖ ∧
          n - 1 ≤ (pencil (projectedStress F x) v).rank ∧
          ‖pencil (projectedStress F x) v‖ ≤ M ∧
          (determinant (projectedStress F x) v = 0 →
            d ≤ ‖fderiv ℝ (determinant (projectedStress F x)) v‖) := by
  obtain ⟨δ, a, d, M, hδ, ha, hd, hM, hreg⟩ := exists_angular_frame_neighborhood hn hγ
  refine ⟨δ, a, d, M, hδ, ha, hd, hM, ?_⟩
  intro N F U K hU hK hKU hF hi hr hclose x hx
  exact hreg (projectedStress F x)
    (projectedStress_norm_sub_cube_lt_of_cNorm hU hK hKU hF hi hr hδ hclose hx)

end JanetCartan.ActualCarriers
