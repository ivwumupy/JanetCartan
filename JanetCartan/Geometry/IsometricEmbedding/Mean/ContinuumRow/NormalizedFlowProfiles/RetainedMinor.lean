module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.NormalizedFlowProfiles.CarrierInputs
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds.Principal

/-!
# The supplied minor on the original doubled coefficient domain

The minor is supplied by the retained cell's frozen refinement. We perturb
that same minor, without selecting a second refinement or moving the incidence
point to the cell center. The frame threshold precedes the varying frame.

Sources: `app:ch_waves:thm:leading`, `app:ch_background:prop:bg-normalized`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.NormalizedFlowProfiles
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport CoefficientBounds

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- A supplied frozen minor buffer gives a gap for the identical adapted
denominator on the entire supplied coefficient set. Its producer is the
frozen open refinement in `exists_actual_null_gaps`; this theorem retains the
chosen row and column instead of making a new existential choice. The actual
carrier comparison is derived from primitive frame closeness
(`app:ch_waves:thm:leading`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_minor_gap_threshold {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)}
    (hx : MapsTo Prod.fst K
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hc : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterCube (3 * P.radius / 2))
    (row col : Fin n) {μ : ℝ} (hμ : 0 < μ)
    (hminor : ∀ w ∈ K, 2 * μ ≤ |(cubePencil (P.toFun w.2)).adjugate row col|) :
    ∃ δ > (0 : ℝ), ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      (∀ x ∈ U, ∀ i, (Q.1 x i).IsSymm) →
      ∀ w ∈ K,
        μ * (T.data.localReference.determinantGap / 2) ≤
          |carrierAdaptedDenominator T Q row col w| := by
  let κ := T.data.localReference.determinantGap / 2
  have hκ : 0 < κ := half_pos T.data.localReference.determinantGap_pos
  obtain ⟨d, hd, hdata⟩ := exists_patch_null_data_radius hP T.data.adapted.normal
    (lt_min hμ hκ)
  obtain ⟨e, he, hgrad⟩ := exists_buffered_carrier_value_threshold T hd
  refine ⟨min d e, lt_min hd he, ?_⟩
  intro Q hclose hsymm w hw
  have hs : ∀ x ∈ closedBall (0 : Euclidean n) T.data.localReference.stateRadius,
      ContDiffAt ℝ 6 (Q.1 - fun _ ↦ cubeStress n) x :=
    fun x hx ↦ ((Q.2.1.contDiffAt (hU.mem_nhds (hphysical hx))).sub
      contDiffAt_const).of_le (by simp)
  have hframe : ‖Q.1 w.1 - cubeStress n‖ < d := by
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt
      (isCompact_closedBall _ _) hs (hx hw) (Nat.zero_le 6)
    have hv : ‖Q.1 w.1 - cubeStress n‖ ≤
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hb
    exact hv.trans_lt (hclose.trans_le (min_le_left _ _))
  have hz : w.2 ∈ parameterInterior (2 * P.radius) :=
    fun i ↦ ((hc hw).2 i).trans_lt (by linarith [hP.1])
  have hξ := hgrad Q (hclose.trans_le (min_le_right _ _)) w.1 (hc hw).1 w.2 hz
  obtain ⟨hadj, hroot⟩ := hdata (Q.1 w.1) (T.carrierGradient Q w.1 w.2) w.2
    (hc hw).2 hframe hξ
  have hm : μ ≤ |(pencil (Q.1 w.1) (T.carrierGradient Q w.1 w.2)).adjugate row col| := by
    have he := (abs_entry_le_frobenius
      ((pencil (Q.1 w.1) (T.carrierGradient Q w.1 w.2)).adjugate -
        (cubePencil (P.toFun w.2)).adjugate) row col).trans_lt
          (hadj.trans_le (min_le_left _ _))
    change |(pencil (Q.1 w.1) (T.carrierGradient Q w.1 w.2)).adjugate row col -
      (cubePencil (P.toFun w.2)).adjugate row col| < μ at he
    have htri := abs_sub_abs_le_abs_sub ((cubePencil (P.toFun w.2)).adjugate row col)
      ((pencil (Q.1 w.1) (T.carrierGradient Q w.1 w.2)).adjugate row col)
    rw [abs_sub_comm] at htri
    linarith [hminor w hw]
  have hr : κ ≤ fderiv ℝ (determinant (Q.1 w.1))
      (T.carrierGradient Q w.1 w.2) T.data.adapted.normal := by
    have hf := T.data.localReference.determinant_gap _
      (T.data.buffered_mem w.2 (fun i ↦ (hz i).le))
    have hh := (abs_lt.mp (hroot.trans_le (min_le_right _ _))).1
    dsimp [κ] at *
    linarith
  exact (adaptedTimeCoefficient_bounds _ (hsymm w.1 (hphysical (hx hw))) _
    (T.carrier_characteristic Q (hc hw).1 hz) _ hμ hκ hm hr).1

/-- All-order bounds and a fixed low direction bound on the supplied cell,
with smoothness on its original doubled coefficient ball. The only minor
input is the frozen algebraic buffer for the SAME row and column; the current
gap and coefficient bounds are proved. The final source-family application
uses `exists_admitted_source_frame_profiles` to discharge every frame norm
(`app:ch_waves:eq:joint-tame`, `app:ch_background:prop:bg-normalized`). -/
theorem exists_retained_direction_frame_bounds {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean n × Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hx : MapsTo Prod.fst (closedBall a (2 * ρ))
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hphysical : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hc : closedBall a (2 * ρ) ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterCube (3 * P.radius / 2))
    (row col : Fin n) {μ : ℝ} (hμ : 0 < μ)
    (hminor : ∀ w ∈ closedBall a (2 * ρ),
      2 * μ ≤ |(cubePencil (P.toFun w.2)).adjugate row col|) :
    ∃ δ M : ℝ, ∃ A : ℕ → ℝ, 0 < δ ∧ 0 < M ∧ (∀ m, 0 < A m) ∧
      ∀ Q,
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q.1 - fun _ ↦ cubeStress n) < δ →
        (∀ x ∈ U, ∀ i, (Q.1 x i).IsSymm) →
        (∀ w ∈ closedBall a (2 * ρ),
          μ * (T.data.localReference.determinantGap / 2) ≤
            |carrierAdaptedDenominator T Q row col w|) ∧
        ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col) (ball a (2 * ρ)) ∧
        cNorm (closedBall a ρ) 1 (carrierTransportDirection T Q row col) ≤ M ∧
        ∀ m, cNorm (closedBall a ρ) m (carrierTransportDirection T Q row col) ≤
          A m * (1 + cNorm (closedBall (0 : Euclidean n)
            T.data.localReference.stateRadius) (m + 2) Q.1) := by
  have hsub : closedBall a ρ ⊆ closedBall a (2 * ρ) :=
    closedBall_subset_closedBall (by linarith)
  have hc' : closedBall a (2 * ρ) ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius) := fun w hw ↦
    ⟨(hc hw).1, fun i ↦ ((hc hw).2 i).trans_lt (by linarith [hP.1])⟩
  obtain ⟨d, hd, hgap⟩ :=
    exists_retained_minor_gap_threshold T hP hx hphysical hc row col hμ hminor
  obtain ⟨e, L, he, hL, hlow⟩ := exists_actualInput_low_bound T hP a ρ
    (fun w hw ↦ hx (hsub hw)) hphysical (hsub.trans hc')
  obtain ⟨B, hB, hhigh⟩ := exists_actualInput_frame_bound T hP a ρ
    (fun w hw ↦ hx (hsub hw)) hphysical (hsub.trans hc')
  let g := μ * (T.data.localReference.determinantGap / 2)
  have hg : 0 < g := mul_pos hμ (half_pos T.data.localReference.determinantGap_pos)
  obtain ⟨M, A, hM, hA, hformula⟩ := exists_principal_formula_bounds
    a hρ T.data.adapted.normal row col hL hg
  refine ⟨min d e, M, fun m ↦ A m * (1 + B m), lt_min hd he, hM,
    fun m ↦ mul_pos (hA m) (by have := hB m; positivity), ?_⟩
  intro Q hclose hsymm
  have hgapQ := hgap Q (hclose.trans_le (min_le_left _ _)) hsymm
  have hdom : closedBall a (2 * ρ) ⊆ inputDomain T :=
    fun w hw ↦ ⟨⟨hphysical (hx hw), (hc' hw).1⟩, (hc' hw).2⟩
  have hs : ContDiffOn ℝ ∞ (carrierTransportDirection T Q row col)
      (ball a (2 * ρ)) := by
    intro w hw
    have hf := (smooth_actualInput T hP Q).contDiffAt
      ((isOpen_inputDomain T).mem_nhds (hdom (ball_subset_closedBall hw)))
    have hp : actualInput T Q w ∈ admissibleInputs T.data.adapted.normal row col
        ‖actualInput T Q w‖ g :=
      ⟨mem_closedBall_zero_iff.mpr le_rfl, hgapQ w (ball_subset_closedBall hw)⟩
    exact ((smoothAt_direction hg hp).comp w hf).contDiffWithinAt
  obtain ⟨hlowQ, hhighQ⟩ := hformula (inputDomain T) (isOpen_inputDomain T)
    (hsub.trans hdom) (actualInput T Q) (smooth_actualInput T hP Q)
    (hlow Q (hclose.trans_le (min_le_right _ _))) (fun w hw ↦ hgapQ w (hsub hw))
  refine ⟨hgapQ, hs, hlowQ, ?_⟩
  intro m
  have hb : cNorm (closedBall a ρ) m (carrierTransportDirection T Q row col) ≤
      A m * (1 + cNorm (closedBall a ρ) m (actualInput T Q)) := by
    have hh := hhighQ m
    change _ + cNorm (closedBall a ρ) m (carrierTransportDirection T Q row col) ≤ _ at hh
    linarith only [hh, cNorm_nonneg (closedBall a ρ) m (right col ∘ actualInput T Q),
      cNorm_nonneg (closedBall a ρ) m (left row ∘ actualInput T Q),
      cNorm_nonneg (closedBall a ρ) m (denominator T.data.adapted.normal row col ∘ actualInput T Q),
      cNorm_nonneg (closedBall a ρ) m
        (fun w ↦ (denominator T.data.adapted.normal row col (actualInput T Q w))⁻¹)]
  apply hb.trans
  have hi : 1 + cNorm (closedBall a ρ) m (actualInput T Q) ≤
      (1 + B m) * (1 + cNorm (closedBall (0 : Euclidean n)
        T.data.localReference.stateRadius) (m + 2) Q.1) := by
    have hh := hhigh Q m
    nlinarith [cNorm_nonneg (closedBall (0 : Euclidean n)
      T.data.localReference.stateRadius) (m + 2) Q.1]
  exact (mul_le_mul_of_nonneg_left hi (hA m).le).trans_eq (by ring)

end JanetCartan.ContinuumRow.NormalizedFlowProfiles
