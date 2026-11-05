module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalCarrier
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.Restriction

/-!
# Differences of the literal retained carriers

Consumer: the positive-reference root/ODE/inverse comparison in
`FamilyInputs.PositiveReference.HamiltonDependence`.
For `app:lem:common-hamilton-phase` and `app:ch_osc:prop:osc-normal`, Step 4',
the literal `transportPosition` is the initial-position coordinate of the
retained inverse chart. Its differences cost no derivative of that inverse.
The literal physical carrier-gradient differences cost one phase derivative.
These are estimates for the actual outputs, not a continuity hypothesis.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ActualCarriers CurrentFullPhase FrozenMenu HamiltonPhase
open ConstructedCarrierJets ContinuumRow ContinuumRow.CanonicalCarrier

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The literal `Y = d_ζ S` is exactly the initial-position component of the
SAME retained Hamilton inverse (`app:lem:common-hamilton-phase` and
`app:ch_background:defn:bg-carriers`). No choice of a comparison chart occurs. -/
theorem transportPosition_eq_coordinates_snd (Q : _)
    {p : Euclidean n × CarrierParameter}
    (hp : T.carrierRestriction (p.1, parameter p.2) ∈ (T.currentChart Q).target) :
    transportPosition T Q p =
      ((T.currentChart Q).coordinates (T.carrierRestriction (p.1, parameter p.2))).2 := by
  rw [transportPosition_eq_hamiltonGradient]
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hinput : HasFDerivAt (fun ζ : Euclidean (n - 1) ↦ (p.1, ((0 : ℝ), ζ)))
      ((0 : Euclidean (n - 1) →L[ℝ] Euclidean n).prod
        ((0 : Euclidean (n - 1) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ _)))
      (T.reference.spatialPatch (parameter p.2)) :=
    (hasFDerivAt_const _ _).prodMk ((hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _))
  have hd := ((T.currentChart Q).hasFDerivAt_phase hp).comp
    (T.reference.spatialPatch (parameter p.2)) hinput
  dsimp only [Function.comp_def] at hd
  rw [hd.fderiv]
  simp [phaseDifferential_apply, PatchQuantitativeFamily.carrierRestriction]

/-- A fixed compact restriction transfers inverse-coordinate differences to
the literal transport position with zero derivative loss. The physical and
carrier buffers, and every constant, precede both frames
(`app:ch_osc:prop:osc-normal`, Step 4'). The positive-reference inverse comparison is supplied separately by
`exists_retained_positiveReference_comparison`. -/
theorem exists_transportPosition_sub_le_coordinates {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × CarrierParameter)}
    {L : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKU : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)))
    (hLT : L ⊆ T.target)
    (hmap : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      T.carrierRestriction (p.1, parameter p.2)) K L) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧ ∀ Q Q₀ m,
      cNorm K m (transportPosition T Q - transportPosition T Q₀) ≤
        D m * cNorm L m ((T.currentChart Q).coordinates - (T.currentChart Q₀).coordinates) := by
  let O := ball (0 : Euclidean n) T.physicalRadius ×ˢ
    (parameter ⁻¹' parameterInterior (2 * P.radius))
  have hO : IsOpen O := isOpen_ball.prod
    ((isOpen_parameterInterior _).preimage parameter.continuous)
  let ψ := fun p : Euclidean n × CarrierParameter ↦
    T.carrierRestriction (p.1, parameter p.2)
  have hψ : ContDiffOn ℝ ∞ ψ O :=
    (T.carrierRestriction_smooth hP).comp
      (contDiffOn_fst.prodMk (parameter.contDiff.contDiffOn.comp contDiffOn_snd
        (fun _ _ ↦ mem_univ _))) (fun _ hp ↦ hp)
  choose D hD hb using fun m ↦ exists_cNorm_fixed_pullback_le_jet_bound
    (G := Euclidean (n - 1)) hK
    (fun p hp ↦ hψ.contDiffAt (hO.mem_nhds (hKU hp))) m
  refine ⟨D, hD, ?_⟩
  intro Q Q₀ m
  let f := (T.currentChart Q).coordinates - (T.currentChart Q₀).coordinates
  let S : (ℝ × Euclidean (n - 1)) →L[ℝ] Euclidean (n - 1) :=
    ContinuousLinearMap.snd ℝ _ _
  have hcoords (Q : _) : ∀ z ∈ L, ContDiffAt ℝ ∞ (T.currentChart Q).coordinates z := by
    intro z hz
    exact (T.family.coordinates_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius) (hLT hz)))
  have hf : ∀ z ∈ L, ContDiffAt ℝ ∞ f z :=
    fun z hz ↦ (hcoords Q z hz).sub (hcoords Q₀ z hz)
  have he : cNorm K m (transportPosition T Q - transportPosition T Q₀) =
      cNorm K m ((S ∘ f) ∘ ψ) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro p hp
    filter_upwards [hO.mem_nhds (hKU hp)] with w hw
    have htarget (Q : _) := T.carrierRestriction_mem_target Q
      (show (w.1, parameter w.2) ∈ ball (0 : Euclidean n) T.physicalRadius ×ˢ
        parameterInterior (2 * P.radius) from hw)
    simp only [Pi.sub_apply, transportPosition_eq_coordinates_snd T Q (htarget Q),
      transportPosition_eq_coordinates_snd T Q₀ (htarget Q₀)]
    rfl
  rw [he]
  apply hb m (S ∘ f) (cNorm L m f) (cNorm_nonneg ..)
    (fun p hp ↦ (S.contDiff.contDiffAt.comp _ (hf _ (hmap hp))).of_le (by simp))
  intro j hj p hp
  calc
    _ ≤ ‖S‖ * ‖iteratedFDeriv ℝ j f (ψ p)‖ :=
      S.norm_iteratedFDeriv_comp_left (hf _ (hmap hp)) (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ j f (ψ p)‖ :=
      mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_snd_le ℝ ℝ
        (Euclidean (n - 1))) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
        (fun z hz ↦ (hf z hz).of_le (by simp : (m : ℕ∞ω) ≤ ∞)) (hmap hp) hj

/-- The retained physical carrier-gradient difference costs exactly one full
phase derivative on the fixed target compact. This uses the literal
`T.carrierGradient`, including all joint physical/carrier derivatives
(`app:ch_background:prop:bg-frame`, `app:ch_osc:prop:osc-normal`, Step 4'). -/
theorem exists_carrierGradient_sub_le_phase {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)}
    {L : Set (Euclidean n × (ℝ × Euclidean (n - 1)))}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKU : K ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
    (hLT : L ⊆ T.target) (hmap : MapsTo T.carrierRestriction K L) :
    ∃ D : ℕ → ℝ, (∀ m, 0 < D m) ∧ ∀ Q Q₀ m,
      cNorm K m (fun p ↦ T.carrierGradient Q p.1 p.2 - T.carrierGradient Q₀ p.1 p.2) ≤
        D m * cNorm L (m + 1)
          (phase (T.currentChart Q).coordinates - phase (T.currentChart Q₀).coordinates) := by
  let O := ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)
  have hO : IsOpen O := isOpen_ball.prod (isOpen_parameterInterior _)
  choose D hD hb using fun m ↦ exists_cNorm_fixed_pullback_le_jet_bound
    (G := Euclidean n) hK
    (fun p hp ↦ (T.carrierRestriction_smooth hP).contDiffAt (hO.mem_nhds (hKU hp))) m
  refine ⟨D, hD, ?_⟩
  intro Q Q₀ m
  let f := (T.currentChart Q).chartMomentum - (T.currentChart Q₀).chartMomentum
  let s := phase (T.currentChart Q).coordinates - phase (T.currentChart Q₀).coordinates
  have hphase (Q : _) : ∀ z ∈ L, ContDiffAt ℝ ∞ (phase (T.currentChart Q).coordinates) z := by
    intro z hz
    exact (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (ball_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius ≤ 2 * T.family.radius) (hLT hz)))
  have hf : ∀ z ∈ L, ContDiffAt ℝ ∞ f z := fun z hz ↦
    (contDiffAt_chartMomentum_of_phase (T.currentChart Q) (hLT hz) (hphase Q z hz)).sub
      (contDiffAt_chartMomentum_of_phase (T.currentChart Q₀) (hLT hz) (hphase Q₀ z hz))
  have he : cNorm K m (fun p ↦ T.carrierGradient Q p.1 p.2 - T.carrierGradient Q₀ p.1 p.2) =
      cNorm K m (f ∘ T.carrierRestriction) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro p hp
    filter_upwards [hO.mem_nhds (hKU hp)] with w hw
    exact congrArg₂ (· - ·)
      (hasGradientAt_carrierPhase (T.currentChart Q) T.reference.spatialPatch
        (T.carrierRestriction_mem_target Q hw)).gradient
      (hasGradientAt_carrierPhase (T.currentChart Q₀) T.reference.spatialPatch
        (T.carrierRestriction_mem_target Q₀ hw)).gradient
  rw [he]
  apply hb m f (cNorm L (m + 1) s) (cNorm_nonneg ..)
    (fun p hp ↦ (hf _ (hmap hp)).of_le (by simp))
  intro j hj p hp
  exact (norm_iteratedFDeriv_chartMomentum_sub_le (T.currentChart Q) (T.currentChart Q₀)
    (hLT (hmap hp)) (hLT (hmap hp)) (hphase Q _ (hmap hp)) (hphase Q₀ _ (hmap hp)) j).trans
      (norm_iteratedFDeriv_le_cNorm_of_contDiffAt hL
        (fun z hz ↦ ((hphase Q z hz).sub (hphase Q₀ z hz)).of_le
          (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞)) (hmap hp) (by omega))

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
