module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.StressPrimitives
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference.NullFlowDependence.CompactComposition
public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds.PotentialFormula
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalAmplitude

/-!
# Primitive differences of the literal null-transport coefficients

Consumer: `PositiveReference`'s application of
`NullFlowDependence.exists_cNorm_carrier_transport_sub_lt`, for
`app:ch_background:prop:bg-frame` and `app:ch_osc:prop:osc-normal`, Step 4'.
The potential retains the derivative of the same adjugate nullvector and all
induced Christoffel terms. Compact formula ranges are obtained from the fixed
reference and primitive closeness, rather than assumed output continuity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 100000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
open ActualCarriers FrozenMenu CurrentFullPhase NullTransport CoefficientBounds
open ProjectedStressFrame GeometricProfile FullPhaseCharts.InverseEstimates

private theorem fixed_comp_tolerance
    {E A B : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {K : Set E} {V : Set A} (hK : IsCompact K) (hV : IsOpen V)
    {a : A → B} {f₀ : E → A} (ha : ContDiffOn ℝ ∞ a V)
    (hf₀ : ∀ x ∈ K, ContDiffAt ℝ ∞ f₀ x) (hr₀ : MapsTo f₀ K V)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ f : E → A, (∀ x ∈ K, ContDiffAt ℝ ∞ f x) →
      cNorm K m (f - f₀) < δ → cNorm K m (a ∘ f - a ∘ f₀) < ε := by
  obtain ⟨L, _hL, _hLV, d, hd, hb⟩ :=
    NullFlowDependence.exists_cNorm_comp_sub_lt_with_buffer hK hV ha hf₀ hr₀ m hε
  exact ⟨d, hd, fun f hf hsmall ↦ hb a f ha hf
    (by simpa only [sub_self, cNorm_zero] using hd) hsmall⟩

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- The joint frame/gradient input difference is bounded by its two primitive
differences, on any fixed compact coefficient domain. The fixed projection
costs no derivative. The Hamilton comparison supplies the gradient term and
`exists_projectedStress_sub_tolerance` supplies the frame term.
Source: `app:ch_waves:thm:leading`, `app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_actualInput_sub_bound {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} {KF : Set (Euclidean n)}
    (hK : IsCompact K) (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hKU : K ⊆ inputDomain T) (hx : MapsTo Prod.fst K KF) :
    ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧ ∀ Q Q₀, ∀ m,
      cNorm K m (actualInput T Q - actualInput T Q₀) ≤
        B m * cNorm KF m (Q.1 - Q₀.1) +
        cNorm K m (fun w ↦ T.carrierGradient Q w.1 w.2 -
          T.carrierGradient Q₀ w.1 w.2) := by
  obtain ⟨B, hB, hb⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := Fin n → MetricTensor n) hK hKF
    (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  refine ⟨B, hB, ?_⟩
  intro Q Q₀ m
  have hs Q' := smooth_actualInput T hP Q'
  have hat Q' w (hw : w ∈ K) :=
    (hs Q').contDiffAt ((isOpen_inputDomain T).mem_nhds (hKU hw))
  have hp := cNorm_prodMk_le_on K hK m
    (fun w hw ↦ ((hat Q w hw).fst.sub (hat Q₀ w hw).fst).of_le (by simp))
    (fun w hw ↦ ((hat Q w hw).snd.sub (hat Q₀ w hw).snd).of_le (by simp))
  exact hp.trans (add_le_add
    (hb (Q.1 - Q₀.1) (fun x hx ↦
      (Q.2.1.sub Q₀.2.1).contDiffAt (hU.mem_nhds (hKFU hx))) m) le_rfl)

/-- Differences of the same primitive frame/gradient input control the
normalized direction and the actual adjugate nullvector. Only the reference
denominator must be nonzero; the compact formula buffer is constructed.
The actual minor producer supplies this gap. Source:
`app:ch_waves:thm:leading`, `app:ch_background:prop:bg-frame`. -/
theorem exists_carrier_direction_nullvector_sub_tolerance
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} (hK : IsCompact K)
    (hKU : K ⊆ inputDomain T) (Q₀ : _) (row col : Fin n)
    (hden₀ : ∀ w ∈ K, carrierAdaptedDenominator T Q₀ row col w ≠ 0)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Q,
      cNorm K m (actualInput T Q - actualInput T Q₀) < δ →
      cNorm K m (carrierTransportDirection T Q row col -
        carrierTransportDirection T Q₀ row col) < ε ∧
      cNorm K m (carrierNullvector T Q col - carrierNullvector T Q₀ col) < ε := by
  let V := {p : Input n | denominator T.data.adapted.normal row col p ≠ 0}
  have hV : IsOpen V := isOpen_ne.preimage (smooth_denominator _ row col).continuous
  have hd : ContDiffOn ℝ ∞ (direction T.data.adapted.normal row col) V := by
    intro p hp
    have hp' : p ∈ admissibleInputs T.data.adapted.normal row col ‖p‖
        |denominator T.data.adapted.normal row col p| := by
      change p ∈ closedBall 0 ‖p‖ ∧
        |denominator T.data.adapted.normal row col p| ≤
          |denominator T.data.adapted.normal row col p|
      exact ⟨mem_closedBall_zero_iff.mpr le_rfl, le_rfl⟩
    exact (smoothAt_direction (ν := T.data.adapted.normal) (r := row) (c := col)
      (abs_pos.mpr hp) hp').contDiffWithinAt
  have hf Q w (hw : w ∈ K) :=
    (smooth_actualInput T hP Q).contDiffAt ((isOpen_inputDomain T).mem_nhds (hKU hw))
  obtain ⟨dd, hdd, hdir⟩ := fixed_comp_tolerance hK hV hd (hf Q₀)
    (show MapsTo (actualInput T Q₀) K V from hden₀) m hε
  obtain ⟨dk, hdk, hnull⟩ := fixed_comp_tolerance hK isOpen_univ
    (smooth_right col).contDiffOn (hf Q₀) (mapsTo_univ _ _) m hε
  refine ⟨min dd dk, lt_min hdd hdk, ?_⟩
  intro Q hsmall
  exact ⟨hdir (actualInput T Q) (hf Q) (hsmall.trans_le (min_le_left _ _)),
    hnull (actualInput T Q) (hf Q) (hsmall.trans_le (min_le_right _ _))⟩

private theorem derivative_sub_bound
    {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    {K Ω : Set E} (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω)
    {f g : E → A} (hf : ContDiffOn ℝ ∞ f Ω) (hg : ContDiffOn ℝ ∞ g Ω) (m : ℕ) :
    cNorm K m (fderiv ℝ f - fderiv ℝ g) ≤ cNorm K (m + 1) (f - g) := by
  have he : cNorm K m (fderiv ℝ f - fderiv ℝ g) =
      cNorm K m (fderiv ℝ (f - g)) := by
    apply cNorm_eq_of_eventuallyEq _ m
    intro x hx
    filter_upwards [hΩ.mem_nhds (hKΩ hx)] with y hy
    exact (fderiv_sub ((hf.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))
      ((hg.contDiffAt (hΩ.mem_nhds hy)).differentiableAt (by simp))).symm
  rw [he]
  exact cNorm_fderiv_le K m (f - g)

/-- The literal potential is continuous in the primitive frame/gradient input
with one additional derivative, and in the immersion with loss two. This
proves the coefficient premise of the positive-null-flow comparison, including
the full connection term. The reference immersion supplies the metric unit;
the actual minor construction supplies the reference denominator gap.
No potential, nullvector-derivative or compact-range continuity is assumed.
Source: `app:ch_waves:thm:leading`, `app:ch_background:prop:bg-frame`. -/
theorem exists_carrier_potential_sub_tolerance
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} {KF : Set (Euclidean n)}
    (hK : IsCompact K) (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hKU : K ⊆ inputDomain T) (hx : MapsTo Prod.fst K KF)
    (Q₀ : _) {F₀ : Euclidean n → Euclidean N}
    (hF₀ : ContDiffOn ℝ ∞ F₀ U) (hi₀ : IsImmersionOn F₀ U)
    (row col : Fin n)
    (hden₀ : ∀ w ∈ K, carrierAdaptedDenominator T Q₀ row col w ≠ 0)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Q (F : Euclidean n → Euclidean N),
      ContDiffOn ℝ ∞ F U →
      cNorm K (m + 1) (actualInput T Q - actualInput T Q₀) < δ →
      cNorm KF (m + 2) (F - F₀) < δ →
      cNorm K m (carrierTransportPotential T Q F row col -
        carrierTransportPotential T Q₀ F₀ row col) < ε := by
  let V := {p : PotentialJet n N | IsUnit (firstJetMetric p.2.2.1) ∧
    denominator T.data.adapted.normal row col p.1 ≠ 0}
  have hmetric : Continuous (fun p : PotentialJet n N ↦ firstJetMetric p.2.2.1) :=
    contDiff_firstJetMetric.continuous.comp continuous_snd.snd.fst
  have hV : IsOpen V :=
    (Units.isOpen.preimage hmetric).inter
      (isOpen_ne.preimage ((smooth_denominator _ row col).continuous.comp continuous_fst))
  have ha : ContDiffOn ℝ ∞ (potentialFormula T.data.adapted.normal row col) V := by
    intro p hp
    exact (smoothAt_potentialFormula T.data.adapted.normal row col
      (p := p) hp.1 hp.2).contDiffWithinAt
  let v Q (F : Euclidean n → Euclidean N) (w : Euclidean n × Euclidean 3) : PotentialJet n N :=
    (actualInput T Q w, fderiv ℝ (carrierNullvector T Q col) w, stressJet F w.1)
  have hk Q : ContDiffOn ℝ ∞ (carrierNullvector T Q col) (inputDomain T) := by
    change ContDiffOn ℝ ∞ (right col ∘ actualInput T Q) (inputDomain T)
    exact (smooth_right col).comp_contDiffOn (smooth_actualInput T hP Q)
  have hJ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U) :
      ContDiffOn ℝ ∞ (fun w : Euclidean n × Euclidean 3 ↦ stressJet F w.1)
        (inputDomain T) :=
    (contDiffOn_stressJet hU hF).comp contDiffOn_fst (fun _ hw ↦ hw.1.1)
  have hv Q F (hF : ContDiffOn ℝ ∞ F U) : ContDiffOn ℝ ∞ (v Q F) (inputDomain T) :=
    (smooth_actualInput T hP Q).prodMk
      (((hk Q).fderiv_of_isOpen (isOpen_inputDomain T) (by simp)).prodMk (hJ F hF))
  have hat Q F hF w (hw : w ∈ K) :=
    (hv Q F hF).contDiffAt ((isOpen_inputDomain T).mem_nhds (hKU hw))
  have hr₀ : MapsTo (v Q₀ F₀) K V := fun w hw ↦
    ⟨firstJetMetric_isUnit_of_injective (hi₀ w.1 (hKU hw).1.1), hden₀ w hw⟩
  obtain ⟨d, hd, hpot⟩ := fixed_comp_tolerance hK hV ha (hat Q₀ F₀ hF₀) hr₀ m hε
  obtain ⟨dk, hdk, hnull⟩ := exists_carrier_direction_nullvector_sub_tolerance T hP
    hK hKU Q₀ row col hden₀ (m + 1) (show 0 < d / 3 by positivity)
  obtain ⟨B, hB, hb⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := StressJet n N) hK hKF (ψ := Prod.fst)
    (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  refine ⟨min dk (min (d / 3) (d / (6 * B m))),
    lt_min hdk (lt_min (by positivity) (div_pos hd (mul_pos (by norm_num) (hB m)))), ?_⟩
  intro Q F hF hinput hmap
  have hksmall := (hnull Q (hinput.trans_le (min_le_left _ _))).2
  have hdsmall := (derivative_sub_bound (isOpen_inputDomain T) hKU (hk Q) (hk Q₀) m).trans_lt hksmall
  have hjsmall : cNorm K m ((fun w : Euclidean n × Euclidean 3 ↦ stressJet F w.1) -
      (fun w ↦ stressJet F₀ w.1)) < d / 3 := by
    have hb' := hb (stressJet F - stressJet F₀) (fun x hx ↦
      ((contDiffOn_stressJet hU hF).sub (contDiffOn_stressJet hU hF₀)).contDiffAt
        (hU.mem_nhds (hKFU hx))) m
    have hj := CurrentGeometricNeighborhood.cNorm_stressJet_sub_le hKF hU hKFU hF hF₀ m
    have hm := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 6) (hB m))).mp
      (hmap.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact (hb'.trans (mul_le_mul_of_nonneg_left hj (hB m).le)).trans_lt (by nlinarith)
  have hinput' := (cNorm_mono_order (Nat.le_succ m)).trans_lt
    (hinput.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hp₂ := cNorm_prodMk_le_on K hK m
    (f := fderiv ℝ (carrierNullvector T Q col) - fderiv ℝ (carrierNullvector T Q₀ col))
    (g := fun w : Euclidean n × Euclidean 3 ↦ stressJet F w.1 - stressJet F₀ w.1)
    (fun w hw ↦ ((hat Q F hF w hw).snd.fst.sub (hat Q₀ F₀ hF₀ w hw).snd.fst).of_le (by simp))
    (fun w hw ↦ ((hat Q F hF w hw).snd.snd.sub (hat Q₀ F₀ hF₀ w hw).snd.snd).of_le (by simp))
  have hp₁ := cNorm_prodMk_le_on K hK m
    (f := actualInput T Q - actualInput T Q₀)
    (g := fun w ↦ (fderiv ℝ (carrierNullvector T Q col) w -
      fderiv ℝ (carrierNullvector T Q₀ col) w, stressJet F w.1 - stressJet F₀ w.1))
    (fun w hw ↦ ((hat Q F hF w hw).fst.sub (hat Q₀ F₀ hF₀ w hw).fst).of_le (by simp))
    (fun w hw ↦ ((hat Q F hF w hw).snd.sub (hat Q₀ F₀ hF₀ w hw).snd).of_le (by simp))
  have hvs : cNorm K m (v Q F - v Q₀ F₀) < d := by
    have hh := hp₁.trans_lt ((add_le_add le_rfl hp₂).trans_lt
      (add_lt_add hinput' (add_lt_add hdsmall hjsmall)))
    have heq : v Q F - v Q₀ F₀ = fun w ↦ ((actualInput T Q - actualInput T Q₀) w,
        (fderiv ℝ (carrierNullvector T Q col) w - fderiv ℝ (carrierNullvector T Q₀ col) w,
          stressJet F w.1 - stressJet F₀ w.1)) := rfl
    rw [heq]
    exact hh.trans_le (by linarith)
  have hout := hpot (v Q F) (hat Q F hF) hvs
  have he : cNorm K m (potentialFormula T.data.adapted.normal row col ∘ v Q F -
      potentialFormula T.data.adapted.normal row col ∘ v Q₀ F₀) =
      cNorm K m (carrierTransportPotential T Q F row col -
        carrierTransportPotential T Q₀ F₀ row col) := by
    apply cNorm_eq_of_eventuallyEq _ m
    intro w hw
    filter_upwards [(isOpen_inputDomain T).mem_nhds (hKU hw)] with y hy
    exact congrArg₂ (· - ·) (potentialFormula_actual T hP Q hF row col hy)
      (potentialFormula_actual T hP Q₀ hF₀ row col hy)
  rwa [he] at hout

/-- Primitive frame, retained Hamilton-gradient and immersion differences
control both coefficients of the actual positive-null-transport equation.
The requested coefficient order `m` uses frame and gradient order `m + 1`
and immersion order `m + 2`; the threshold precedes all varying data.
`exists_projectedStress_sub_tolerance` and the retained Hamilton comparison
are the producers of the first two differences. The actual minor construction
supplies the reference denominator gap. Source:
`app:ch_background:prop:bg-frame`, `app:ch_waves:thm:leading`. -/
theorem exists_carrier_coefficients_primitive_sub_tolerance
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)} {KF : Set (Euclidean n)}
    (hK : IsCompact K) (hKF : IsCompact KF) (hKFU : KF ⊆ U)
    (hKU : K ⊆ inputDomain T) (hx : MapsTo Prod.fst K KF)
    (Q₀ : _) {F₀ : Euclidean n → Euclidean N}
    (hF₀ : ContDiffOn ℝ ∞ F₀ U) (hi₀ : IsImmersionOn F₀ U)
    (row col : Fin n)
    (hden₀ : ∀ w ∈ K, carrierAdaptedDenominator T Q₀ row col w ≠ 0)
    (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Q (F : Euclidean n → Euclidean N),
      ContDiffOn ℝ ∞ F U →
      cNorm KF (m + 1) (Q.1 - Q₀.1) +
        cNorm K (m + 1) (fun w ↦ T.carrierGradient Q w.1 w.2 -
          T.carrierGradient Q₀ w.1 w.2) +
        cNorm KF (m + 2) (F - F₀) < δ →
      cNorm K m (carrierTransportDirection T Q row col -
        carrierTransportDirection T Q₀ row col) +
      cNorm K m (carrierTransportPotential T Q F row col -
        carrierTransportPotential T Q₀ F₀ row col) < ε := by
  obtain ⟨dd, hdd, hdirection⟩ := exists_carrier_direction_nullvector_sub_tolerance
    T hP hK hKU Q₀ row col hden₀ m (half_pos hε)
  obtain ⟨dp, hdp, hpotential⟩ := exists_carrier_potential_sub_tolerance T hP hK hKF
    hKFU hKU hx Q₀ hF₀ hi₀ row col hden₀ m (half_pos hε)
  obtain ⟨B, hB, hb⟩ := exists_actualInput_sub_bound T hP hK hKF hKFU hKU hx
  have hB' : 0 < B (m + 1) + 1 := by linarith [hB (m + 1)]
  refine ⟨min dp (min dd dp / (B (m + 1) + 1)),
    lt_min hdp (div_pos (lt_min hdd hdp) hB'), ?_⟩
  intro Q F hF hsmall
  have hq := cNorm_nonneg KF (m + 1) (Q.1 - Q₀.1)
  have hg := cNorm_nonneg K (m + 1) (fun w ↦
    T.carrierGradient Q w.1 w.2 - T.carrierGradient Q₀ w.1 w.2)
  have hf := cNorm_nonneg KF (m + 2) (F - F₀)
  have hsum := (lt_div_iff₀ hB').mp (hsmall.trans_le (min_le_right _ _))
  have hin : cNorm K (m + 1) (actualInput T Q - actualInput T Q₀) < min dd dp := by
    have hh := hb Q Q₀ (m + 1)
    have hnonneg := mul_nonneg (hB (m + 1)).le (add_nonneg hg hf)
    nlinarith
  have hmap : cNorm KF (m + 2) (F - F₀) < dp := by
    have hh := hsmall.trans_le (min_le_left _ _)
    linarith
  have hd := (hdirection Q ((cNorm_mono_order (Nat.le_succ m)).trans_lt
    (hin.trans_le (min_le_left _ _)))).1
  have hp := hpotential Q F hF (hin.trans_le (min_le_right _ _)) hmap
  linarith

/-- Primitive input differences control the exact reduced coefficient in
`coefficientsOfCarrier_data` on fixed physical/carrier compact sets, including
`CoefficientNormCharts.field.carrier`. The same fixed relabeling is used for
both carriers; no detector continuity is assumed. Source:
`app:ch_background:eq:bg-full-complex-amplitude`,
`app:ch_osc:prop:osc-normal`, Step 4'. -/
theorem exists_canonical_reduced_sub_tolerance
    {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n × Euclidean 3)}
    {L : Set (Euclidean n × ContinuumRow.CarrierParameter)}
    (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ inputDomain T)
    (hLK : MapsTo (fun p : Euclidean n × ContinuumRow.CarrierParameter ↦
      (p.1, ContinuumRow.CanonicalCarrier.parameter p.2)) L K)
    (Q₀ : _) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Q,
      cNorm K m (actualInput T Q - actualInput T Q₀) < δ →
      cNorm L m ((fun p : Euclidean n × ContinuumRow.CarrierParameter ↦
        (quadratic (Q.1 p.1)
          (T.carrierGradient Q p.1 (ContinuumRow.CanonicalCarrier.parameter p.2))).ofLp) -
        (fun p ↦ (quadratic (Q₀.1 p.1)
          (T.carrierGradient Q₀ p.1 (ContinuumRow.CanonicalCarrier.parameter p.2))).ofLp)) < ε := by
  let a : Input n → Fin n → ℝ := fun p ↦ (quadratic p.1 p.2).ofLp
  have ha : ContDiff ℝ ∞ a := PiLp.contDiff_ofLp.comp contDiff_quadratic
  let ψ := fun p : Euclidean n × ContinuumRow.CarrierParameter ↦
    (p.1, ContinuumRow.CanonicalCarrier.parameter p.2)
  have hψ : ContDiff ℝ ∞ ψ := contDiff_fst.prodMk
    (ContinuumRow.CanonicalCarrier.parameter.contDiff.comp contDiff_snd)
  obtain ⟨B, hB, hb⟩ := ConstructedCarrierJets.exists_cNorm_fixed_pullback_le
    (G := Fin n → ℝ) hL hK (fun _ _ ↦ hψ.contDiffAt) hLK
  have hf Q w (hw : w ∈ K) :=
    (smooth_actualInput T hP Q).contDiffAt ((isOpen_inputDomain T).mem_nhds (hKU hw))
  obtain ⟨d, hd, hc⟩ := fixed_comp_tolerance hK isOpen_univ ha.contDiffOn
    (hf Q₀) (mapsTo_univ _ _) m (div_pos hε (hB m))
  refine ⟨d, hd, ?_⟩
  intro Q hsmall
  have hcomp := hc (actualInput T Q) (hf Q) hsmall
  have hbound := hb (a ∘ actualInput T Q - a ∘ actualInput T Q₀)
    (fun w hw ↦ (ha.contDiffAt.comp w (hf Q w hw)).sub
      (ha.contDiffAt.comp w (hf Q₀ w hw))) m
  exact hbound.trans_lt (by
    simpa only [mul_comm] using (lt_div_iff₀ (hB m)).mp hcomp)

end JanetCartan.ContinuumNormal.CarrierVariation.FamilyInputs.PositiveReference
