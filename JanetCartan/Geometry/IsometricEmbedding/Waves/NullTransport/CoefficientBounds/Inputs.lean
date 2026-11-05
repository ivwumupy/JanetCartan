module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.CoefficientBounds.Algebra
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets.LowBounds

/-!
# Primitive joint budgets for the actual null coefficients

The consumer is the fixed-jet composition in `app:ch_waves:eq:joint-tame`.
The frame and carrier gradient are both instantiated from the same immersion;
all low and high constants are chosen before that immersion.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace JanetCartan.NullTransport.CoefficientBounds

section Pair
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The two primitive coefficient inputs retain one high norm
(`app:ch_waves:eq:joint-tame`). -/
theorem cNorm_pair_le (a : E) {ρ : ℝ} (r : ℕ)
    {U : Set E} (hU : IsOpen U) (hball : closedBall a ρ ⊆ U)
    {f : E → F} {g : E → G} (hf : ContDiffOn ℝ ∞ f U)
    (hg : ContDiffOn ℝ ∞ g U) :
    cNorm (closedBall a ρ) r (fun x ↦ (f x, g x)) ≤
      (r + 1 : ℝ) * (cNorm (closedBall a ρ) r f + cNorm (closedBall a ρ) r g) := by
  have hfr (x : E) (hx : x ∈ closedBall a ρ) : ContDiffAt ℝ r f x :=
    (hf.contDiffAt (hU.mem_nhds (hball hx))).of_le (by simp)
  have hgr (x : E) (hx : x ∈ closedBall a ρ) : ContDiffAt ℝ r g x :=
    (hg.contDiffAt (hU.mem_nhds (hball hx))).of_le (by simp)
  have hF := cNorm_nonneg (closedBall a ρ) r f
  have hG := cNorm_nonneg (closedBall a ρ) r g
  have h := cNorm_le_sum_of_bounds (s := closedBall a ρ) (r := r)
    (f := fun x ↦ (f x, g x))
    (C := fun _ ↦ cNorm (closedBall a ρ) r f + cNorm (closedBall a ρ) r g)
    (fun _ _ ↦ by positivity) (by
      intro j hj x hx
      rw [iteratedFDeriv_prodMk (hfr x hx) (hgr x hx) (by exact_mod_cast hj),
        ContinuousMultilinearMap.opNorm_prod]
      exact max_le
        ((norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
          (fun y hy ↦ hfr y hy) hx hj).trans (by linarith))
        ((norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall a ρ)
          (fun y hy ↦ hgr y hy) hx hj).trans (by linarith)))
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] using h

end Pair

open ActualCarriers FrozenMenu CurrentFullPhase ProjectedStressFrame
open ActualCarriers.ConstructedCarrierJets

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)

/-- The same frame and gradient as the literal coefficients in
`ActualCoefficients` (`app:ch_waves:thm:leading`). -/
def actualInput (Q : {Q : Euclidean n → Fin n → MetricTensor n //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (w : Euclidean n × Euclidean 3) : Input n :=
  (Q.1 w.1, T.carrierGradient Q w.1 w.2)

/-- Common open domain of the primitive coefficient inputs
(`app:ch_waves:eq:joint-tame`). -/
def inputDomain : Set (Euclidean n × Euclidean 3) :=
  (U ∩ ball (0 : Euclidean n) T.physicalRadius) ×ˢ parameterInterior (2 * P.radius)

/-- The common input domain is open, so its joint derivatives are ordinary
Fréchet derivatives (`app:ch_waves:eq:joint-tame`). -/
theorem isOpen_inputDomain : IsOpen (inputDomain T) :=
  (hU.inter isOpen_ball).prod (isOpen_parameterInterior _)

/-- Joint input regularity, without assuming coefficient regularity
(`app:ch_waves:eq:joint-tame`). -/
theorem smooth_actualInput {c C : ℝ} (hP : P.IsValid c C) (Q : _) :
    ContDiffOn ℝ ∞ (actualInput T Q) (inputDomain T) :=
  (Q.2.1.comp contDiffOn_fst (fun _ hw ↦ hw.1.1)).prodMk
    ((T.carrierGradient_smooth hP Q).mono fun _ hw ↦ ⟨hw.1.2, hw.2⟩)

/-- Primitive `C⁶` frame closeness supplies a fixed joint `C¹` budget for
the actual input. This supplies the value range and the low direction bound
in `app:ch_waves:thm:leading`, independently of high immersion norms. -/
theorem exists_actualInput_low_bound {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean n × Euclidean 3) (ρ : ℝ)
    (hx : MapsTo Prod.fst (closedBall a ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hballU : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ U)
    (hc : closedBall a ρ ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius)) :
    ∃ δ L : ℝ, 0 < δ ∧ 0 < L ∧ ∀ Q,
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q.1 - fun _ ↦ cubeStress n) < δ →
      cNorm (closedBall a ρ) 1 (actualInput T Q) ≤ L := by
  obtain ⟨δ, Lξ, hδ, hLξ, hξ⟩ :=
    T.exists_carrierGradient_low_bound hP (isCompact_closedBall a ρ) hc
  obtain ⟨A, hA, ha⟩ := exists_cNorm_fixed_pullback_le
    (G := Fin n → MetricTensor n) (isCompact_closedBall a ρ) (isCompact_closedBall _ _)
    (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  let LQ := 1 + cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 1
    (fun _ : Euclidean n ↦ cubeStress n)
  have hLQ : 0 < LQ := by
    have := cNorm_nonneg (closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
      1 (fun _ : Euclidean n ↦ cubeStress n)
    dsimp [LQ]
    linarith
  refine ⟨min δ 1, 2 * (A 1 * LQ + Lξ), lt_min hδ zero_lt_one,
    by have := hA 1; positivity, ?_⟩
  intro Q hclose
  have hQ := T.frame_low_bound hballU Q (hclose.trans_le (min_le_right _ _))
  have hQ' := ha Q.1 (fun x hx ↦ Q.2.1.contDiffAt (hU.mem_nhds (hballU hx))) 1
  have hξ' := hξ Q (hclose.trans_le (min_le_left _ _))
  have hdom : closedBall a ρ ⊆ inputDomain T :=
    fun w hw ↦ ⟨⟨hballU (hx hw), (hc hw).1⟩, (hc hw).2⟩
  have hb := cNorm_pair_le a 1 (isOpen_inputDomain T) hdom
    (Q.2.1.comp contDiffOn_fst (fun _ hw ↦ hw.1.1))
    ((T.carrierGradient_smooth hP Q).mono fun _ hw ↦ ⟨hw.1.2, hw.2⟩)
  change cNorm (closedBall a ρ) 1 (actualInput T Q) ≤ _ at hb
  dsimp only [Function.comp_def] at hQ'
  change cNorm _ 1 Q.1 ≤ LQ at hQ
  have hQ'' := hQ'.trans (mul_le_mul_of_nonneg_left hQ (hA 1).le)
  norm_num only [Nat.cast_one, Function.comp_def] at hb
  linarith

/-- The projected stress loss two and the identical carrier-gradient loss
four yield a joint input estimate with fixed reserve four. No input high
estimate is assumed (`app:ch_waves:eq:joint-tame`). -/
theorem exists_projected_actualInput_bound {c C : ℝ} (hP : P.IsValid c C)
    (a : Euclidean n × Euclidean 3) (ρ : ℝ)
    (hx : MapsTo Prod.fst (closedBall a ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hc : closedBall a ρ ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      parameterInterior (2 * P.radius))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (C₀ : ℝ) {κmet κ : ℝ} (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 4 F ≤ C₀ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        ∀ m, cNorm (closedBall a ρ) m (actualInput T Q) ≤
          A m * (1 + cNorm K (m + 4) F) := by
  obtain ⟨D, hD, hd⟩ := exists_cNorm_fixed_pullback_le
    (G := Fin n → MetricTensor n) (isCompact_closedBall a ρ) (isCompact_closedBall _ _)
    (ψ := Prod.fst) (fun _ _ ↦ contDiff_fst.contDiffAt) hx
  obtain ⟨B, hB, hb⟩ := T.exists_projected_carrierGradient_sharp_bound
    (N := N) hP (isCompact_closedBall a ρ) hc hK hKU hball C₀ hκmet hκ
  choose A hA ha using fun m ↦ exists_cNorm_projectedStress_le_tame
    (N := N) (0 : Euclidean n) T.data.localReference.stateRadius_pos C₀ hκmet hκ m
  refine ⟨fun m ↦ (m + 1) * (D m * ((m + 1) * A m) + B m),
    fun m ↦ by have := hD m; have := hA m; have := hB m; positivity, ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow
  dsimp only
  intro m
  let Q := (⟨projectedStress F,
    contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩ :
      {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
  have hs := Q.2.1
  have hframe := frame_cNorm_le_of_componentwise
    (isCompact_closedBall (0 : Euclidean n) T.data.localReference.stateRadius)
    (fun x hx ↦ (hs.contDiffAt (hU.mem_nhds (hKU (hball hx)))).of_le
      (by simp : (m : ℕ∞ω) ≤ ∞))
    (mul_nonneg (hA m).le (by linarith [cNorm_nonneg K (m + 2) F]))
    (ha m F U K hU hK hball hKU hF hi hlowF hmet hnormal)
  have hframe' := hd Q.1
    (fun x hx ↦ hs.contDiffAt (hU.mem_nhds (hKU (hball hx)))) m
  have hgrad := hb F hF hi hrank hlowF hmet hnormal hlow m
  have hdom : closedBall a ρ ⊆ inputDomain T :=
    fun w hw ↦ ⟨⟨hKU (hball (hx hw)), (hc hw).1⟩, (hc hw).2⟩
  have hpair := cNorm_pair_le a m (isOpen_inputDomain T) hdom
    (hs.comp contDiffOn_fst (fun _ hw ↦ hw.1.1))
    ((T.carrierGradient_smooth hP Q).mono fun _ hw ↦ ⟨hw.1.2, hw.2⟩)
  apply hpair.trans
  have horder : cNorm K (m + 2) F ≤ cNorm K (m + 4) F := cNorm_mono_order (by omega)
  have hframe'' : cNorm (closedBall a ρ) m (fun w ↦ Q.1 w.1) ≤
      (D m * ((m + 1) * A m)) * (1 + cNorm K (m + 4) F) := by
    apply hframe'.trans
    apply (mul_le_mul_of_nonneg_left hframe (hD m).le).trans
    calc
      _ = (D m * ((m + 1) * A m)) * (1 + cNorm K (m + 2) F) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) horder)
        (mul_nonneg (hD m).le (mul_nonneg (by positivity) (hA m).le))
  have hsum := add_le_add hframe'' hgrad
  have hh := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ m + 1)
  exact hh.trans_eq (by ring)

end JanetCartan.NullTransport.CoefficientBounds
