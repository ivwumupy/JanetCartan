module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalPhase
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedCarrierJets

/-!
# Primitive budgets for the literal Hamilton transported position

The geometry input of `exists_carrierL2Extension_globalNormal_of_primitiveNorms`
is the covector derivative of the retained phase. Its order `m` uses immersion
order `m + 4`, so the constructor's order `s + 2` uses `s + 6`.
Source: `app:ch_background:eq:bg-mixed-input`, `app:ch_background:eq:bg-T`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Metric Filter
open scoped ContDiff InnerProductSpace Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.CanonicalCarrier
open ActualCarriers FrozenMenu CurrentFullPhase HamiltonPhase ProjectedStressFrame
open ActualCarriers.ConstructedCarrierJets

private def covectorInclusion (n : ℕ) :
    Euclidean (n - 1) →L[ℝ] Euclidean n × (ℝ × Euclidean (n - 1)) :=
  (ContinuousLinearMap.inr ℝ (Euclidean n) (ℝ × Euclidean (n - 1))).comp
    (ContinuousLinearMap.inr ℝ ℝ (Euclidean (n - 1)))

private def covectorExtraction (n : ℕ) :
    ((Euclidean n × (ℝ × Euclidean (n - 1))) →L[ℝ] ℝ) →L[ℝ] Euclidean (n - 1) :=
  (InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((ContinuousLinearMap.compL ℝ (Euclidean (n - 1))
      (Euclidean n × (ℝ × Euclidean (n - 1))) ℝ).flip (covectorInclusion n))

private theorem norm_covectorExtraction_le (n : ℕ) : ‖covectorExtraction n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro L
  change ‖(InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm
    (L.comp (covectorInclusion n))‖ ≤ 1 * ‖L‖
  rw [LinearIsometryEquiv.norm_map, one_mul]
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro v
  simpa [covectorInclusion] using L.le_opNorm (0, (0, v))

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

private def phaseRestriction (p : Euclidean n × CarrierParameter) :
    Euclidean n × (ℝ × Euclidean (n - 1)) :=
  T.carrierRestriction (p.1, parameter p.2)

private theorem phaseRestriction_smooth {c C : ℝ} (hP : P.IsValid c C) :
    ContDiffOn ℝ ∞ (phaseRestriction T)
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ
        (parameter ⁻¹' parameterInterior (2 * P.radius))) :=
  (T.carrierRestriction_smooth hP).comp
    (contDiffOn_fst.prodMk (parameter.contDiff.contDiffOn.comp contDiffOn_snd
      (fun _ _ ↦ mem_univ _))) (fun _ hp ↦ hp)

private theorem transportPosition_eq_extraction (Q : _)
    {p : Euclidean n × CarrierParameter}
    (hp : p ∈ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius))) :
    transportPosition T Q p = covectorExtraction n
      (fderiv ℝ (phase (T.currentChart Q).coordinates) (phaseRestriction T p)) := by
  rw [transportPosition_eq_hamiltonGradient]
  let S := phase (T.currentChart Q).coordinates
  have hp' : phaseRestriction T p ∈ (T.currentChart Q).target :=
    T.carrierRestriction_mem_target Q (q := (p.1, parameter p.2)) hp
  have hS : DifferentiableAt ℝ S (phaseRestriction T p) :=
    ((T.currentChart Q).hasFDerivAt_phase hp').differentiableAt
  have hi : HasFDerivAt (fun ζ : Euclidean (n - 1) ↦ (p.1, (0, ζ)))
      (covectorInclusion n) (T.reference.spatialPatch (parameter p.2)) := by
    simpa [covectorInclusion] using
      ((covectorInclusion n).hasFDerivAt (x := T.reference.spatialPatch (parameter p.2))).const_add
        (p.1, ((0 : ℝ), (0 : Euclidean (n - 1))))
  have hd := (hS.hasFDerivAt.comp
    (f := fun ζ : Euclidean (n - 1) ↦ (p.1, (0, ζ)))
    (T.reference.spatialPatch (parameter p.2)) hi).fderiv
  change (InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm
    (fderiv ℝ (fun ζ ↦ S (p.1, (0, ζ))) _) = _
  exact congrArg (InnerProductSpace.toDual ℝ (Euclidean (n - 1))).symm hd

/-- The actual Hamilton transported position has a fixed pullback estimate
from one full phase derivative. The domain is independent of the current
frame, and the function is the literal `d_ζ S`, not the ODE footpoint.
Consumer: the geometry budget in `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem exists_transportPosition_le_phase {c C : ℝ} (hP : P.IsValid c C)
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hLO : L ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius))) :
    ∃ A : ℕ → ℝ, (∀ m, 0 < A m) ∧ ∀ Q m,
      cNorm L m (transportPosition T Q) ≤ A m *
        cNorm (closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
          T.data.adapted.baseData.2) T.family.radius) (m + 1)
          (phase (T.currentChart Q).coordinates) := by
  let O := ball (0 : Euclidean n) T.physicalRadius ×ˢ
    (parameter ⁻¹' parameterInterior (2 * P.radius))
  have hO : IsOpen O := isOpen_ball.prod
    ((isOpen_parameterInterior _).preimage parameter.continuous)
  have hψ : ∀ x ∈ L, ContDiffAt ℝ ∞ (phaseRestriction T) x :=
    fun x hx ↦ (phaseRestriction_smooth T hP).contDiffAt (hO.mem_nhds (hLO hx))
  choose A hA hb using fun m ↦ exists_cNorm_fixed_pullback_le_jet_bound
    (G := Euclidean (n - 1)) hL hψ m
  refine ⟨A, hA, fun Q m ↦ ?_⟩
  let S := phase (T.currentChart Q).coordinates
  let Kphase := closedBall (T.data.adapted.embedding T.data.adapted.baseData.1,
    T.data.adapted.baseData.2) T.family.radius
  have hS : ∀ x ∈ Kphase, ContDiffAt ℝ ∞ S x := fun x hx ↦
    (T.family.phase_smooth Q).contDiffAt (isOpen_ball.mem_nhds
      (closedBall_subset_ball (by linarith [T.family.radius_pos] :
        T.family.radius < 2 * T.family.radius) hx))
  have hψK : MapsTo (phaseRestriction T) L Kphase := fun p hp ↦
    ball_subset_closedBall (T.carrierRestriction_mem_target Q (hLO hp))
  let g := covectorExtraction n ∘ fderiv ℝ S
  have hg : ∀ x ∈ Kphase, ContDiffAt ℝ ∞ g x := fun x hx ↦
    (covectorExtraction n).contDiff.contDiffAt.comp x
      ((hS x hx).fderiv_right (m := ∞) (by simp))
  have he : cNorm L m (transportPosition T Q) = cNorm L m (g ∘ phaseRestriction T) := by
    apply GeometricProfile.cNorm_eq_of_eventuallyEq _ m
    intro p hp
    exact eventuallyEq_of_mem (hO.mem_nhds (hLO hp))
      (fun q hq ↦ transportPosition_eq_extraction T Q hq)
  rw [he]
  apply hb m g (cNorm Kphase (m + 1) S) (cNorm_nonneg ..)
    (fun x hx ↦ (hg _ (hψK hx)).of_le (by simp))
  intro j hj x hx
  calc
    _ ≤ ‖covectorExtraction n‖ *
        ‖iteratedFDeriv ℝ j (fderiv ℝ S) (phaseRestriction T x)‖ :=
      (covectorExtraction n).norm_iteratedFDeriv_comp_left
        ((hS _ (hψK hx)).fderiv_right (m := ∞) (by simp)) (by simp)
    _ ≤ 1 * ‖iteratedFDeriv ℝ j (fderiv ℝ S) (phaseRestriction T x)‖ :=
      mul_le_mul_of_nonneg_right (norm_covectorExtraction_le n) (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ (j + 1) S (phaseRestriction T x)‖ := by
      rw [one_mul, norm_iteratedFDeriv_fderiv]
    _ ≤ _ := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      (fun y hy ↦ (hS y hy).of_le (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞))
      (hψK hx) (by omega)

/-- Sharp one-high estimate for the SAME projected-stress transported
position. All constants precede the immersion and its high norms.
Source: `app:ch_background:eq:bg-mixed-input`; the global carrier constructor
uses this at `m = s + 2`. -/
theorem exists_projected_transportPosition_bound {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hLO : L ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)))
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
        ∀ m, cNorm L m (transportPosition T Q) ≤ A m * (1 + cNorm K (m + 4) F) := by
  obtain ⟨D, hD, hd⟩ := exists_transportPosition_le_phase T hP hL hLO
  obtain ⟨B, hB, hb⟩ := T.exists_projected_phase_sharp_bound
    (N := N) hK hKU hball C₀ hκmet hκ
  refine ⟨fun m ↦ D m * B (m + 1), fun m ↦ mul_pos (hD m) (hB _), ?_⟩
  intro F hF hi hrank hlowF hmet hnormal hlow
  dsimp only
  intro m
  apply (hd _ m).trans
  simpa only [Nat.add_assoc, Nat.reduceAdd, mul_assoc] using
    mul_le_mul_of_nonneg_left (hb F hF hi hrank hlowF hmet hnormal hlow (m + 1)) (hD m).le

/-- The exact low geometry and order-`s+2` high geometry premises of the
released global carrier constructor, with a common additive reserve fourteen.
The fixed primitive `C¹⁵` immersion budget supplies the low geometry bound;
the initial scalar contributes only a nonnegative term. All constants precede
both varying inputs. Source: `app:ch_background:eq:bg-mixed-input`. -/
theorem exists_projected_transportPosition_primitive_bounds {N : ℕ}
    {c C : ℝ} (hP : P.IsValid c C)
    {L : Set (Euclidean n × CarrierParameter)} (hL : IsCompact L)
    (hLO : L ⊆ ball (0 : Euclidean n) T.physicalRadius ×ˢ
      (parameter ⁻¹' parameterInterior (2 * P.radius)))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    {M₁₅ κmet κ : ℝ} (hM₁₅ : 0 ≤ M₁₅) (hκmet : 0 < κmet) (hκ : 0 < κ)
    (Kinitial : Set (Euclidean (n - 1) × Euclidean 3)) :
    ∃ M > 0, ∃ B : ℕ → ℝ, (∀ s, 1 ≤ B s) ∧
      ∀ (F : Euclidean n → Euclidean N) (hF : ContDiffOn ℝ ∞ F U)
        (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U),
        cNorm K 15 F ≤ M₁₅ →
        (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
        (∀ x ∈ K, ∀ w ∈ normalSpace F x,
          κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
        ∀ hlow : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
            (projectedStress F - fun _ ↦ cubeStress n) < T.family.threshold,
        let Q := ⟨projectedStress F,
          contDiffOn_pi.mpr (contDiffOn_projectedStress hU hF hi hrank), hlow⟩
        cNorm L 3 (transportPosition T Q) ≤ M ∧
        ∀ (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) s,
          1 + cNorm L (s + 2) (transportPosition T Q) ≤
            B s * (1 + cNorm K (s + 14) F + cNorm Kinitial (s + 14) initial) := by
  obtain ⟨A, hA, hb⟩ := exists_projected_transportPosition_bound T (N := N)
    hP hL hLO hK hKU hball M₁₅ hκmet hκ
  refine ⟨A 3 * (1 + M₁₅), mul_pos (hA 3) (by positivity),
    fun s ↦ 1 + A (s + 2), fun s ↦ by linarith [hA (s + 2)], ?_⟩
  intro F hF hi hrank hFM hmet hnormal hlow
  dsimp only
  have hfour : cNorm K 4 F ≤ M₁₅ := (cNorm_mono_order (by omega)).trans hFM
  have hseven : cNorm K (3 + 4) F ≤ M₁₅ := (cNorm_mono_order (by omega)).trans hFM
  have hh := hb F hF hi hrank hfour hmet hnormal hlow
  constructor
  · exact (hh 3).trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hseven) (hA 3).le)
  · intro initial s
    have hs := hh (s + 2)
    have horder : cNorm K ((s + 2) + 4) F ≤ cNorm K (s + 14) F :=
      cNorm_mono_order (by omega)
    have hh' := hs.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl 1) horder) (hA (s + 2)).le)
    have hf0 := cNorm_nonneg K (s + 14) F
    have hr0 := cNorm_nonneg Kinitial (s + 14) initial
    nlinarith [mul_nonneg (hA (s + 2)).le hr0]

end JanetCartan.ContinuumRow.CanonicalCarrier
