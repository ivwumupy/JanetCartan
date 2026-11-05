module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence.Gradient
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.ConstructedIncidence.Primitive
public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.IncidenceRoots.Frozen

/-!
# Incidence comparison from primitive frame closeness

This discharges the value, scalar derivative and full Fréchet derivative
comparison obligations on one fixed buffered cylinder. All carriers are the
canonical carriers of the supplied quantitative chart family. The consumer is
`exists_uniform_current_incidence_roots`, Step 3 of
`app:ch_seed:prop:seed-actual-menu`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ActualCarriers
open FrozenMenu CharacteristicRoot CurrentFullPhase

/-- The frozen scalar derivative is unchanged on adjoining the physical
variable (`app:ch_seed:prop:seed-actual-menu`, Step 3). -/
theorem scalarDerivative_frozenDeterminantIncidence_lift {n : ℕ} {P : Patch n}
    {c C : ℝ} (hP : P.IsValid c C) (z : Euclidean 3)
    (p : (Euclidean n × Euclidean n) × ℝ)
    (hz : incidenceParameter z p.2 ∈ parameterCube P.radius) :
    scalarDerivative (fun w : (Euclidean n × Euclidean n) × ℝ ↦
      frozenDeterminantIncidence P z (w.1.2, w.2)) p =
      scalarDerivative (frozenDeterminantIncidence P z) (p.1.2, p.2) := by
  have hh := ((contDiffAt_frozenDeterminantIncidence hP z (p.1.2, p.2) hz).differentiableAt
    (by simp)).hasFDerivAt.comp p (((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).snd).prodMk
      (hasFDerivAt_snd (𝕜 := ℝ) (p := p)))
  exact congrArg (fun L ↦ L (0, 1)) hh.fderiv

namespace CurrentFullPhase.PatchQuantitativeFamily
variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- On any prescribed buffered cylinder inside the fixed physical and
construction balls, primitive frame `C⁶` closeness gives joint smoothness
and all three incidence comparisons. The tolerance and threshold precede the
current frame, and no carrier or incidence jet error is assumed
(`app:ch_seed:prop:seed-actual-menu`, Step 3).

The compact construction ball contains the retained frame ball. The finite
assembly takes minima of these positive thresholds for its fixed refinement. -/
theorem exists_current_incidence_comparison_threshold {c C : ℝ} (hP : P.IsValid c C)
    {b r : ℝ} (hBU : closedBall (0 : Euclidean n) b ⊆ U)
    (hframe : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆
      closedBall (0 : Euclidean n) b)
    (hr : 3 * r < T.physicalRadius) (hrb : 3 * r < b)
    (k : Euclidean n) (ρ : ℝ) (z : Euclidean 3) (a : ℝ)
    (hparam : ∀ t ∈ Icc (-a) a, incidenceParameter z t ∈ parameterCube P.radius)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n //
      ContDiffOn ℝ ∞ Q U ∧ cNorm (closedBall (0 : Euclidean n)
        T.data.localReference.stateRadius) 6 (Q - fun _ ↦ cubeStress n) < T.family.threshold}),
      cNorm (closedBall (0 : Euclidean n) b) 6 (Q.1 - fun _ ↦ cubeStress n) < δ →
      ∀ p ∈ closedBall (0 : Euclidean n) (3 * r) ×ˢ closedBall k (2 * ρ),
      ∀ t ∈ Icc (-a) a,
        let f := currentIncidence Q.1 (T.carrier Q) z
        let f₀ := frozenDeterminantIncidence P z
        ContDiffAt ℝ ∞ f (p, t) ∧
        |f (p, t) - f₀ (p.2, t)| < ε ∧
        |scalarDerivative f (p, t) - scalarDerivative f₀ (p.2, t)| < ε ∧
        ‖fderiv ℝ f (p, t) - fderiv ℝ
          (fun w : (Euclidean n × Euclidean n) × ℝ ↦ f₀ (w.1.2, w.2)) (p, t)‖ < ε := by
  let S := (closedBall (0 : Euclidean n) (3 * r) ×ˢ closedBall k (2 * ρ)) ×ˢ Icc (-a) a
  let G₀ : Euclidean n × Euclidean 3 → Euclidean n := fun w ↦ P.toFun w.2
  let F₀ := incidencePrimitive (fun _ : Euclidean n ↦ cubeStress n) G₀ z
  have hS : IsCompact S := ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).prod
    isCompact_Icc
  have hG₀ (p : (Euclidean n × Euclidean n) × ℝ) (hp : p ∈ S) :
      ContDiffAt ℝ ∞ G₀ (p.1.1, incidenceParameter z p.2) :=
    (hP.2.2.2.1.contDiffAt ((isOpen_parameterInterior _).mem_nhds
      (parameterCube_subset_doubledInterior hP.1 (hparam p.2 hp.2)))).comp (p.1.1, incidenceParameter z p.2) contDiffAt_snd
  have hF₀ : ∀ p ∈ S, ContDiffAt ℝ ∞ F₀ p :=
    fun p hp ↦ contDiffAt_incidencePrimitive contDiffAt_const (hG₀ p hp)
  have hJ : IsCompact ((fun p ↦ (F₀ p, fderiv ℝ F₀ p)) '' S) :=
    hS.image_of_continuousOn (fun p hp ↦ (hF₀ p hp).continuousAt.continuousWithinAt.prodMk
      ((hF₀ p hp).fderiv_right (m := ∞) (by simp)).continuousAt.continuousWithinAt)
  obtain ⟨d, hd, hjet⟩ := exists_uniform_incidence_firstJet_radius hJ hε
  obtain ⟨e, he, hG⟩ := T.exists_carrier_joint_comparison_threshold hP (half_pos hd)
  refine ⟨min e (d / 2), lt_min he (half_pos hd), fun Q hQ p hp t ht ↦ ?_⟩
  have hreg : ∀ x ∈ closedBall (0 : Euclidean n) b,
      ContDiffAt ℝ 6 (Q.1 - fun _ ↦ cubeStress n) x := fun x hx ↦
    ((Q.2.1.contDiffAt (hU.mem_nhds (hBU hx))).sub contDiffAt_const).of_le (by simp)
  have hlocal : cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q.1 - fun _ ↦ cubeStress n) < e :=
    (cNorm_mono_set_of_contDiffAt hframe (isCompact_closedBall _ _) hreg).trans_lt
      (hQ.trans_le (min_le_left _ _))
  have hx : p.1 ∈ ball (0 : Euclidean n) T.physicalRadius := closedBall_subset_ball hr hp.1
  have hxb : p.1 ∈ closedBall (0 : Euclidean n) b :=
    closedBall_subset_closedBall hrb.le hp.1
  have hz := hparam t ht
  have hg := hG Q hlocal p.1 hx (incidenceParameter z t) hz
  have hQx := Q.2.1.contDiffAt (hU.mem_nhds (hBU hxb))
  have hvQ : ‖Q.1 p.1 - cubeStress n‖ ≤ d / 2 := by
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      hreg hxb (by omega : 0 ≤ 6)
    have hv : ‖Q.1 p.1 - cubeStress n‖ ≤
        cNorm (closedBall (0 : Euclidean n) b) 6 (Q.1 - fun _ ↦ cubeStress n) := by
      simpa only [norm_iteratedFDeriv_zero, Pi.sub_apply] using hb
    exact hv.trans (hQ.le.trans (min_le_right _ _))
  have hdQ : ‖fderiv ℝ Q.1 p.1 - fderiv ℝ (fun _ : Euclidean n ↦ cubeStress n) p.1‖ ≤ d / 2 := by
    have hb := norm_iteratedFDeriv_le_cNorm_of_contDiffAt (isCompact_closedBall _ _)
      hreg hxb (by omega : 1 ≤ 6)
    rw [norm_iteratedFDeriv_one, fderiv_sub (hQx.differentiableAt (by simp))
      (differentiableAt_const (cubeStress n))] at hb
    exact hb.trans (hQ.le.trans (min_le_right _ _))
  let G : Euclidean n × Euclidean 3 → Euclidean n := fun w ↦ T.carrierGradient Q w.1 w.2
  let F := incidencePrimitive Q.1 G z
  have hpS : (p, t) ∈ S := ⟨hp, ht⟩
  have hGs : ContDiffAt ℝ ∞ G (p.1, incidenceParameter z t) :=
    (T.carrierGradient_smooth hP Q).contDiffAt
      ((isOpen_ball.prod (isOpen_parameterInterior _)).mem_nhds
        ⟨hx, parameterCube_subset_doubledInterior hP.1 hz⟩)
  have hFs : ContDiffAt ℝ ∞ F (p, t) := contDiffAt_incidencePrimitive hQx hGs
  have hprim := incidencePrimitive_firstJet_comparison
    (Q := Q.1) (Q₀ := fun _ ↦ cubeStress n) (G := G) (G₀ := G₀)
    (z := z) (p := (p, t)) (half_pos hd).le
    (hQx.differentiableAt (by simp)) (differentiableAt_const (cubeStress n))
    (hGs.differentiableAt (by simp)) ((hG₀ (p, t) hpS).differentiableAt (by simp))
    hvQ hg.1 hdQ hg.2
  have hcomp := hjet (F₀ (p, t), fderiv ℝ F₀ (p, t)) ⟨(p, t), hpS, rfl⟩
    (F (p, t), fderiv ℝ F (p, t))
    (hprim.1.trans_lt (half_lt_self hd)) (hprim.2.trans_lt (half_lt_self hd))
  have houter := (contDiff_incidenceCoefficient (n := n)).differentiable (by simp)
  have hfull : ‖fderiv ℝ (incidenceCoefficient ∘ F) (p, t) -
      fderiv ℝ (incidenceCoefficient ∘ F₀) (p, t)‖ < ε := by
    rw [fderiv_comp _ houter.differentiableAt (hFs.differentiableAt (by simp)),
      fderiv_comp _ houter.differentiableAt ((hF₀ (p, t) hpS).differentiableAt (by simp))]
    exact hcomp.2
  refine ⟨(contDiff_incidenceCoefficient (n := n)).contDiffAt.comp _ hFs, hcomp.1, ?_, hfull⟩
  rw [← scalarDerivative_frozenDeterminantIncidence_lift hP z (p, t) hz]
  have hh := (fderiv ℝ (incidenceCoefficient ∘ F) (p, t) -
    fderiv ℝ (incidenceCoefficient ∘ F₀) (p, t)).le_opNorm (0, 1)
  have hhn : |scalarDerivative (incidenceCoefficient ∘ F) (p, t) -
      scalarDerivative (incidenceCoefficient ∘ F₀) (p, t)| ≤
      ‖fderiv ℝ (incidenceCoefficient ∘ F) (p, t) -
        fderiv ℝ (incidenceCoefficient ∘ F₀) (p, t)‖ := by
    simpa only [scalarDerivative, sub_apply, Real.norm_eq_abs,
      Prod.norm_def, norm_zero, norm_one, max_eq_right zero_le_one, mul_one] using hh
  exact hhn.trans_lt hfull

end CurrentFullPhase.PatchQuantitativeFamily
end JanetCartan.ActualCarriers
