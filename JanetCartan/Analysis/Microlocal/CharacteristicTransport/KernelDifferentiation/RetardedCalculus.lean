module

public import JanetCartan.Analysis.ODE.PositiveTransport.ParametricIntegral
public import JanetCartan.Analysis.Operator.RetardedSobolev.Transverse
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ScalarReduction
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Output differentiation of a retarded kernel

The finite time integral in `app:ch_regular_base:eq:energy-complete-residual`
retains its upper endpoint. These lemmas are consumed by the literal compact
Fourier kernel, whose joint smoothness is established from the primitive data.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.CharacteristicTransport.KernelDifferentiation
variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Smoothness of the variable-endpoint primitive used in
`app:ch_regular_base:eq:energy-complete-residual`. Compact time intervals
supply the domination; the integrand retains its output parameter. -/
theorem contDiff_retardedPrimitive {g : Euclidean n × ℝ → F}
    (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Euclidean n ↦ ∫ s in a..p.1, g (p.2, s)) := by
  have h : ContDiff ℝ ∞ (fun p : ℝ × Euclidean n ↦ ∫ r in (0:ℝ)..1,
      g (p.2, (p.1 - a) * r + a)) := by
    rw [← contDiffOn_univ]
    apply contDiffOn_fixedIntervalIntegral (F := fun z : ℝ × (ℝ × Euclidean n) ↦
      g (z.2.2, (z.2.1 - a) * z.1 + a)) isOpen_univ
    intro z _
    exact (hg.comp (contDiff_snd.snd.prodMk
      (((contDiff_snd.fst.sub contDiff_const).mul contDiff_fst).add contDiff_const))).contDiffAt
  have hh := (contDiff_fst.sub (contDiff_const (c := a))).smul h
  convert hh using 1
  funext p
  simpa using (intervalIntegral.smul_integral_comp_mul_add
    (fun s ↦ g (p.2, s)) (a := 0) (b := 1) (p.1 - a) a).symm

/-- The output derivative of the retarded primitive, including the upper
endpoint in `app:ch_regular_base:eq:energy-complete-residual`. Source time
is fixed in the derivative under the integral. -/
theorem fderiv_retardedPrimitive_apply {g : Euclidean (n + 1) × ℝ → F} (hg : ContDiff ℝ ∞ g)
    (a : ℝ) (x w : Euclidean (n + 1)) :
    fderiv ℝ (fun y ↦ ∫ s in a..y 0, g (y,s)) x w =
      (w 0) • g (x, x 0) + ∫ s in a..x 0, fderiv ℝ (fun y ↦ g (y,s)) x w := by
  let H : ℝ × Euclidean (n + 1) → F := fun p ↦ ∫ s in a..p.1, g (p.2,s)
  have hH : Differentiable ℝ H := (contDiff_retardedPrimitive hg a).differentiable (by simp)
  have hc : HasFDerivAt (fun y : Euclidean (n + 1) ↦ (y 0,y))
      ((EuclideanSpace.proj 0).prod (ContinuousLinearMap.id ℝ _)) x :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))).hasFDerivAt.prodMk (hasFDerivAt_id x)
  have hcomp := (hH (x 0,x)).hasFDerivAt.comp x (f := fun y ↦ (y 0,y)) hc
  change (fderiv ℝ (H ∘ fun y ↦ (y 0,y)) x) w = _
  rw [hcomp.fderiv]
  change fderiv ℝ H (x 0,x) (w 0,w) = _
  have ht : (fderiv ℝ H (x 0,x)) (w 0,0) = (w 0) • g (x,x 0) := by
    have hct : Continuous (fun s ↦ g (x,s)) := hg.continuous.comp
      (continuous_const.prodMk continuous_id)
    have hh := intervalIntegral.integral_hasDerivAt_right (hct.intervalIntegrable a (x 0))
      hct.aestronglyMeasurable.stronglyMeasurableAtFilter hct.continuousAt
    have he := ((hH (x 0,x)).hasFDerivAt.comp (x 0)
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) (x 0) x)).fderiv
    have he' := congrArg (fun L : ℝ →L[ℝ] F ↦ L (w 0)) (he.symm.trans hh.hasFDerivAt.fderiv)
    exact he'
  have hp : fderiv ℝ H (x 0,x) (0,w) =
      ∫ s in a..x 0, fderiv ℝ (fun y ↦ g (y,s)) x w := by
    have hi := RetardedSobolev.hasFDerivAt_intervalIntegral_parameter_of_contDiff
      (hg.of_le (by simp)) a (x 0) x
    have he := ((hH (x 0,x)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right (x 0) x)).fderiv
    have he' := congrArg (fun L : Euclidean (n + 1) →L[ℝ] F ↦ L w) (he.symm.trans hi.fderiv)
    change fderiv ℝ H (x 0,x) (0,w) = _ at he'
    have hdi : IntervalIntegrable (fun s ↦ (fderiv ℝ g (x,s)).comp
        (ContinuousLinearMap.inl ℝ (Euclidean (n + 1)) ℝ)) volume a (x 0) :=
      (((hg.continuous_fderiv (by simp)).comp
        (continuous_const.prodMk continuous_id)).clm_comp continuous_const).intervalIntegrable _ _
    rw [he', ContinuousLinearMap.intervalIntegral_apply hdi]
    apply intervalIntegral.integral_congr
    intro s _
    exact congrArg (fun L : Euclidean (n + 1) →L[ℝ] F ↦ L w)
      (((hg.differentiable (by simp)) (x,s)).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left x s)).fderiv.symm
  rw [show (w 0,w) = (w 0,0) + (0,w) by simp, map_add, ht, hp]
open WKB
variable {n : ℕ} {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedSpace ℝ F] [CompleteSpace F]

/-- The full physical first-order operator passes through the retarded time
integral, retaining exactly its time-coefficient endpoint and its zeroth-order
term (`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem firstOrderApply_retardedPrimitive {g : Euclidean (n + 1) × ℝ → F} (hg : ContDiff ℝ ∞ g)
    (C : Euclidean (n + 1) → Fin (n + 1) → F →L[ℂ] F)
    (D : Euclidean (n + 1) → F →L[ℂ] F) (a : ℝ) (x : Euclidean (n + 1)) :
    firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
      (fun y ↦ ∫ s in a..y 0, g (y,s)) x =
      C x 0 (g (x,x 0)) + ∫ s in a..x 0,
        firstOrderApply (fun y j ↦ (C y j).toLinearMap) (fun y ↦ (D y).toLinearMap)
          (fun y ↦ g (y,s)) x := by
  have hd : Continuous (fun p : Euclidean (n + 1) × ℝ ↦
      fderiv ℝ (fun y ↦ g (y,p.2)) p.1) := by
    have hh := contDiffOn_parameterFDeriv (U := Set.univ) (V := Set.univ)
      isOpen_univ isOpen_univ hg.contDiffOn
    exact (contDiffOn_univ.mp (by simpa using hh)).continuous
  have hi (j : Fin (n + 1)) : IntervalIntegrable
      (fun s ↦ partialDeriv (fun y ↦ g (y,s)) x j) volume a (x 0) :=
    ((hd.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const).intervalIntegrable _ _
  have hv : IntervalIntegrable (fun s ↦ g (x,s)) volume a (x 0) :=
    (hg.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hc (j : Fin (n + 1)) : IntervalIntegrable
      (fun s ↦ C x j (partialDeriv (fun y ↦ g (y,s)) x j)) volume a (x 0) :=
    ((C x j).continuous.comp
      ((hd.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const)).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun s ↦ D x (g (x,s))) volume a (x 0) :=
    ((D x).continuous.comp (hg.continuous.comp
      (continuous_const.prodMk continuous_id))).intervalIntegrable _ _
  have hsum : IntervalIntegrable (fun s ↦ ∑ j, C x j
      (partialDeriv (fun y ↦ g (y,s)) x j)) volume a (x 0) := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun j _ ↦ hc j)
  simp only [partialDeriv] at hi hc hsum
  simp only [firstOrderApply, partialDeriv, fderiv_retardedPrimitive_apply hg,
    ContinuousLinearMap.coe_coe, map_add]
  rw [intervalIntegral.integral_add hsum hb,
    intervalIntegral.integral_finsetSum (fun j _ ↦ hc j)]
  simp only [Finset.sum_add_distrib]
  have he : (∑ j : Fin (n + 1), C x j
      ((EuclideanSpace.single j (1:ℝ) 0) • g (x,x 0))) = C x 0 (g (x,x 0)) := by
    rw [Fin.sum_univ_succ]
    simp [EuclideanSpace.single]
  rw [he]
  have hm (j : Fin (n + 1)) : C x j (∫ s in a..x 0,
      fderiv ℝ (fun y ↦ g (y,s)) x (EuclideanSpace.single j 1)) =
      ∫ s in a..x 0, C x j (fderiv ℝ (fun y ↦ g (y,s)) x (EuclideanSpace.single j 1)) :=
    ((C x j).intervalIntegral_comp_comm (hi j)).symm
  simp_rw [hm, ← (D x).intervalIntegral_comp_comm hv]
  exact add_assoc _ _ _

end JanetCartan.CharacteristicTransport.KernelDifferentiation
