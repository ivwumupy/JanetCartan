module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.NullTransport.Reduction
public import JanetCartan.Geometry.IsometricEmbedding.Normal.SmoothProjection
public import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# Joint regularity of the actual reduced operator

The zeroth-order normalized coefficient in `app:ch_waves:thm:leading` involves
physical derivatives at fixed carrier parameters. This leaf proves their joint
regularity, including the actual induced connection, from a smooth family of
immersions. Its consumer is `contDiffOn_normalizedZerothCoefficient`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.NullTransport

variable {n N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {s : Set (Euclidean n × E)}

/-- Physical differentiation at fixed parameters preserves joint smoothness
on the open patch of `app:ch_waves:thm:leading`. -/
theorem contDiffOn_physicalPartialDeriv {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {f : Euclidean n × E → W} (hs : IsOpen s)
    (hf : ContDiffOn ℝ ∞ f s) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun p ↦ partialDeriv (fun x ↦ f (x, p.2)) p.1 i) s := by
  have hd := (hf.fderiv_of_isOpen hs (m := ∞) (by simp)).clm_apply
    (contDiffOn_const (c := (EuclideanSpace.single i 1, (0 : E))))
  apply hd.congr
  intro p hp
  have hf' := (hf.contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)
  have he0 : HasFDerivAt (fun x : Euclidean n ↦ (x, p.2))
      ((ContinuousLinearMap.id ℝ (Euclidean n)).prod 0) p.1 :=
    (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
  have he := hf'.hasFDerivAt.comp (f := fun x ↦ (x, p.2)) p.1 he0
  change HasFDerivAt (fun x ↦ f (x, p.2)) _ p.1 at he
  rw [partialDeriv, he.fderiv]
  rfl

-- Use the established Frobenius matrix norm, not the nested product norm.
private def coefficientEntry (i j : Fin n) : MetricTensor n →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ ℝ) j).comp
      (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n ↦ Fin n → ℝ) i))

private def coefficientTensor (n : ℕ) : (Fin n → Fin n → ℝ) →L[ℝ] MetricTensor n :=
  { LinearMap.id with cont := continuous_id }

/-- Joint regularity of the induced metric of the family in
`app:ch_waves:eq:reduced-symbol`. -/
theorem contDiffOn_inducedMetric_joint {F : Euclidean n × E → Euclidean N}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s) :
    ContDiffOn ℝ ∞ (fun p ↦ inducedMetric (fun x ↦ F (x, p.2)) p.1) s := by
  apply (coefficientTensor n).contDiff.comp_contDiffOn
  exact contDiffOn_pi.mpr fun i ↦ contDiffOn_pi.mpr fun j ↦
    (contDiffOn_physicalPartialDeriv hs hF i).inner ℝ
      (contDiffOn_physicalPartialDeriv hs hF j)

/-- Immersion supplies invertibility, so the inverse metric in the actual
connection is jointly smooth (`app:ch_waves:eq:reduced-symbol`). -/
theorem contDiffOn_inducedMetric_inv_joint {F : Euclidean n × E → Euclidean N}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : ∀ p ∈ s, Function.Injective (fderiv ℝ (fun x ↦ F (x, p.2)) p.1)) :
    ContDiffOn ℝ ∞ (fun p ↦ (inducedMetric (fun x ↦ F (x, p.2)) p.1)⁻¹) s := by
  intro p hp
  have hu := (inducedMetric_posDef (himm p hp)).isUnit
  have hi : ContDiffAt ℝ ∞ Ring.inverse (inducedMetric (fun x ↦ F (x, p.2)) p.1) := by
    simpa only [IsUnit.unit_spec] using contDiffAt_ringInverse ℝ hu.unit
  simpa only [Matrix.nonsing_inv_eq_ringInverse, Function.comp_def] using
    hi.comp_contDiffWithinAt p (contDiffOn_inducedMetric_joint hs hF p hp)

/-- All actual Christoffel terms are jointly smooth for the supplied smooth
family of immersions (`app:ch_waves:eq:reduced-symbol`). -/
theorem contDiffOn_christoffel_joint {F : Euclidean n × E → Euclidean N}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : ∀ p ∈ s, Function.Injective (fderiv ℝ (fun x ↦ F (x, p.2)) p.1))
    (i j k : Fin n) :
    ContDiffOn ℝ ∞ (fun p ↦ christoffel (fun x ↦ F (x, p.2)) p.1 i j k) s := by
  have hg (a b : Fin n) := (coefficientEntry a b).contDiff.comp_contDiffOn
    (contDiffOn_inducedMetric_joint hs hF)
  have hgi (a b : Fin n) := (coefficientEntry a b).contDiff.comp_contDiffOn
    (contDiffOn_inducedMetric_inv_joint hs hF himm)
  unfold christoffel
  apply contDiffOn_const.mul
  apply ContDiffOn.sum
  intro l _
  exact (hgi k l).mul (((contDiffOn_physicalPartialDeriv hs (hg j l) i).add
    (contDiffOn_physicalPartialDeriv hs (hg i l) j)).sub
      (contDiffOn_physicalPartialDeriv hs (hg i j) l))

/-- Joint smoothness of `P_G u` follows from smooth immersion, frame and
covector fields, retaining the connection (`app:ch_waves:eq:reduced-symbol`). -/
theorem contDiffOn_reducedOperator_joint {F : Euclidean n × E → Euclidean N}
    {Q : Euclidean n × E → Fin n → MetricTensor n}
    {u : Euclidean n × E → Euclidean n}
    (hs : IsOpen s) (hF : ContDiffOn ℝ ∞ F s)
    (himm : ∀ p ∈ s, Function.Injective (fderiv ℝ (fun x ↦ F (x, p.2)) p.1))
    (hQ : ∀ i a b, ContDiffOn ℝ ∞ (fun p ↦ Q p i a b) s)
    (hu : ContDiffOn ℝ ∞ u s) (i : Fin n) :
    ContDiffOn ℝ ∞ (fun p ↦ reducedOperator (fun x ↦ F (x, p.2))
      (fun x ↦ Q (x, p.2)) (fun x ↦ u (x, p.2)) p.1 i) s := by
  have huc := (contDiffOn_piLp 2).mp hu
  simp only [reducedOperator, tensorPairing, symmCovariantDeriv]
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  apply (hQ i a b).mul
  apply ContDiffOn.sub
  · exact ((contDiffOn_physicalPartialDeriv hs (huc b) a).add
      (contDiffOn_physicalPartialDeriv hs (huc a) b)).div_const 2
  · exact ContDiffOn.sum fun k _ ↦
      (contDiffOn_christoffel_joint hs hF himm a b k).mul (huc k)

end JanetCartan.NullTransport
