module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Leading.FullModulation.UniformCoefficients.Principal

/-!
# The existing potential formula with full-modulation derivatives

Only the derivative input is restricted to physical/carrier directions; the
value input still contains the independent full covector. This reuses the
literal finite-jet formula, including all Christoffel terms, from
`NullTransport.CoefficientBounds` (`app:ch_waves:thm:leading`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.LeadingWave.FullModulation.UniformCoefficients
open NullTransport NullTransport.CoefficientBounds ProjectedStressFrame GeometricProfile

variable {n N : ℕ}

/-- Fixed inclusion used only to evaluate physical derivatives in the already
published potential formula (`app:ch_waves:eq:joint-tame`). -/
def physicalCarrierInclusion : (Euclidean n × Euclidean 3) →L[ℝ]
    Euclidean n × (Euclidean 3 × Euclidean (n - 1)) :=
  (ContinuousLinearMap.fst ℝ _ _).prod ((ContinuousLinearMap.snd ℝ _ _).prod 0)

/-- Full joint derivative input for the same transport potential
(`app:ch_waves:eq:joint-tame`). -/
abbrev FullPotentialJet (n N : ℕ) := Input n ×
  (((Euclidean n × (Euclidean 3 × Euclidean (n - 1))) →L[ℝ] Euclidean n) × StressJet n N)

/-- The published finite-jet potential evaluated on the full derivative
(`app:ch_waves:thm:leading`). -/
def fullPotentialFormula (ν : Euclidean n) (r c : Fin n) (p : FullPotentialJet n N) : ℝ :=
  potentialFormula ν r c (p.1, p.2.1.comp physicalCarrierInclusion, p.2.2)

/-- Smoothness uses precisely the metric and denominator gaps of the original
formula (`app:ch_waves:eq:joint-tame`). -/
theorem smoothAt_fullPotentialFormula (ν : Euclidean n) (r c : Fin n)
    {p : FullPotentialJet n N} (hmet : IsUnit (firstJetMetric p.2.2.1))
    (hden : denominator ν r c p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (fullPotentialFormula ν r c) p :=
by
  have hm : ContDiff ℝ ∞ (fun q : FullPotentialJet n N ↦
      (q.1, q.2.1.comp (physicalCarrierInclusion (n := n)), q.2.2)) :=
    contDiff_fst.prodMk ((contDiff_snd.fst.clm_comp contDiff_const).prodMk contDiff_snd.snd)
  exact (smoothAt_potentialFormula ν r c
    (p := (p.1, p.2.1.comp physicalCarrierInclusion, p.2.2)) hmet hden).comp p hm.contDiffAt

/-- Physical derivatives with both independent parameters fixed are evaluations
of the full joint derivative (`app:ch_waves:eq:joint-tame`). -/
theorem physical_partial_eq_full_joint
    {k : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Euclidean n}
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hk : DifferentiableAt ℝ k w) (a b : Fin n) :
    partialDeriv (fun x ↦ k (x, w.2) b) w.1 a =
      (fderiv ℝ k w (EuclideanSpace.single a 1, 0)) b := by
  have he : HasFDerivAt (fun x : Euclidean n ↦ (x, w.2))
      ((ContinuousLinearMap.id ℝ (Euclidean n)).prod 0) w.1 :=
    (hasFDerivAt_id w.1).prodMk (hasFDerivAt_const w.2 w.1)
  have hd := (EuclideanSpace.proj (𝕜 := ℝ) b).hasFDerivAt.comp w.1
    (hk.hasFDerivAt.comp w.1 he)
  change HasFDerivAt (fun x ↦ k (x, w.2) b) _ w.1 at hd
  rw [partialDeriv, hd.fderiv]
  rfl

open ActualCarriers FrozenMenu CurrentFullPhase

/-- The finite-jet formula equals the named full potential on its open domain,
including every physical covariant derivative (`app:ch_waves:thm:leading`). -/
theorem fullPotentialFormula_actual {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : _) {F : Euclidean n → Euclidean N} (hF : ContDiffOn ℝ ∞ F U)
    (r c : Fin n) {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))}
    (hw : w ∈ inputDomain T) :
    fullPotentialFormula T.data.adapted.normal r c
      (fullInput T Q w, fderiv ℝ (nullvector T Q c) w, stressJet F w.1) =
      transportPotential T Q F r c w := by
  have hk : DifferentiableAt ℝ (nullvector T Q c) w :=
    ((smooth_right c).comp_contDiffOn (smooth_fullInput T Q)).contDiffAt
      ((isOpen_inputDomain T).mem_nhds hw) |>.differentiableAt (by simp)
  have hp := physical_partial_eq_full_joint hk
  simp only [fullPotentialFormula, potentialFormula, physicalCarrierInclusion,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, transportPotential, reducedOperator, tensorPairing,
    symmCovariantDeriv, dotProduct, hp,
    ← secondJetChristoffel_eq_at (hF.contDiffAt (hU.mem_nhds hw.2))]
  rfl

end JanetCartan.LeadingWave.FullModulation.UniformCoefficients
