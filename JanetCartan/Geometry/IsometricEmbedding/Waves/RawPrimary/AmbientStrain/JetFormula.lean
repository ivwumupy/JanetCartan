module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.FrameBounds
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.Correction.CoefficientBounds

/-!
# Finite jets for the cubic ambient residual

The coefficient in `app:ch_waves:eq:WKB-residual` uses the actual projected
stress of the immersion second jet and one joint derivative of the correction.
The inverse Gram, both complex quadratures and the Christoffel terms are
part of the formula, not analytic inputs. Its consumer is the joint strain
estimate in `app:ch_waves:eq:WKB-strain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Matrix
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.RawPrimary.AmbientStrain
open ProjectedStressFrame GeometricProfile NullTransport NullTransport.CoefficientBounds

variable {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The SAME projected cube frame as a function of the immersion jet
(`app:ch_waves:eq:WKB-residual`). -/
def jetFrame (J : StressJet n N) : Fin n → MetricTensor n :=
  fun i ↦ jetStress (cubeStress n i) J

/-- The residual uses two immersion derivatives and one correction derivative
(`app:ch_waves:eq:WKB-strain`). -/
abbrev Jet (n N : ℕ) (Z : Type*) [NormedAddCommGroup Z] [NormedSpace ℝ Z] :=
  StressJet n N × (EuclideanSpace ℂ (Fin n) ×
    ((Euclidean n × Z) →L[ℝ] EuclideanSpace ℂ (Fin n)))

/-- The full covariant reduced operator on correction jets, before reconstruction
(`app:ch_waves:eq:WKB-residual`). -/
def reducedJet (p : Jet n N Z) : Fin n → ℂ := fun i ↦
  (∑ a, ∑ k, (jetFrame p.1 i a k : ℂ) *
    (p.2.2 (EuclideanSpace.single a 1, 0)) k) -
  ∑ k, (∑ a, ∑ b, (jetFrame p.1 i a b : ℂ) *
    (secondJetChristoffel p.1 a b k : ℂ)) * p.2.1 k

/-- The literal inverse-Gram coefficient of `2τ³`, in the Frobenius tensor
space (`app:ch_waves:eq:WKB-residual`). -/
def reconstructionJet (p : Jet n N Z) : Matrix (Fin n) (Fin n) ℂ :=
  WKB.stressReconstruction (jetFrame p.1) (reducedJet p)

/-- Smoothness of the actual projected frame on the primitive geometric gap
locus (`app:ch_waves:eq:WKB-strain`). -/
theorem contDiffAt_jetFrame {J : StressJet n N}
    (hmet : IsUnit (jetMetric J)) (hA : IsUnit (jetAmbient J)) :
    ContDiffAt ℝ ∞ jetFrame J :=
  contDiffAt_pi.mpr fun i ↦ contDiffAt_jetStress hmet hA (cubeStress n i)

private def matrixOfEntries (𝕜 : Type*) [RCLike 𝕜] :
    (Fin n → Fin n → 𝕜) →L[ℝ] Matrix (Fin n) (Fin n) 𝕜 :=
  { LinearMap.id with cont := continuous_id }

/-- The Frobenius Gram polynomial is smooth
(`app:ch_waves:eq:WKB-residual`). -/
theorem contDiff_stressGram : ContDiff ℝ ∞ (@WKB.stressGram n n) := by
  apply (matrixOfEntries ℝ).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ ∞ (fun Q : Fin n → MetricTensor n ↦ ∑ a, ∑ b, Q i a b * Q j a b)
  apply ContDiff.sum
  intro a _
  apply ContDiff.sum
  intro b _
  exact ((Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.comp
    (contDiff_pi.mp contDiff_id i)).mul
      ((Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.comp
        (contDiff_pi.mp contDiff_id j))

/-- All covariant reduced coefficients are smooth on the metric and normal
gap locus (`app:ch_waves:eq:WKB-grading`). -/
theorem contDiffAt_reducedJet {p : Jet n N Z}
    (hmet : IsUnit (jetMetric p.1)) (hA : IsUnit (jetAmbient p.1))
    (hg : IsUnit (firstJetMetric p.1.1)) :
    ContDiffAt ℝ ∞ reducedJet p := by
  have hQ := (contDiffAt_jetFrame hmet hA).comp p contDiffAt_fst
  have hq (i a b : Fin n) : ContDiffAt ℝ ∞
      (fun q : Jet n N Z ↦ (jetFrame q.1 i a b : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p
      ((Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.contDiffAt.comp p
        (contDiffAt_pi.mp hQ i))
  have hc (a b k : Fin n) : ContDiffAt ℝ ∞
      (fun q : Jet n N Z ↦ (secondJetChristoffel q.1 a b k : ℂ)) p :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p
      ((contDiffAt_secondJetChristoffel hg a b k).comp p contDiffAt_fst)
  have hd (a k : Fin n) : ContDiffAt ℝ ∞
      (fun q : Jet n N Z ↦ (q.2.2 (EuclideanSpace.single a 1, 0)) k) p :=
    (EuclideanSpace.proj (𝕜 := ℂ) k).restrictScalars ℝ |>.contDiff.contDiffAt.comp p
      (contDiffAt_snd.snd.clm_apply contDiffAt_const)
  have hv (k : Fin n) : ContDiffAt ℝ ∞ (fun q : Jet n N Z ↦ q.2.1 k) p :=
    ((EuclideanSpace.proj (𝕜 := ℂ) k).restrictScalars ℝ).contDiff.contDiffAt.comp p
      contDiffAt_snd.fst
  apply contDiffAt_pi.mpr
  intro i
  exact (ContDiffAt.sum fun a _ ↦ ContDiffAt.sum fun k _ ↦ (hq i a k).mul (hd a k)).sub
    (ContDiffAt.sum fun k _ ↦ (ContDiffAt.sum fun a _ ↦
      ContDiffAt.sum fun b _ ↦ (hq i a b).mul (hc a b k)).mul (hv k))

/-- The actual inverse Gram is differentiated inside the reconstruction.
No bound or regularity of the ambient strain is an input
(`app:ch_waves:eq:WKB-strain`). -/
theorem contDiffAt_reconstructionJet {p : Jet n N Z}
    (hmet : IsUnit (jetMetric p.1)) (hA : IsUnit (jetAmbient p.1))
    (hg : IsUnit (firstJetMetric p.1.1))
    (hGram : IsUnit (WKB.stressGram (jetFrame p.1))) :
    ContDiffAt ℝ ∞ reconstructionJet p := by
  have hQ := (contDiffAt_jetFrame hmet hA).comp p contDiffAt_fst
  have hInv := (contDiffAt_matrix_inv hGram).comp p
    (contDiff_stressGram.contDiffAt.comp p hQ)
  have hr := contDiffAt_reducedJet hmet hA hg (Z := Z)
  apply (matrixOfEntries ℂ).contDiff.contDiffAt.comp p
  apply contDiffAt_pi.mpr
  intro a
  apply contDiffAt_pi.mpr
  intro b
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  change ContDiffAt ℝ ∞ (fun q : Jet n N Z ↦
    ∑ i, ∑ j, ((WKB.stressGram (jetFrame q.1))⁻¹ i j : ℂ) * reducedJet q j *
      (jetFrame q.1 i a b : ℂ)) p
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp p
    ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.contDiffAt.comp p hInv)).mul
      (contDiffAt_pi.mp hr j)).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp p
          ((Matrix.entryLinearMap ℝ ℝ a b).toContinuousLinearMap.contDiff.contDiffAt.comp p
            (contDiffAt_pi.mp hQ i)))

/-- The finite formula is the original complex operator at the original
physical point and parameters (`app:ch_waves:eq:WKB-residual`). -/
theorem reconstructionJet_actual {F : Euclidean n → Euclidean N}
    {b : Euclidean n × Z → EuclideanSpace ℂ (Fin n)} {w : Euclidean n × Z}
    (hF : ContDiffAt ℝ ∞ F w.1) (hi : Function.Injective (fderiv ℝ F w.1))
    (hb : DifferentiableAt ℝ b w) :
    reconstructionJet (stressJet F w.1, b w, fderiv ℝ b w) =
      WKB.stressReconstruction (projectedStress F w.1)
        (fun i ↦ complexReducedOperator F (projectedStress F)
          (fun x ↦ b (x, w.2)) w.1 i) := by
  have hQ : jetFrame (stressJet F w.1) = projectedStress F w.1 :=
    funext fun i ↦ jetStress_stressJet (hF.of_le (by simp)) hi i
  have hd (a k : Fin n) : partialDeriv (fun x ↦ b (x, w.2) k) w.1 a =
      (fderiv ℝ b w (EuclideanSpace.single a 1, 0)) k := by
    have he : HasFDerivAt (fun x : Euclidean n ↦ (x, w.2))
        ((ContinuousLinearMap.id ℝ (Euclidean n)).prod 0) w.1 :=
      (hasFDerivAt_id w.1).prodMk (hasFDerivAt_const w.2 w.1)
    have hh := ((EuclideanSpace.proj (𝕜 := ℂ) k).restrictScalars ℝ).hasFDerivAt.comp w.1
      (hb.hasFDerivAt.comp w.1 he)
    change HasFDerivAt (fun x ↦ b (x, w.2) k) _ w.1 at hh
    rw [partialDeriv, hh.fderiv]
    rfl
  unfold reconstructionJet
  rw [hQ]
  congr 1
  funext i
  simp only [reducedJet, hQ, complexReducedOperator, principalCoefficient,
    reducedZerothCoefficient, hd, secondJetChristoffel_eq_at hF,
    Complex.ofReal_neg, Complex.ofReal_sum, Complex.ofReal_mul, neg_mul,
    Finset.sum_neg_distrib, sub_eq_add_neg, PiLp.toLp_apply]

end JanetCartan.RawPrimary.AmbientStrain
