module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets.Support
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
/-!
# Frequency measurability of the actual output jets

For `app:ch_response:thm:response-literal-transfer`, the source integral is
jointly measurable in the target and the two frequencies. Its ordered target
derivatives are measurable as limits of difference quotients. The existing
compact-source identity identifies these derivatives with the true output-jet
kernels, without assuming joint continuity of target derivatives or frequency
smoothness of either phase. The final scalar theorem supplies the measurability
premise for dominated frequency differentiation in `FrequencyJets.Differentiation`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope
open FourierIntegral NormalComparison JanetCartan.Localization

-- Use the topology of the Frobenius norm, as in the matrix derivative API.
local instance frequencyJetMeasurabilityMatrixTopology (r : ℕ) : TopologicalSpace (Matrix (Fin r) (Fin r) ℂ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin r) (n := Fin r)
    (α := ℂ)).toUniformSpace.toTopologicalSpace

/-- Difference quotients preserve joint measurability under target-only smoothness.
This supplies the measurable matrix jets of the source integral for
`app:ch_response:thm:response-literal-transfer`. -/
private theorem stronglyMeasurable_matrixJets {n r : ℕ}
    (g : Euclidean n → (Euclidean n × Euclidean n) → Matrix (Fin r) (Fin r) ℂ)
    (hg : StronglyMeasurable (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      g p.1 p.2))
    (hs : ∀ p, ContDiff ℝ ∞ (fun x ↦ g x p)) (α : List (Fin n)) :
    StronglyMeasurable (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      normalMatrixDerivList α (fun x ↦ g x p.2) p.1) := by
  induction α with
  | nil => exact hg
  | cons i α ih =>
    apply stronglyMeasurable_of_tendsto (𝓝[≠] (0 : ℝ))
      (f := fun (t : ℝ) (p : Euclidean n × (Euclidean n × Euclidean n)) ↦ t⁻¹ •
        (normalMatrixDerivList α (fun x ↦ g x p.2)
          (p.1 + t • EuclideanSpace.single i 1) -
          normalMatrixDerivList α (fun x ↦ g x p.2) p.1))
    · intro t
      exact ((ih.comp_measurable
        ((measurable_fst.add measurable_const).prodMk measurable_snd)).sub ih).const_smul (t⁻¹)
    · apply tendsto_pi_nhds.mpr
      intro p
      exact (((contDiff_normalMatrixDerivList (hs p.2) α).differentiable
        (by simp) p.1).hasFDerivAt.hasLineDerivAt
        (EuclideanSpace.single i 1)).tendsto_slope_zero

variable {n r : ℕ}

/-- Measurable parameter integration for the undifferentiated split-phase kernel
in `app:ch_response:thm:response-literal-transfer`. -/
private theorem stronglyMeasurable_sourceKernel_joint (τ : Euclidean n → Euclidean n → ℝ)
    (σ : Euclidean n → Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (hτ : Continuous (fun p : Euclidean n × Euclidean n ↦ τ p.1 p.2))
    (hσ : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      σ p.1.1 p.1.2 p.2))
    (hA : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A p.1.1 p.1.2 p.2)) :
    StronglyMeasurable (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      sourceKernel (fun y ↦ τ p.1 p.2.1 + σ p.2.1 p.2.2 y) A p.1 p.2.1) := by
  have hc : Continuous (fun q : (Euclidean n × (Euclidean n × Euclidean n)) ×
      Euclidean n ↦ phaseOscillation
        (fun y ↦ τ q.1.1 q.1.2.1 + σ q.1.2.1 q.1.2.2 y) q.2 •
          A q.1.1 q.2 q.1.2.1) := by
    have ht : Continuous (fun q : (Euclidean n × (Euclidean n × Euclidean n)) ×
        Euclidean n ↦ τ q.1.1 q.1.2.1 + σ q.1.2.1 q.1.2.2 q.2) :=
      (hτ.comp (f := fun q : (Euclidean n × (Euclidean n × Euclidean n)) ×
          Euclidean n ↦ (q.1.1, q.1.2.1)) (by fun_prop)).add
        (hσ.comp (f := fun q : (Euclidean n × (Euclidean n × Euclidean n)) ×
          Euclidean n ↦ (q.1.2, q.2)) (by fun_prop))
    have ha : Continuous (fun q : (Euclidean n × (Euclidean n × Euclidean n)) ×
        Euclidean n ↦ A q.1.1 q.2 q.1.2.1) :=
      hA.comp (f := fun q : (Euclidean n × (Euclidean n × Euclidean n)) ×
        Euclidean n ↦ ((q.1.1, q.2), q.1.2.1)) (by fun_prop)
    exact (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp ht).mul continuous_const)).smul ha
  exact hc.stronglyMeasurable.integral_prod_right

/-- Joint measurability of the actual output-jet source kernel, used to justify
frequency differentiation in `app:ch_response:thm:response-literal-transfer`.
Only the target slices of `τ` and source slices of `σ` need be smooth. -/
theorem stronglyMeasurable_sourceKernel_outputJet_splitPhase
    (τ : Euclidean n → Euclidean n → ℝ)
    (σ : Euclidean n → Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (hτ : Continuous (fun p : Euclidean n × Euclidean n ↦ τ p.1 p.2))
    (hσ : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      σ p.1.1 p.1.2 p.2))
    (hτs : ∀ η, ContDiff ℝ ∞ (τ · η))
    (hσs : ∀ η θ, ContDiff ℝ ∞ (σ η θ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A p.1.1 p.1.2 p.2))
    {Ks : Set (Euclidean n)} (hKs : IsCompact Ks)
    (hs : ∀ x y η, y ∉ Ks → A x y η = 0) (α : List (Fin n)) :
    StronglyMeasurable (fun p : Euclidean n × (Euclidean n × Euclidean n) ↦
      sourceKernel (fun y ↦ τ p.1 p.2.1 + σ p.2.1 p.2.2 y)
        (outputJetAmplitude τ α A) p.1 p.2.1) := by
  have hAs (η : Euclidean n) :
      ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η) :=
    hA.comp (contDiff_id.prodMk contDiff_const)
  have hm := stronglyMeasurable_matrixJets
    (fun x p ↦ sourceKernel (fun y ↦ τ x p.1 + σ p.1 p.2 y) A x p.1)
    (stronglyMeasurable_sourceKernel_joint τ σ A hτ hσ hA.continuous)
    (fun p ↦ contDiff_sourceKernel_splitPhase τ (σ p.1 p.2) A p.1
      (hτs p.1) (hσs p.1 p.2) (hAs p.1) hKs (fun x y hy ↦ hs x y p.1 hy)) α
  have he (p : Euclidean n × (Euclidean n × Euclidean n)) :=
    normalMatrixDerivList_sourceKernel_splitPhase τ (σ p.2.1 p.2.2) A p.2.1
      (hτs p.2.1) (hσs p.2.1 p.2.2) (hAs p.2.1) hKs
      (fun x y hy ↦ hs x y p.2.1 hy) α p.1
  simpa only [he] using hm

/-- Frequency measurability of the actual output-jet kernel acting on an almost
everywhere strongly measurable Fourier datum. This supplies the vector integrand
premise in `app:ch_response:thm:response-literal-transfer`. -/
theorem aestronglyMeasurable_sourceKernel_outputJet_mulVec_splitPhase
    (τ : Euclidean n → Euclidean n → ℝ)
    (σ : Euclidean n → Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (hτ : Continuous (fun p : Euclidean n × Euclidean n ↦ τ p.1 p.2))
    (hσ : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      σ p.1.1 p.1.2 p.2))
    (hτs : ∀ η, ContDiff ℝ ∞ (τ · η))
    (hσs : ∀ η θ, ContDiff ℝ ∞ (σ η θ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A p.1.1 p.1.2 p.2))
    {Ks : Set (Euclidean n)} (hKs : IsCompact Ks)
    (hs : ∀ x y η, y ∉ Ks → A x y η = 0)
    (H : Euclidean n → EuclideanSpace ℂ (Fin r)) (hH : AEStronglyMeasurable H volume)
    (α : List (Fin n)) (x : Euclidean n) :
    AEStronglyMeasurable (fun p : Euclidean n × Euclidean n ↦
      (sourceKernel (fun y ↦ τ x p.1 + σ p.1 p.2 y)
        (outputJetAmplitude τ α A) x p.1).mulVec (H p.2)) (volume.prod volume) := by
  have hm := (stronglyMeasurable_sourceKernel_outputJet_splitPhase
    τ σ A hτ hσ hτs hσs hA hKs hs α).comp_measurable
      (g := fun p : Euclidean n × Euclidean n ↦ (x, p))
      (measurable_const.prodMk measurable_id)
  have hc : Continuous (fun q : Matrix (Fin r) (Fin r) ℂ × EuclideanSpace ℂ (Fin r) ↦
      q.1.mulVec q.2) := continuous_fst.matrix_mulVec (by fun_prop)
  exact hc.comp_aestronglyMeasurable (hm.aestronglyMeasurable.prodMk
    (hH.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))


/-- Scalar coordinates of the true output-jet integrand are measurable for the
product frequency measure in `app:ch_response:thm:response-literal-transfer`. -/
theorem aestronglyMeasurable_sourceKernel_outputJet_mulVec_splitPhase_apply
    (τ : Euclidean n → Euclidean n → ℝ)
    (σ : Euclidean n → Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (hτ : Continuous (fun p : Euclidean n × Euclidean n ↦ τ p.1 p.2))
    (hσ : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      σ p.1.1 p.1.2 p.2))
    (hτs : ∀ η, ContDiff ℝ ∞ (τ · η))
    (hσs : ∀ η θ, ContDiff ℝ ∞ (σ η θ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A p.1.1 p.1.2 p.2))
    {Ks : Set (Euclidean n)} (hKs : IsCompact Ks)
    (hs : ∀ x y η, y ∉ Ks → A x y η = 0)
    (H : Euclidean n → EuclideanSpace ℂ (Fin r)) (hH : AEStronglyMeasurable H volume)
    (α : List (Fin n)) (x : Euclidean n) (i : Fin r) :
    AEStronglyMeasurable (fun p : Euclidean n × Euclidean n ↦
      (sourceKernel (fun y ↦ τ x p.1 + σ p.1 p.2 y)
        (outputJetAmplitude τ α A) x p.1).mulVec (H p.2) i) (volume.prod volume) := by
  exact (continuous_apply i).comp_aestronglyMeasurable
    (aestronglyMeasurable_sourceKernel_outputJet_mulVec_splitPhase
      τ σ A hτ hσ hτs hσs hA hKs hs H hH α x)

/-- The actual ordered scalar target derivatives are measurable in frequency.
Together with `norm_euclideanCoordinateDerivList_sourceKernel_splitPhase_le_majorant`,
this supplies the analytic premises for dominated frequency differentiation in
`app:ch_response:thm:response-literal-transfer`. -/
theorem aestronglyMeasurable_euclideanCoordinateDerivList_sourceKernel_splitPhase
    (τ : Euclidean n → Euclidean n → ℝ)
    (σ : Euclidean n → Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (hτ : Continuous (fun p : Euclidean n × Euclidean n ↦ τ p.1 p.2))
    (hσ : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      σ p.1.1 p.1.2 p.2))
    (hτs : ∀ η, ContDiff ℝ ∞ (τ · η))
    (hσs : ∀ η θ, ContDiff ℝ ∞ (σ η θ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A p.1.1 p.1.2 p.2))
    {Ks : Set (Euclidean n)} (hKs : IsCompact Ks)
    (hs : ∀ x y η, y ∉ Ks → A x y η = 0)
    (H : Euclidean n → EuclideanSpace ℂ (Fin r)) (hH : AEStronglyMeasurable H volume)
    (α : List (Fin n)) (x : Euclidean n) (i : Fin r) :
    AEStronglyMeasurable (fun p : Euclidean n × Euclidean n ↦
      AmplitudeBound.euclideanCoordinateDerivList α (fun z ↦
        (sourceKernel (fun y ↦ τ z p.1 + σ p.1 p.2 y) A z p.1).mulVec (H p.2) i) x)
      (volume.prod volume) := by
  have hAs (η : Euclidean n) :
      ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η) :=
    hA.comp (contDiff_id.prodMk contDiff_const)
  have he (p : Euclidean n × Euclidean n) :=
    euclideanCoordinateDerivList_sourceKernel_splitPhase τ (σ p.1 p.2) A p.1
      (hτs p.1) (hσs p.1 p.2) (hAs p.1) hKs (fun x y hy ↦ hs x y p.1 hy)
      (H p.2) i α x
  simp_rw [he]
  exact aestronglyMeasurable_sourceKernel_outputJet_mulVec_splitPhase_apply
    τ σ A hτ hσ hτs hσs hA hKs hs H hH α x i

end JanetCartan.ResponseTransfer.LowEnvelope
