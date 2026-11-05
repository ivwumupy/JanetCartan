module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets.Differentiation.Bounds
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets.Differentiation.DominatedCoordinates
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FrequencyJets.Differentiation.Measurability
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Dominated frequency differentiation for split-phase source kernels

For `app:ch_response:thm:response-literal-transfer`, compact source and frequency
carriers and primitive amplitude/target-phase profiles imply absolute frequency
integrability, smoothness, and the exact ordered target-derivative identity.
The majorants, measurability, and derivative interchange are proved in the three
imported leaves and instantiated here. No physical L¹ datum or smooth frequency
dependence of either phase is needed. The forward and reverse literal-graph
specializations, Fourier datum, and outer normalization are supplied by the
consuming `FrequencyJets` construction.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral NormalComparison AmplitudeBound JanetCartan.Localization

variable {n r : ℕ}

/-- Smooth scalar matrix action used before dominated frequency integration in
`app:ch_response:thm:response-literal-transfer`. -/
private theorem contDiff_sourceKernel_mulVec_splitPhase_apply
    (τ : Euclidean n → Euclidean n → ℝ) (σ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (η : Euclidean n)
    (hτ : ContDiff ℝ ∞ (τ · η)) (hσ : ContDiff ℝ ∞ σ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {Ks : Set (Euclidean n)} (hKs : IsCompact Ks)
    (hs : ∀ x y, y ∉ Ks → A x y η = 0) (v : Fin r → ℂ) (i : Fin r) :
    ContDiff ℝ ∞ (fun x ↦
      (sourceKernel (fun y ↦ τ x η + σ y) A x η).mulVec v i) := by
  have hk := contDiff_sourceKernel_splitPhase τ σ A η hτ hσ hA hKs hs
  change ContDiff ℝ ∞ (fun x ↦ ∑ j, _ * v j)
  exact ContDiff.sum fun j _ ↦ ((matrixEntryEvaluation i j).contDiff.comp hk).mul contDiff_const

variable (τ : Euclidean n → Euclidean n → ℝ)
    (σ : Euclidean n → Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (hτ : Continuous (fun p : Euclidean n × Euclidean n ↦ τ p.1 p.2))
    (hσ : Continuous (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      σ p.1.1 p.1.2 p.2))
    (hτs : ∀ η, ContDiff ℝ ∞ (τ · η))
    (hσs : ∀ η θ, ContDiff ℝ ∞ (σ η θ))
    (hA : ContDiff ℝ ∞ (fun p : (Euclidean n × Euclidean n) × Euclidean n ↦
      A p.1.1 p.1.2 p.2))
    {Ks Kη : Set (Euclidean n)} (hKs : IsCompact Ks) (hKη : IsCompact Kη)
    (hs : ∀ x y η, y ∉ Ks → A x y η = 0)
    (hf : ∀ x y η, η ∉ Kη → A x y η = 0)
    (C : ℕ → ℕ → ℝ) (P : ℕ → ℝ)
    (hC : ∀ m k, 0 ≤ C m k) (hP : ∀ j, 0 ≤ P j)
    (hAj : ∀ η (β : List (Fin n)) k x y,
      ‖iteratedFDeriv ℝ k (fun w ↦ normalMatrixDerivList β (fun z ↦ A z w η) x) y‖ ≤
        C β.length k)
    (hτj : ∀ η ∈ Kη, ∀ j, 1 ≤ j → ∀ x,
      ‖iteratedFDeriv ℝ j (fun z ↦ τ z η) x‖ ≤ P j)
    (H : Euclidean n → EuclideanSpace ℂ (Fin r)) (hH : Integrable H)

include hτ hσ hτs hσs hA hKs hKη hs hf hC hP hAj hτj hH

/-- Absolute joint frequency integrability of every actual output-jet integrand
in `app:ch_response:thm:response-literal-transfer`. This justifies Fubini and
coordinate evaluation for the consuming forward/reverse graph identities. -/
theorem integrable_sourceKernel_outputJet_mulVec_splitPhase
    (α : List (Fin n)) (x : Euclidean n) :
    Integrable (fun p : Euclidean n × Euclidean n ↦
      (sourceKernel (fun y ↦ τ x p.1 + σ p.1 p.2 y)
        (outputJetAmplitude τ α A) x p.1).mulVec (H p.2)) (volume.prod volume) := by
  have hAs (η : Euclidean n) :
      ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η) :=
    hA.comp (contDiff_id.prodMk contDiff_const)
  apply (integrable_compactFrequencyJetMajorant Ks hKη C P α hH).mono'
    (aestronglyMeasurable_sourceKernel_outputJet_mulVec_splitPhase
      τ σ A hτ hσ hτs hσs hA hKs hs H hH.aestronglyMeasurable α x)
  exact Filter.Eventually.of_forall fun p ↦
    norm_sourceKernel_outputJetAmplitude_mulVec_le_majorant τ A
      (fun η θ y ↦ τ x η + σ η θ y) C P hC hP hτs hAs hKs hs hf hAj hτj α H x p

/-- The iterated frequency integral agrees coordinatewise with the product
integral for every output jet (`app:ch_response:thm:response-literal-transfer`).
This is the transport from dominated differentiation to the literal graph's
integration order. -/
theorem integral_sourceKernel_outputJet_mulVec_splitPhase_apply
    (α : List (Fin n)) (x : Euclidean n) (i : Fin r) :
    (∫ η, ∫ θ, (sourceKernel (fun y ↦ τ x η + σ η θ y)
      (outputJetAmplitude τ α A) x η).mulVec (H θ)) i =
    ∫ p : Euclidean n × Euclidean n,
      (sourceKernel (fun y ↦ τ x p.1 + σ p.1 p.2 y)
        (outputJetAmplitude τ α A) x p.1).mulVec (H p.2) i ∂(volume.prod volume) := by
  have hi := integrable_sourceKernel_outputJet_mulVec_splitPhase
    τ σ A hτ hσ hτs hσs hA hKs hKη hs hf C P hC hP hAj hτj H hH α x
  rw [← integral_prod _ hi]
  exact eval_integral (fun j ↦ hi.eval j) i

/-- Smoothness of the compact split-phase frequency integral from the primitive
profiles and an L¹ Fourier datum (`app:ch_response:thm:response-literal-transfer`).
The consuming literal graphs instantiate the phases and restore normalization. -/
theorem contDiff_integral_sourceKernel_splitPhase :
    ContDiff ℝ ∞ (fun x ↦ ∫ η, ∫ θ,
      (sourceKernel (fun y ↦ τ x η + σ η θ y) A x η).mulVec (H θ)) := by
  have hAs (η : Euclidean n) :
      ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η) :=
    hA.comp (contDiff_id.prodMk contDiff_const)
  apply contDiff_pi.mpr
  intro i
  have he (x : Euclidean n) := integral_sourceKernel_outputJet_mulVec_splitPhase_apply
    τ σ A hτ hσ hτs hσs hA hKs hKη hs hf C P hC hP hAj hτj H hH [] x i
  simp only [outputJetAmplitude_nil] at he
  simp_rw [he]
  apply contDiff_integral_of_dominated_coordinateDerivs
    (b := fun α ↦ compactFrequencyJetMajorant r Ks Kη C P α H)
  · intro p
    exact contDiff_sourceKernel_mulVec_splitPhase_apply τ (σ p.1 p.2) A p.1
      (hτs p.1) (hσs p.1 p.2) (hAs p.1) hKs (fun x y hy ↦ hs x y p.1 hy) (H p.2) i
  · intro α x
    exact aestronglyMeasurable_euclideanCoordinateDerivList_sourceKernel_splitPhase
      τ σ A hτ hσ hτs hσs hA hKs hs H hH.aestronglyMeasurable α x i
  · intro α
    exact integrable_compactFrequencyJetMajorant Ks hKη C P α hH
  · intro α p x
    exact norm_euclideanCoordinateDerivList_sourceKernel_splitPhase_le_majorant
      τ σ A C P hC hP hτs hσs hAs hKs hs hf hAj hτj α H x p i

/-- Every ordered target derivative passes through the two frequency integrals
and produces the actual modified amplitude
(`app:ch_response:thm:response-literal-transfer`). All domination and
measurability premises are discharged from the primitive profiles above. -/
theorem euclideanCoordinateDerivList_integral_sourceKernel_splitPhase
    (α : List (Fin n)) (x : Euclidean n) (i : Fin r) :
    euclideanCoordinateDerivList α (fun z ↦ (∫ η, ∫ θ,
      (sourceKernel (fun y ↦ τ z η + σ η θ y) A z η).mulVec (H θ)) i) x =
    (∫ η, ∫ θ, (sourceKernel (fun y ↦ τ x η + σ η θ y)
      (outputJetAmplitude τ α A) x η).mulVec (H θ)) i := by
  have hAs (η : Euclidean n) :
      ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η) :=
    hA.comp (contDiff_id.prodMk contDiff_const)
  have he (z : Euclidean n) := integral_sourceKernel_outputJet_mulVec_splitPhase_apply
    τ σ A hτ hσ hτs hσs hA hKs hKη hs hf C P hC hP hAj hτj H hH [] z i
  simp only [outputJetAmplitude_nil] at he
  simp_rw [he]
  rw [euclideanCoordinateDerivList_integral_of_dominated
    (b := fun β ↦ compactFrequencyJetMajorant r Ks Kη C P β H)
    (fun p ↦ contDiff_sourceKernel_mulVec_splitPhase_apply τ (σ p.1 p.2) A p.1
      (hτs p.1) (hσs p.1 p.2) (hAs p.1) hKs (fun z y hy ↦ hs z y p.1 hy) (H p.2) i)
    (fun β z ↦ aestronglyMeasurable_euclideanCoordinateDerivList_sourceKernel_splitPhase
      τ σ A hτ hσ hτs hσs hA hKs hs H hH.aestronglyMeasurable β z i)
    (fun β ↦ integrable_compactFrequencyJetMajorant Ks hKη C P β hH)
    (fun β p z ↦ norm_euclideanCoordinateDerivList_sourceKernel_splitPhase_le_majorant
      τ σ A C P hC hP hτs hσs hAs hKs hs hf hAj hτj β H z p i)]
  rw [integral_sourceKernel_outputJet_mulVec_splitPhase_apply
    τ σ A hτ hσ hτs hσs hA hKs hKη hs hf C P hC hP hAj hτj H hH α x i]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p ↦
    euclideanCoordinateDerivList_sourceKernel_splitPhase τ (σ p.1 p.2) A p.1
      (hτs p.1) (hσs p.1 p.2) (hAs p.1) hKs (fun z y hy ↦ hs z y p.1 hy) (H p.2) i α x

end JanetCartan.ResponseTransfer.LowEnvelope
