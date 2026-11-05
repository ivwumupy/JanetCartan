module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.FourierReconstruction.Inversion
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.SourceKernel
/-!
# Literal graph reconstruction from the low Fourier envelope

Source-variable Fubini and the literal forward and weighted reverse identities
in `app:ch_response:thm:response-literal-transfer`. The full matrix amplitudes
retain both physical positions. The datum lives in an actual complex Euclidean
Hilbert space; coordinate coercions only match the existing graph operator API.
The source-frequency compactness argument is supplied in the `Compact` module.
-/

open MeasureTheory
open scoped Matrix.Norms.Frobenius
@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.LowEnvelope
open JanetCartan.Localization FourierIntegral
variable {n r : ℕ}
local instance : ContinuousENorm (Matrix (Fin r) (Fin r) ℂ) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid
    (Matrix (Fin r) (Fin r) ℂ) inferInstance).toContinuousENorm
local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin r) (Fin r) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin r → Fin r → ℂ))
private def matrixAction : Matrix (Fin r) (Fin r) ℂ →L[ℂ]
    ((Fin r → ℂ) →L[ℂ] (Fin r → ℂ)) :=
  (Matrix.toLin'.trans LinearMap.toContinuousLinearMap).toContinuousLinearEquiv.toContinuousLinearMap
private theorem matrixAction_apply (A : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) : matrixAction A v = A.mulVec v := rfl
private theorem integrable_matrix_product
    {a : Euclidean n → Matrix (Fin r) (Fin r) ℂ} (ha : Integrable a)
    {H : Euclidean n → Fin r → ℂ} (hH : Integrable H)
    {p : Euclidean n × Euclidean n → ℂ} (hp : Continuous p)
    (hn : ∀ z, ‖p z‖ ≤ 1) :
    Integrable (fun z : Euclidean n × Euclidean n ↦
      p z • (a z.1).mulVec (H z.2)) (volume.prod volume) := by
  have hi := (matrixAction.integrable_comp ha).op_fst_snd
    (op := fun (T : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ)) v ↦ T v)
    (by fun_prop) ⟨1, fun T v ↦ by simpa using T.le_opNorm v⟩ hH
  exact hi.bdd_smul 1 hp.aestronglyMeasurable (Filter.Eventually.of_forall hn)

private theorem sourceIntegral_inverseFourier_pi {a : Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (ha : Continuous a) (hc : HasCompactSupport a)
    (ψ : Euclidean n → ℝ) (hψ : Continuous ψ)
    {H : Euclidean n → Fin r → ℂ} (hH : Integrable H) :
    (∫ y, phaseOscillation ψ y • (a y).mulVec
      (∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) y • H θ)) =
    ∫ θ, (∫ y, (phaseOscillation ψ y *
      phaseOscillation (fun z ↦ inner ℝ z θ) y) • a y).mulVec (H θ) := by
  have hi : Integrable a := ha.integrable_of_hasCompactSupport hc
  have hp : Continuous (fun z : Euclidean n × Euclidean n ↦
      phaseOscillation ψ z.1 * phaseOscillation (fun y ↦ inner ℝ y z.2) z.1) := by
    unfold phaseOscillation
    fun_prop
  have hn : ∀ z : Euclidean n × Euclidean n,
      ‖phaseOscillation ψ z.1 * phaseOscillation (fun y ↦ inner ℝ y z.2) z.1‖ ≤ 1 := by
    intro z
    simp [norm_phaseOscillation]
  calc
    _ = ∫ y, ∫ θ, (phaseOscillation ψ y *
        phaseOscillation (fun z ↦ inner ℝ z θ) y) • (a y).mulVec (H θ) := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hθ : Integrable (fun θ ↦ phaseOscillation (fun z ↦ inner ℝ z θ) y • H θ) :=
        hH.bdd_smul 1 (by unfold phaseOscillation; fun_prop)
          (Filter.Eventually.of_forall (fun θ ↦ (norm_phaseOscillation _ _).le))
      rw [← matrixAction_apply, ← (matrixAction (a y)).integral_comp_comm hθ, ← integral_smul]
      congr 1
      funext θ
      simp only [matrixAction_apply, Matrix.mulVec_smul, mul_smul]
    _ = ∫ θ, ∫ y, (phaseOscillation ψ y *
        phaseOscillation (fun z ↦ inner ℝ z θ) y) • (a y).mulVec (H θ) :=
      integral_integral_swap (integrable_matrix_product hi hH hp hn)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with θ
      let T : Matrix (Fin r) (Fin r) ℂ →L[ℂ] (Fin r → ℂ) :=
        (ContinuousLinearMap.apply ℂ (Fin r → ℂ) (H θ)).comp matrixAction
      have hb : Integrable (fun y ↦ (phaseOscillation ψ y *
          phaseOscillation (fun z ↦ inner ℝ z θ) y) • a y) :=
        hi.bdd_smul 1 (hp.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun y ↦ hn (y, θ)))
      have ht := T.integral_comp_comm hb
      change (∫ y, ((phaseOscillation ψ y *
        phaseOscillation (fun z ↦ inner ℝ z θ) y) • a y).mulVec (H θ)) =
        (∫ y, (phaseOscillation ψ y *
        phaseOscillation (fun z ↦ inner ℝ z θ) y) • a y).mulVec (H θ) at ht
      simpa only [Matrix.smul_mulVec] using ht

private theorem sourceIntegral_inverseFourier
    {a : Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (ha : Continuous a) (hc : HasCompactSupport a)
    (ψ : Euclidean n → ℝ) (hψ : Continuous ψ)
    {H : Euclidean n → EuclideanSpace ℂ (Fin r)} (hH : Integrable H) :
    (∫ y, phaseOscillation ψ y • (a y).mulVec
      (⇑(∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) y • H θ))) =
    ∫ θ, (∫ y, (phaseOscillation ψ y *
      phaseOscillation (fun z ↦ inner ℝ z θ) y) • a y).mulVec (H θ) := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
  have hi := sourceIntegral_inverseFourier_pi ha hc ψ hψ
    (e.toContinuousLinearMap.integrable_comp hH)
  have he (y : Euclidean n) :
      (⇑(∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) y • H θ)) =
      ∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) y • (H θ : Fin r → ℂ) := by
    exact (e.integral_comp_comm _).symm
  have hE (v : EuclideanSpace ℂ (Fin r)) : e.toContinuousLinearMap v = ⇑v := rfl
  simpa only [hE, he] using hi

/-- Literal low-support L² forward reconstruction, with both physical positions
and the graph's single outer normalization. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem graphOperator_lowSupport_reconstruction
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ζ : Euclidean n) (ρ : ℝ) (x : Euclidean n)
    (ha : ∀ η, Continuous (fun y ↦ A x y η))
    (hc : ∀ η, HasCompactSupport (fun y ↦ A x y η))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    graphOperator S A (fun y ↦ carrier ρ (fun z ↦ inner ℝ z ζ) y • ⇑(f y)) x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (forwardSourcePhase S ζ ρ x η θ) A x η).mulVec
          (paperL2FourierTransform f θ) := by
  have hF := (paperL2FourierTransform_lowSupport_L1 f hΛ hs).1
  have hinv := paperL2FourierTransform_lowSupport_inverse_ae f hΛ hs
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  let ψ := forwardSourcePhase S ζ ρ x η 0
  have hp (y : Euclidean n) : phaseOscillation ψ y =
      graphOscillation S x y η * carrier ρ (fun z ↦ inner ℝ z ζ) y := by
    change phaseOscillation (forwardSourcePhase S ζ ρ x η 0) y = _
    rw [phaseOscillation_forwardSourcePhase]
    simp [phaseOscillation]
  have he := sourceIntegral_inverseFourier (ha η) (hc η) ψ
    (by change Continuous (fun y ↦ forwardSourcePhase S ζ ρ x η 0 y)
        unfold forwardSourcePhase
        fun_prop) hF
  calc
    _ = ∫ y, phaseOscillation ψ y • (A x y η).mulVec
        (⇑(∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) y •
          paperL2FourierTransform f θ)) := by
      apply integral_congr_ae
      filter_upwards [hinv] with y hy
      rw [hy, hp]
      simp only [Matrix.mulVec_smul, mul_smul]
    _ = _ := by
      rw [he]
      simp only [sourceKernel, hp, phaseOscillation_forwardSourcePhase]

/-- Literal reverse reconstruction for arbitrary low-support L² envelopes,
retaining the Jacobian, inverse matrix, and all three physical/frequency cutoffs
(`app:ch_response:thm:response-literal-transfer`). -/
theorem weightedReverseGraph_lowSupport_reconstruction
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (φ : Euclidean n → ℝ) (hφ : Continuous φ)
    (ρ : ℝ) (y : Euclidean n) (hS : ∀ η, Continuous (fun x ↦ S x η))
    (ha : ∀ η, Continuous (fun x ↦ reverseFullAmplitude S U χs χt χg y x η))
    (hc : ∀ η, HasCompactSupport (fun x ↦ reverseFullAmplitude S U χs χt χg y x η))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    weightedReverseGraph S U χs χt χg (fun x ↦ carrier ρ φ x • ⇑(f x)) y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (reverseSourcePhase S φ ρ y η θ)
          (reverseFullAmplitude S U χs χt χg) y η).mulVec
            (paperL2FourierTransform f θ) := by
  have hF := (paperL2FourierTransform_lowSupport_L1 f hΛ hs).1
  have hinv := paperL2FourierTransform_lowSupport_inverse_ae f hΛ hs
  rw [weightedReverseGraph_eq_integral_reverseFullAmplitude]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  let ψ := reverseSourcePhase S φ ρ y η 0
  have hp (x : Euclidean n) : phaseOscillation ψ x =
      star (graphOscillation S x y η) * carrier ρ φ x := by
    change phaseOscillation (reverseSourcePhase S φ ρ y η 0) x = _
    rw [phaseOscillation_reverseSourcePhase]
    simp [phaseOscillation]
  have he := sourceIntegral_inverseFourier (ha η) (hc η) ψ
    (by change Continuous (fun x ↦ reverseSourcePhase S φ ρ y η 0 x)
        unfold reverseSourcePhase
        fun_prop) hF
  calc
    _ = ∫ x, phaseOscillation ψ x •
        (reverseFullAmplitude S U χs χt χg y x η).mulVec
        (⇑(∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x •
          paperL2FourierTransform f θ)) := by
      apply integral_congr_ae
      filter_upwards [hinv] with x hx
      rw [hx, hp]
      simp only [Matrix.mulVec_smul, mul_smul]
    _ = _ := by
      rw [he]
      simp only [sourceKernel, hp, phaseOscillation_reverseSourcePhase]
/-- Literal reverse reconstruction for arbitrary low-support L² envelopes,
for any full reverse amplitude, including complete complementary amplitudes
(`app:ch_response:thm:response-literal-transfer`). -/
theorem reverseGraph_lowSupport_reconstruction
    (S : Euclidean n → Euclidean n → ℝ)
    (A : FullAmplitude n r) (φ : Euclidean n → ℝ) (hφ : Continuous φ)
    (ρ : ℝ) (y : Euclidean n) (hS : ∀ η, Continuous (fun x ↦ S x η))
    (ha : ∀ η, Continuous (fun x ↦ A y x η))
    (hc : ∀ η, HasCompactSupport (fun x ↦ A y x η))
    (f : Lp (α := Euclidean n) (EuclideanSpace ℂ (Fin r)) 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperL2FourierTransform f θ = 0) :
    (((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ x,
      star (graphOscillation S x y η) • (A y x η).mulVec (carrier ρ φ x • ⇑(f x))) =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (reverseSourcePhase S φ ρ y η θ)
          (A) y η).mulVec
            (paperL2FourierTransform f θ) := by
  have hF := (paperL2FourierTransform_lowSupport_L1 f hΛ hs).1
  have hinv := paperL2FourierTransform_lowSupport_inverse_ae f hΛ hs
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  let ψ := reverseSourcePhase S φ ρ y η 0
  have hp (x : Euclidean n) : phaseOscillation ψ x =
      star (graphOscillation S x y η) * carrier ρ φ x := by
    change phaseOscillation (reverseSourcePhase S φ ρ y η 0) x = _
    rw [phaseOscillation_reverseSourcePhase]
    simp [phaseOscillation]
  have he := sourceIntegral_inverseFourier (ha η) (hc η) ψ
    (by change Continuous (fun x ↦ reverseSourcePhase S φ ρ y η 0 x)
        unfold reverseSourcePhase
        fun_prop) hF
  calc
    _ = ∫ x, phaseOscillation ψ x •
        (A y x η).mulVec
        (⇑(∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x •
          paperL2FourierTransform f θ)) := by
      apply integral_congr_ae
      filter_upwards [hinv] with x hx
      rw [hx, hp]
      simp only [Matrix.mulVec_smul, mul_smul]
    _ = _ := by
      rw [he]
      simp only [sourceKernel, hp, phaseOscillation_reverseSourcePhase]
/-- Literal low-support L¹ ∩ L² forward reconstruction using the ordinary Fourier integral, with both physical positions
and the graph's single outer normalization. Source:
`app:ch_response:thm:response-literal-transfer`. -/
theorem graphOperator_paperFourierTransform_reconstruction
    (S : Euclidean n → Euclidean n → ℝ) (A : FullAmplitude n r)
    (ζ : Euclidean n) (ρ : ℝ) (x : Euclidean n)
    (ha : ∀ η, Continuous (fun y ↦ A x y η))
    (hc : ∀ η, HasCompactSupport (fun y ↦ A x y η))
    (f : Euclidean n → EuclideanSpace ℂ (Fin r))
    (hf : Integrable f) (hf₂ : MemLp f 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperFourierTransform f θ = 0) :
    graphOperator S A (fun y ↦ carrier ρ (fun z ↦ inner ℝ z ζ) y • ⇑(f y)) x =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (forwardSourcePhase S ζ ρ x η θ) A x η).mulVec
          (⇑(paperFourierTransform f θ : EuclideanSpace ℂ (Fin r))) := by
  have hF := (paperFourierTransform_lowSupport_L1 hf hf₂ hΛ hs).1
  have hinv := paperFourierTransform_lowSupport_inverse_ae hf hf₂ hΛ hs
  unfold graphOperator
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  let ψ := forwardSourcePhase S ζ ρ x η 0
  have hp (y : Euclidean n) : phaseOscillation ψ y =
      graphOscillation S x y η * carrier ρ (fun z ↦ inner ℝ z ζ) y := by
    change phaseOscillation (forwardSourcePhase S ζ ρ x η 0) y = _
    rw [phaseOscillation_forwardSourcePhase]
    simp [phaseOscillation]
  have he := sourceIntegral_inverseFourier (ha η) (hc η) ψ
    (by change Continuous (fun y ↦ forwardSourcePhase S ζ ρ x η 0 y)
        unfold forwardSourcePhase
        fun_prop) hF
  calc
    _ = ∫ y, phaseOscillation ψ y • (A x y η).mulVec
        (⇑(∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) y •
          paperFourierTransform f θ)) := by
      apply integral_congr_ae
      filter_upwards [hinv] with y hy
      rw [hy, hp]
      simp only [Matrix.mulVec_smul, mul_smul]
    _ = _ := by
      rw [he]
      simp only [sourceKernel, hp, phaseOscillation_forwardSourcePhase]

/-- Literal reverse reconstruction using the ordinary Fourier integral on L¹ ∩ L²,
retaining the Jacobian, inverse matrix, and all three physical/frequency cutoffs
(`app:ch_response:thm:response-literal-transfer`). -/
theorem weightedReverseGraph_paperFourierTransform_reconstruction
    (S : Euclidean n → Euclidean n → ℝ)
    (U : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ)
    (χs χt χg : Euclidean n → ℝ) (φ : Euclidean n → ℝ) (hφ : Continuous φ)
    (ρ : ℝ) (y : Euclidean n) (hS : ∀ η, Continuous (fun x ↦ S x η))
    (ha : ∀ η, Continuous (fun x ↦ reverseFullAmplitude S U χs χt χg y x η))
    (hc : ∀ η, HasCompactSupport (fun x ↦ reverseFullAmplitude S U χs χt χg y x η))
    (f : Euclidean n → EuclideanSpace ℂ (Fin r))
    (hf : Integrable f) (hf₂ : MemLp f 2 volume)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hs : ∀ᵐ θ ∂volume, Λ < ‖θ‖ → paperFourierTransform f θ = 0) :
    weightedReverseGraph S U χs χt χg (fun x ↦ carrier ρ φ x • ⇑(f x)) y =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ η, ∫ θ,
        (sourceKernel (reverseSourcePhase S φ ρ y η θ)
          (reverseFullAmplitude S U χs χt χg) y η).mulVec
            (⇑(paperFourierTransform f θ : EuclideanSpace ℂ (Fin r))) := by
  have hF := (paperFourierTransform_lowSupport_L1 hf hf₂ hΛ hs).1
  have hinv := paperFourierTransform_lowSupport_inverse_ae hf hf₂ hΛ hs
  rw [weightedReverseGraph_eq_integral_reverseFullAmplitude]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with η
  let ψ := reverseSourcePhase S φ ρ y η 0
  have hp (x : Euclidean n) : phaseOscillation ψ x =
      star (graphOscillation S x y η) * carrier ρ φ x := by
    change phaseOscillation (reverseSourcePhase S φ ρ y η 0) x = _
    rw [phaseOscillation_reverseSourcePhase]
    simp [phaseOscillation]
  have he := sourceIntegral_inverseFourier (ha η) (hc η) ψ
    (by change Continuous (fun x ↦ reverseSourcePhase S φ ρ y η 0 x)
        unfold reverseSourcePhase
        fun_prop) hF
  calc
    _ = ∫ x, phaseOscillation ψ x •
        (reverseFullAmplitude S U χs χt χg y x η).mulVec
        (⇑(∫ θ, phaseOscillation (fun z ↦ inner ℝ z θ) x •
          paperFourierTransform f θ)) := by
      apply integral_congr_ae
      filter_upwards [hinv] with x hx
      rw [hx, hp]
      simp only [Matrix.mulVec_smul, mul_smul]
    _ = _ := by
      rw [he]
      simp only [sourceKernel, hp, phaseOscillation_reverseSourcePhase]
end JanetCartan.ResponseTransfer.LowEnvelope

