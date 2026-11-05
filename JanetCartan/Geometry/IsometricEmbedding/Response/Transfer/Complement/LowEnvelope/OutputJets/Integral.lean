module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.LowEnvelope.OutputJets.Basic

/-!
# Differentiating the compact source integral

For `app:ch_response:thm:response-literal-transfer`, domination follows from
joint smoothness and the original compact source cutoff. It is not an assumed
output estimate. The ordered coordinate derivatives act on the full matrix.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponseTransfer.LowEnvelope

open FourierIntegral JanetCartan.Localization NormalComparison

variable {n r : ℕ}

/-- Removing a target-only real constant from the source phase changes the
kernel by a unit complex scalar (`app:ch_response:thm:response-literal-transfer`). -/
theorem sourceKernel_sub_const (ψ : Euclidean n → ℝ) (t : ℝ)
    (A : FullAmplitude n r) (x η : Euclidean n) :
    sourceKernel (fun y ↦ ψ y - t) A x η =
      Complex.exp ((-t : ℂ) * Complex.I) • sourceKernel ψ A x η := by
  have he (y : Euclidean n) : phaseOscillation (fun z ↦ ψ z - t) y =
      Complex.exp ((-t : ℂ) * Complex.I) * phaseOscillation ψ y := by
    simp only [phaseOscillation, Complex.ofReal_sub, sub_mul, Complex.exp_sub,
      neg_mul, Complex.exp_neg]
    ring
  simp only [sourceKernel, he, mul_smul, integral_smul]

/-- Source-kernel norms are unchanged by output demodulation. Consequently the
existing source integration-by-parts theorem applies to each output jet without
any new phase-gap premise (`app:ch_response:thm:response-literal-transfer`). -/
theorem norm_sourceKernel_sub_const (ψ : Euclidean n → ℝ) (t : ℝ)
    (A : FullAmplitude n r) (x η : Euclidean n) :
    ‖sourceKernel (fun y ↦ ψ y - t) A x η‖ = ‖sourceKernel ψ A x η‖ := by
  rw [sourceKernel_sub_const, norm_smul]
  have he : ‖Complex.exp ((-t : ℂ) * Complex.I)‖ = 1 := by
    simpa using Complex.norm_exp_ofReal_mul_I (-t)
  rw [he, one_mul]

/-- Every ordered output derivative passes through a fixed compact source
integral (`app:ch_response:thm:response-literal-transfer`). -/
theorem normalMatrixDerivList_setIntegral
    {K : Set (Euclidean n)} (hK : IsCompact K)
    {f : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ f p.1 p.2))
    (α : List (Fin n)) :
    normalMatrixDerivList α (fun x ↦ ∫ y in K, f x y) =
      fun x ↦ ∫ y in K, normalMatrixDerivList α (fun z ↦ f z y) x := by
  let : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hK.measure_lt_top⟩
  induction α with
  | nil => rfl
  | cons i α ih =>
    funext x
    simp only [normalMatrixDerivList, ih]
    have hg := (contDiff_joint_normalMatrixDerivList hf α).contDiffOn
      (s := (Set.univ : Set (Euclidean n)) ×ˢ Set.univ)
    rw [fderiv_compactParameterIntegral isOpen_univ isOpen_univ hK
      (Set.subset_univ _) hg (Set.mem_univ x)]
    exact ContinuousLinearMap.integral_apply
      (integrableOn_parameterFDeriv isOpen_univ isOpen_univ hK
        (Set.subset_univ _) hg (Set.mem_univ x)) _

/-- Ordered target differentiation under the full Lebesgue source integral;
the support hypothesis is uniform in the target position. This is the
compact-cutoff justification in `app:ch_response:thm:response-literal-transfer`. -/
theorem normalMatrixDerivList_sourceIntegral
    {K : Set (Euclidean n)} (hK : IsCompact K)
    {f : Euclidean n → Euclidean n → Matrix (Fin r) (Fin r) ℂ}
    (hf : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ f p.1 p.2))
    (hs : ∀ x y, y ∉ K → f x y = 0) (α : List (Fin n)) :
    normalMatrixDerivList α (fun x ↦ ∫ y, f x y) =
      fun x ↦ ∫ y, normalMatrixDerivList α (fun z ↦ f z y) x := by
  have he : (fun x ↦ ∫ y, f x y) = fun x ↦ ∫ y in K, f x y := by
    funext x
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (hs x)).symm
  rw [he, normalMatrixDerivList_setIntegral hK hf]
  funext x
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  have hz : (fun z ↦ f z y) = 0 := funext fun z ↦ hs z y hy
  rw [hz, normalMatrixDerivList_zero]
  rfl

/-- The derivative of the actual split-phase kernel is the source kernel of
the actual modified amplitude. This supplies the integral identity consumed by
`norm_sourceKernel_le` in `app:ch_response:thm:response-literal-transfer`. -/
theorem normalMatrixDerivList_sourceKernel_splitPhase
    (τ : Euclidean n → Euclidean n → ℝ) (σ : Euclidean n → ℝ)
    (A : FullAmplitude n r) (η : Euclidean n)
    (hτ : ContDiff ℝ ∞ (fun x ↦ τ x η)) (hσ : ContDiff ℝ ∞ σ)
    (hA : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦ A p.1 p.2 η))
    {K : Set (Euclidean n)} (hK : IsCompact K)
    (hs : ∀ x y, y ∉ K → A x y η = 0) (α : List (Fin n)) (x : Euclidean n) :
    normalMatrixDerivList α
        (fun z ↦ sourceKernel (fun y ↦ τ z η + σ y) A z η) x =
      sourceKernel (fun y ↦ τ x η + σ y) (outputJetAmplitude τ α A) x η := by
  have hf : ContDiff ℝ ∞ (fun p : Euclidean n × Euclidean n ↦
      phaseOscillation (fun y ↦ τ p.1 η + σ y) p.2 • A p.1 p.2 η) :=
    (contDiff_outputOscillation ((hτ.comp contDiff_fst).add
      (hσ.comp contDiff_snd))).smul hA
  change normalMatrixDerivList α (fun z ↦ ∫ y,
    phaseOscillation (fun w ↦ τ z η + σ w) y • A z y η) x = _
  rw [normalMatrixDerivList_sourceIntegral hK hf
    (fun z y hy ↦ by simp [hs z y hy])]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y ↦
    normalMatrixDerivList_splitPhase τ σ α A x y η hτ
      (hA.comp (contDiff_id.prodMk contDiff_const))

end JanetCartan.ResponseTransfer.LowEnvelope
