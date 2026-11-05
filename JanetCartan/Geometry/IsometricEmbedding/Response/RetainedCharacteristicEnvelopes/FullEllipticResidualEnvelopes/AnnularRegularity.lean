module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.PrimitiveSobolev
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularSobolev.Modulation
public import JanetCartan.Analysis.Microlocal.CharacteristicTransport.CompleteResidual.OperatorIdentity

/-!
# Actual parameter regularity of the annular PDO family

Compact frequency integration and the original smooth source give a smooth
compact output representative for the actual annular bounded PDO. This
qualitative step justifies adding its ordered derivatives to the independently
estimated full-frequency remainder. No full response bound is used.
Consumer: full elliptic and residual PDO envelopes in
`app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
open FourierIntegral FourierIntegral.FullLowBounds Pseudodifferential
open DirectEvolution.AnnularComplement DirectEvolution.AnnularSobolev
open JanetCartan.ResponseTransfer.Complement
open JanetCartan.ResponseTransfer.Complement.ParameterDerivatives
open JanetCartan.ResponseTransfer.Complement.ParameterDerivatives.Hilbert
open CharacteristicTransport.CompleteResidual
variable {d r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin r)
local notation "Mat" => Matrix (Fin r) (Fin r) ℂ
local notation "H" => Lp F 2 (volume : Measure E)

/-- The actual annular PDO response, with its literal source and output
carriers, is smooth in the original parameter. The complete symbol is fixed
while the parameter varies; both Hilbert orientations are covered.
This supplies differentiability needed for the full-tail addition in
`app:ch_response:eq:direct-envelope-profile`. -/
theorem contDiffOn_complete_diagonal_annular_envelope
    {V : Set P} (hV : IsOpen V) {S X₀ : Set E}
    (hS : IsCompact S) (hX₀ : IsCompact X₀) [CompactSpace X₀]
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hmask : tsupport χout ∪ tsupport χsource ⊆ X₀)
    (σ : E → E → Mat) (hσ : ContDiff ℝ ∞ (Function.uncurry σ))
    (θ : E → ℂ) (hθ : ContDiff ℝ ∞ θ) (hcθ : HasCompactSupport θ)
    (φ : P → E → ℝ) (hφ : ContDiff ℝ ∞ (Function.uncurry φ))
    (hcφ : ∀ c, Continuous (φ c)) (lam : ℝ)
    (a : P → E → F) (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (V ×ˢ univ))
    (has : ∀ c ∈ V, tsupport (a c) ⊆ S)
    (u : P → H) (hu : ∀ c ∈ V, u c =ᵐ[volume] a c) (adj : Bool) :
    ContDiffOn ℝ ∞ (fun c ↦ demodulatedL2Operator lam (φ c) (hcφ c)
      (annularGraphOrientation adj (maskedPhysicalPDO χout χsource
        (fun y ξ ↦ θ ξ • σ y ξ))) (u c)) V := by
  let A : FullAmplitude (d+1) r := fun y z ξ ↦ (χout y * χsource z) • σ y ξ
  have hA : ContDiff ℝ ∞ (fun q : E × E × E ↦ A q.1 q.2.1 q.2.2) :=
    ((ho.comp contDiff_fst).mul (hs.comp contDiff_snd.fst)).smul
      (hσ.comp (contDiff_fst.prodMk contDiff_snd.snd))
  have hΘ : ContDiff ℝ ∞ (Function.uncurry (fun y ξ : E ↦ inner ℝ y ξ)) :=
    contDiff_fst.inner ℝ contDiff_snd
  have hzero (x : E) (hx : x ∉ X₀) (z ξ : E) :
      (if adj then A z x ξ else A x z ξ) = 0 := by
    cases adj
    · have hz := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hmask (Or.inl h)))
      simp only [Bool.false_eq_true, ↓reduceIte, A, hz, zero_mul, zero_smul]
    · have hz := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hmask (Or.inr h)))
      simp only [↓reduceIte, A, hz, mul_zero, zero_smul]
  have hJ := contDiffOn_annularSourceIntegrand_localCarrierPhase adj true
    (fun y ξ : E ↦ inner ℝ y ξ) A 0 φ lam a hV
    isClosed_univ isOpen_univ (Subset.refl univ) hΘ.contDiffOn
    (fun _ _ _ _ ↦ mem_univ _)
    (fun k l ↦ (AmplitudeBound.matrixEntryEvaluation k l).contDiff.comp hA)
    contDiff_const isOpen_univ hX₀.isClosed hS.isClosed (subset_univ _) (subset_univ _)
    hφ.contDiffOn ha has hzero
  have hκ := contDiffOn_annularSourceKernelObservation_of_joint adj true
    (fun y ξ : E ↦ inner ℝ y ξ) A 0 φ lam a hV hJ hS has
  let θa : E → ℂ := fun ξ ↦ if adj then star (θ ξ) else θ ξ
  have hθa : ContDiff ℝ ∞ θa := by
    cases adj
    · exact hθ
    · exact Complex.conjCLE.contDiff.comp hθ
  let κ : (P × E) → E → F := fun q ξ ↦ θa ξ •
    annularSourceKernelObservation adj true (fun y η : E ↦ inner ℝ y η)
      A 0 (φ q.1) lam (a q.1) q.2 ξ
  have hk : ContDiffOn ℝ ∞ (Function.uncurry κ) ((V ×ˢ univ) ×ˢ univ) :=
    (hθa.comp_contDiffOn contDiffOn_snd).smul hκ
  have hsκ (q : P × E) (_hq : q ∈ V ×ˢ univ) (ξ : E) (hξ : ξ ∉ tsupport θ) : κ q ξ = 0 := by
    have hz := image_eq_zero_of_notMem_tsupport hξ
    simp only [κ,θa,hz,star_zero,ite_self,zero_smul]
  let g : P → E → F := fun c x ↦ ∫ ξ, κ (c,x) ξ
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ) :=
    contDiffOn_integral_parameterCompactSupport (μ := volume) (hV.prod isOpen_univ)
      hk hcθ hsκ
  have hgs (c : P) (_hc : c ∈ V) (x : E) (hx : x ∉ X₀) : g c x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with ξ
    have hz := annularSourceKernelObservation_eq_zero_of_amplitude adj true
      (fun y η : E ↦ inner ℝ y η) A 0 (φ c) lam (a c) x ξ (fun z ↦ hzero x hx z ξ)
    simp only [κ,hz,smul_zero,Pi.zero_apply]
  have hregular := contDiffOn_compactVectorL2Family hX₀ hV hg
  apply hregular.congr
  intro c hc
  let w := carrierMultiplication lam (φ c) (hcφ c) (u c)
  have hw : w =ᵐ[volume] fun z ↦ carrier lam (φ c) z • a c z := by
    filter_upwards [carrierMultiplication_ae lam (φ c) (hcφ c) (u c),hu c hc] with z hz ha
    rw [hz,ha]
  have hphys (x z ξ : E) (hh : x ∉ X₀ ∨ z ∉ X₀) : A x z ξ = 0 := by
    rcases hh with hx | hz
    · have he := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hmask (Or.inl h)))
      simp only [A,he,zero_mul,zero_smul]
    · have he := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hmask (Or.inr h)))
      simp only [A,he,mul_zero,zero_smul]
  have hr := annularGraphOrientation_frequencyCut_ae adj (fun y ξ : E ↦ inner ℝ y ξ)
    hΘ A hA hX₀ hX₀ hphys θ hθ hcθ (φ c) lam (a c) w hw
  have hcut : fullGraphOperator (fun y ξ : E ↦ inner ℝ y ξ)
      (frequencyCutFullAmplitude θ A) =
      maskedPhysicalPDO χout χsource (fun y ξ ↦ θ ξ • σ y ξ) := by
    congr 1
    funext y z ξ
    exact smul_comm _ _ _
  rw [hcut] at hr
  apply Lp.ext
  filter_upwards [carrierMultiplication_ae (-lam) (φ c) (hcφ c)
      (annularGraphOrientation adj (maskedPhysicalPDO χout χsource (fun y ξ ↦ θ ξ • σ y ξ)) w),
    hr,compactVectorL2Family_ae hX₀ hg hgs hc] with x hx hr hg
  change carrierMultiplication (-lam) (φ c) (hcφ c)
    (annularGraphOrientation adj (maskedPhysicalPDO χout χsource (fun y ξ ↦ θ ξ • σ y ξ)) w) x = _
  rw [hx,hr,hg]
  dsimp only [g,κ,θa]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with ξ
  cases adj <;> simp only [annularSourceKernelObservation, Bool.false_eq_true, ↓reduceIte,
    demodulatedForwardAnnularSourceKernel,demodulatedAdjointAnnularSourceKernel]
  all_goals exact smul_comm _ _ _

end JanetCartan.ResponseTransfer.FullEllipticResidualEnvelopes
