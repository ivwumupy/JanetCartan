module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SourceBounds.Support
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.AnnularComplement.SupportedIdentity
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.LocalIntegral

/-!
# Joint smoothness of the literal annular source integrands

For `app:ch_response:lem:energy-carrier-jets`, the two Boolean indices select
orientation and physical/demodulated observation. They only select among the
four published literal kernels. In particular, the demodulator remains inside
the differentiated integrand. The supported phase extension agrees with the
original integrand everywhere, including the full unbounded frequency tail.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open FourierIntegral JanetCartan.Localization
variable {n r : ℕ} {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
local notation "E" => Euclidean n
local notation "F" => EuclideanSpace ℂ (Fin r)

/-- Select one of the four existing literal kernels, without changing its
phase, amplitude or Fourier normalization (`app:ch_response:lem:energy-carrier-jets`). -/
def annularSourceKernelObservation (adj demod : Bool)
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) : F :=
  if adj then
    if demod then demodulatedAdjointAnnularSourceKernel Θ A π φ lam a x ξ
    else adjointAnnularSourceKernel Θ A π φ lam a x ξ
  else
    if demod then demodulatedForwardAnnularSourceKernel Θ A π φ lam a x ξ
    else forwardAnnularSourceKernel Θ A π φ lam a x ξ

/-- The actual integrand for physical or demodulated observation, with the
original complete amplitude. External differentiation acts on every displayed
factor (`app:ch_response:lem:energy-carrier-jets`). -/
def annularSourceIntegrand (adj demod : Bool)
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ z : E) : F :=
  (if demod then carrier (-lam) φ x else 1) •
    (if adj then
      phaseOscillation (adjointCarrierSourcePhase Θ φ lam x ξ) z •
        adjointAnnularSourceAmplitude A π lam a x ξ z
    else
      phaseOscillation (forwardCarrierSourcePhase Θ φ lam x ξ) z •
        forwardAnnularSourceAmplitude A π lam a x ξ z)

/-- Move only the fixed output scalar through the source integral; the literal
normalization is retained (`app:ch_response:lem:energy-carrier-jets`). -/
theorem annularSourceKernelObservation_eq_integral (adj demod : Bool)
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ : E) :
    annularSourceKernelObservation adj demod Θ A π φ lam a x ξ =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ • ∫ z,
        annularSourceIntegrand adj demod Θ A π φ lam a x ξ z := by
  cases adj <;> cases demod <;>
    simp only [annularSourceKernelObservation, annularSourceIntegrand,
      Bool.false_eq_true, ↓reduceIte, one_smul,
      demodulatedForwardAnnularSourceKernel, demodulatedAdjointAnnularSourceKernel,
      forwardAnnularSourceKernel, adjointAnnularSourceKernel, integral_smul]
  all_goals exact smul_comm _ _ _

/-- The source envelope alone supplies fixed source support, for either
orientation and observation (`app:ch_response:lem:energy-carrier-jets`). -/
theorem annularSourceIntegrand_eq_zero_of_source_eq_zero (adj demod : Bool)
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ z : E) (hz : a z = 0) :
    annularSourceIntegrand adj demod Θ A π φ lam a x ξ z = 0 := by
  cases adj <;> simp [annularSourceIntegrand, forwardAnnularSourceAmplitude,
    adjointAnnularSourceAmplitude, hz]

/-- Supported phase replacement is an exact pointwise identity for the whole
integrand, hence for all its derivatives. The support set can be unbounded in
frequency (`app:ch_response:lem:energy-carrier-jets`). -/
theorem annularSourceIntegrand_phase_congr (adj demod : Bool)
    (Θ Θ' : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F)
    (he : ∀ x z ξ, A x z ξ ≠ 0 → Θ' x ξ = Θ x ξ) (x ξ z : E) :
    annularSourceIntegrand adj demod Θ' A π φ lam a x ξ z =
      annularSourceIntegrand adj demod Θ A π φ lam a x ξ z := by
  cases adj
  · by_cases h : A x z ξ = 0
    · simp [annularSourceIntegrand, forwardAnnularSourceAmplitude,
        annularComplementAmplitude, frequencyCutFullAmplitude, h]
    · simp only [annularSourceIntegrand, Bool.false_eq_true, ite_false,
        forwardCarrierSourcePhase, phaseOscillation, he x z ξ h]
  · by_cases h : A z x ξ = 0
    · simp [annularSourceIntegrand, adjointAnnularSourceAmplitude,
        annularComplementAmplitude, frequencyCutFullAmplitude, h]
    · simp only [annularSourceIntegrand, ite_true, adjointCarrierSourcePhase,
        phaseOscillation, he z x ξ h]

private theorem contDiffAt_annularSourceIntegrand_of_smooth_phase
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
    (hΘ : ContDiff ℝ ∞ (Function.uncurry Θ))
    (hA : ∀ i j, ContDiff ℝ ∞ (fun q : E × E × E => A q.1 q.2.1 q.2.2 i j))
    (hπ : ContDiff ℝ ∞ π) (q : ((P × E) × E) × E)
    (hφout : ContDiffAt ℝ ∞ (Function.uncurry φ) (q.1.1.1, q.1.1.2))
    (hφsource : ContDiffAt ℝ ∞ (Function.uncurry φ) (q.1.1.1, q.2))
    (ha : ContDiffAt ℝ ∞ (Function.uncurry a) (q.1.1.1, q.2)) :
    ContDiffAt ℝ ∞ (fun p : ((P × E) × E) × E =>
      annularSourceIntegrand adj demod Θ A π (φ p.1.1.1) lam
        (a p.1.1.1) p.1.1.2 p.1.2 p.2) q := by
  have hφx : ContDiffAt ℝ ∞ (fun p : ((P × E) × E) × E => φ p.1.1.1 p.1.1.2) q :=
    hφout.comp q
      (contDiffAt_fst.fst.fst.prodMk contDiffAt_fst.fst.snd)
  have hφz : ContDiffAt ℝ ∞ (fun p : ((P × E) × E) × E => φ p.1.1.1 p.2) q :=
    hφsource.comp q
      (contDiffAt_fst.fst.fst.prodMk contDiffAt_snd)
  have haz := ha.comp q
      (f := fun p : ((P × E) × E) × E => (p.1.1.1, p.2))
      (contDiffAt_fst.fst.fst.prodMk contDiffAt_snd)
  have hd : ContDiffAt ℝ ∞ (fun p : ((P × E) × E) × E =>
      if demod then carrier (-lam) (φ p.1.1.1) p.1.1.2 else 1) q := by
    cases demod
    · exact contDiffAt_const
    · exact (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp q
        (contDiffAt_const.mul hφx))).cexp
  have hcut : ContDiffAt ℝ ∞ (fun p : ((P × E) × E) × E =>
      1 - π (lam⁻¹ • p.1.2)) q :=
    contDiffAt_const.sub (hπ.contDiffAt.comp q (contDiffAt_fst.snd.const_smul _))
  apply hd.smul
  cases adj <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · apply ContDiffAt.smul (𝕜' := ℂ)
    · change ContDiffAt ℝ ∞ (fun p : ((P × E) × E) × E =>
        Complex.exp (((Θ p.1.1.2 p.1.2 - inner ℝ p.2 p.1.2 +
          lam * φ p.1.1.1 p.2 : ℝ) : ℂ) * Complex.I)) q
      exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp q
        (((hΘ.contDiffAt.comp q (contDiffAt_fst.fst.snd.prodMk contDiffAt_fst.snd)).sub
          (contDiffAt_snd.inner ℝ contDiffAt_fst.snd)).add
            (contDiffAt_const.mul hφz))).mul contDiffAt_const).cexp
    · apply PiLp.contDiff_toLp.contDiffAt.comp
      apply contDiffAt_pi.mpr
      intro i
      change ContDiffAt ℝ ∞ (fun p : ((P × E) × E) × E =>
        ∑ j, ((1 - π (lam⁻¹ • p.1.2)) * A p.1.1.2 p.2 p.1.2 i j) *
          (a p.1.1.1 p.2).ofLp j) q
      apply ContDiffAt.sum
      intro j _
      exact (hcut.mul ((hA i j).contDiffAt.comp q
        (contDiffAt_fst.fst.snd.prodMk (contDiffAt_snd.prodMk contDiffAt_fst.snd)))).mul
          (contDiffAt_pi.mp (PiLp.contDiff_ofLp.contDiffAt.comp q haz) j)
  · apply ContDiffAt.smul (𝕜' := ℂ)
    · change ContDiffAt ℝ ∞ (fun p : ((P × E) × E) × E =>
        Complex.exp (((inner ℝ p.1.1.2 p.1.2 - Θ p.2 p.1.2 +
          lam * φ p.1.1.1 p.2 : ℝ) : ℂ) * Complex.I)) q
      exact ((Complex.ofRealCLM.contDiff.contDiffAt.comp q
        (((contDiffAt_fst.fst.snd.inner ℝ contDiffAt_fst.snd).sub
          (hΘ.contDiffAt.comp q (contDiffAt_snd.prodMk contDiffAt_fst.snd))).add
            (contDiffAt_const.mul hφz))).mul contDiffAt_const).cexp
    · apply PiLp.contDiff_toLp.contDiffAt.comp
      apply contDiffAt_pi.mpr
      intro i
      change ContDiffAt ℝ ∞ (fun p : ((P × E) × E) × E =>
        ∑ j, star ((1 - π (lam⁻¹ • p.1.2)) * A p.2 p.1.1.2 p.1.2 j i) *
          (a p.1.1.1 p.2).ofLp j) q
      apply ContDiffAt.sum
      intro j _
      exact (Complex.conjCLE.contDiff.contDiffAt.comp q
        (hcut.mul ((hA j i).contDiffAt.comp q
          (contDiffAt_snd.prodMk (contDiffAt_fst.fst.snd.prodMk contDiffAt_fst.snd))))).mul
          (contDiffAt_pi.mp (PiLp.contDiff_ofLp.contDiffAt.comp q haz) j)

/-- Primitive smoothness implies joint smoothness in parameter, output,
frequency and source. This auxiliary global-phase version is used only after
supported extension; no global smoothness of the original phase is required.
Source: `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_annularSourceIntegrand_of_smooth_phase
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
    {U : Set P} (hU : IsOpen U)
    (hΘ : ContDiff ℝ ∞ (Function.uncurry Θ))
    (hA : ∀ i j, ContDiff ℝ ∞ (fun q : E × E × E => A q.1 q.2.1 q.2.2 i j))
    (hπ : ContDiff ℝ ∞ π)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (U ×ˢ univ))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
      annularSourceIntegrand adj demod Θ A π (φ q.1.1.1) lam
        (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ) := by
  intro q hq
  exact (contDiffAt_annularSourceIntegrand_of_smooth_phase adj demod Θ A π φ lam a
    hΘ hA hπ q
    (hφ.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hq.1.1.1, mem_univ _⟩))
    (hφ.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hq.1.1.1, mem_univ _⟩))
    (ha.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hq.1.1.1, mem_univ _⟩))).contDiffWithinAt

/-- Smoothness of the original supported integrand, across bounded frequencies,
high-pass regions and the entire tail. The closed supported chart lies inside
an open smoothness domain; it need not be compact. Consumer: source-integral
interchange in `app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_annularSourceIntegrand
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
    {U : Set P} (hU : IsOpen U) {D O : Set (E × E)}
    (hD : IsClosed D) (hO : IsOpen O) (hDO : D ⊆ O)
    (hΘ : ContDiffOn ℝ ∞ (Function.uncurry Θ) O)
    (hsD : ∀ x z ξ, A x z ξ ≠ 0 → (x, ξ) ∈ D)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun q : E × E × E => A q.1 q.2.1 q.2.2 i j))
    (hπ : ContDiff ℝ ∞ π)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (U ×ˢ univ))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
      annularSourceIntegrand adj demod Θ A π (φ q.1.1.1) lam
        (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ) := by
  obtain ⟨Θ', hΘ', he⟩ := exists_smooth_phase_extension Θ hD hO hDO hΘ
  apply (contDiffOn_annularSourceIntegrand_of_smooth_phase adj demod Θ' A π φ lam a
    hU hΘ' hA hπ hφ ha).congr
  intro q _
  exact (annularSourceIntegrand_phase_congr adj demod Θ Θ' A π (φ q.1.1.1) lam
    (a q.1.1.1) (fun x z ξ h => (he (x, ξ) (hsD x z ξ h)).eq_of_nhds)
    q.1.1.2 q.1.2 q.2).symm

/-- Amplitude zeros kill the entire original integrand, including its actual
demodulator (`app:ch_response:lem:energy-carrier-jets`). -/
theorem annularSourceIntegrand_eq_zero_of_amplitude (adj demod : Bool)
    (Θ : E → E → ℝ) (A : FullAmplitude n r) (π : E → ℂ)
    (φ : E → ℝ) (lam : ℝ) (a : E → F) (x ξ z : E)
    (hz : (if adj then A z x ξ else A x z ξ) = 0) :
    annularSourceIntegrand adj demod Θ A π φ lam a x ξ z = 0 := by
  cases adj <;> simp_all [annularSourceIntegrand, forwardAnnularSourceAmplitude,
    adjointAnnularSourceAmplitude, annularComplementAmplitude, frequencyCutFullAmplitude]

/-- Both the graph phase and the varying carrier phase may be smooth only on
their supported neighborhoods. The source and observation supports lie inside
the carrier neighborhood; elsewhere the original integrand is locally zero.
This is the primitive producer used by the elapsed regularity endpoint in
`app:ch_response:lem:energy-carrier-jets`. -/
theorem contDiffOn_annularSourceIntegrand_localCarrierPhase
    (adj demod : Bool) (Θ : E → E → ℝ) (A : FullAmplitude n r)
    (π : E → ℂ) (φ : P → E → ℝ) (lam : ℝ) (a : P → E → F)
    {U : Set P} (hU : IsOpen U) {D O : Set (E × E)}
    (hD : IsClosed D) (hO : IsOpen O) (hDO : D ⊆ O)
    (hΘ : ContDiffOn ℝ ∞ (Function.uncurry Θ) O)
    (hsD : ∀ x z ξ, A x z ξ ≠ 0 → (x, ξ) ∈ D)
    (hA : ∀ i j, ContDiff ℝ ∞ (fun q : E × E × E => A q.1 q.2.1 q.2.2 i j))
    (hπ : ContDiff ℝ ∞ π)
    {V X K : Set E} (hV : IsOpen V) (hX : IsClosed X) (hK : IsClosed K)
    (hXV : X ⊆ V) (hKV : K ⊆ V)
    (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (U ×ˢ V))
    (ha : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ univ))
    (hs : ∀ c ∈ U, tsupport (a c) ⊆ K)
    (hsX : ∀ x ∉ X, ∀ z ξ, (if adj then A z x ξ else A x z ξ) = 0) :
    ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
      annularSourceIntegrand adj demod Θ A π (φ q.1.1.1) lam
        (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ) := by
  obtain ⟨Θ', hΘ', he⟩ := exists_smooth_phase_extension Θ hD hO hDO hΘ
  have hJ : ContDiffOn ℝ ∞ (fun q : ((P × E) × E) × E =>
      annularSourceIntegrand adj demod Θ' A π (φ q.1.1.1) lam
        (a q.1.1.1) q.1.1.2 q.1.2 q.2) (((U ×ˢ univ) ×ˢ univ) ×ˢ univ) := by
    intro q hq
    by_cases hz : q.2 ∈ K
    · by_cases hx : q.1.1.2 ∈ X
      · exact (contDiffAt_annularSourceIntegrand_of_smooth_phase adj demod Θ' A π φ lam a
          hΘ' hA hπ q
          (hφ.contDiffAt ((hU.prod hV).mem_nhds ⟨hq.1.1.1, hXV hx⟩))
          (hφ.contDiffAt ((hU.prod hV).mem_nhds ⟨hq.1.1.1, hKV hz⟩))
          (ha.contDiffAt ((hU.prod isOpen_univ).mem_nhds
            ⟨hq.1.1.1, mem_univ _⟩))).contDiffWithinAt
      · apply ContDiffAt.contDiffWithinAt
        apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
        filter_upwards [(continuous_fst.fst.snd.tendsto q)
          (hX.isOpen_compl.mem_nhds hx)] with p hp
        exact annularSourceIntegrand_eq_zero_of_amplitude adj demod Θ' A π _ lam _ _ _ _
          (hsX p.1.1.2 hp p.2 p.1.2)
    · apply ContDiffAt.contDiffWithinAt
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [(continuous_fst.fst.fst.tendsto q) (hU.mem_nhds hq.1.1.1),
        (continuous_snd.tendsto q) (hK.isOpen_compl.mem_nhds hz)] with p hp hpz
      exact annularSourceIntegrand_eq_zero_of_source_eq_zero adj demod Θ' A π _ lam _ _ _ _
        (image_eq_zero_of_notMem_tsupport (fun h => hpz (hs p.1.1.1 hp h)))
  apply hJ.congr
  intro q _
  exact (annularSourceIntegrand_phase_congr adj demod Θ Θ' A π (φ q.1.1.1) lam
    (a q.1.1.1) (fun x z ξ h => (he (x, ξ) (hsD x z ξ h)).eq_of_nhds)
    q.1.1.2 q.1.2 q.2).symm

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
