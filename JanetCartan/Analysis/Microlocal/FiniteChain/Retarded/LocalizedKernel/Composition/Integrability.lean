module

public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.Composition.Smooth
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.FrequencyIntegration
public import JanetCartan.Analysis.Microlocal.FiniteChain.Retarded.LocalizedKernel.NormalCoordinates

/-!
# Joint absolute convergence for the regularized retarded composition

The normal difference is bounded by the two weight supports. The two frequency
variables are controlled separately by the regularizer and the input symbol.
This proves joint integrability, including the source, for the actual integrands
of `app:ch_regular:lem:finite-chain`, before applying physical Fubini.
-/

@[expose] public noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.FiniteChain.Retarded.LocalizedKernel
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
private theorem compactSupport_full_of_weight_factors
    (α β : ℝ × E → ℝ) (mi : (ℝ × E) → (ℝ × E) → ℂ) (r : ℝ × E → ℂ)
    (hα : HasCompactSupport α) (hβ : HasCompactSupport β)
    (hi : HasCompactSupport (Function.uncurry mi)) (hr : HasCompactSupport r)
    (f : (ℝ × TangentialVariables E) × (ℝ × E) → ℂ)
    (hf : ∀ p, f p ≠ 0 → α (p.1.2.1.1+p.1.1,p.1.2.1.2) ≠ 0 ∧
      β p.1.2.1 ≠ 0 ∧ r p.1.2.2.1 ≠ 0 ∧ mi p.2 p.1.2.2.2 ≠ 0) :
    HasCompactSupport f := by
  let T : ((ℝ × E) × (ℝ × E)) × ((ℝ × E) × ((ℝ × E) × (ℝ × E))) →
      (ℝ × TangentialVariables E) × (ℝ × E) :=
    fun q => ((q.1.1.1-q.1.2.1, q.1.2, q.2.1, q.2.2.2), q.2.2.1)
  apply HasCompactSupport.of_support_subset_isCompact
    (((hα.prod hβ).prod (hr.prod hi)).image (show Continuous T by fun_prop))
  intro p hp
  obtain ⟨ha,hb,hr,hi⟩ := hf p hp
  refine ⟨(((p.1.2.1.1+p.1.1,p.1.2.1.2),p.1.2.1),
    (p.1.2.2.1,(p.2,p.1.2.2.2))),
    ⟨⟨subset_tsupport α ha, subset_tsupport β hb⟩,
      ⟨subset_tsupport r hr, subset_tsupport (Function.uncurry mi) hi⟩⟩, ?_⟩
  simp [T]

/-- The complete lower integrand, including its source, has compact support in
all integration variables (`app:ch_regular:lem:finite-chain`). -/
theorem hasCompactSupport_lowerIntegrand_source
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : HasCompactSupport α) (hβ : HasCompactSupport β)
    (hi : HasCompactSupport (Function.uncurry mi)) (hr : HasCompactSupport r) :
    HasCompactSupport (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      lowerIntegrand α β mi mo r p.2 xo p.1 * u p.2) := by
  apply compactSupport_full_of_weight_factors α β mi r hα hβ hi hr
  intro p hp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hz <;>
    simp [lowerIntegrand, lowerAmplitude, hz] at hp

/-- The literal upper integrand has the same compact carrier, with the input
at the later time (`app:ch_regular:lem:finite-chain`). -/
theorem hasCompactSupport_upperIntegrand_source
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : HasCompactSupport α) (hβ : HasCompactSupport β)
    (hi : HasCompactSupport (Function.uncurry mi)) (hr : HasCompactSupport r) :
    HasCompactSupport (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      upperIntegrand α β mi mo r p.2 xo p.1 * u p.2) := by
  apply compactSupport_full_of_weight_factors α β mi r hα hβ hi hr
  intro p hp
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hz <;>
    simp [upperIntegrand, upperAmplitude, hz] at hp

/-- Continuity with the source included, used to establish absolute convergence
of the lower physical/Fourier integrals (`app:ch_regular:lem:finite-chain`). -/
theorem continuous_lowerIntegrand_source
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : Continuous α) (hβ : Continuous β)
    (hi : Continuous (Function.uncurry mi)) (ho : Continuous (Function.uncurry mo))
    (hr : Continuous r) (hu : Continuous u) :
    Continuous (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      lowerIntegrand α β mi mo r p.2 xo p.1 * u p.2) := by
  have hi' : Continuous (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      mi p.2 p.1.2.2.2) := hi.comp (continuous_snd.prodMk continuous_fst.snd.snd.snd)
  have ho' : Continuous (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      mo xo p.1.2.2.1) := ho.comp (continuous_const.prodMk continuous_fst.snd.snd.fst)
  unfold lowerIntegrand lowerAmplitude packedPhase phase
  fun_prop

/-- Continuity of the literal upper source integrand
(`app:ch_regular:lem:finite-chain`). -/
theorem continuous_upperIntegrand_source
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : Continuous α) (hβ : Continuous β)
    (hi : Continuous (Function.uncurry mi)) (ho : Continuous (Function.uncurry mo))
    (hr : Continuous r) (hu : Continuous u) :
    Continuous (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      upperIntegrand α β mi mo r p.2 xo p.1 * u p.2) := by
  have hi' : Continuous (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      mi p.2 p.1.2.2.2) := hi.comp (continuous_snd.prodMk continuous_fst.snd.snd.snd)
  have ho' : Continuous (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      mo xo p.1.2.2.1) := ho.comp (continuous_const.prodMk continuous_fst.snd.snd.fst)
  unfold upperIntegrand upperAmplitude packedUpperPhase adjointPhase
  fun_prop

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Joint absolute convergence in the normal, common-base, both frequency and
source variables for the lower orientation (`app:ch_regular:lem:finite-chain`).
Restriction to the nonnegative normal half-space is included. -/
theorem integrable_lowerIntegrand_source
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : Continuous α) (hβ : Continuous β)
    (hi : Continuous (Function.uncurry mi)) (ho : Continuous (Function.uncurry mo))
    (hr : Continuous r) (hu : Continuous u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r) :
    Integrable (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      lowerIntegrand α β mi mo r p.2 xo p.1 * u p.2)
      (((volume.restrict (Ici (0 : ℝ))).prod volume).prod volume) :=
  (continuous_lowerIntegrand_source α β mi mo r u xo hα hβ hi ho hr hu).integrable_of_hasCompactSupport
      (hasCompactSupport_lowerIntegrand_source α β mi mo r u xo hsα hsβ hsi hsr)

/-- Full joint absolute convergence for the literal upper orientation, including
the normal half-space (`app:ch_regular:lem:finite-chain`). -/
theorem integrable_upperIntegrand_source
    (α β : ℝ × E → ℝ) (mi mo : (ℝ × E) → (ℝ × E) → ℂ)
    (r u : ℝ × E → ℂ) (xo : ℝ × E)
    (hα : Continuous α) (hβ : Continuous β)
    (hi : Continuous (Function.uncurry mi)) (ho : Continuous (Function.uncurry mo))
    (hr : Continuous r) (hu : Continuous u)
    (hsα : HasCompactSupport α) (hsβ : HasCompactSupport β)
    (hsi : HasCompactSupport (Function.uncurry mi)) (hsr : HasCompactSupport r) :
    Integrable (fun p : (ℝ × TangentialVariables E) × (ℝ × E) =>
      upperIntegrand α β mi mo r p.2 xo p.1 * u p.2)
      (((volume.restrict (Ici (0 : ℝ))).prod volume).prod volume) :=
  (continuous_upperIntegrand_source α β mi mo r u xo hα hβ hi ho hr hu).integrable_of_hasCompactSupport
      (hasCompactSupport_upperIntegrand_source α β mi mo r u xo hsα hsβ hsi hsr)

end JanetCartan.FiniteChain.Retarded.LocalizedKernel
