module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.UniformParameterSources
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ParameterObservationAssembly
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ObservedParameterRemainders.Totalization

/-!
# The observed parameter remainder from original source profiles

This applies both actual producers: original compact phase/source profiles
give the norm derivatives of the same inverse-source remainder, and the
literal demodulated observation gives their same-order Fourier bound. One
depth is chosen before histories, parameters, and directions. No estimate
for source derivatives, observation derivatives, or the desired remainder
is added as a hypothesis.

The original source cutoff contains the initialized inner recut. The phase
is only totalized outside the retained parameter domain to write a total
carrier-multiplication family; all its retained germs and mixed jets agree.
Consumer: the remainder field of
`parameter_inverse_reserved_envelope_of_finite_remainders`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff NNReal ENNReal JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential ArbitraryAccuracy SmallSupport
open ResponseTransfer ResponseTransfer.SourceNegative ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open RegularSector RegularSector.Realization RegularSector.Characteristic.RetardedLocalization
open ObservedParameterRemainders

variable {d q : ℕ} {ι : Type*}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "FR" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The SAME initialized inverse and complete solver have a uniform observed
parameter remainder, derived from the original recut source, positive
operator estimates, and primitive profiles. The selected depth is `N+s`
for every actual source-jet term. The constant precedes all family members,
parameters, and unit directions. The displayed profiles are retained
literally; this theorem does not infer additional tame scalar dependence
(`app:ch_regular:eq:inverse-remainder`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_observed_parameter_remainders_of_original_profiles
    (W : Set E) (hW : MeasurableSet W)
    (R : ι → LocalL2 W F →L[ℂ] LocalL2 W F)
    (hreal : ∀ i, conjugateOperator (R i).toLinearMap = (R i).toLinearMap)
    (hR : ∀ i, ‖R i‖ < 1)
    (Cgain Dcoeff : ℕ → ℝ) (a : ι → ℕ → ℝ) (b : ℕ) (θ : ℝ)
    (hKloc : ∀ i, ‖realOutputCompression (R i)‖ ≤ θ) (hθ : θ < 1)
    (hCgain : ∀ j, 0 ≤ Cgain j) (hDcoeff : ∀ j, 0 ≤ Dcoeff j)
    (ha : ∀ i j, 0 ≤ a i j) (ham : ∀ i, Monotone (a i))
    (hgain : ∀ i j (u : LocalL2 W FR), MemRestrictionSobolev W j u →
      (MemRestrictionSobolev W (j+1) (realOutputCompression (R i) u) ∧
        restrictionSobolevNorm W (j+1) (realOutputCompression (R i) u) ≤ Cgain (j+1) *
          (restrictionSobolevNorm W j u + (1 + a i (j+1+b)) * ‖u‖)) ∧
      (MemRestrictionSobolev W (j+1) ((realOutputCompression (R i)).adjoint u) ∧
        restrictionSobolevNorm W (j+1) ((realOutputCompression (R i)).adjoint u) ≤ Cgain (j+1) *
          (restrictionSobolevNorm W j u + (1 + a i (j+1+b)) * ‖u‖)))
    {V : Set Par} {X : Set E} (hV : IsOpen V) (hX : IsCompact X)
    (Hphase : ℕ → ℝ) (hHphase : ∀ m, 0 ≤ Hphase m) (Csource : ℕ → ℕ → ℝ)
    (ρ A K L : ι → ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (φ : ι → Par → E → ℝ)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (φ i)) (V ×ˢ univ))
    (f : ι → Par → E → F)
    (hf : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (f i)) (V ×ˢ univ))
    (hs : ∀ i c, c ∈ V → tsupport (f i c) ⊆ X)
    (hm : ∀ i c, c ∈ V → ∀ vs : List Par,
      MemLp (fun x ↦ parameterListJet (fun z ↦ f i z x) vs c) 2 volume)
    (hmem : ∀ i c (hc : c ∈ V) vs (j : ℕ),
      MemVectorFourierSobolev (j : ℝ) ((hm i c hc vs).toLp _))
    (hprofile : ∀ i c (hc : c ∈ V) vs, (∀ w ∈ vs, ‖w‖ ≤ 1) → ∀ j : ℕ,
      vectorFourierSobolevNorm (j : ℝ) ((hm i c hc vs).toLp _) ≤
        Csource vs.length j * (A i * K i ^ vs.length) * K i ^ j)
    (hphase : ∀ i c, c ∈ V → ∀ x ∈ X, ∀ m,
      ‖iteratedFDeriv ℝ m (Function.uncurry (φ i)) (c,x)‖ ≤ Hphase m * K i ^ m)
    (χ : ι → E → ℝ) (S : Set E) (gap upper : ℝ) (Pphase Xcut : ℕ → ℝ)
    (g : ∀ i c, c ∈ V → SourceGeometry (χ i) (φ i c) S gap upper (L i) Pphase Xcut)
    (hSW : S ⊆ W)
    (hcoeff : ∀ i j, 1 + a i (j+b) ≤ Dcoeff j * L i ^ j) (hLK : ∀ i, L i ≤ K i)
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hwindow : ∀ i, K i ≤ ρ i ^ (1-ν))
    (hmphysical : ∀ i c, MemLp (modulatedSource (χ i) (φ i c) (f i c) (ρ i)) 2 volume)
    (source : ι → Par → LocalL2 W F)
    (hsource : ∀ i c, c ∈ V → source i c = restrictL2 W
      ((hmphysical i c).toLp (modulatedSource (χ i) (φ i c) (f i c) (ρ i))))
    {x : E} (χ₃ : ContDiffBump x) (hχ₃ : tsupport (χ₃ : E → ℝ) ⊆ W)
    (Op : ι → H →L[ℂ] H)
    {Xφ : Set E} (hXφ : IsCompact Xφ)
    (hsφ : ∀ i c, c ∈ V → tsupport (φ i c) ⊆ Xφ)
    (Pobs Csolver Ccoefficient : ℕ → ℝ)
    (hPobs : ∀ j, 0 ≤ Pobs j) (hCsolver : ∀ s, 0 ≤ Csolver s)
    (hCcoefficient : ∀ s, 0 ≤ Ccoefficient s)
    (hphaseObs : ∀ i c, c ∈ V → ∀ y ∈ Xφ, ∀ j, 1 ≤ j →
      ‖iteratedFDeriv ℝ j (Function.uncurry (φ i)) (c,y)‖ ≤ Pobs j * K i ^ j)
    (high : ι → ℕ → ℝ) (hhigh : ∀ i s, 0 ≤ high i s)
    (hcoefficient : ∀ i s, 1 + high i s ≤ Ccoefficient s * L i ^ s)
    (hsolver : ∀ i (s : ℕ) (z : H), MemVectorFourierSobolev (s : ℝ) z →
      MemVectorFourierSobolev (s : ℝ) (Op i z) ∧
        vectorFourierSobolevNorm (s : ℝ) (Op i z) ≤
          Csolver s * (vectorFourierSobolevNorm (s : ℝ) z + high i s * ‖z‖)) :
    ∀ s k, ∃ (N : ℕ) (D : ℝ), 0 ≤ D ∧ ∀ i c, c ∈ V →
      ∀ v : Fin k → Par, (∀ j, ‖v j‖ ≤ 1) →
        let u := fun z ↦ complexNeumannInverse (R i) (hR i)
          (((R i)^(N+s)) (source i z))
        let observed := fun z ↦ carrierMultiplication (-(ρ i))
          (totalizedObservationPhase V (φ i) z)
          (continuous_totalizedObservationPhase (hφ i) z)
          (Op i (zeroExtend hW (bumpL2 (p := 2) le_rfl χ₃ (u z))))
        MemVectorFourierSobolev (s : ℝ) (iteratedFDeriv ℝ k observed c v) ∧
          vectorFourierSobolevNorm (s : ℝ) (iteratedFDeriv ℝ k observed c v) ≤ D * A i := by
  classical
  by_cases hVne : V.Nonempty
  · obtain ⟨c₀, hc₀⟩ := hVne
    have hL : ∀ i, 1 ≤ L i := fun i ↦ (g i c₀ hc₀).scale_one_le
    obtain ⟨hsmooth, CP, _hCP, hpower⟩ := exists_uniform_actual_parameter_source_remainders
      W hW R hreal hR Cgain Dcoeff a b θ hKloc hθ hCgain hDcoeff ha ham hgain
      hV isOpen_univ hX (subset_univ _) Hphase hHphase Csource ρ A K L hρ hA hK
      φ hφ f hf hs hm hmem hprofile hphase χ S gap upper Pphase Xcut g hSW
      hcoeff hLK hν hν1 hwindow hmphysical source hsource
    have hsTot (i : ι) (c : Par) (hc : c ∈ V) :
        tsupport (totalizedObservationPhase V (φ i) c) ⊆ Xφ := by
      rw [totalizedObservationPhase_of_mem (φ i) hc]
      exact hsφ i c hc
    have hpTot (i : ι) (c : Par) (hc : c ∈ V) (y : E) (hy : y ∈ Xφ) (j : ℕ)
        (hj : 1 ≤ j) :
        ‖iteratedFDeriv ℝ j (Function.uncurry (totalizedObservationPhase V (φ i))) (c,y)‖ ≤
          Pobs j * K i ^ j := by
      rw [iteratedFDeriv_totalizedObservationPhase hV (φ i) j hc y]
      exact hphaseObs i c hc y hy j hj
    exact observed_parameter_remainder_of_actual_source_jets W hW χ₃ hχ₃ R hR Op source
      V hV hsmooth ρ L K A hρ hL hLK hν hwindow hA
      (fun i ↦ totalizedObservationPhase V (φ i))
      (fun i ↦ continuous_totalizedObservationPhase (hφ i))
      (fun i ↦ contDiffOn_totalizedObservationPhase (hφ i)) hXφ hsTot
      Pobs Csolver Ccoefficient hPobs hCsolver hCcoefficient hpTot
      high hhigh hcoefficient hsolver CP hpower
  · intro s k
    refine ⟨0, 0, le_rfl, ?_⟩
    intro i c hc
    exact False.elim (hVne ⟨c, hc⟩)

end JanetCartan.FixedDomainInverse

