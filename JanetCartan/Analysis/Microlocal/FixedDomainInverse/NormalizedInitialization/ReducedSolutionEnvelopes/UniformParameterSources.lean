module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ComplexParameterRemainder

/-!
# Uniform actual parameter-source remainders

Apply the explicit original-source remainder with one common choice of its
constants before histories and unit parameter directions. The source identity
is the literal recut admission identity; all norm derivatives and their
Sobolev estimates are proved, not assumed. This supplies the source input of
`observed_parameter_remainder_of_actual_source_jets` at the same `N+s`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ContDiff JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential ArbitraryAccuracy
open ResponseTransfer ResponseTransfer.SourceNegative ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open RegularSector RegularSector.Realization RegularSector.Characteristic.RetardedLocalization

variable {d q : ℕ} {ι : Type*}
local notation "E" => Euclidean (d+1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "FR" => EuclideanSpace ℝ (Fin q)

/-- The original compact parameter localization constructs a physical source
class for every parameter. Inside the retained domain its phase and amplitude
are continuous and compactly supported; outside it the original parameter
cutoff makes the source zero. Thus the total `hmphysical` used below adds no
global phase-regularity hypothesis to the initializer
(`app:ch_response:eq:response-graded-source`). -/
theorem memLp_original_product_modulated_source_of_parameter_support
    {V : Set Par} {Ω X : Set E} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hX : IsCompact X) (hXΩ : X ⊆ Ω)
    {φ : Par → E → ℝ} (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ Ω))
    {f : Par → E → F} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ X)
    (hzero : ∀ c, c ∉ V → f c = 0)
    {χ : E → ℝ} (hχ : Continuous χ)
    (ρ : ℝ) (c : Par) : MemLp (modulatedSource χ (φ c) (f c) ρ) 2 volume := by
  by_cases hc : c ∈ V
  · have hphysical := contDiffOn_productParameterSourceFunction_localized
      hV hΩ hX.isClosed hXΩ ρ hφ hf hs
    have hfc : Continuous (fun x ↦ carrier ρ (φ c) x • f c x) :=
      hphysical.continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun x ↦ ⟨hc, mem_univ x⟩)
    have hcompact : HasCompactSupport (modulatedSource χ (φ c) (f c) ρ) :=
      hX.of_isClosed_subset (isClosed_tsupport _)
        ((tsupport_smul_subset_right _ _).trans
          ((tsupport_smul_subset_right _ _).trans (hs c hc)))
    exact (hχ.smul hfc).memLp_of_hasCompactSupport hcompact
  · have he : modulatedSource χ (φ c) (f c) ρ = 0 := by
      funext x
      simp only [modulatedSource, hzero c hc, Pi.zero_apply, smul_zero]
    rw [he]
    exact MemLp.zero

/-- Primitive original profiles give one uniform constant family for every
actual inverse-source parameter remainder. The underlying source is fixed
before the depth, and the original real gain constant and coefficient shift
are retained. The physical source class is the original recut admitted class;
no derivative identity or derivative norm estimate is an input
(`app:ch_regular:eq:inverse-remainder`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem exists_uniform_actual_parameter_source_remainders
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
    {V : Set Par} {Ω X : Set E} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hX : IsCompact X) (hXΩ : X ⊆ Ω)
    (Hphase : ℕ → ℝ) (hHphase : ∀ m, 0 ≤ Hphase m) (Csource : ℕ → ℕ → ℝ)
    (ρ A K L : ι → ℝ)
    (hρ : ∀ i, 1 ≤ ρ i) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 1 ≤ K i)
    (φ : ι → Par → E → ℝ)
    (hφ : ∀ i, ContDiffOn ℝ ∞ (Function.uncurry (φ i)) (V ×ˢ Ω))
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
      ((hmphysical i c).toLp (modulatedSource (χ i) (φ i c) (f i c) (ρ i)))) :
    (∀ i, ContDiffOn ℝ ∞ (source i) V) ∧
      ∃ CP : ℕ → ℕ → ℕ → ℝ, (∀ N s k, 0 ≤ CP N s k) ∧
        ∀ i N s k c, c ∈ V → ∀ v : Fin k → Par, (∀ j, ‖v j‖ ≤ 1) →
          let u := fun z ↦ complexNeumannInverse (R i) (hR i)
            (((R i)^(N+s)) (source i z))
          let jet := iteratedFDeriv ℝ k u c v
          MemRestrictionSobolev W s jet ∧ restrictionSobolevNorm W s jet ≤
            CP N s k * (A i * ρ i ^ k * K i ^ (k+(d+1)+1)) * L i ^ s *
              (L i / ρ i)^N := by
  have hphysical (i : ι) (c : Par) (hc : c ∈ V) :
      ContDiffOn ℝ ∞
        (Function.uncurry (fun z ↦ modulatedSource (χ i) (φ i z) (f i z) (ρ i)))
        (V ×ˢ univ) :=
    ((g i c hc).cutoff_smooth.comp_contDiffOn contDiffOn_snd).smul
      (contDiffOn_productParameterSourceFunction_localized
        hV hΩ hX.isClosed hXΩ (ρ i) (hφ i) (hf i) (hs i))
  have hphysicalSupport (i : ι) (c : Par) (hc : c ∈ V) :
      tsupport (modulatedSource (χ i) (φ i c) (f i c) (ρ i)) ⊆ X :=
    (tsupport_smul_subset_right _ _).trans
      ((tsupport_smul_subset_right _ _).trans (hs i c hc))
  constructor
  · intro i c hc
    have hclass := (restrictL2 W : Lp F 2 (volume : Measure E) →L[ℝ] LocalL2 W F).contDiff.comp_contDiffOn
      (contDiffOn_productParameterSourceClass hX hV (hphysical i c hc)
        (hphysicalSupport i) (hmphysical i))
    exact (hclass.congr (fun z hz ↦ hsource i z hz)) c hc
  · let cost := fun N s k ↦ 6 *
      (inverseTameConstant θ Cgain s * (powerGainConstant Cgain Dcoeff s + Dcoeff s) *
        ((localDualityConstant (d+1) N (EuclideanSpace.basisFun (Fin q) ℝ) *
          modulatedSourceNegativeConstant (d+1) N S gap upper ν Pphase Xcut
            (fun j ↦ (2 : ℝ)^k * UniformPhase.unitSobolevBudget (d+1) q X Hphase Csource k j)) *
          powerGainConstant Cgain Dcoeff N))
    refine ⟨fun N s k ↦ |cost N s k|, fun N s k ↦ abs_nonneg _, ?_⟩
    intro i N s k c hc v hv u jet
    obtain ⟨_, hmj, hbj⟩ := inverse_remainder_product_parameter_jet
      hW (R i) (hreal i) (hR i) (hKloc i) hθ hCgain hDcoeff (ha i) (ham i) (hgain i)
      hV hΩ hX hXΩ Hphase hHphase Csource k (ρ i) (A i) (K i)
      (hρ i) (hA i) (hK i) (hφ i) (hf i) (hs i) hc (hm i c hc) (hmem i c hc)
      (fun vs _ hvs j ↦ hprofile i c hc vs hvs j) v hv (hphase i c hc)
      (g i c hc) hSW (hcoeff i) (hLK i) hν hν1 (hwindow i)
      (hmphysical i) (source i) (hsource i) N s
    refine ⟨hmj, hbj.trans ?_⟩
    have hL0 := zero_le_one.trans (g i c hc).scale_one_le
    have hρ0 := zero_le_one.trans (hρ i)
    have hK0 := zero_le_one.trans (hK i)
    have hAi := hA i
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self (cost N s k)) (by positivity))
        (pow_nonneg hL0 _)) (pow_nonneg (div_nonneg hL0 hρ0) _)

end JanetCartan.FixedDomainInverse
