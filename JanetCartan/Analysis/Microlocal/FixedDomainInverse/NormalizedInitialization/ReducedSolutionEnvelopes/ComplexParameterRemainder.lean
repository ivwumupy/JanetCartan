module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.ProductParameterRemainder

/-!
# Actual parameter derivatives of the same complex inverse remainder

The two original real source quadratures are estimated separately by the
initialized inverse and then recombined before demodulation. The fixed
complex inverse and every residual power commute with the actual norm
derivatives of the original compact source family. This closes the local
source input to the parameter observation estimate, at the same depth and
Sobolev order, in `app:ch_response:eq:response-graded-reduced`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential ArbitraryAccuracy
open ResponseTransfer ResponseTransfer.SourceNegative ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open RegularSector RegularSector.Realization RegularSector.Characteristic.RetardedLocalization

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "FR" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- The genuine parameter derivative of the original complex source
commutes with its fixed inverse and residual power. The source identity
is on the original parameter neighborhood; no identity for differentiated
admissions is assumed (`app:ch_regular:eq:finite-neumann-identity`). -/
theorem iteratedFDeriv_fixed_complex_inverse_product_source_of_eq
    {W : Set E}
    (R : LocalL2 W F →L[ℂ] LocalL2 W F) (hR : ‖R‖ < 1) (depth : ℕ)
    {V : Set Par} (hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    (g : Par → E → F)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (g c) ⊆ X)
    (hm : ∀ c, MemLp (g c) 2 volume)
    (admitted : Par → LocalL2 W F)
    (hadmitted : ∀ c ∈ V, admitted c = restrictL2 W ((hm c).toLp (g c)))
    (k : ℕ) (v : Fin k → Par) {c : Par} (hc : c ∈ V) :
    iteratedFDeriv ℝ k
        (fun c' ↦ complexNeumannInverse R hR ((R ^ depth) (admitted c'))) c v =
      complexNeumannInverse R hR ((R ^ depth)
        (restrictL2 W
          ((ResponseTransfer.FullSourceEnvelopes.fullSource_parameterJet_memLp
            hX hV hg hs k v hc).toLp
              (fun x ↦ iteratedFDeriv ℝ k (fun c' ↦ g c' x) c v)))) := by
  let source := fun c' ↦ (hm c').toLp (g c')
  let T : H →L[ℝ] LocalL2 W F :=
    (((complexNeumannInverse R hR).comp (R ^ depth)).restrictScalars ℝ).comp (restrictL2 W)
  have he : (fun c' ↦ complexNeumannInverse R hR ((R ^ depth) (admitted c'))) =ᶠ[nhds c]
      T ∘ source := by
    filter_upwards [hV.mem_nhds hc] with c' hc'
    change complexNeumannInverse R hR ((R ^ depth) (admitted c')) =
      complexNeumannInverse R hR ((R ^ depth) (restrictL2 W ((hm c').toLp (g c'))))
    rw [hadmitted c' hc']
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  have hdiff := T.iteratedFDeriv_comp_left
    (((contDiffOn_productParameterSourceClass hX hV hg hs hm).contDiffAt
      (hV.mem_nhds hc)).of_le (by simp)) (le_refl (k : ℕ∞ω))
  have hid := iteratedFDeriv_productParameterSourceClass hX hV hg hs hm k v hc
  exact (congrArg (fun m ↦ m v) hdiff).trans (congrArg T hid)

/-- Compact joint smoothness of the original source supplies norm-smoothness
of every remainder family of the same inverse. This is the regularity input
of the actual parameter Leibniz observation, without a smooth-output premise
(`app:ch_response:thm:response-literal-transfer`). -/
theorem contDiffOn_fixed_complex_inverse_product_source_of_eq
    {W : Set E}
    (R : LocalL2 W F →L[ℂ] LocalL2 W F) (hR : ‖R‖ < 1) (depth : ℕ)
    {V : Set Par} (hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    (g : Par → E → F)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (g c) ⊆ X)
    (hm : ∀ c, MemLp (g c) 2 volume)
    (admitted : Par → LocalL2 W F)
    (hadmitted : ∀ c ∈ V, admitted c = restrictL2 W ((hm c).toLp (g c))) :
    ContDiffOn ℝ ∞
      (fun c ↦ complexNeumannInverse R hR ((R ^ depth) (admitted c))) V := by
  let T : H →L[ℝ] LocalL2 W F :=
    (((complexNeumannInverse R hR).comp (R ^ depth)).restrictScalars ℝ).comp (restrictL2 W)
  have hT := T.contDiff.comp_contDiffOn
    (contDiffOn_productParameterSourceClass hX hV hg hs hm)
  apply hT.congr
  intro c hc
  change complexNeumannInverse R hR ((R ^ depth) (admitted c)) =
    complexNeumannInverse R hR ((R ^ depth) (restrictL2 W ((hm c).toLp (g c))))
  rw [hadmitted c hc]

/-- Original phase/source profiles give the complex remainder on the actual
physical source derivative. Both real quadratures use the SAME inverse,
source cutoff, spatial order `s`, and depth `N+s`. The numerical factor
six comes from their fixed Sobolev recombination; the amplitude and scale
powers are unchanged (`app:ch_regular:eq:inverse-remainder`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem inverse_remainder_actual_product_complex_source
    {W : Set E} (hW : MeasurableSet W)
    (R : LocalL2 W F →L[ℂ] LocalL2 W F)
    (hreal : conjugateOperator R.toLinearMap = R.toLinearMap) (hR : ‖R‖ < 1)
    {Cgain Dcoeff a : ℕ → ℝ} {b : ℕ} {θ : ℝ}
    (hKloc : ‖(realOutputCompression R)‖ ≤ θ) (hθ : θ < 1)
    (hCgain : ∀ j, 0 ≤ Cgain j) (hDcoeff : ∀ j, 0 ≤ Dcoeff j)
    (ha : ∀ j, 0 ≤ a j) (ham : Monotone a)
    (hgain : ∀ j u, MemRestrictionSobolev W j u →
      (MemRestrictionSobolev W (j + 1) ((realOutputCompression R) u) ∧
        restrictionSobolevNorm W (j + 1) ((realOutputCompression R) u) ≤ Cgain (j + 1) *
          (restrictionSobolevNorm W j u + (1 + a (j + 1 + b)) * ‖u‖)) ∧
      (MemRestrictionSobolev W (j + 1) ((realOutputCompression R).adjoint u) ∧
        restrictionSobolevNorm W (j + 1) ((realOutputCompression R).adjoint u) ≤ Cgain (j + 1) *
          (restrictionSobolevNorm W j u + (1 + a (j + 1 + b)) * ‖u‖)))
    {V : Set Par} {Ω X : Set E} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hX : IsCompact X) (hXΩ : X ⊆ Ω)
    (Hphase : ℕ → ℝ) (hHphase : ∀ m, 0 ≤ Hphase m)
    (Csource : ℕ → ℕ → ℝ)
    (k : ℕ) (ρ A K : ℝ) (hρ : 1 ≤ ρ) (hA : 0 ≤ A) (hK : 1 ≤ K)
    {φ : Par → E → ℝ} (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ Ω))
    {f : Par → E → F} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ X) {c : Par} (hc : c ∈ V)
    (hm : ∀ vs : List Par,
      MemLp (fun x ↦ parameterListJet (fun a ↦ f a x) vs c) 2 volume)
    (hmem : ∀ vs (j : ℕ), MemVectorFourierSobolev (j : ℝ) ((hm vs).toLp _))
    (hprofile : ∀ vs, vs.length ≤ k → (∀ w ∈ vs, ‖w‖ ≤ 1) → ∀ j : ℕ,
      vectorFourierSobolevNorm (j : ℝ) ((hm vs).toLp _) ≤
        Csource vs.length j * (A * K ^ vs.length) * K ^ j)
    (v : Fin k → Par) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hphase : ∀ x ∈ X, ∀ m,
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (c, x)‖ ≤ Hphase m * K ^ m)
    {χ : E → ℝ} {S : Set E} {gap upper L : ℝ} {Pphase Xcut : ℕ → ℝ}
    (g : SourceGeometry χ (φ c) S gap upper L Pphase Xcut) (hSW : S ⊆ W)
    (hcoeff : ∀ j, 1 + a (j + b) ≤ Dcoeff j * L ^ j) (hLK : L ≤ K)
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hwindow : K ≤ ρ ^ (1 - ν))
    (N s : ℕ) :
    let derivative := fun x ↦ iteratedFDeriv ℝ k
      (fun c' ↦ modulatedSource χ (φ c') (f c') ρ x) c v
    ∃ hd : MemLp derivative 2 volume,
      let datum := restrictL2 W (hd.toLp derivative)
      let CN := modulatedSourceNegativeConstant (d + 1) N S gap upper ν Pphase Xcut
        (fun j ↦ (2 : ℝ)^k * UniformPhase.unitSobolevBudget (d + 1) q X Hphase Csource k j)
      MemRestrictionSobolev W s (complexNeumannInverse R hR ((R ^ (N+s)) datum)) ∧
      restrictionSobolevNorm W s (complexNeumannInverse R hR ((R ^ (N+s)) datum)) ≤
        (6 * (inverseTameConstant θ Cgain s * (powerGainConstant Cgain Dcoeff s + Dcoeff s) *
          ((localDualityConstant (d + 1) N (EuclideanSpace.basisFun (Fin q) ℝ) * CN) *
            powerGainConstant Cgain Dcoeff N))) *
          (A * ρ ^ k * K ^ (k + (d + 1) + 1)) * L ^ s * (L / ρ) ^ N := by
  intro derivative
  obtain ⟨hd, hre⟩ := inverse_remainder_actual_product_source_quadrature
    hW (realOutputCompression R) hKloc hθ hCgain hDcoeff ha ham hgain
    hV hΩ hX hXΩ Hphase hHphase Csource k ρ A K hρ hA hK hφ hf hs hc
    hm hmem hprofile v hv hphase g hSW hcoeff hLK hν hν1 hwindow N s 1 (by simp)
  obtain ⟨hdi, him⟩ := inverse_remainder_actual_product_source_quadrature
    hW (realOutputCompression R) hKloc hθ hCgain hDcoeff ha ham hgain
    hV hΩ hX hXΩ Hphase hHphase Csource k ρ A K hρ hA hK hφ hf hs hc
    hm hmem hprofile v hv hphase g hSW hcoeff hLK hν hν1 hwindow N s
      (-Complex.I) (by simp)
  refine ⟨hd, ?_⟩
  dsimp only at hre him ⊢
  simp only [one_smul] at hre
  let datum := restrictL2 W (hd.toLp derivative)
  have hbound := complex_inverse_power_remainder_of_real_quadratures R hreal hR s (N+s)
    (l2RealPart (volume.restrict W) datum)
    (l2RealPart (volume.restrict W) (-Complex.I • datum))
    hre.1 him.1 hre.2 him.2
  dsimp only at hbound
  have he := congrArg (fun z ↦ complexNeumannInverse R hR ((R^(N+s)) z))
    (quadrature_decomposition datum)
  refine ⟨(congrArg (MemRestrictionSobolev W s) he).mp hbound.1, ?_⟩
  exact ((congrArg (restrictionSobolevNorm W s) he).symm.le.trans hbound.2).trans_eq
    (by simp only [mul_assoc])

/-- The actual norm derivative of the original admitted complex source,
after the SAME inverse and residual power, has the derived remainder
estimate. Joint smoothness and the derivative identity are proved from the
original compact physical source. This is the precise source-family input
to the parameter observation theorem; no derivative-admission estimate or
output Sobolev jet is assumed (`app:ch_regular:eq:inverse-remainder`). -/
theorem inverse_remainder_product_parameter_jet
    {W : Set E} (hW : MeasurableSet W)
    (R : LocalL2 W F →L[ℂ] LocalL2 W F)
    (hreal : conjugateOperator R.toLinearMap = R.toLinearMap) (hR : ‖R‖ < 1)
    {Cgain Dcoeff a : ℕ → ℝ} {b : ℕ} {θ : ℝ}
    (hKloc : ‖(realOutputCompression R)‖ ≤ θ) (hθ : θ < 1)
    (hCgain : ∀ j, 0 ≤ Cgain j) (hDcoeff : ∀ j, 0 ≤ Dcoeff j)
    (ha : ∀ j, 0 ≤ a j) (ham : Monotone a)
    (hgain : ∀ j u, MemRestrictionSobolev W j u →
      (MemRestrictionSobolev W (j + 1) ((realOutputCompression R) u) ∧
        restrictionSobolevNorm W (j + 1) ((realOutputCompression R) u) ≤ Cgain (j + 1) *
          (restrictionSobolevNorm W j u + (1 + a (j + 1 + b)) * ‖u‖)) ∧
      (MemRestrictionSobolev W (j + 1) ((realOutputCompression R).adjoint u) ∧
        restrictionSobolevNorm W (j + 1) ((realOutputCompression R).adjoint u) ≤ Cgain (j + 1) *
          (restrictionSobolevNorm W j u + (1 + a (j + 1 + b)) * ‖u‖)))
    {V : Set Par} {Ω X : Set E} (hV : IsOpen V) (hΩ : IsOpen Ω)
    (hX : IsCompact X) (hXΩ : X ⊆ Ω)
    (Hphase : ℕ → ℝ) (hHphase : ∀ m, 0 ≤ Hphase m)
    (Csource : ℕ → ℕ → ℝ)
    (k : ℕ) (ρ A K : ℝ) (hρ : 1 ≤ ρ) (hA : 0 ≤ A) (hK : 1 ≤ K)
    {φ : Par → E → ℝ} (hφ : ContDiffOn ℝ ∞ (Function.uncurry φ) (V ×ˢ Ω))
    {f : Par → E → F} (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (f c) ⊆ X) {c : Par} (hc : c ∈ V)
    (hm : ∀ vs : List Par,
      MemLp (fun x ↦ parameterListJet (fun a ↦ f a x) vs c) 2 volume)
    (hmem : ∀ vs (j : ℕ), MemVectorFourierSobolev (j : ℝ) ((hm vs).toLp _))
    (hprofile : ∀ vs, vs.length ≤ k → (∀ w ∈ vs, ‖w‖ ≤ 1) → ∀ j : ℕ,
      vectorFourierSobolevNorm (j : ℝ) ((hm vs).toLp _) ≤
        Csource vs.length j * (A * K ^ vs.length) * K ^ j)
    (v : Fin k → Par) (hv : ∀ i, ‖v i‖ ≤ 1)
    (hphase : ∀ x ∈ X, ∀ m,
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (c, x)‖ ≤ Hphase m * K ^ m)
    {χ : E → ℝ} {S : Set E} {gap upper L : ℝ} {Pphase Xcut : ℕ → ℝ}
    (g : SourceGeometry χ (φ c) S gap upper L Pphase Xcut) (hSW : S ⊆ W)
    (hcoeff : ∀ j, 1 + a (j + b) ≤ Dcoeff j * L ^ j) (hLK : L ≤ K)
    {ν : ℝ} (hν : 0 < ν) (hν1 : ν < 1) (hwindow : K ≤ ρ ^ (1 - ν))
    (hmphysical : ∀ c', MemLp (modulatedSource χ (φ c') (f c') ρ) 2 volume)
    (admitted : Par → LocalL2 W F)
    (hadmitted : ∀ c' ∈ V, admitted c' =
      restrictL2 W ((hmphysical c').toLp (modulatedSource χ (φ c') (f c') ρ)))
    (N s : ℕ) :
    let family := fun c' ↦ complexNeumannInverse R hR ((R ^ (N+s)) (admitted c'))
    let jet := iteratedFDeriv ℝ k family c v
    let CN := modulatedSourceNegativeConstant (d + 1) N S gap upper ν Pphase Xcut
      (fun j ↦ (2 : ℝ)^k * UniformPhase.unitSobolevBudget (d + 1) q X Hphase Csource k j)
    ContDiffOn ℝ ∞ family V ∧
      MemRestrictionSobolev W s jet ∧ restrictionSobolevNorm W s jet ≤
        (6 * (inverseTameConstant θ Cgain s * (powerGainConstant Cgain Dcoeff s + Dcoeff s) *
          ((localDualityConstant (d + 1) N (EuclideanSpace.basisFun (Fin q) ℝ) * CN) *
            powerGainConstant Cgain Dcoeff N))) *
          (A * ρ ^ k * K ^ (k + (d + 1) + 1)) * L ^ s * (L / ρ) ^ N := by
  intro family jet CN
  let physical := fun c' x ↦ modulatedSource χ (φ c') (f c') ρ x
  have hphysical : ContDiffOn ℝ ∞ (Function.uncurry physical) (V ×ˢ univ) :=
    (g.cutoff_smooth.comp_contDiffOn contDiffOn_snd).smul
      (contDiffOn_productParameterSourceFunction_localized
        hV hΩ hX.isClosed hXΩ ρ hφ hf hs)
  have hsphysical : ∀ c' ∈ V, tsupport (physical c') ⊆ X := by
    intro c' hc'
    exact (tsupport_smul_subset_right _ _).trans
      ((tsupport_smul_subset_right _ _).trans (hs c' hc'))
  refine ⟨contDiffOn_fixed_complex_inverse_product_source_of_eq R hR (N+s)
    hV hX physical hphysical hsphysical hmphysical admitted hadmitted, ?_⟩
  obtain ⟨hd, hb⟩ := inverse_remainder_actual_product_complex_source
    hW R hreal hR hKloc hθ hCgain hDcoeff ha ham hgain
    hV hΩ hX hXΩ Hphase hHphase Csource k ρ A K hρ hA hK hφ hf hs hc
    hm hmem hprofile v hv hphase g hSW hcoeff hLK hν hν1 hwindow N s
  have hjet := iteratedFDeriv_fixed_complex_inverse_product_source_of_eq R hR (N+s)
    hV hX physical hphysical hsphysical hmphysical admitted hadmitted k v hc
  change jet = _ at hjet
  rw [hjet]
  exact hb

end JanetCartan.FixedDomainInverse

