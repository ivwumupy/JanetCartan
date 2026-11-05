module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.SourceParameterCoordinates.Sobolev
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.Remainder
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.InverseRemainder

/-!
# The same inverse remainder in the original product parameters

The normalized carrier jet is constructed from the ORIGINAL phase and source
profiles. Its explicit Sobolev budget supplies the negative-source estimate
for the same real inverse. In particular, no negative norm estimate for a
source derivative is assumed. The physical derivative retains the original
cutoff and both real quadratures.

Consumers: differentiated finite Neumann expansion in
`app:ch_response:eq:response-graded-reduced` and the ordered joint response
jets in `app:ch_response:cor:current-atoms`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential ArbitraryAccuracy
open ResponseTransfer ResponseTransfer.SourceNegative ResponseTransfer.Complement
open ResponseTransfer.Complement.ParameterDerivatives
open RegularSector.Characteristic.RetardedLocalization

variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "Par" => Euclidean 3 × Euclidean d
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "FR" => EuclideanSpace ℝ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- Actual source-parameter derivatives commute with the SAME inverse and
residual powers. The representative premise is the original admission
identity on the open parameter set, supplied by
`RetainedCharacteristicEnvelopes.fullPrimary_originalGeometry_admitted_response_words`.
The compact-family theorem proves norm differentiability from joint smoothness;
no derivative identity or derivative-admission bound is assumed.
Consumer: the differentiated finite Neumann remainder
(`app:ch_regular:eq:finite-neumann-identity`). -/
theorem iteratedFDeriv_fixed_inverse_product_source_of_eq
    {W : Set E}
    (Kloc : LocalL2 W FR →L[ℝ] LocalL2 W FR) (depth : ℕ)
    {V : Set Par} (hV : IsOpen V) {X : Set E} (hX : IsCompact X)
    (g : Par → E → F)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (V ×ˢ univ))
    (hs : ∀ c ∈ V, tsupport (g c) ⊆ X)
    (hm : ∀ c, MemLp (g c) 2 volume)
    (admitted : Par → LocalL2 W FR) (ζ : ℂ)
    (hadmitted : ∀ c ∈ V, admitted c =
      l2RealPart (volume.restrict W) (ζ • restrictL2 W ((hm c).toLp (g c))))
    (k : ℕ) (v : Fin k → Par) {c : Par} (hc : c ∈ V) :
    iteratedFDeriv ℝ k
        (fun c' ↦ neumannInverse Kloc ((Kloc ^ depth) (admitted c'))) c v =
      neumannInverse Kloc ((Kloc ^ depth)
        (l2RealPart (volume.restrict W) (ζ • restrictL2 W
          ((ResponseTransfer.FullSourceEnvelopes.fullSource_parameterJet_memLp hX hV hg hs k v hc).toLp
            (fun x ↦ iteratedFDeriv ℝ k (fun c' ↦ g c' x) c v))))) := by
  let source := fun c' ↦ (hm c').toLp (g c')
  let quadrature : H →L[ℝ] LocalL2 W FR :=
    (l2RealPart (volume.restrict W)).comp
      (((ζ • ContinuousLinearMap.id ℂ (LocalL2 W F)).restrictScalars ℝ).comp (restrictL2 W))
  let T : H →L[ℝ] LocalL2 W FR :=
    (neumannInverse Kloc).comp ((Kloc ^ depth).comp quadrature)
  have he : (fun c' ↦ neumannInverse Kloc ((Kloc ^ depth) (admitted c'))) =ᶠ[nhds c]
      T ∘ source := by
    filter_upwards [hV.mem_nhds hc] with c' hc'
    change neumannInverse Kloc ((Kloc ^ depth) (admitted c')) =
      neumannInverse Kloc ((Kloc ^ depth)
        (l2RealPart (volume.restrict W) (ζ • restrictL2 W ((hm c').toLp (g c')))))
    rw [hadmitted c' hc']
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  have hdiff := T.iteratedFDeriv_comp_left
    (((contDiffOn_productParameterSourceClass hX hV hg hs hm).contDiffAt
      (hV.mem_nhds hc)).of_le (by simp)) (le_refl (k : ℕ∞ω))
  have hid := iteratedFDeriv_productParameterSourceClass hX hV hg hs hm k v hc
  exact (congrArg (fun m ↦ m v) hdiff).trans (congrArg T hid)

/-- The explicit uniform carrier-jet budget is an actual Sobolev envelope.
It uses the original source derivatives through order `j + (d+1) + 1`,
and parameter orders at most `k`. The polynomial factor
`ρ^k K^(k+(d+1)+1)` is independent of the spatial order and later accuracy.
This is the input to `inverse_remainder_modulatedSource_real_quadrature`,
with the original real inverse unchanged
(`app:ch_regular:eq:inverse-remainder`). -/
theorem productParameterCarrierJet_sobolevEnvelope_of_original_profiles
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
      ‖iteratedFDeriv ℝ m (Function.uncurry φ) (c, x)‖ ≤ Hphase m * K ^ m) :
    SobolevEnvelopeBounds (productParameterCarrierJet ρ φ f k v c)
      (memLp_productParameterCarrierJet_of_original hV hΩ hX hXΩ ρ hφ hf hs k v hc)
      (A * ρ ^ k * K ^ (k + (d + 1) + 1)) K
      (fun j ↦ (2 : ℝ)^k * UniformPhase.unitSobolevBudget (d + 1) q X Hphase Csource k j) := by
  let jet := productParameterCarrierJet ρ φ f k v c
  let hjm := memLp_productParameterCarrierJet_of_original hV hΩ hX hXΩ ρ hφ hf hs k v hc
  have hregular (j : ℕ) : MemVectorFourierSobolev (j : ℝ) (hjm.toLp jet) :=
    memVectorFourierSobolev_productParameterCarrierJet_of_original hV hΩ hX hXΩ
      ρ hφ hf hs k v hc j
  refine ⟨contDiff_productParameterCarrierJet_of_original hV hΩ hX hXΩ ρ hφ hf hs k v hc,
    by positivity, hK, (fun j ↦ mul_nonneg (by positivity)
      (UniformPhase.unitSobolevBudget_nonneg X hHphase Csource k j)),
    fun j ↦ InactiveSource.memLp_weighted_vectorFourier _ _ (hregular j), ?_⟩
  intro j
  rw [InactiveSource.eLpNorm_weighted_vectorFourier _ _ (hregular j)]
  exact norm_productParameterCarrierJet_sobolev_le_unit
    hV hΩ hX hXΩ Hphase hHphase Csource k ρ A K hρ hA hK hφ hf hs hc
    hm hmem hprofile v hv j (fun x hx m _ ↦ hphase x hx m)

/-- Derive the actual differentiated-admission remainder from primitive
phase/source profiles and the normalized inverse's original gain estimates.
The source is the literal derivative of `χ exp(iρφ) f`, not the derivative
of its envelope alone. Taking `ζ = 1` and `ζ = -I` gives the two original
real admissions. The coefficient shift `b`, inverse, and power `N+s` remain
unchanged; only the explicit fixed polynomial source-jet cost is displayed.
The final finite Neumann observation absorbs that cost by increasing depth
(`app:ch_regular:eq:inverse-remainder`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem inverse_remainder_actual_product_source_quadrature
    {W : Set E} (hW : MeasurableSet W)
    (Kloc : LocalL2 W FR →L[ℝ] LocalL2 W FR)
    {Cgain Dcoeff a : ℕ → ℝ} {b : ℕ} {θ : ℝ}
    (hKloc : ‖Kloc‖ ≤ θ) (hθ : θ < 1)
    (hCgain : ∀ j, 0 ≤ Cgain j) (hDcoeff : ∀ j, 0 ≤ Dcoeff j)
    (ha : ∀ j, 0 ≤ a j) (ham : Monotone a)
    (hgain : ∀ j u, MemRestrictionSobolev W j u →
      (MemRestrictionSobolev W (j + 1) (Kloc u) ∧
        restrictionSobolevNorm W (j + 1) (Kloc u) ≤ Cgain (j + 1) *
          (restrictionSobolevNorm W j u + (1 + a (j + 1 + b)) * ‖u‖)) ∧
      (MemRestrictionSobolev W (j + 1) (Kloc.adjoint u) ∧
        restrictionSobolevNorm W (j + 1) (Kloc.adjoint u) ≤ Cgain (j + 1) *
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
    (N s : ℕ) (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    let derivative := fun x ↦ iteratedFDeriv ℝ k
      (fun c' ↦ modulatedSource χ (φ c') (f c') ρ x) c v
    ∃ hd : MemLp derivative 2 volume,
      let datum := l2RealPart (volume.restrict W) (ζ • restrictL2 W (hd.toLp derivative))
      let CN := modulatedSourceNegativeConstant (d + 1) N S gap upper ν Pphase Xcut
        (fun j ↦ (2 : ℝ)^k * UniformPhase.unitSobolevBudget (d + 1) q X Hphase Csource k j)
      MemRestrictionSobolev W s (neumannInverse Kloc ((Kloc ^ (N + s)) datum)) ∧
      restrictionSobolevNorm W s (neumannInverse Kloc ((Kloc ^ (N + s)) datum)) ≤
        (inverseTameConstant θ Cgain s * (powerGainConstant Cgain Dcoeff s + Dcoeff s) *
          ((localDualityConstant (d + 1) N (EuclideanSpace.basisFun (Fin q) ℝ) * CN) *
            powerGainConstant Cgain Dcoeff N)) *
          (A * ρ ^ k * K ^ (k + (d + 1) + 1)) * L ^ s * (L / ρ) ^ N := by
  intro derivative
  let jet := productParameterCarrierJet ρ φ f k v c
  let hjm := memLp_productParameterCarrierJet_of_original hV hΩ hX hXΩ ρ hφ hf hs k v hc
  have henv := productParameterCarrierJet_sobolevEnvelope_of_original_profiles
    hV hΩ hX hXΩ Hphase hHphase Csource k ρ A K hρ hA hK hφ hf hs hc
    hm hmem hprofile v hv hphase
  have hphysical := contDiffOn_productParameterSourceFunction_localized
    hV hΩ hX.isClosed hXΩ ρ hφ hf hs
  have hsame (x : E) : modulatedSource χ (φ c) jet ρ x = derivative x := by
    have hcsource : ContDiffAt ℝ ∞ (fun c' ↦ (carrier ρ (φ c') x • f c' x)) c :=
      (hphysical.contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hc, mem_univ x⟩)).comp c
        (contDiffAt_id.prodMk contDiffAt_const)
    change χ x • (carrier ρ (φ c) x • productParameterCarrierJet ρ φ f k v c x) =
      iteratedFDeriv ℝ k ((χ x) • fun c' ↦ (carrier ρ (φ c') x • f c' x)) c v
    rw [carrier_mul_productParameterCarrierJet,
      iteratedFDeriv_const_smul_apply (hcsource.of_le (by simp))]
    rfl
  let hd : MemLp derivative 2 volume :=
    (source_memLp g hjm ρ).ae_eq (Filter.Eventually.of_forall hsame)
  refine ⟨hd, ?_⟩
  have hlp : (source_memLp g hjm ρ).toLp (modulatedSource χ (φ c) jet ρ) =
      hd.toLp derivative := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall hsame
  have hbound := inverse_remainder_modulatedSource_real_quadrature hW Kloc hKloc hθ
    hCgain hDcoeff ha ham hgain g hSW hcoeff henv hLK hρ hν hν1 hwindow N s ζ hζ
  dsimp only at hbound ⊢
  rw [hlp] at hbound
  exact hbound

end JanetCartan.FixedDomainInverse
