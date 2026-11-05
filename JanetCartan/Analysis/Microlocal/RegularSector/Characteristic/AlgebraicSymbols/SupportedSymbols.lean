module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.AlgebraicSymbols.PrimitiveInverse
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization
public import JanetCartan.Analysis.Microlocal.NormalComparison.InverseBounds.TransportExtension.PairedCoordinates

/-!
# Both physical masks on the actual algebraic residual symbols

These smoothness and support proofs retain physical frequency `2πξ`, the
original source and output masks, all derivatives of the entire algebraic
symbol, and the zeroth-order coefficient. The quantitative derivative budgets
remain a separate obligation. Consumers: `GraphNormalAmplitudeBounds` for
`directPDOSymbols` indices zero and three in
`app:ch_regular_base:eq:energy-complete-residual` of `paper-v2.tex`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
open ResidualCoordinates PdoRealization EvolutionIntegral
open JanetCartan.CharacteristicTransport.CompleteResidual
open AmplitudeBound NormalComparison
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "P" => Euclidean (2 * (d + 1))
local notation "CMat" => Matrix (Fin q) (Fin q) ℂ

/-- Global smoothness of the masked symbol in the exact cycle/paired-position
coordinates consumed by the existing PDO calculus. Physical frequency is
`2πξ`, and both masks remain in the amplitude.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_maskedPhysicalPDOCycleSymbol
    {χout χsource : E → ℂ} (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    {c : E → E → CMat} (hc : ContDiff ℝ ∞ (Function.uncurry c)) :
    ContDiff ℝ ∞ (Function.uncurry (maskedPhysicalPDOCycleSymbol χout χsource c)) := by
  have hx := (normalLeftPosition (d + 1)).contDiff.comp
    (show ContDiff ℝ ∞ (Prod.snd : E × P → P) from contDiff_snd)
  have hy := (normalRightPosition (d + 1)).contDiff.comp
    (show ContDiff ℝ ∞ (Prod.snd : E × P → P) from contDiff_snd)
  have hη : ContDiff ℝ ∞ (fun p : E × P ↦ (2 * Real.pi) • p.1) :=
    (contDiff_const (c := (2 * Real.pi : ℝ))).smul contDiff_fst
  exact ((ho.comp hx).mul (hs.comp hy)).smul (hc.comp (hx.prodMk hη))

/-- The full physical derivative is smooth in physical position and frequency.
The symbol is differentiated as a whole; the sum contains every first-order
coefficient and retains the zeroth-order `B` term.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem contDiff_physicalSymbolApply
    {A : E → Fin (d + 1) → CMat} {B : E → CMat} {c : E → E → CMat}
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B)
    (hc : ContDiff ℝ ∞ (Function.uncurry c)) :
    ContDiff ℝ ∞ (Function.uncurry (physicalSymbolApply A B c)) := by
  have hd : ContDiff ℝ ∞ (fun p : E × E ↦ fderiv ℝ (fun y ↦ c y p.2) p.1) := by
    have hh := contDiffOn_parameterFDeriv (U := univ) (V := univ)
      isOpen_univ isOpen_univ hc.contDiffOn
    exact contDiffOn_univ.mp (by simpa using hh)
  apply ContDiff.add
  · apply ContDiff.sum
    intro a _
    have hAa : ContDiff ℝ ∞ (fun p : E × E ↦ A p.1 a) :=
      ((ContinuousLinearMap.proj a : (Fin (d + 1) → CMat) →L[ℝ] CMat).contDiff.comp hA).comp
        contDiff_fst
    exact hAa.mul (hd.clm_apply contDiff_const)
  · exact (hB.comp contDiff_fst).mul hc

/-- A supported symbol only requires smooth coefficients near its closed
physical carrier. Outside the carrier its full physical action has zero
germs, including the `B` term. This supplies the global supported extension
for the original local coefficients in `energy-complete-residual`. -/
theorem contDiff_physicalSymbolApply_on_carrier
    {A : E → Fin (d + 1) → CMat} {B : E → CMat} {c : E → E → CMat}
    {K U : Set E} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U)
    (hc : ContDiff ℝ ∞ (Function.uncurry c))
    (hsupport : ∀ x, x ∉ K → ∀ η, c x η = 0) :
    ContDiff ℝ ∞ (Function.uncurry (physicalSymbolApply A B c)) := by
  have hd : ContDiff ℝ ∞ (fun p : E × E ↦ fderiv ℝ (fun y ↦ c y p.2) p.1) := by
    have hh := contDiffOn_parameterFDeriv (U := univ) (V := univ)
      isOpen_univ isOpen_univ hc.contDiffOn
    exact contDiffOn_univ.mp (by simpa using hh)
  have hzero (x : E) (hx : x ∉ K) (η : E) : physicalSymbolApply A B c x η = 0 := by
    have he : (fun y ↦ c y η) =ᶠ[𝓝 x] (fun _ ↦ 0) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
      exact hsupport y hy η
    have hf : fderiv ℝ (fun y ↦ c y η) x = 0 := by
      simpa using he.fderiv_eq (𝕜 := ℝ)
    simp [physicalSymbolApply, partialDeriv, hf, hsupport x hx η]
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hp : p.1 ∈ K
  · have hAp := (hA.contDiffAt (hU.mem_nhds (hKU hp))).comp p contDiffAt_fst
    have hBp := (hB.contDiffAt (hU.mem_nhds (hKU hp))).comp p contDiffAt_fst
    apply ContDiffAt.add
    · apply ContDiffAt.sum
      intro a _
      have ha := (ContinuousLinearMap.proj a : (Fin (d + 1) → CMat) →L[ℝ] CMat).contDiff (n := ∞)
      exact (ha.contDiffAt.comp p hAp).mul (hd.contDiffAt.clm_apply contDiffAt_const)
    · exact hBp.mul hc.contDiffAt
  · apply (contDiffAt_const (c := (0 : CMat))).congr_of_eventuallyEq
    have hn := (continuous_fst : Continuous (Prod.fst : E × E → E)).continuousAt.preimage_mem_nhds
      (hK.isOpen_compl.mem_nhds hp)
    filter_upwards [hn] with w hw
    exact hzero w.1 hw w.2

/-- Fixed masks give one paired-position support box for ANY literal symbol,
including its full physical derivative. No frequency cutoff or symbol value
is used to enlarge the box. Consumer: `GraphNormalAmplitudeBounds.support`.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem maskedPhysicalPDOCycleSymbol_supported
    {χout χsource : E → ℂ} {R : ℝ}
    (ho : SupportedInCenteredBox R χout) (hs : SupportedInCenteredBox R χsource)
    (c : E → E → CMat) :
    ∀ ξ i j, SupportedInCenteredBox R
      (fun z ↦ maskedPhysicalPDOCycleSymbol χout χsource c ξ z i j) := by
  intro ξ i j z hz k
  have hoz : χout (normalLeftPosition (d + 1) z) ≠ 0 := by
    intro h
    apply hz
    change ((χout (normalLeftPosition (d + 1) z) *
      χsource (normalRightPosition (d + 1) z)) •
      c (normalLeftPosition (d + 1) z) ((2 * Real.pi) • ξ)) i j = 0
    simp [h]
  have hsz : χsource (normalRightPosition (d + 1) z) ≠ 0 := by
    intro h
    apply hz
    change ((χout (normalLeftPosition (d + 1) z) *
      χsource (normalRightPosition (d + 1) z)) •
      c (normalLeftPosition (d + 1) z) ((2 * Real.pi) • ξ)) i j = 0
    simp [h]
  by_cases hk : k.val < d + 1
  · exact ho _ hoz ⟨k.val, hk⟩
  · have hj : k.val - (d + 1) < d + 1 := by omega
    have he : d + 1 + (k.val - (d + 1)) = k.val := by omega
    have hrow := hs _ hsz ⟨k.val - (d + 1), hj⟩
    change |z ⟨d + 1 + (k.val - (d + 1)), by omega⟩| ≤ R at hrow
    simpa only [he] using hrow

/-- Compact physical masks determine the support radius before any coefficient
field or symbol is chosen. Both PDOs share this fixed radius.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem exists_common_maskedPhysicalPDOCycleSymbol_support
    {χout χsource : E → ℂ} (ho : HasCompactSupport χout) (hs : HasCompactSupport χsource) :
    ∃ R > 0, ∀ c : E → E → CMat, ∀ ξ i j,
      SupportedInCenteredBox R (fun z ↦ maskedPhysicalPDOCycleSymbol χout χsource c ξ z i j) := by
  obtain ⟨Ro, hRo⟩ := ho.isBounded.exists_norm_le
  obtain ⟨Rs, hRs⟩ := hs.isBounded.exists_norm_le
  let R := 1 + max 0 Ro + max 0 Rs
  have hR : 0 < R := by dsimp [R]; positivity
  refine ⟨R, hR, ?_⟩
  apply maskedPhysicalPDOCycleSymbol_supported
  · intro x hx a
    exact (PiLp.norm_apply_le x a).trans ((hRo x (subset_tsupport χout hx)).trans
      (by dsimp [R]; linarith [le_max_right 0 Ro, le_max_left 0 Rs]))
  · intro x hx a
    exact (PiLp.norm_apply_le x a).trans ((hRs x (subset_tsupport χsource hx)).trans
      (by dsimp [R]; linarith [le_max_right 0 Rs, le_max_left 0 Ro]))

/-- Both actual supported algebraic symbols have global joint smoothness and
ONE fixed paired-position box. The source is exactly `conicSourceSymbol` and
the inverse is exactly `conicBminus`; the third residual is the full
`physicalSymbolApply`, with all cutoff derivatives and `B` retained.

The parent supplies the same-root open chart and geometric product containment;
`exists_conicBminus_fieldRoot_weighted_cNorm_bounds` constructs the off-root
interval from which this containment must be proved. This result alone does
not assert derivative bounds or an operator estimate.
Source: `app:ch_regular_base:eq:energy-complete-residual`. -/
theorem conicAlgebraicSymbols_smooth_supported
    (ℓ : Euclidean d →L[ℝ] ℝ) (i : Fin (d + 1))
    {Ω : Set E} {Q : E → Fin (d + 1) → MetricTensor (d + 1)} (hQ : ContDiffOn ℝ ∞ Q Ω)
    {D : Set (RootState (Euclidean d))} (hD : IsOpen D)
    {h : RootState (Euclidean d) → ℝ} (hh : ContDiffOn ℝ ∞ h D)
    (hmap : ∀ w ∈ D, (coordinateSplit i).symm (w.1, w.2.1) ∈ Ω)
    (r c : Fin (d + 1)) {X F : Set E}
    (hXF : X ×ˢ F ⊆ complementDomain i Q h r c D)
    (ρ : Euclidean d → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : tsupport ρ ⊆ {η | 0 < ℓ η})
    (σ : RootState (Euclidean d) → ℝ) (hσ : ContDiff ℝ ∞ σ)
    (hsσ : ∀ w ∈ tsupport σ, EvolutionIntegral.KernelIdentification.timeSpacePoint w.1 w.2.1 ∈ X)
    (β : E → ℂ) (hβ : ContDiff ℝ ∞ β)
    (hsβ : ∀ ξ ∈ tsupport β, normalizeCovector ℓ ξ ∈ F)
    (χout χsource : E → ℂ) (ho : ContDiff ℝ ∞ χout) (hs : ContDiff ℝ ∞ χsource)
    (hco : HasCompactSupport χout) (hcs : HasCompactSupport χsource)
    (A : E → Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (B : E → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (hA : ContDiff ℝ ∞ A) (hB : ContDiff ℝ ∞ B) :
    let b := directAlgebraicSymbol (conicBminus ℓ i Q h r c) (conicSourceSymbol ℓ ρ σ) β
    ∃ R > 0,
      ContDiff ℝ ∞ (Function.uncurry (maskedPhysicalPDOCycleSymbol χout χsource b)) ∧
      ContDiff ℝ ∞ (Function.uncurry
        (maskedPhysicalPDOCycleSymbol χout χsource (physicalSymbolApply A B b))) ∧
      (∀ ξ j k, SupportedInCenteredBox R
        (fun z ↦ maskedPhysicalPDOCycleSymbol χout χsource b ξ z j k)) ∧
      (∀ ξ j k, SupportedInCenteredBox R
        (fun z ↦ maskedPhysicalPDOCycleSymbol χout χsource (physicalSymbolApply A B b) ξ z j k)) := by
  intro b
  have hb := contDiff_conicAlgebraicSymbol ℓ i hQ hD hh hmap r c hXF
    ρ hρ hsρ σ hσ hsσ β hβ hsβ
  obtain ⟨R, hR, hsupport⟩ := exists_common_maskedPhysicalPDOCycleSymbol_support
    (q := d + 1) hco hcs
  exact ⟨R, hR, contDiff_maskedPhysicalPDOCycleSymbol ho hs hb,
    contDiff_maskedPhysicalPDOCycleSymbol ho hs (contDiff_physicalSymbolApply hA hB hb),
    hsupport b, hsupport (physicalSymbolApply A B b)⟩

end JanetCartan.RegularSector.Characteristic.AlgebraicSymbols
