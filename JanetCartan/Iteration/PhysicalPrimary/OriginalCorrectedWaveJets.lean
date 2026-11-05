module

public import JanetCartan.Iteration.PhysicalPrimary.Envelope
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.CompletionAssembly.CorrectedPrimaryProfiles
public import JanetCartan.Iteration.PhysicalSampling.OriginalColoredRates
public import JanetCartan.Iteration.PhysicalPrimary.OriginalUncutSourceApplication
public import JanetCartan.Iteration.PhysicalPrimary.OriginalLocalWaves
public meta import JanetCartan.Iteration.PhysicalPrimary.OriginalCorrectedWaveJetsTemplate

/-!
# Sharp spatial jets of the unchanged corrected atom

The displacement envelope retains its original factor `τ`. This file freezes
only the physical/carrier parameter, restores the literal original phase, and
uses both radial comparisons to obtain `λ^(q-1)`, including the inverse carrier
at `q = 0`. It does not construct or recut a response. The quantitative
response producer is the actual stage13 reconstruction; the corrected
raw-plus-response displacement envelope remains an explicit instantiation
obligation.

The original-data commands below prove the radial comparisons and the actual
baseline/shifted comparison-region admissions, without new geometry inputs.
They do not yet supply the full fixed-K Picard family or its uniform mass.
Consumer: `exists_cutSampledPrimary_physical_profiles_on_original_sample`, then
`main:eq:primary-fixed-scales`. This file therefore does not assert completed
original full-wave or sampled Sobolev profiles.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalPrimary.OriginalCorrectedWaveJets

open CorrectedAtoms RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- The physical-jet cost precedes the history, rate and carrier parameter.
The phase cost includes the upper radial comparison; the outer scalar includes
the lower radial comparison (`main:eq:primary-fixed-scales`). -/
def sharpJetCost (Cτ Cfreq : ℝ) (a s : ℕ → ℝ) (q : ℕ) : ℝ :=
  Cτ * (2 : ℝ) ^ q * RawPrimary.atomJetConstant a (fun j ↦ Cfreq * s (j - 1)) q

/-- Positivity of the fixed sharp profile, without an order-zero exception. -/
theorem sharpJetCost_nonneg {Cτ Cfreq : ℝ} (hCτ : 0 ≤ Cτ) (hCfreq : 0 ≤ Cfreq)
    {a s : ℕ → ℝ} (ha : ∀ j, 0 ≤ a j) (hs : ∀ j, 0 ≤ s j) (q : ℕ) :
    0 ≤ sharpJetCost Cτ Cfreq a s q := by
  exact mul_nonneg (mul_nonneg hCτ (by positivity))
    (RawPrimary.atomJetConstant_nonneg (fun j _ ↦ ha j)
      (fun j _ _ ↦ mul_nonneg hCfreq (hs _)))

/-- Sharp physical jets of the literal corrected atom, from its joint
*displacement* envelope and the original unscaled phase. Only restrictions by
`x ↦ (x,param)` are used; no derivative reserve or dimension factor is lost.
The response is unchanged, and its quantitative reconstruction is not repeated
here (`app:ch_response:cor:current-atoms`, `main:eq:primary-fixed-scales`). -/
theorem corrected_atom_sharp_spatial_jets
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    {τ : ℝ} (hτ : 0 < τ)
    (hresponse : ContDiffOn ℝ ∞
      (fun w ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 w.1) Ω)
    {O : Set (Euclidean n)} (hO : IsOpen O)
    (param : Euclidean 3 × Euclidean (n - 1))
    (hOΩ : ∀ x ∈ O, (x, param) ∈ Ω)
    (a s : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : ∀ j, 0 ≤ s j)
    {lam L Cτ Cfreq : ℝ} (hlam : 1 ≤ lam) (hL : 0 ≤ L) (hLlam : L ≤ lam)
    (hCfreq : 0 ≤ Cfreq) (hfrequency : |τ⁻¹| ≤ Cfreq * lam)
    (hτlam : τ ≤ Cτ * lam⁻¹)
    (hdisplacement : ∀ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ j
        (fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ) (x, param)‖ ≤
          τ * a j * L ^ j)
    (hphaseJets : ∀ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ (j + 1) (fun y ↦ phase T Q y param.2) x‖ ≤ s j * L ^ j) :
    ContDiffOn ℝ ∞ (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r param) O ∧
      ∀ q, ∀ x ∈ O,
        ‖iteratedFDeriv ℝ q (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r param) x‖ ≤
          sharpJetCost Cτ Cfreq a s q * lam ^ ((q : ℝ) - 1) := by
  have hA := contDiffOn_fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ.ne' hresponse
  have hAslice : ContDiffOn ℝ ∞
      (fun x : Euclidean n ↦
        fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ (x, param)) O :=
    hA.comp (contDiffOn_id.prodMk contDiffOn_const) hOΩ
  have hphaseSlice : ContDiffOn ℝ ∞ (fun x : Euclidean n ↦ phase T Q x param.2) O :=
    (RawPrimary.contDiffOn_fullPhase T Q hphase).comp
      (contDiffOn_id.prodMk contDiffOn_const) hOΩ
  have hphysicalDisplacement : ∀ j, ∀ x ∈ O,
      ‖iteratedFDeriv ℝ j
        (fun y ↦ fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ (y, param)) x‖ ≤
          τ * a j * L ^ j := by
    intro j x hx
    exact (AmplitudeGrades.norm_iteratedFDeriv_physical_slice_le hΩ hA (hOΩ x hx) j).trans
      (hdisplacement j x hx)
  have hscaledPhase : ∀ j : ℕ, 1 ≤ j → ∀ x ∈ O,
      ‖iteratedFDeriv ℝ j (fun y ↦ phase T Q y param.2 / τ) x‖ ≤
        (Cfreq * s (j - 1)) * lam * L ^ (j - 1) := by
    intro j hj x hx
    have hgrade : ‖iteratedFDeriv ℝ j (fun y ↦ phase T Q y param.2) x‖ ≤
        s (j - 1) * L ^ (j - 1) := by
      cases j with
      | zero => omega
      | succ i => exact hphaseJets i x hx
    have he : (fun y ↦ phase T Q y param.2 / τ) =
        τ⁻¹ • (fun y ↦ phase T Q y param.2) := by
      ext y
      simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [he, iteratedFDeriv_const_smul_apply
      ((hphaseSlice.contDiffAt (hO.mem_nhds hx)).of_le (by simp)),
      norm_smul, Real.norm_eq_abs]
    calc
      _ ≤ (Cfreq * lam) * (s (j - 1) * L ^ (j - 1)) :=
        mul_le_mul hfrequency hgrade (norm_nonneg _)
          (mul_nonneg hCfreq (zero_le_one.trans hlam))
      _ = _ := by ring
  have hmod : Set.EqOn
      (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r param)
      (fun x ↦ Complex.exp (Complex.I * (phase T Q x param.2 / τ : ℝ)) •
        fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ (x, param)) O := by
    intro x hx
    exact fullCorrectedPrimaryAtom_eq_modulated T Q F row col Φ Y χ B r
      hΩ hspace hphase hF hi hα hnonzero hτ.ne' (w := (x, param)) (hOΩ x hx)
  exact physical_jets_le_inverse_carrier hO
    (fullCorrectedPrimaryAtom T Q F row col Φ Y χ B τ r param)
    (fun x ↦ phase T Q x param.2 / τ)
    (fun x ↦ fullCorrectedDisplacementAmplitude T Q F row col Φ Y χ B r τ (x, param))
    (hphaseSlice.div_const τ) hAslice hmod
    a (fun j ↦ Cfreq * s (j - 1)) ha (fun j ↦ mul_nonneg hCfreq (hs _))
    hτ.le hlam hL hLlam hτlam hphysicalDisplacement hscaledPhase

/-- One explicit upper cost of a finite radial menu. It does not choose new
radial labels and is independent of all histories and frequencies. -/
def finiteRadialCost {ι : Type*} [Finite ι] (radial : ι → ℝ) : ℝ := by
  letI := Fintype.ofFinite ι
  exact 1 + ∑ i, radial i

/-- The same finite radial labels have one nonnegative prehistory upper cost. -/
theorem finiteRadialCost_bounds {ι : Type*} [Finite ι] {radial : ι → ℝ}
    (hr : ∀ i, 1 ≤ radial i) :
    1 ≤ finiteRadialCost radial ∧ ∀ i, radial i ≤ finiteRadialCost radial := by
  classical
  let _ := Fintype.ofFinite ι
  have hs : 0 ≤ ∑ i, radial i := Finset.sum_nonneg fun i _ ↦ zero_le_one.trans (hr i)
  refine ⟨by dsimp only [finiteRadialCost]; linarith, fun i ↦ ?_⟩
  have hi : radial i ≤ ∑ j, radial j :=
    Finset.single_le_sum (fun j _ ↦ zero_le_one.trans (hr j)) (Finset.mem_univ i)
  dsimp only [finiteRadialCost]
  linarith

/-- Both sharp remodulation comparisons hold for the SAME genuine original
rate `(radial*λ)⁻¹`. In particular the lower comparison gives constant one,
and the history coefficient scale fits λ itself, not just the larger radial
frequency (`main:eq:primary-fixed-scales`). -/
theorem radial_rate_bounds {Rinit radial Cfreq : ℝ}
    (hR : 1 ≤ Rinit) (hradial : 1 ≤ radial) (hupper : radial ≤ Cfreq) (stage : ℕ) :
    let lam := historyScale Rinit growthExponent stage ^ carrierExponent
    let rate := (radial * lam)⁻¹
    1 ≤ lam ∧ 0 < rate ∧ rate ≤ lam⁻¹ ∧ |rate⁻¹| ≤ Cfreq * lam ∧
      currentCoefficientScale Rinit stage ≤ lam := by
  intro lam rate
  have hT : 1 ≤ historyScale Rinit growthExponent stage :=
    hR.trans (le_historyScale hR stage)
  have hlam : 1 ≤ lam := Real.one_le_rpow hT (by norm_num [carrierExponent])
  have hlamp : 0 < lam := zero_lt_one.trans_le hlam
  have hrp : 0 < radial := zero_lt_one.trans_le hradial
  have hr : lam ≤ radial * lam := le_mul_of_one_le_left hlamp.le hradial
  refine ⟨hlam, inv_pos.mpr (mul_pos hrp hlamp), ?_, ?_, ?_⟩
  · simpa only [one_div, rate] using one_div_le_one_div_of_le hlamp hr
  · dsimp only [rate]
    rw [inv_inv, abs_of_nonneg (mul_nonneg hrp.le hlamp.le)]
    exact mul_le_mul_of_nonneg_right hupper hlamp.le
  · exact Real.rpow_le_rpow_of_exponent_le hT
      (show coefficientExponent ≤ carrierExponent by
        norm_num [coefficientExponent, carrierExponent])

end JanetCartan.PhysicalPrimary.OriginalCorrectedWaveJets
end

construct_original_sharp_radial_comparisons
retain_original_sharp_cutoff_interior
retain_original_sharp_active_comparison_region
retain_original_sharp_shifted_comparison_region
