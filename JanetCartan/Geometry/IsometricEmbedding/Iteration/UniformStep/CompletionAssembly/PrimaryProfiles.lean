module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.PhysicalBounds.GradedAtoms
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.PhysicalCompletion.CutProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.PrimaryProfiles
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.UniformStep.SampleBudgets
public import JanetCartan.Analysis.Operator.RealQuadratures.RealPart

/-!
# Primary profiles from the original displacement envelopes

The same-response displacement envelopes of `CorrectedAtoms.JointProfiles`
and the original phase grades imply physical atom jets by the existing graded
oscillation theorem.  The canonical source integral transfers those jets using
its original Fourier-variation budget.  The final jets below are then cut,
realified, periodized and synthesized at the literal original mesh.

The consumers are `StageConstants.ComponentEstimates.primarySobolev` and
`primaryL2`.  All profile constants precede the stage frequency, fields and
sample shifts.  No primary-size estimate, alternative primitive field, or
new successful-stage hypothesis is introduced.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff

namespace JanetCartan.UniformStep

variable {n N : ℕ}

/-- Remodulate the original corrected displacement amplitude with its SAME
phase.  The amplitude and phase jets are the outputs of
`CorrectedAtoms.fullCorrectedDisplacementAmplitude_joint_bounds` and the
original history phase profiles; `fullCorrectedPrimaryAtom_eq_modulated`
supplies `hmod`.  The result is the physical atom-jet input of the canonical
Fourier integral (`app:ch_response:cor:current-atoms`,
`main:eq:joint-physical-profile`). -/
theorem primary_physical_jets_of_displacement_envelope
    {U : Set (Euclidean n)} (hU : IsOpen U)
    (Z : Euclidean n → EuclideanSpace ℂ (Fin N))
    (φ : Euclidean n → ℝ) (A : Euclidean n → EuclideanSpace ℂ (Fin N))
    (hφ : ContDiffOn ℝ ∞ φ U) (hA : ContDiffOn ℝ ∞ A U)
    (hmod : EqOn Z (fun x ↦ Complex.exp (Complex.I * (φ x : ℂ)) • A x) U)
    (a s : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : ∀ j, 0 ≤ s j)
    {lam L : ℝ} (hlam : 1 ≤ lam) (hL : 0 ≤ L) (hLlam : L ≤ lam)
    (hAj : ∀ j, ∀ x ∈ U, ‖iteratedFDeriv ℝ j A x‖ ≤ a j * L ^ j)
    (hφj : ∀ j, 1 ≤ j → ∀ x ∈ U,
      ‖iteratedFDeriv ℝ j φ x‖ ≤ s j * lam * L ^ (j - 1)) :
    ContDiffOn ℝ ∞ Z U ∧ ∀ q, ∀ x ∈ U,
      ‖iteratedFDeriv ℝ q Z x‖ ≤
        ((2 : ℝ) ^ q * RawPrimary.atomJetConstant a s q) * lam ^ q := by
  have hprod : ContDiffOn ℝ ∞
      (fun x ↦ Complex.exp (Complex.I * (φ x : ℂ)) • A x) U :=
    (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hφ)).cexp.smul hA
  refine ⟨hprod.congr hmod, ?_⟩
  intro q x hx
  have he : Z =ᶠ[nhds x] (fun y ↦ Complex.exp (Complex.I * (φ y : ℂ)) • A y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hmod hy
  rw [(he.iteratedFDeriv ℝ q).self_of_nhds]
  have hc : 0 ≤ RawPrimary.atomJetConstant a s q :=
    RawPrimary.atomJetConstant_nonneg (fun j _ ↦ ha j) (fun j _ _ ↦ hs j)
  have hb := RawPrimary.norm_iteratedFDeriv_oscillatoryAtom_le (m := q) hU
    (hφ.of_le (by simp)) (hA.of_le (by simp)) (zero_le_one.trans hlam) hL
    (fun j _ ↦ ha j) (fun j _ _ ↦ hs j) hx
    (fun j _ ↦ hAj j x hx) (fun j hj _ ↦ hφj j hj x hx)
  calc
    _ ≤ RawPrimary.atomJetConstant a s q * (lam + L) ^ q := hb
    _ ≤ RawPrimary.atomJetConstant a s q * (2 * lam) ^ q :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (add_nonneg (zero_le_one.trans hlam) hL) (by linarith) q) hc
    _ = _ := by rw [mul_pow]; ring

/-- The original physical cutoff turns the final canonical atom's physical
jets into the exact real periodic Sobolev profiles needed by the primary
synthesis.  The jet producer is the same-source canonical integral with its
original total Fourier variation.  Cutoff and norm-conversion constants are
fixed before frequency or atom selection (`main:eq:joint-physical-profile`). -/
theorem exists_primary_atom_cut_sobolev_of_physical_jets
    (D : LocalDomain) (Cphys : ℕ → ℝ) (hCphys : ∀ q, 0 ≤ Cphys q) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ lam : ℝ, 1 ≤ lam →
      ∀ Z : Euclidean n → EuclideanSpace ℂ (Fin N),
      ContDiffOn ℝ ∞ Z (D.chart n) →
      (∀ q, ∀ x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut,
        ‖iteratedFDeriv ℝ q Z x‖ ≤ Cphys q * lam ^ q) →
      ∀ q : ℕ, periodicSobolevNorm q
        (Periodization.cutToTorus (physicalCutoff D) (euclideanRealPart ∘ Z)) ≤
          C q * lam ^ (q : ℝ) := by
  have hcut : (physicalCutoff (n := n) D).rOut < D.chartRadius := by
    dsimp only [physicalCutoff]
    linarith [D.coreRadius_lt_chartRadius]
  obtain ⟨Ccut, hCcut, hcutProfile⟩ := CurrentMean.exists_cutToTorus_local_profile_bound
    (N := N) hcut (hcut.trans D.chartRadius_lt_half) (physicalCutoff (n := n) D)
    (physicalCutoff D).contDiff
    (physicalCutoff (n := n) D).tsupport_eq.le
  let total (q : ℕ) := ∑ j ∈ Finset.range (q + 1), Cphys j
  have htotal (q : ℕ) : 0 ≤ total q := Finset.sum_nonneg (fun j _ ↦ hCphys j)
  refine ⟨fun q ↦ Ccut q * total q, fun q ↦ mul_nonneg (hCcut q) (htotal q), ?_⟩
  intro lam hlam Z hZ hjet q
  have hreal : ContDiffOn ℝ ∞ (euclideanRealPart ∘ Z) (D.chart n) :=
    euclideanRealPart.contDiff.comp_contDiffOn hZ
  have hnorm : cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut)
      q (euclideanRealPart ∘ Z) ≤ total q * lam ^ q := by
    have hjets : ∀ j ≤ q,
        ∀ x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut,
        ‖iteratedFDeriv ℝ j (euclideanRealPart ∘ Z) x‖ ≤ Cphys j * lam ^ q := by
      intro j hj x hx
      have hxD : x ∈ D.chart n := closedBall_subset_ball hcut hx
      have hp := euclideanRealPart.norm_iteratedFDeriv_comp_left
        (hZ.contDiffAt (isOpen_ball.mem_nhds hxD)) (by simp : (j : ℕ∞ω) ≤ ∞)
      have hrealJet : ‖iteratedFDeriv ℝ j (euclideanRealPart ∘ Z) x‖ ≤
          ‖iteratedFDeriv ℝ j Z x‖ :=
        hp.trans ((mul_le_mul_of_nonneg_right euclideanRealPart_norm_le (norm_nonneg _)).trans_eq
          (one_mul _))
      exact hrealJet.trans ((hjet j x hx).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hlam hj) (hCphys j)))
    simpa only [total, Finset.sum_mul] using cNorm_le_sum_of_bounds
      (C := fun j ↦ Cphys j * lam ^ q)
      (fun j _ ↦ mul_nonneg (hCphys j) (pow_nonneg (zero_le_one.trans hlam) q)) hjets
  have hprofile := (hcutProfile (euclideanRealPart ∘ Z) hreal).2 q
  have hs : periodicSobolevNorm q
      (Periodization.cutToTorus (physicalCutoff D) (euclideanRealPart ∘ Z)) ≤
        Ccut q * cNorm (closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut)
          q (euclideanRealPart ∘ Z) :=
    (le_add_of_nonneg_left (cNorm_nonneg _ _ _)).trans hprofile
  exact hs.trans ((mul_le_mul_of_nonneg_left hnorm (hCcut q)).trans_eq
    (by rw [Real.rpow_natCast]; ring))

open SeparatedSampling CanonicalRowComparison

/-- Apply the actual original sample count and mass to the final canonical
physical jets.  This proves both primary Sobolev and L² stage profiles, with
one constant family chosen before histories and shifts
(`main:eq:joint-physical-profile`, `main:eq:step-L2`).  The canonical integral
producer still has to supply the displayed physical jets for its own final
atoms; no synthesized primary norm is assumed. -/
theorem exists_originalMesh_primary_profiles {G : Type*} [Fintype G]
    (D : LocalDomain) (p : ℕ) {B W : ℝ} (hB : 0 ≤ B) {P : G → ℝ}
    {weights : G → Point → ℝ} {w : ℝ → ℝ}
    (hw : WindowBounds p w W) (hweights : ∀ a, PatchBounds (weights a) B (P a))
    (Cphys : ℕ → ℝ) (hCphys : ∀ q, 0 ≤ Cphys q) :
    ∃ C : ℕ → ℝ, (∀ q, 0 ≤ C q) ∧
      ∀ R : ℝ, 1 ≤ R → ∀ δ : ℝ, 0 ≤ δ →
      ∀ shifts : G → Lattice → Point,
      ∀ Z : SampleIndex p B weights w (R ^ (-separationExponent)) shifts →
          Euclidean n → EuclideanSpace ℂ (Fin N),
      (∀ i, ContDiffOn ℝ ∞ (Z i) (D.chart n)) →
      (∀ i q, ∀ x ∈ closedBall (0 : Euclidean n) (physicalCutoff (n := n) D).rOut,
        ‖iteratedFDeriv ℝ q (Z i) x‖ ≤ Cphys q * (R ^ carrierExponent) ^ q) →
      let μ := sampleWeight (p := p) B weights w (R ^ (-separationExponent)) shifts
      let primary := Periodization.cutToTorus (physicalCutoff D)
        (sampledPrimary (δ * R ^ forcingExponent n) μ Z)
      (∀ q : ℕ, periodicSobolevNorm q primary ≤
        C q * δ * R ^ displacementLoss n * (R ^ carrierExponent) ^ (q : ℝ)) ∧
      periodicL2Norm primary ≤ C 0 * δ * R ^ displacementLoss n := by
  obtain ⟨Catom, hCatom, hatom⟩ := exists_primary_atom_cut_sobolev_of_physical_jets
    (N := N) D Cphys hCphys
  let Ccount := (Fintype.card G : ℝ) * countConstant p B
  let Cmass := countConstant p B * ((∑ a, P a) * W ^ 3)
  let C := fun q ↦ Real.sqrt 2 * Catom q * Real.sqrt (Ccount * Cmass)
  refine ⟨C, fun q ↦ mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hCatom q))
    (Real.sqrt_nonneg _), ?_⟩
  intro R hR δ hδ shifts Z hZ hjet
  obtain ⟨hCcount, hCmass, hμ, hcount, hmass, _, _⟩ :=
    sampled_weight_budgets_originalScale p hB hw hweights hR shifts
  have hlam : 1 ≤ R ^ carrierExponent := Real.one_le_rpow hR (by norm_num [carrierExponent])
  have hprofile (i) (q : ℕ) := hatom (R ^ carrierExponent) hlam (Z i) (hZ i) (hjet i) q
  constructor
  · intro q
    exact cut_sampled_primary_sobolev_le_of_contDiffOn D _ hμ hZ q hR hδ (hCatom q)
      hCcount hCmass hcount hmass (fun i ↦ hprofile i q)
  · exact cut_sampled_primary_l2_le_of_contDiffOn D _ hμ hZ hR hδ (hCatom 0)
      hCcount hCmass hcount hmass (fun i ↦ by
        simpa only [Nat.cast_zero, Real.rpow_zero, mul_one] using hprofile i 0)

end JanetCartan.UniformStep
