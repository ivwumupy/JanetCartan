module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.MeasuredAmplitudeProfiles
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.EvolutionIntegratedLocalization.CompactKernels

/-!
# Measured elapsed-amplitude profiles and supports

The original measurement pair preserves the primitive comparable grades and
shrinks the existing elapsed carrier in both literal orientations. These are
the measured inputs to the supported-collar integral leakage deduction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open FourierIntegral FiniteChain.Graph FiniteChain.Graph.KernelEstimates
open FiniteChain.Retarded.KernelDecay EvolutionLocalization.PrimitiveGrades
open RegularSector.Characteristic.EvolutionIntegral EvolutionIntegratedLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => JointVariables E

/-- The original real measurement pair multiplies the complete elapsed amplitude
in both literal orientations (`app:ch_regular_base:eq:measured-adjoint`). -/
theorem measured_orientedElapsedAmplitude_eq
    (μ ν : E → ℝ) (e : E ≃ₗᵢ[ℝ] E) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (backward : Bool) (r : ℝ) (x y ξ : E) :
    orientedElapsedAmplitude backward b
        (fun z ↦ (μ (e z) : ℂ)*χout z) (fun z ↦ (ν (e z) : ℂ)*χsource z) β r x y ξ =
      ((μ (e x) : ℂ)*(ν (e y) : ℂ)) •
        orientedElapsedAmplitude backward b χout χsource β r x y ξ := by
  cases backward
  · simp only [orientedElapsedAmplitude, Bool.false_eq_true, ite_false, elapsedAmplitude, smul_smul]
    congr 1
    ring
  · simp only [orientedElapsedAmplitude, ite_true, elapsedAmplitude, Matrix.conjTranspose_smul,
      map_mul, Complex.star_def, Complex.conj_ofReal, smul_smul]
    congr 1
    ring

/-- Multiplying by the original measurement masks retains the same comparable
carrier, orders, graph cutoffs and proof localizers. The profile is chosen
before charts, coefficients, elapsed time and scales. Consumer: the measured
`hglobalGrades` input of the supported integral leakage theorem
(`app:ch_regular:eq:high-amplitude`, `app:ch_regular:eq:chain-tail`). -/
theorem exists_measured_elapsed_comparable_profiles
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (D : AmplitudeProfiles) :
    ∃ Dm : AmplitudeProfiles,
      Dm.symbolOffset = D.symbolOffset ∧ Dm.graphCutoffOffset = D.graphCutoffOffset ∧
      Dm.outputCutoffOffset = D.outputCutoffOffset ∧ Dm.inputMaskOffset = D.inputMaskOffset ∧
      Dm.outputMaskOffset = D.outputMaskOffset ∧ Dm.offset = D.offset ∧
    ∀ (e : E ≃ₗᵢ[ℝ] E) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
      (backward : Bool) (r ρ S L : ℝ), 1 ≤ L →
    ∀ (mi mo : LocalizerSymbol (d+1)) (χA χo : E → ℝ) (x y : E) (K : Set V),
      HasAmplitudeGrades D ρ S L
        (orientedElapsedAmplitude backward b χout χsource β r) mi mo χA χo x y K →
      HasAmplitudeGrades Dm ρ S L
        (orientedElapsedAmplitude backward b
          (fun z ↦ (μ (e z) : ℂ)*χout z) (fun z ↦ (ν (e z) : ℂ)*χsource z) β r)
        mi mo χA χo x y K := by
  obtain ⟨C, hC, hprofile⟩ := exists_measurement_pair_joint_profile μ ν hμ hν hμc hνc
  let Dm : AmplitudeProfiles := { D with
    symbol := derivativeConvolution C D.symbol
    symbol_nonneg := derivativeConvolution_nonneg hC D.symbol_nonneg }
  refine ⟨Dm, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro e b χout χsource β backward r ρ S L hL mi mo χA χo x y K hg
  have hpair : ContDiff ℝ ∞ (fun z : V ↦ (μ (e z.1.1) : ℂ)*(ν (e z.1.2) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp (hμ.comp (e.contDiff.comp contDiff_fst.fst))).mul
      (Complex.ofRealCLM.contDiff.comp (hν.comp (e.contDiff.comp contDiff_fst.snd)))
  refine { hg with symbol_smooth := ?_, symbol_bound := ?_ }
  · convert hpair.smul hg.symbol_smooth using 1
    funext p
    exact measured_orientedElapsedAmplitude_eq μ ν e b χout χsource β backward r _ _ _
  · intro k p hp
    have hm j : ‖iteratedFDeriv ℝ j
        (fun w : V ↦ (μ (e w.1.1) : ℂ)*(ν (e w.1.2) : ℂ)) p‖ ≤ C j * L ^ (j+0) :=
      ((hprofile e).2.1 j p).trans (le_mul_of_one_le_right (hC j) (one_le_pow₀ hL))
    have hh := norm_iteratedFDeriv_smul_le_amplitude_grades hpair hg.symbol_smooth
      hC (zero_le_one.trans hL) 0 D.symbolOffset p hm (fun j ↦ hg.symbol_bound j p hp) k
    simpa only [measured_orientedElapsedAmplitude_eq, zero_add, Dm] using hh

/-- Measurement only shrinks the full graph-amplitude support, so the original
comparable carrier still controls both orientations
(`app:ch_regular:eq:joint-kernel-phase`, `app:ch_regular:eq:chain-tail`). -/
theorem measured_elapsed_jointAmplitude_tsupport_subset
    (μ ν : E → ℝ) (e : E ≃ₗᵢ[ℝ] E) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (backward : Bool) (r ρ : ℝ)
    (mi mo : LocalizerSymbol (d+1)) (χA χo : E → ℝ) (x y : E) :
    tsupport (jointAmplitude ρ (orientedElapsedAmplitude backward b
      (fun z ↦ (μ (e z) : ℂ)*χout z) (fun z ↦ (ν (e z) : ℂ)*χsource z) β r)
        mi mo χA χo x y) ⊆
    tsupport (jointAmplitude ρ (orientedElapsedAmplitude backward b χout χsource β r)
      mi mo χA χo x y) := by
  have he : jointAmplitude ρ (orientedElapsedAmplitude backward b
      (fun z ↦ (μ (e z) : ℂ)*χout z) (fun z ↦ (ν (e z) : ℂ)*χsource z) β r)
        mi mo χA χo x y = fun p : V ↦
      ((μ (e p.1.1) : ℂ)*(ν (e p.1.2) : ℂ)) •
        jointAmplitude ρ (orientedElapsedAmplitude backward b χout χsource β r)
          mi mo χA χo x y p := by
    funext p
    simp only [jointAmplitude, measured_orientedElapsedAmplitude_eq, smul_smul]
    congr 1
    ring
  rw [he]
  exact tsupport_smul_subset_right _ _

/-- The same elapsed support and upper cutoff survive measurement; the two
measurement masks remain inside the literal forward/adjoint amplitudes.
Consumer: the supported-collar integral estimate
(`app:ch_regular_base:eq:fixed-time-representation`, `app:ch_regular:eq:chain-tail`). -/
theorem measured_jointElapsedAmplitude_tsupport_subset
    (μ ν : E → ℝ) (e : E ≃ₗᵢ[ℝ] E) (b : TwoTimeAmplitude d q)
    (χout χsource β : E → ℂ) (backward : Bool) (ρ : ℝ)
    (mi mo : LocalizerSymbol (d+1)) (χA χo : E → ℝ) (x y : E) (θ : ℝ → ℂ) :
    tsupport (fun p : ℝ × V ↦ θ p.1 • jointElapsedAmplitude backward ρ b
      (fun z ↦ (μ (e z) : ℂ)*χout z) (fun z ↦ (ν (e z) : ℂ)*χsource z) β
        mi mo χA χo x y p) ⊆
    tsupport (fun p : ℝ × V ↦ θ p.1 • jointElapsedAmplitude backward ρ b
      χout χsource β mi mo χA χo x y p) := by
  have he : (fun p : ℝ × V ↦ θ p.1 • jointElapsedAmplitude backward ρ b
      (fun z ↦ (μ (e z) : ℂ)*χout z) (fun z ↦ (ν (e z) : ℂ)*χsource z) β
        mi mo χA χo x y p) = fun p : ℝ × V ↦
      ((μ (e p.2.1.1) : ℂ)*(ν (e p.2.1.2) : ℂ)) •
        (θ p.1 • jointElapsedAmplitude backward ρ b χout χsource β mi mo χA χo x y p) := by
    funext p
    simp only [jointElapsedAmplitude, jointAmplitude, measured_orientedElapsedAmplitude_eq, smul_smul]
    congr 1
    ring
  rw [he]
  exact tsupport_smul_subset_right _ _

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
