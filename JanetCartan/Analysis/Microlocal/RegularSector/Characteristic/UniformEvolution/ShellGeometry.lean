module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.UniformEvolution.Geometry

/-!
# Fixed collared frequency domain and whole-image shell compacts

Use the section of `UniformAmplitudes.ConicConstruction` without selecting a
new one. Two angular margins and a temporal aperture give the inner frequency
domain; the positive spatial collar removes its vertex. The actual compact
sets from `ConicPhase.Assembly` then supply every normalized-source-band and
elapsed-image inclusion, and the finite phase-time constant.

Consumer: `hDDcore`, `hcollar`, `hshell`, `hmapK`, and `htime` in the signed
retarded primitive theorem (`app:ch_regular_base:lem:retarded-kernel`). The
right multiplier must still be placed in this domain by its finite-mask
construction; that support inclusion is not presumed here.
-/

@[expose] public noncomputable section
open Set Metric
open scoped ContDiff
namespace JanetCartan.RegularSector.Characteristic.UniformEvolution
open ConicPhase FourierIntegral EvolutionIntegral WholeImageGeometry
variable {d : ℕ}
local notation "Z" => RootState (Euclidean d)
local notation "E" => Euclidean (d + 1)

/-- Buffered spacetime cone with the required positive spatial collar, on the
retained section (`app:ch_regular_base:lem:retarded-kernel`). -/
def retainedFrequencyDomain (ℓ : Euclidean d →L[ℝ] ℝ) (z : Z) (ε T c : ℝ) : Set E :=
  fullAngularCone ℓ z.2.2 (ε / 4) (T / 2) ∩ {ξ | c < ‖spatialPart ξ‖}

/-- The actual collared domain is open (`retarded-kernel`). -/
theorem isOpen_retainedFrequencyDomain (ℓ : Euclidean d →L[ℝ] ℝ)
    (z : Z) (ε T c : ℝ) : IsOpen (retainedFrequencyDomain ℓ z ε T c) :=
  (isOpen_fullAngularCone _ _ _ _).inter
    (isOpen_lt continuous_const spatialPartCLM.continuous.norm)

/-- The closure lies in the inner spatial cone, which itself has a margin in
the larger smoothness cone. This closes the vertex issue for `hDDcore`. -/
theorem closure_retainedFrequencyDomain_subset (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : Z} {ε T c : ℝ} (hε : 0 < ε) (hT : 0 < T) (hc : 0 < c) :
    closure (retainedFrequencyDomain ℓ z ε T c) ⊆
      spatialPart ⁻¹' angularCone ℓ z.2.2 (ε / 2) := by
  have h := closure_fullAngularCone_collar_subset ℓ (η₀ := z.2.2)
    (half_pos hε) hT hc
  intro ξ hξ
  exact (h (by simpa only [retainedFrequencyDomain, div_div,
    show (2 : ℝ) * 2 = 4 by norm_num] using hξ)).1

/-- The spatial collar supplies the full-frequency lower bound required by
the primitive theorem, without replacing spatial order by an assumption. -/
theorem retainedFrequencyDomain_norm_lt (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : Z} {ε T c : ℝ} {ξ : E}
    (hξ : ξ ∈ retainedFrequencyDomain ℓ z ε T c) : c < ‖ξ‖ :=
  hξ.2.trans_le (SymbolBudgets.norm_spatialPart_le ξ)

/-- All normalized shells can use the single larger full cone. Both aperture
and angular comparisons are fixed before the chart (`retarded-kernel`). -/
theorem retainedFrequencyDomain_subset_fullAngularCone
    (ℓ : Euclidean d →L[ℝ] ℝ) {z : Z} {ε T c : ℝ}
    (hε : 0 < ε) (hT : 0 ≤ T) :
    retainedFrequencyDomain ℓ z ε T c ⊆ fullAngularCone ℓ z.2.2 ε T := by
  intro ξ hξ
  refine ⟨⟨hξ.1.1.1, ball_subset_ball (by linarith) hξ.1.1.2⟩, ?_⟩
  exact hξ.1.2.trans_le (mul_le_mul_of_nonneg_right (by linarith) hξ.1.1.1.le)

/-- Explicit compact sets contain every dyadic normalized source band of the
actual collared domain. Every elapsed image lies in the corresponding joint
jet set, and the time cost is finite and nonnegative. This discharges those
geometric inputs for any supplied annulus, without a phase or operator bound
(`app:ch_regular_base:eq:fixed-time-representation`). -/
theorem retained_shell_compacts (ℓ : Euclidean d →L[ℝ] ℝ)
    {z : Z} {ε T c a b : ℝ} (hε : 0 < ε) (hT : 0 ≤ T) (ha : 0 < a) (n : ℕ) :
    let ra := a / (1 + T + ‖z.2.2‖ + ε)
    let rb := (1 + ‖ℓ‖) * b
    let K := elapsedJetSet ℓ z ε ra rb b
    0 < ra ∧ IsCompact K ∧
      0 ≤ SymbolBudgets.phaseTimeConstant K n ε ∧
      (∀ j : ℕ, ∀ p ∈ elapsedPhysicalBox z (ε / 2) ×ˢ
        normalizedSourceBand (retainedFrequencyDomain ℓ z ε T c) ((2 : ℝ)^j) a b,
        SymbolBudgets.phasePairInclusion p ∈ K) ∧
      (∀ r ∈ Icc 0 ε, MapsTo (SymbolBudgets.elapsedPoint r) K
        (bufferedJetSet ℓ z ε ra rb)) := by
  dsimp only
  refine ⟨div_pos ha (by positivity), isCompact_elapsedJetSet _ _ _ _ _ _,
    SymbolBudgets.phaseTimeConstant_nonneg _ _ hε.le, ?_, ?_⟩
  · intro j p hp
    apply normalizedSourceBand_mem_elapsedJetSet ℓ hε.le hT ha (by positivity : 0 < (2 : ℝ)^j)
    refine ⟨⟨ball_subset_ball (by linarith) hp.1.1,
      ball_subset_ball (by linarith) hp.1.2⟩, ?_, hp.2.2⟩
    exact retainedFrequencyDomain_subset_fullAngularCone ℓ hε hT hp.2.1
  · intro r hr
    exact elapsedJetSet_mapsTo ℓ hr

end JanetCartan.RegularSector.Characteristic.UniformEvolution
