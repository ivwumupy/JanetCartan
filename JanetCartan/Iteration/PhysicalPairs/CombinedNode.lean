module
public import JanetCartan.Geometry.IsometricEmbedding.Mean.Current.WholeSourceSampledAmplitude
/-! # Demodulated jets of the unchanged baseline-plus-angular wave

The original zero-safe angular coefficient is a real scalar, constant in the
physical variable. Differentiating the literal sum therefore introduces no
new phase or cutoff. Consumer: the source-data specialization of the native
whole-node estimate in `OriginalSelectedWaves.GenuineNodeProfile`.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option warningAsError true
open Set
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.PhysicalPairs.CombinedNode
open UniformStep
variable {n N : ℕ}
local notation "E" => Euclidean n
local notation "H" => EuclideanSpace ℂ (Fin N)
local notation "M" => Matrix (Fin N) (Fin n) ℂ

/-- Exact exponential convention used by the native corrected-parent identity;
this does not differentiate or change the original carrier phase. -/
theorem amplitude_eq_exp (Z : E → H) (θ : E → ℝ) (x : E) :
    sampledDerivativeAmplitude (fun _ : Unit ↦ Z) (fun _ ↦ θ) () x =
      Complex.exp (-Complex.I * (θ x : ℂ)) • sampledDerivative (fun _ : Unit ↦ Z) () x := by
  unfold sampledDerivativeAmplitude
  congr 1
  unfold wavePhase
  congr 1
  push_cast
  ring

/-- Demodulation distributes over the original baseline and the whole angular
field with the same carrier phase (`main:eq:primary`). -/
theorem amplitude_add_smul (Z W : E → H) (θ : E → ℝ) (b : ℝ) (x : E)
    (hZ : DifferentiableAt ℝ Z x) (hW : DifferentiableAt ℝ W x) :
    sampledDerivativeAmplitude (fun _ : Unit ↦ Z + b • W) (fun _ ↦ θ) () x =
      sampledDerivativeAmplitude (fun _ : Unit ↦ Z) (fun _ ↦ θ) () x +
        b • sampledDerivativeAmplitude (fun _ : Unit ↦ W) (fun _ ↦ θ) () x := by
  have hd : sampledDerivative (fun _ : Unit ↦ Z + b • W) () x =
      sampledDerivative (fun _ : Unit ↦ Z) () x +
        b • sampledDerivative (fun _ : Unit ↦ W) () x := by
    change RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N
      (fderiv ℝ (Z + b • W) x) = _
    rw [fderiv_add hZ (hW.const_smul b), fderiv_const_smul hW, map_add, map_smul]
    rfl
  unfold sampledDerivativeAmplitude
  rw [hd, smul_add]
  congr 1
  exact smul_comm _ _ _

/-- The same identity on the original open source chart, usable for every
ordinary spatial derivative rather than a within derivative at its boundary. -/
theorem amplitude_add_smul_eqOn (Z W : E → H) (θ : E → ℝ) (b : ℝ)
    {U : Set E} (hU : IsOpen U) (hZ : ContDiffOn ℝ ∞ Z U)
    (hW : ContDiffOn ℝ ∞ W U) :
    EqOn (sampledDerivativeAmplitude (fun _ : Unit ↦ Z + b • W) (fun _ ↦ θ) ())
      (sampledDerivativeAmplitude (fun _ : Unit ↦ Z) (fun _ ↦ θ) () +
        b • sampledDerivativeAmplitude (fun _ : Unit ↦ W) (fun _ ↦ θ) ()) U := by
  intro x hx
  exact amplitude_add_smul Z W θ b x
    ((hZ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))
    ((hW.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))

/-- The identical scalar factor in `[0,1]` costs no extra angular variation in
any demodulated jet; no frequency or sample-cardinality estimate is used. -/
theorem jet_add_smul_le {A B : E → M} {x : E} {q : ℕ} {b C D : ℝ}
    (hb : 0 ≤ b ∧ b ≤ 1) (hA : ContDiffAt ℝ q A x) (hB : ContDiffAt ℝ q B x)
    (hC : ‖iteratedFDeriv ℝ q A x‖ ≤ C) (hD : ‖iteratedFDeriv ℝ q B x‖ ≤ D) :
    ‖iteratedFDeriv ℝ q (A + b • B) x‖ ≤ C + D := by
  change ‖iteratedFDeriv ℝ q (A + fun y ↦ b • B y) x‖ ≤ C + D
  rw [iteratedFDeriv_add_apply hA (hB.const_smul b), iteratedFDeriv_const_smul_apply' hB]
  calc
    _ ≤ ‖iteratedFDeriv ℝ q A x‖ + ‖b • iteratedFDeriv ℝ q B x‖ := norm_add_le _ _
    _ ≤ C + D := add_le_add hC (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact (mul_le_mul_of_nonneg_right hb.2 (norm_nonneg _)).trans (by simpa using hD))

/-- The unchanged zero-safe full angular factor needs no angular field
regularity outside its support. On its support, use only the same-phase
parent/whole amplitudes and their already-produced estimates. -/
theorem amplitude_jet_add_smul_le (Z W : E → H) (θ : E → ℝ) {b C D : ℝ}
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x ∈ U) {q : ℕ}
    (hb : 0 ≤ b ∧ b ≤ 1) (hD0 : 0 ≤ D)
    (hZ : ContDiffOn ℝ ∞ Z U) (hW : b ≠ 0 → ContDiffOn ℝ ∞ W U)
    (hA : ContDiffAt ℝ q (sampledDerivativeAmplitude (fun _ : Unit ↦ Z) (fun _ ↦ θ) ()) x)
    (hB : b ≠ 0 → ContDiffAt ℝ q
      (sampledDerivativeAmplitude (fun _ : Unit ↦ W) (fun _ ↦ θ) ()) x)
    (hC : ‖iteratedFDeriv ℝ q (sampledDerivativeAmplitude (fun _ : Unit ↦ Z)
      (fun _ ↦ θ) ()) x‖ ≤ C)
    (hD : b ≠ 0 → ‖iteratedFDeriv ℝ q (sampledDerivativeAmplitude
      (fun _ : Unit ↦ W) (fun _ ↦ θ) ()) x‖ ≤ D) :
    ‖iteratedFDeriv ℝ q (sampledDerivativeAmplitude
      (fun _ : Unit ↦ Z + b • W) (fun _ ↦ θ) ()) x‖ ≤ C + D := by
  by_cases hz : b = 0
  · simp only [hz, zero_smul, add_zero]
    exact hC.trans (le_add_of_nonneg_right hD0)
  · have he := amplitude_add_smul_eqOn Z W θ b hU hZ (hW hz)
    have he' : sampledDerivativeAmplitude (fun _ : Unit ↦ Z + b • W) (fun _ ↦ θ) ()
        =ᶠ[nhds x] sampledDerivativeAmplitude (fun _ : Unit ↦ Z) (fun _ ↦ θ) () +
          b • sampledDerivativeAmplitude (fun _ : Unit ↦ W) (fun _ ↦ θ) () :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨U,hU.mem_nhds hx,he⟩
    rw [(he'.iteratedFDeriv ℝ q).eq_of_nhds]
    exact jet_add_smul_le hb hA (hB hz) hC (hD hz)

end JanetCartan.PhysicalPairs.CombinedNode
end
