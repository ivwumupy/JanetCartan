module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets.AffinePullback
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Normalization

/-!
# Uniform phase seminorms for elapsed time

The phase in `app:ch_regular_base:eq:fixed-time-representation` is the sum
of a fixed quadratic time pairing, a bounded time translation, and a fixed
affine pullback of the original two-time phase. Its budget is therefore linear
in the original joint phase seminorm, uniformly for `r∈[0,Δ]`.
-/

@[expose] public noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
open FourierIntegral FullAmplitudePrimitiveBudget.Local
variable {d : ℕ}

/-- The fixed time pairing in the elapsed phase (`fixed-time-representation`). -/
def timePairing (p : Point (d + 1)) : ℝ := p.1.1 0 * p.2 0

/-- The time covector in the elapsed translation (`fixed-time-representation`). -/
def timeCovector (p : Point (d + 1)) : ℝ := p.2 0

private theorem contDiff_timeCovector : ContDiff ℝ ∞ (timeCovector (d := d)) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (d + 1)) 0).contDiff.comp contDiff_snd

private theorem contDiff_timePairing : ContDiff ℝ ∞ (timePairing (d := d)) :=
  ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin (d + 1)) 0).contDiff.comp
    (contDiff_fst.comp contDiff_fst)).mul contDiff_timeCovector

/-- The fixed time contribution to the phase budget. It depends on the
slab length and the fixed chart, but not on the original phase. -/
def phaseTimeConstant (K : Set (Point (d + 1))) (j : ℕ) (Δ : ℝ) : ℝ :=
  cNorm K j timePairing + Δ * cNorm K j timeCovector

/-- Nonnegativity of the fixed time contribution (`fixed-time-representation`). -/
theorem phaseTimeConstant_nonneg (K : Set (Point (d + 1))) (j : ℕ)
    {Δ : ℝ} (hΔ : 0 ≤ Δ) : 0 ≤ phaseTimeConstant K j Δ :=
  add_nonneg (cNorm_nonneg _ _ _) (mul_nonneg hΔ (cNorm_nonneg _ _ _))

/-- Uniform phase seminorm transfer with no derivative loss and with the
original phase occurring linearly. The lower time is exactly `t-r`.
Consumer: the phase high quantity of `app:ch_regular_base:eq:fio-input`. -/
theorem cNorm_elapsedPhase_le
    {K : Set (Point (d + 1))} {J U : Set (TwoTimePoint d)}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (Ψ : TwoTimePhase d) (hΨ : ContDiffOn ℝ ∞ (jointPhase Ψ) U)
    {Δ r : ℝ} (hr : r ∈ Icc 0 Δ) (hmap : MapsTo (elapsedPoint r) K J) (j : ℕ) :
    cNorm K j (fun p : Point (d + 1) ↦ elapsedPhase Ψ r p.1.1 p.2) ≤
      phaseTimeConstant K j Δ + cNorm J j (jointPhase Ψ) := by
  let T : Point (d + 1) → ℝ := timePairing + (-r) • timeCovector
  have hT : ContDiff ℝ ∞ T := contDiff_timePairing.add
    (contDiff_timeCovector.const_smul (-r))
  have hTbound : cNorm K j T ≤ phaseTimeConstant K j Δ := by
    apply (cNorm_add_le hK (contDiff_timePairing.of_le (by simp))
      ((contDiff_timeCovector.const_smul (-r)).of_le (by simp))).trans
    change cNorm K j timePairing + cNorm K j ((-r) • timeCovector) ≤ _
    rw [cNorm_smul (-r) (contDiff_timeCovector.of_le (by simp)), norm_neg,
      Real.norm_eq_abs, abs_of_nonneg hr.1]
    unfold phaseTimeConstant
    nlinarith [mul_le_mul_of_nonneg_right hr.2 (cNorm_nonneg K j timeCovector)]
  have helapsed : ContDiff ℝ ∞ (elapsedPoint (d := d) r) :=
    elapsedLinear.contDiff.add contDiff_const
  have hcomp : ∀ p ∈ K, ContDiffAt ℝ j (jointPhase Ψ ∘ elapsedPoint r) p := by
    intro p hp
    exact ((hΨ.contDiffAt (hU.mem_nhds (hJU (hmap hp)))).comp p
      helapsed.contDiffAt).of_le (by simp)
  have he : (fun p : Point (d + 1) ↦ elapsedPhase Ψ r p.1.1 p.2) =
      T + jointPhase Ψ ∘ elapsedPoint r := by
    funext p
    simp only [T, Pi.add_apply, Pi.smul_apply, smul_eq_mul, timePairing, timeCovector,
      Function.comp_apply, jointPhase, elapsedPoint_eq, elapsedPhase]
    ring
  rw [he]
  exact (cNorm_add_le_of_contDiffAt hK (fun _ _ ↦ hT.contDiffAt.of_le (by simp)) hcomp).trans
    (add_le_add hTbound (cNorm_comp_elapsedPoint_le hJ hU hJU hΨ r hmap j))

/-- Degree-one normalization of the original two-time phase, before the
elapsed substitution. Consumer: the phase reserve of the whole-image constructor. -/
def normalizedTwoTimePhase (R : ℝ) (Ψ : TwoTimePhase d) : TwoTimePhase d :=
  fun t s y η ↦ R⁻¹ * Ψ t s y (R • η)

/-- The degree-one normalized elapsed phase is literally the elapsed phase
of the normalized original phase. This identity does not assume homogeneity. -/
theorem normalizedPhase_elapsedPhase {R : ℝ} (hR : R ≠ 0)
    (Ψ : TwoTimePhase d) (r : ℝ) :
    WholeImageGeometry.normalizedPhase R (elapsedPhase Ψ r) =
      elapsedPhase (normalizedTwoTimePhase R Ψ) r := by
  funext x ξ
  simp only [WholeImageGeometry.normalizedPhase, elapsedPhase, spatialPart_smul,
    normalizedTwoTimePhase, PiLp.smul_apply, smul_eq_mul]
  field_simp

/-- Uniform actual normalized phase budget, at every radius and including
all joint time derivatives. It is a direct input to the whole-image phase
reserve, after the fixed chart's coordinate restriction. Source: the
fixed-time representation and `app:ch_regular_base:eq:actual-normal-amplitude`. -/
theorem cNorm_normalizedElapsedPhase_le
    {K : Set (Point (d + 1))} {J U : Set (TwoTimePoint d)}
    (hK : IsCompact K) (hJ : IsCompact J) (hU : IsOpen U) (hJU : J ⊆ U)
    (Ψ : TwoTimePhase d) {R : ℝ} (hR : R ≠ 0)
    (hΨ : ContDiffOn ℝ ∞ (jointPhase (normalizedTwoTimePhase R Ψ)) U)
    {Δ r : ℝ} (hr : r ∈ Icc 0 Δ) (hmap : MapsTo (elapsedPoint r) K J) (j : ℕ) :
    cNorm K j (fun p : Point (d + 1) ↦
      WholeImageGeometry.normalizedPhase R (elapsedPhase Ψ r) p.1.1 p.2) ≤
      phaseTimeConstant K j Δ + cNorm J j (jointPhase (normalizedTwoTimePhase R Ψ)) := by
  rw [normalizedPhase_elapsedPhase hR]
  exact cNorm_elapsedPhase_le hK hJ hU hJU _ hΨ hr hmap j

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.SymbolBudgets
