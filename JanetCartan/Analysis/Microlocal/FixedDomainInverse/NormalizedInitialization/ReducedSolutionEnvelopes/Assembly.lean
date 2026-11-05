module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.Observation
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ReducedSolutionEnvelopes.Remainder
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Inverse

/-!
# The complex reduced inverse envelope from the original real remainders

This closes the observation and remainder part of
`app:ch_response:eq:response-graded-reduced`. The actual normalized inverse
supplies the real contraction, its uncorrected solver supplies the integer
Fourier estimate, and the retained coefficient and primary phase profiles
supply all polynomial costs. The original two real remainder estimates give
the complex remainder on the same Neumann series.

The remaining finite-word input is explicit: every full normalized residual
power, on the combined original recut source, must have its demodulated
envelope. The characteristic, reflected, and full elliptic word producers
must instantiate this input on the same operators. This conditional deduction
does not assert construction of those finite-word envelopes or a tame
one-high estimate for arbitrary scalar data.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set
open scoped ContDiff ENNReal NNReal JanetCartan.RegularSector.Realization

namespace JanetCartan.FixedDomainInverse

open LocalSobolev Pseudodifferential ResponseTransfer ResponseTransfer.Complement
open SmallSupport RegularSector RegularSector.Realization

variable {n r : ℕ} {ι : Type*}
local notation "E" => Euclidean n
local notation "RF" => EuclideanSpace ℝ (Fin r)
local notation "CF" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp CF 2 (volume : Measure E)

local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- Restriction of the scalar field preserves each literal residual power.
This identifies the complex powers used by the actual source estimates
with the real-linear finite Neumann assembly, without changing the source
(`app:ch_regular:eq:finite-neumann-identity`). -/
theorem complex_operator_power_restrictScalars_apply
    {U : Set E} (T : LocalL2 U CF →L[ℂ] LocalL2 U CF) (j : ℕ) (u : LocalL2 U CF) :
    ((T.restrictScalars ℝ)^j) u = (T^j) u := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ', pow_succ']
    change T (((T.restrictScalars ℝ)^j) u) = T ((T^j) u)
    exact congrArg T ih

/-- The actual real inverse remainders and primitive profiles supply the
complete smoothing-observation input of the inverse-envelope theorem.
`sources i false/true` are the original `χ₂`-recut admitted quadratures,
fixed before the proof depth; `χ₃` is the SAME inverse plateau bump.
The one-high coefficient term is kept through the observation calculation,
and the real remainder orders are unchanged. The only envelope premise is
the independent finite-word estimate on the very same complex source and
operators (`app:ch_regular:eq:inverse-remainder`,
`app:ch_response:eq:response-graded-reduced`). -/
theorem reduced_solution_envelope_of_normalized_real_remainders
    (U : Set E) (hU : MeasurableSet U) {x : E} (χ₃ : ContDiffBump x)
    (hχ₃ : tsupport (χ₃ : E → ℝ) ⊆ U)
    (R : ι → LocalL2 U CF →L[ℂ] LocalL2 U CF)
    (hreal : ∀ i, conjugateOperator (R i).toLinearMap = (R i).toLinearMap)
    {κ : ℝ} (hκ : κ < 1) (hR : ∀ i, ‖realOutputCompression (R i)‖ ≤ κ)
    (S : ι → H →L[ℂ] H)
    (sources : ι → Bool → LocalL2 U RF)
    (ρ L K A : ι → ℝ) {ν : ℝ}
    (hρ : ∀ i, 1 ≤ ρ i) (hL : ∀ i, 1 ≤ L i) (hLK : ∀ i, L i ≤ K i)
    (hν : 0 < ν) (hν₁ : ν < 1) (hwindow : ∀ i, K i ≤ (ρ i) ^ (1-ν))
    (hA : ∀ i, 0 ≤ A i)
    (φ : ι → E → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hcφ : ∀ i, HasCompactSupport (φ i))
    (P Csolver Ccoefficient : ℕ → ℝ)
    (hP : ∀ j, 0 ≤ P j) (hCsolver : ∀ s, 0 ≤ Csolver s)
    (hCcoefficient : ∀ s, 0 ≤ Ccoefficient s)
    (hphase : ∀ i j, 1 ≤ j → ∀ y,
      ‖iteratedFDeriv ℝ j (φ i) y‖ ≤ P j * L i ^ j)
    (high : ι → ℕ → ℝ) (hhigh : ∀ i s, 0 ≤ high i s)
    (hcoefficient : ∀ i s, 1 + high i s ≤ Ccoefficient s * L i ^ s)
    (hsolver : ∀ i (s : ℕ) (z : H), MemVectorFourierSobolev (s : ℝ) z →
      MemVectorFourierSobolev (s : ℝ) (S i z) ∧
        vectorFourierSobolevNorm (s : ℝ) (S i z) ≤
          Csolver s * (vectorFourierSobolevNorm (s : ℝ) z + high i s * ‖z‖))
    (CP : ℕ → ℕ → ℝ) (hCP : ∀ s N, 0 ≤ CP s N)
    (hpower : ∀ i N s b,
      let Kr := realOutputCompression (R i)
      let v := neumannInverse Kr ((Kr^(N+s)) (sources i b))
      MemRestrictionSobolev U s v ∧ restrictionSobolevNorm U s v ≤
        CP s N * A i * L i ^ s * (L i / ρ i)^N) :
    let source := fun i ↦ l2ComplexInclusion (volume.restrict U) (sources i false) +
      Complex.I • l2ComplexInclusion (volume.restrict U) (sources i true)
    let observe : ι → LocalL2 U CF →ₗ[ℝ] H := fun i ↦
      (((carrierMultiplication (-(ρ i)) (φ i) (hφ i).continuous).restrictScalars ℝ).comp
        (((S i).restrictScalars ℝ).comp
          (((zeroExtend (F := CF) (p := 2) hU).toContinuousLinearMap).comp
            (bumpL2 (p := 2) le_rfl χ₃ : LocalL2 U CF →L[ℝ] LocalL2 U CF)))).toLinearMap
    (∀ j, HasEnvelopeProfile vectorFourierSobolevScale
      (fun i ↦ observe i (((R i)^j) (source i))) A K) →
    ∃ hcomplex : ∀ i, ‖R i‖ < 1,
      HasEnvelopeProfile vectorFourierSobolevScale
        (fun i ↦ observe i (complexNeumannInverse (R i) (hcomplex i) (source i))) A K := by
  intro source observe hchain
  have hcomplex : ∀ i, ‖R i‖ < 1 := by
    intro i
    rw [← realCompression_norm_eq_of_conjugation (R i) (hreal i)]
    exact (hR i).trans_lt hκ
  let Rreal := fun i ↦ (R i).restrictScalars ℝ
  let Inv := fun i ↦ (complexNeumannInverse (R i) (hcomplex i)).restrictScalars ℝ
  have hInv (i : ι) : Inv i * (1 + Rreal i) = 1 :=
    neumannInverse_mul_add ((R i).restrictScalars ℝ) (by simpa using hcomplex i)
  have hLρ (i : ι) : L i ≤ ρ i := by
    calc
      L i ≤ (ρ i) ^ (1-ν) := (hLK i).trans (hwindow i)
      _ ≤ (ρ i) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (hρ i) (by linarith)
      _ = _ := Real.rpow_one _
  refine ⟨hcomplex, ?_⟩
  apply inverse_hasEnvelopeProfile_of_smoothing_one_le
    (restrictionSobolevScale U CF hU) vectorFourierSobolevScale Rreal Inv observe source
    ρ L K A ν hInv hρ hL (fun i ↦ (hL i).trans (hLK i)) hLK hν hν₁ hwindow hA
  · intro j
    exact (hasEnvelopeProfile_congr (fun i ↦ congrArg (observe i)
      (complex_operator_power_restrictScalars_apply (R i) j (source i)))).mpr (hchain j)
  · intro s
    obtain ⟨D, hD, hcost⟩ := exists_demodulated_bumped_solver_fourier_cost (r := r) χ₃ P hP s
    let CB := D * Csolver s * Ccoefficient s
    have hCB : 0 ≤ CB := mul_nonneg (mul_nonneg hD (hCsolver s)) (hCcoefficient s)
    have hob (i : ι) (v : LocalL2 U CF) (hv : MemRestrictionSobolev U s v) :
        MemVectorFourierSobolev (s : ℝ) (observe i v) ∧
          vectorFourierSobolevNorm (s : ℝ) (observe i v) ≤
            CB * (ρ i)^((3*s : ℕ) : ℝ) * restrictionSobolevNorm U s v := by
      obtain ⟨hm, hb⟩ := hcost U hU hχ₃ (ρ i) (hρ i) (φ i) (hφ i) (hcφ i)
        (fun j hj _ y ↦ (hphase i j hj y).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (hL i)) (hLρ i) j) (hP j)))
        (S i) (Csolver s) (high i s) (hCsolver s) (hhigh i s) (hsolver i s) v hv
      refine ⟨hm, hb.trans ?_⟩
      have hcoef : 1 + high i s ≤ Ccoefficient s * (ρ i)^s :=
        (hcoefficient i s).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_le_one.trans (hL i)) (hLρ i) s) (hCcoefficient s))
      rw [Real.rpow_natCast]
      calc
        _ ≤ (D * Csolver s * (Ccoefficient s * (ρ i)^s)) *
            (ρ i)^(2*s) * restrictionSobolevNorm U s v := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hcoef (mul_nonneg hD (hCsolver s)))
              (pow_nonneg (zero_le_one.trans (hρ i)) _)) restrictionSobolevNorm_nonneg
        _ = _ := by
          have he : (ρ i)^s * (ρ i)^(2*s) = (ρ i)^(3*s) := by
            rw [← pow_add]
            congr 1
            omega
          calc
            _ = CB * ((ρ i)^s * (ρ i)^(2*s)) * restrictionSobolevNorm U s v := by
              dsimp only [CB]
              ring
            _ = _ := by rw [he]
    have hp (i : ι) (N : ℕ) :
        MemRestrictionSobolev U s (Inv i (((Rreal i)^(N+s)) (source i))) ∧
          restrictionSobolevNorm U s (Inv i (((Rreal i)^(N+s)) (source i))) ≤
            (6 * CP s N) * A i * L i ^ s * (L i / ρ i)^N := by
      have hre := hpower i N s false
      have him := hpower i N s true
      have hh := complex_inverse_power_remainder_of_real_quadratures (R i) (hreal i)
        (hcomplex i) s (N+s) (sources i false) (sources i true) hre.1 him.1 hre.2 him.2
      change MemRestrictionSobolev U s (complexNeumannInverse (R i) (hcomplex i)
          (((R i)^(N+s)) (source i))) ∧ _ at hh
      change MemRestrictionSobolev U s (complexNeumannInverse (R i) (hcomplex i)
          (((Rreal i)^(N+s)) (source i))) ∧ _
      rw [complex_operator_power_restrictScalars_apply (R i) (N+s) (source i)]
      exact ⟨hh.1, hh.2.trans_eq (by ring)⟩
    refine ⟨s, ((3*s : ℕ) : ℝ), CB, hCB,
      (fun i v hv ↦ (hob i v hv).1), ?_, fun N ↦ 6 * CP s N,
      (fun N ↦ mul_nonneg (by norm_num) (hCP s N)),
      (fun i N ↦ (hp i N).1), ?_⟩
    · intro i v hv
      calc
        _ = vectorFourierSobolevNorm (s : ℝ) (observe i v) :=
          vectorFourierSobolevScale_gradeNorm s (hob i v hv).1
        _ ≤ CB * (ρ i)^((3*s : ℕ) : ℝ) * restrictionSobolevNorm U s v :=
          (hob i v hv).2
        _ = _ := congrArg (CB * (ρ i)^((3*s : ℕ) : ℝ) * ·)
          (restrictionSobolevScale_gradeNorm hU hv).symm
    · intro i N
      rw [restrictionSobolevScale_gradeNorm hU (hp i N).1]
      exact (hp i N).2

end JanetCartan.FixedDomainInverse
