module

public import JanetCartan.Iteration.PhysicalMean.CrossFourier
public import JanetCartan.Iteration.PhysicalMean.MomentSobolevRow

/-!
# The literal full modified native cross row

The amplitude below is the full measured Hermitian cross with the SAME
source-dependent physical background. The raw amplitude is not replaced by
its principal term. The original native scalar tester retains all halfweights,
square-root sample weights, masks, and the input measure
(`app:ch_mean_pairs:eq:mean-quadratic-low`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean

open CurrentMean CanonicalRowComparison AmplitudeBound AmplitudeBound.PaperEstimates
open Pseudodifferential

/-- The adjoint-convention amplitude of the actual modified cross row. Its
forward kernel contains the unconjugated full cross measurement. -/
def modifiedCrossAdjointAmplitude {n N : ℕ} {X : Type*}
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B G : X → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (i : Fin n) (u : X) (x : Euclidean n) : ℂ :=
  star (complexCrossMeasurement (C x) (B u x) (G u x) i)

/-- The literal full modified amplitude is jointly continuous. No derivative
or norm of a sample label or initial frequency is needed. -/
theorem continuous_modifiedCrossAdjointAmplitude {n N : ℕ} {X : Type*} [TopologicalSpace X]
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B G : X → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : Continuous C) (hB : Continuous (Function.uncurry B))
    (hG : Continuous (Function.uncurry G)) (i : Fin n) :
    Continuous (Function.uncurry (modifiedCrossAdjointAmplitude C B G i)) := by
  let HB := hermitianContinuousBilinear (m := Fin N) (n := Fin n)
  have hv₀ := (hC.comp continuous_snd).clm_apply ((HB.continuous.comp hB).clm_apply hG)
  have hvI := (hC.comp continuous_snd).clm_apply
    ((HB.continuous.comp hB).clm_apply (hG.const_smul Complex.I))
  have hH := (euclideanComplexInclusion.continuous.comp hv₀).sub
    ((euclideanComplexInclusion.continuous.comp hvI).const_smul Complex.I)
  exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n ↦ ℂ) i).continuous.comp hH).star

/-- The modified row has exactly the original full raw amplitude's physical
support; multiplying by the actual background introduces no new cutoff. -/
theorem tsupport_modifiedCrossAdjointAmplitude_subset {n N : ℕ} {X : Type*}
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B G : X → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    {K : Set (Euclidean n)} (hK : IsClosed K) (hG : ∀ u, tsupport (G u) ⊆ K)
    (i : Fin n) (u : X) : tsupport (modifiedCrossAdjointAmplitude C B G i u) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  apply hG u
  apply subset_tsupport
  intro hz
  exact hx (by simp only [modifiedCrossAdjointAmplitude, hz, map_zero, PiLp.zero_apply, star_zero])

/-- The fixed modified-row constant is chosen before every input space,
source measure, sample, frequency, current map, background and scalar tester. -/
def modifiedCrossRowConstant (n N : ℕ) (R : ℝ) : ℝ :=
  rowAmplitudeConstant n R *
    (exists_crossAmplitude_component_fourierSobolev_bound n N (n / 2 + 1)).choose

/-- Nonnegativity of the predata modified-row constant. -/
theorem modifiedCrossRowConstant_nonneg (n N : ℕ) (R : ℝ) :
    0 ≤ modifiedCrossRowConstant n N R :=
  mul_nonneg (rowAmplitudeConstant_nonneg n R)
    (exists_crossAmplitude_component_fourierSobolev_bound n N (n / 2 + 1)).choose_spec.1

/-- The original native scalar entry of the FULL modified row obeys the
sharp bound linear in the SAME source-dependent background's `H^ell` jet
budget `Z`. Only genuine coefficient factors use `C^ell` suprema. In the
canonical application `B = Dν v`, task 42 supplies `Z ≤ C ||v||_{H^m0}` from
the actual individual forward/adjoint pair, with `m0 = ell + 1`.

The input measure, original complete mask and scalar tester never change.
No individual raw operator norm, inverse sample weight or sample/band count
appears in this estimate. -/
theorem norm_modifiedCrossNativeScalarRow_le {n N : ℕ} {X : Type*}
    [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsLocallyFiniteMeasure μ] [SFinite μ]
    (φ : X → Euclidean n → ℝ) (m : X → ℝ)
    (hφ : Continuous (Function.uncurry φ)) (hm : Continuous m) (hms : HasCompactSupport m)
    (C : Euclidean n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n)
    (B G : X → Euclidean n → Matrix (Fin N) (Fin n) ℂ)
    (hC : ContDiff ℝ ∞ C) (hBc : Continuous (Function.uncurry B))
    (hGc : Continuous (Function.uncurry G))
    (hB : ∀ u, ContDiff ℝ ∞ (B u)) (hG : ∀ u, ContDiff ℝ ∞ (G u))
    {K : Set (Euclidean n)} (hK : IsCompact K) (hGK : ∀ u, tsupport (G u) ⊆ K)
    (χ : Euclidean n → ℝ) (hχ : Continuous χ) (hχs : HasCompactSupport χ)
    (hχK : ∀ x ∈ K, χ x = 1) (R : ℝ) (hbox : ∀ x ∈ K, ∀ i, |x i| ≤ R)
    (CC CG Z : ℝ) (hCC : 0 ≤ CC) (hCG : 0 ≤ CG) (hZ : 0 ≤ Z)
    (hCb : cNorm K (n / 2 + 1) C ≤ CC)
    (hGb : ∀ u, m u ≠ 0 → cNorm K (n / 2 + 1) (G u) ≤ CG)
    (hBmem : ∀ u, m u ≠ 0 → ∀ j ≤ n / 2 + 1,
      MemLp (iteratedFDeriv ℝ j (B u)) 2 volume)
    (hBb : ∀ u, m u ≠ 0 →
      (∑ j ∈ Finset.range (n / 2 + 1 + 1), lpNorm (iteratedFDeriv ℝ j (B u)) 2 volume) ≤ Z)
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 (volume : Measure (Euclidean n)))
    (hT : ∀ f : Lp ℂ 2 μ, T f =ᵐ[volume] fun x ↦ ∫ u,
      sampledMomentKernel φ m (fun _ x ↦ (χ x : ℂ)) x u * f u ∂μ)
    (i : Fin n) :
    ‖sampledMomentOperator μ φ m (modifiedCrossAdjointAmplitude C B G i) hφ hm
      (continuous_modifiedCrossAdjointAmplitude C B G hC.continuous hBc hGc i)
      hms hK (tsupport_modifiedCrossAdjointAmplitude_subset C B G hK.isClosed hGK i)‖ ≤
      modifiedCrossRowConstant n N R * ‖T‖ * CC * CG * Z := by
  let D := (exists_crossAmplitude_component_fourierSobolev_bound n N (n / 2 + 1)).choose
  have hD : 0 ≤ D :=
    (exists_crossAmplitude_component_fourierSobolev_bound n N (n / 2 + 1)).choose_spec.1
  have hfull :=
    (exists_crossAmplitude_component_fourierSobolev_bound n N (n / 2 + 1)).choose_spec.2
  let A := D * CC * CG * Z
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hD hCC) hCG) hZ
  have hs : ∀ u, m u ≠ 0 →
      ∃ hf : MemLp (fun x ↦ star (modifiedCrossAdjointAmplitude C B G i u x)) 2 volume,
      MemFourierSobolev (n / 2 + 1 : ℕ)
        (hf.toLp (fun x ↦ star (modifiedCrossAdjointAmplitude C B G i u x))) ∧
      fourierSobolevNorm (n / 2 + 1 : ℕ)
        (hf.toLp (fun x ↦ star (modifiedCrossAdjointAmplitude C B G i u x))) ≤ A := by
    intro u hu
    obtain ⟨hf, hHs, hn⟩ := hfull K hK C (B u) (G u) hC (hB u) (hG u)
      (hGK u) (hBmem u hu) i
    have hcoef : D * cNorm K (n / 2 + 1) C * cNorm K (n / 2 + 1) (G u) ≤
        D * CC * CG :=
      mul_le_mul (mul_le_mul_of_nonneg_left hCb hD) (hGb u hu)
        (cNorm_nonneg _ _ _) (mul_nonneg hD hCC)
    have hbudget : D * cNorm K (n / 2 + 1) C * cNorm K (n / 2 + 1) (G u) *
        (∑ j ∈ Finset.range (n / 2 + 1 + 1), lpNorm (iteratedFDeriv ℝ j (B u)) 2 volume) ≤ A :=
      mul_le_mul hcoef (hBb u hu) (Finset.sum_nonneg fun _ _ ↦ lpNorm_nonneg)
        (mul_nonneg (mul_nonneg hD hCC) hCG)
    simpa only [modifiedCrossAdjointAmplitude, star_star] using
      (show ∃ hf : MemLp (fun x ↦ complexCrossMeasurement (C x) (B u x) (G u x) i) 2 volume,
        MemFourierSobolev (n / 2 + 1 : ℕ) (hf.toLp _) ∧
          fourierSobolevNorm (n / 2 + 1 : ℕ) (hf.toLp _) ≤ A from
        ⟨hf, hHs, hn.trans hbudget⟩)
  have hh := norm_sampledMomentOperator_le_scalarTest_of_sobolev_onMask μ φ m
    (modifiedCrossAdjointAmplitude C B G i) hφ hm
    (continuous_modifiedCrossAdjointAmplitude C B G hC.continuous hBc hGc i) hms hK
    (tsupport_modifiedCrossAdjointAmplitude_subset C B G hK.isClosed hGK i)
    χ hχ hχs hχK R hbox A hA hs T hT
  exact hh.trans_eq (by dsimp [modifiedCrossRowConstant, A, D]; ring)

end JanetCartan.PhysicalMean
