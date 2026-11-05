module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.PrimitiveFactors.ElapsedGrades.Measurability
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.ResidualCoordinates.CoefficientLocalization

/-!
# A smooth direct residual with the original physical derivative

Multiply both original coefficients by the retained chart output plateau.
The resulting nondivergence operator applied to the SAME `W₁` is exactly the
plateau times the retained third amplitude. On the common output it is the
original full physical derivative. This constructs the direct auxiliary form
required by `CompleteFactor`, including the zeroth-order coefficient `B`.
Source: `app:ch_regular_base:eq:energy-complete-residual`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteResidual.SelectedChart RegularSector.FinitePdo
open Characteristic Characteristic.AmplitudeBounds Characteristic.ResidualCoordinates
open Characteristic.EvolutionIntegral Characteristic.EvolutionIntegral.SymbolBudgets
open Characteristic.UniformEvolution Characteristic.EvolutionIntegral.KernelIdentification
open FiniteMasks FiniteMasks.ActualFamily FiniteAlgebraic
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "T" => Characteristic.TwoTimePoint (Euclidean d)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ

/-- Construct the auxiliary coefficient array in `CompleteFactor` by applying
one existing physical plateau to both original coefficients. Its direct
residual is globally smooth, agrees with the full original residual under
the actual common masks, and is literally the plateau times retained `W₂`.
Thus the latter's negative-order profiles can be transferred by Leibniz;
no analytic bound is assumed for the new auxiliary. All column and smoothness
hypotheses are retained outputs of `exists_finite_direct_operator_bounds`
(`app:ch_regular_base:eq:energy-complete-residual`). -/
theorem selected_common_smooth_direct_residual
    (f : ActualMaskFamily Ω x RQ A₀ K M) (p : f.centers)
    (hρb : (f.chart p).bufferRadius ≤ (f.chart p).targetRadius)
    (hsrcρ : (f.chart p).maskRadius ≤ (f.chart p).bufferRadius / 4)
    (output : E → ℝ) (hout : tsupport output ⊆ ball x f.physicalRadius)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat) (W : Fin 3 → T → CMat)
    (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hphysical : ∀ v : T, (f.chart p).timeMask =ᶠ[𝓝 v.1] (fun _ ↦ 1) →
      ∀ j : Fin (d+1), (fun k ↦ W 2 v k j) =
        WKB.firstOrderApply (complexPencilCoefficient Q) (complexPencilZeroth B)
          (fun y k ↦ W 1 (physicalSlice (coordinateSplit (f.chart p).index) v.2.1 v.2.2.2 y) k j)
          ((coordinateSplit (f.chart p).index).symm (v.1, v.2.2.1))) :
    let Aoriginal := fun y i ↦ (coefficient (f.chart p).index Q y i).map Complex.ofReal
    let Boriginal := fun y ↦ (zeroth (f.chart p).index B y).map Complex.ofReal
    let Ac := fun y i ↦ chartOutputMask f p y • Aoriginal y i
    let Bc := fun y ↦ chartOutputMask f p y • Boriginal y
    let b := directRetardedAmplitudes Ac Bc
      (curryCharacteristicMatrix (W 0)) (curryCharacteristicMatrix (W 1)) true
    b = (fun t s y η ↦ chartOutputMask f p (timeSpacePoint t y) • W 2 (t, (s, (y, η)))) ∧
      ContDiff ℝ ∞ (SymbolBudgets.jointAmplitude b) ∧
      ∀ (β : E → ℂ) r,
        elapsedAmplitude b (endpointOutputMask f p output) (chartInputMask f p) β r =
          elapsedAmplitude (directRetardedAmplitudes Aoriginal Boriginal
            (curryCharacteristicMatrix (W 0)) (curryCharacteristicMatrix (W 1)) true)
              (endpointOutputMask f p output) (chartInputMask f p) β r := by
  intro Aoriginal Boriginal Ac Bc b
  have htime := (selected_output_retained_geometry f p hρb hsrcρ).2.2
  have hpw := retained_residual_eq_twoTimePhysicalApply (f.chart p).index Q B (W 1) (W 2)
    (f.chart p).timeMask (hW 1) hphysical
  have hlinear (t s : ℝ) (y η : Euclidean d) : b t s y η =
      chartOutputMask f p (timeSpacePoint t y) •
        twoTimePhysicalApply Aoriginal Boriginal (curryCharacteristicMatrix (W 1)) t s y η := by
    simp only [b, directRetardedAmplitudes, twoTimePhysicalApply, physicalSymbolApply,
      Ac, Bc, Matrix.smul_mul, ← Finset.smul_sum, ← smul_add]
  have he : b = (fun t s y η ↦ chartOutputMask f p (timeSpacePoint t y) • W 2 (t, (s, (y, η)))) := by
    funext t s y η
    rw [hlinear]
    by_cases hz : chartOutputMask f p (timeSpacePoint t y) = 0
    · simp [hz]
    · have hh := hpw (timeSpacePoint t y) (htime _ (subset_tsupport _ hz)) s η
      simpa only [timeSpacePoint_time, spatialPart_timeSpacePoint] using
        congrArg (fun v : CMat ↦ chartOutputMask f p (timeSpacePoint t y) • v) hh.symm
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    exact ((chartPhysicalMasks_properties f p).1.comp
      (contDiff_timeSpacePoint.comp (contDiff_fst.fst.prodMk contDiff_fst.snd.snd))).smul
      ((hW 2).comp evolutionToCharacteristicPoint.contDiff)
  · intro β r
    apply elapsedDirectAmplitude_eq_of_coefficients
    · intro y hy
      have hh := (chartOutputMask_eventuallyEq_one_on_common_output f p output hout hy).eq_of_nhds
      funext i
      change chartOutputMask f p y • Aoriginal y i = Aoriginal y i
      rw [hh, one_smul]
    · intro y hy
      have hh := (chartOutputMask_eventuallyEq_one_on_common_output f p output hout hy).eq_of_nhds
      change chartOutputMask f p y • Boriginal y = Boriginal y
      rw [hh, one_smul]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
