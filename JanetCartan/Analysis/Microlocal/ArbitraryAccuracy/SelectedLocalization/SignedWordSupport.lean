module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedMeasuredLeakage
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.Pairing

/-!
# Support transport of the actual individual signed words

The original measurement supports identify local products with the same global
products on zero-extended inputs. Whole conjugates and literal adjoints remain
individual complex letters; real part is taken only after the complete word.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open RegularSector RegularSector.FiniteResidual.FiniteIdentity
open Characteristic Characteristic.ResidualCoordinates Characteristic.EvolutionIntegral
open Characteristic.PdoRealization FiniteAssembly FiniteEvolution FiniteAlgebraic FinitePdo
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LowBounds Realization
open JanetCartan.CharacteristicTransport.CompleteResidual
open Characteristic.RetardedLocalization LocalSobolev
open ArbitraryAccuracy.ResidualLocalization
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))

/-- Zero extension identifies every ordered mixed word with the same
whole-space factors. Each backward letter uses the original input-mask
support, and each forward letter uses the output-mask support. This includes
reversed adjoint words (`app:ch_regular_base:eq:measured-adjoint`,
`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullPhysicalResidualWord_oriented_zeroExtend
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set (Euclidean (d+1))} (hU : MeasurableSet U)
    (hμU : tsupport μ ⊆ U) (hνU : tsupport ν ⊆ U)
    (w : List ((((f.centers × Fin 3) ⊕ Unit) × Bool) × Bool))
    (u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1)))) :
    let P := fun a : ((f.centers × Fin 3) ⊕ Unit) × Bool ↦ measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a)
    let D := fun a : (((f.centers × Fin 3) ⊕ Unit) × Bool) × Bool ↦
      if a.2 then (P a.1).adjoint else P a.1
    let J := fun a ↦ localRetardedOperator hU U (D a)
    SmallSupport.zeroExtend hU ((w.map J).prod u) =
      (w.map D).prod (SmallSupport.zeroExtend hU u) := by
  intro P D J
  have hletter a (v : LocalL2 U (EuclideanSpace ℂ (Fin (d+1)))) :
      SmallSupport.zeroExtend hU (J a v) = D a (SmallSupport.zeroExtend hU v) := by
    rcases a with ⟨a, backward⟩
    cases backward with
    | false => exact zeroExtend_local_measuredOperator hU hU μ ν hμ hν hμb hνb hμU _ v
    | true =>
      dsimp only [J, D]
      simp only [ite_true, P, measuredOperator_adjoint]
      exact zeroExtend_local_measuredOperator hU hU ν μ hν hμ hνb hμb hνU _ v
  induction w generalizing u with
  | nil => simp
  | cons a w ih =>
    simp only [List.map_cons, List.prod_cons]
    change SmallSupport.zeroExtend hU (J a ((w.map J).prod u)) =
      D a ((w.map D).prod (SmallSupport.zeroExtend hU u))
    rw [hletter, ih]

/-- Zero extension commutes with the complete signed word in the original
composition order. Its real part is taken only after all complex factors.
The actual measurement supports prove the intermediate support absorptions.
Consumer: `NormalizedResidualWords.measured_realResidual_hchain_of_words`
(`app:ch_regular:lem:finite-chain`, `app:ch_regular:eq:chain-tail`). -/
theorem selectedFullPhysicalResidualWord_zeroExtend
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U)
    (hμU : tsupport μ ⊆ U) (hνU : tsupport ν ⊆ U)
    (w : List (((f.centers × Fin 3) ⊕ Unit) × Bool))
    (u : LocalL2 U (EuclideanSpace ℂ (Fin (d+1)))) :
    let P := fun a ↦ measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a)
    let J := fun a ↦ localRetardedOperator hU U (P a)
    SmallSupport.zeroExtend hU ((w.map J).prod u) =
      (w.map P).prod (SmallSupport.zeroExtend hU u) := by
  intro P J
  simpa only [List.map_map, Function.comp_def, Bool.false_eq_true, ite_false] using
    selectedFullPhysicalResidualWord_oriented_zeroExtend
      f hK L Q B W₁ output ho hob hib T μ ν hμ hν hμb hνb hU hμU hνU
      (w.map (fun a ↦ (a, false))) u

/-- The final real projection and zero extension of a complete signed word
agree with the real part of its actual global product. No projection occurs
between letters. Consumer: angular observation of the normalized local inverse
(`app:ch_regular:eq:finite-observation`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem selectedFullPhysicalResidualWord_realPart_zeroExtend
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U)
    (hμU : tsupport μ ⊆ U) (hνU : tsupport ν ⊆ U)
    (w : List (((f.centers × Fin 3) ⊕ Unit) × Bool)) (u : LocalL2 U RF) :
    let P := fun a ↦ measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a)
    let J := fun a ↦ localRetardedOperator hU U (P a)
    SmallSupport.zeroExtend hU (l2RealPart (volume.restrict U)
        ((w.map J).prod (l2ComplexInclusion (volume.restrict U) u))) =
      l2RealPart volume ((w.map P).prod
        (l2ComplexInclusion volume (SmallSupport.zeroExtend hU u))) := by
  intro P J
  have hr (v : LocalL2 U (EuclideanSpace ℂ (Fin (d+1)))) :
      l2RealPart volume (SmallSupport.zeroExtend hU v) =
        SmallSupport.zeroExtend hU (l2RealPart (volume.restrict U) v) :=
    compLp_zeroExtend (euclideanRealPart (ι := Fin (d+1))) hU v
  have hi : l2ComplexInclusion volume (SmallSupport.zeroExtend hU u) =
      SmallSupport.zeroExtend hU (l2ComplexInclusion (volume.restrict U) u) :=
    compLp_zeroExtend (euclideanComplexInclusion (ι := Fin (d+1))) hU u
  rw [← hr, selectedFullPhysicalResidualWord_zeroExtend f hK L Q B W₁ output ho hob hib T
    μ ν hμ hν hμb hνb hU hμU hνU, hi]

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
