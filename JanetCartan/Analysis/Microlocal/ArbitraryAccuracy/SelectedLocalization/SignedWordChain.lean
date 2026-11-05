module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.SignedWordSupport
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.FiniteChains.Alternating
public import Mathlib.Data.List.OfFn

/-!
# Ordered signed words as the actual analytic factor chain

The last entry of an operator list acts first. Reverse the list of chronological
chain factors explicitly, retaining the complete complex word and its final
real projection. The original measurement supports justify zero extension.
-/

@[expose] public noncomputable section
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open ResponseTransfer MeasureTheory Set LocalSobolev
open RegularSector RegularSector.FiniteAssembly RegularSector.Realization
open RegularSector.FiniteMasks.ActualFamily RegularSector.FiniteResidual.FiniteIdentity
open RegularSector.Characteristic.EvolutionIntegral
open RegularSector.Characteristic.RetardedLocalization

/-- Chronological factor-chain order is the reversed operator-list order.
Consumer: the actual signed word in `NormalizedResidualWords.MeasuredDecay`
(`app:ch_regular:lem:finite-chain`). -/
theorem factorChain_eq_reversed_operator_list
    {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ℕ → ι → F →L[ℝ] F) (f : ι → F) (n : ℕ) (i : ι) :
    factorChain (fun j k ↦ (T j k).toLinearMap) f n i =
      (List.ofFn (fun j : Fin n ↦ T j.val i)).reverse.prod (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat, List.prod_cons]
    change T n i (factorChain (fun j k ↦ (T j k).toLinearMap) f n i) =
      T n i ((List.ofFn (fun j : Fin n ↦ T j.val i)).reverse.prod (f i))
    rw [ih]

variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "H" => SpacetimeL2 d (d+1)
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))

/-- Apply the exact support transport to the chronological chain of actual
measured signed letters. The conclusion keeps the same global word, external
halves and whole conjugates, and takes real part only after the word. Consumer:
the normalized inverse's observed local words
(`app:ch_regular:eq:finite-observation`, `app:ch_regular:eq:chain-tail`). -/
theorem selectedFullPhysicalResidual_factorChain_realPart_zeroExtend
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U)
    (hμU : tsupport μ ⊆ U) (hνU : tsupport ν ⊆ U)
    (w : ℕ → ((f.centers × Fin 3) ⊕ Unit) × Bool) (n : ℕ) (u : LocalL2 U RF) :
    let P := fun j ↦ measuredOperator μ ν hμ hν hμb hνb
      (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T (w j))
    let J := fun j (_ : Unit) ↦ localRetardedOperator hU U (P j)
    SmallSupport.zeroExtend hU (l2RealPart (volume.restrict U)
      (factorChain (fun j k ↦ (J j k).toLinearMap)
        (fun _ ↦ l2ComplexInclusion (volume.restrict U) u) n ())) =
      l2RealPart volume ((List.ofFn (fun j : Fin n ↦ P j.val)).reverse.prod
        (l2ComplexInclusion volume (SmallSupport.zeroExtend hU u))) := by
  intro P J
  rw [factorChain_eq_reversed_operator_list]
  have h := selectedFullPhysicalResidualWord_realPart_zeroExtend f hK L Q B W₁
    output ho hob hib T μ ν hμ hν hμb hνb hU hμU hνU
    (List.ofFn (fun j : Fin n ↦ w j.val)).reverse u
  simpa only [List.map_reverse, List.map_ofFn, Function.comp_def, P, J] using h

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
