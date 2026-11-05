module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteResidual.FiniteIdentity.ResidualWords
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.RestrictionFactors.RealCompression

/-!
# The actual real residual powers and their complex words

Use whole-operator reality to identify powers of the same local real residual
with the signed complex word expansion. Individual nonreal letters are never
separately real-compressed before composing. This preserves mixed conjugate
words and the original zero extensions needed in `app:ch_regular:lem:finite-chain`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
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

/-- Reality belongs to the whole physical plus pair
(`app:ch_regular_base:eq:signed-physical-normalization`). -/
private theorem physicalPair_star (S : H →L[ℂ] H) (v : H) :
    physicalPairedSectorSum {()} (fun _ : Unit ↦ S) (star v) =
      star (physicalPairedSectorSum {()} (fun _ : Unit ↦ S) v) := by
  simp only [physicalPairedSectorSum, Finset.sum_singleton]
  change S (star v) + star (S (star (star v))) = star (S v + star (S (star v)))
  simp only [star_add, star_star]
  exact add_comm _ _

/-- Iterate the existing real-inclusion identity on the same local measure
(`app:ch_regular:lem:finite-chain`). -/
private theorem inclusion_localRealCompression_pow_of_star
    {U : Set E} (hU : MeasurableSet U) (P : H →L[ℂ] H)
    (hP : ∀ v, P (star v) = star (P v)) (n : ℕ) (u : LocalL2 U RF) :
    l2ComplexInclusion (volume.restrict U) (((localRealCompression hU U P)^n) u) =
      ((localRetardedOperator hU U P)^n) (l2ComplexInclusion (volume.restrict U) u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change l2ComplexInclusion (volume.restrict U)
      (localRealCompression hU U P (((localRealCompression hU U P)^n) u)) = _
    rw [ArbitraryAccuracy.SelectedLocalization.inclusion_localRealCompression_of_star hU P hP, ih]
    rfl

/-- Powers of the actual real measured residual are the sums of the same
complex chart/term/conjugate words after real inclusion. Reality is proved
for the full physical pair, so no mixed words are lost by compressing the
individual letters (`app:ch_regular:lem:finite-chain`,
`app:ch_regular_base:eq:signed-physical-normalization`). -/
theorem selectedFiniteDirectResidual_measured_real_pow_eq_sum_words
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (n : ℕ) (u : LocalL2 U RF) :
    let retarded := (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let J := fun a : (f.centers × Fin 3) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedPhysicalResidualTerm f L Q B W₁ output ho hob hib T a))
    let P := physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded))
    l2ComplexInclusion (volume.restrict U) (((localRealCompression hU U P)^n) u) =
      ∑ w : Fin n → (f.centers × Fin 3) × Bool,
        (List.ofFn (fun j ↦ J (w j))).prod (l2ComplexInclusion (volume.restrict U) u) := by
  classical
  intro retarded J P
  rw [inclusion_localRealCompression_pow_of_star hU P (physicalPair_star _) n u,
    selectedFiniteDirectResidual_measured_physicalPair_pow_eq_sum_words
      f L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU n,
    sum_apply]

/-- The literal real adjoint of a residual power has the same reversed
complex words after inclusion. It retains the original measure, both masks,
and all conjugate letters (`app:ch_regular_base:eq:measured-adjoint`,
`app:ch_regular:lem:finite-chain`). -/
theorem selectedFiniteDirectResidual_measured_real_pow_adjoint_eq_sum_words
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (n : ℕ) (u : LocalL2 U RF) :
    let retarded := (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let J := fun a : (f.centers × Fin 3) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedPhysicalResidualTerm f L Q B W₁ output ho hob hib T a))
    let P := physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded))
    l2ComplexInclusion (volume.restrict U) (((localRealCompression hU U P)^n).adjoint u) =
      ∑ w : Fin n → (f.centers × Fin 3) × Bool,
        ((List.ofFn (fun j ↦ J (w j))).reverse.map (fun S ↦ S.adjoint)).prod
          (l2ComplexInclusion (volume.restrict U) u) := by
  classical
  intro retarded J P
  have hPa : ∀ v, P.adjoint (star v) = star (P.adjoint v) := by
    intro v
    dsimp only [P]
    rw [physicalPairedSectorSum_adjoint_eq]
    exact physicalPair_star _ v
  have hreal : ((localRealCompression hU U P)^n).adjoint =
      (localRealCompression hU U P.adjoint)^n :=
    (star_pow (localRealCompression hU U P) n).trans
      (congrArg (fun S ↦ S^n) (localRealCompression_adjoint hU hU P))
  rw [hreal, inclusion_localRealCompression_pow_of_star hU P.adjoint hPa n u]
  have hcomplex : (localRetardedOperator hU U P.adjoint)^n =
      ((localRetardedOperator hU U P)^n).adjoint :=
    ((star_pow (localRetardedOperator hU U P) n).trans
      (congrArg (fun S ↦ S^n) (localRetardedOperator_adjoint hU hU P))).symm
  rw [hcomplex, selectedFiniteDirectResidual_measured_physicalPair_pow_adjoint_eq_sum_words
      f L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU n,
    sum_apply]

/-- Powers of the actual normalized complete real residual are sums of the
same half-scaled characteristic, elliptic and conjugate complex words after real inclusion. Reality is proved
for the full physical pair, so no mixed words are lost by compressing the
individual letters (`app:ch_regular:lem:finite-chain`,
`app:ch_regular_base:eq:signed-physical-normalization`). -/
theorem selectedFullResidual_measured_real_pow_eq_sum_words
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (n : ℕ) (u : LocalL2 U RF) :
    let retarded := (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let J := fun a : ((f.centers × Fin 3) ⊕ Unit) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a))
    let P := physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        ((1 / 2 : ℂ) •
          (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded +
            (sourceCutMultiplier output ho hob).comp
              (EllipticComplement.ellipticResidual f hK L Q B))))
    l2ComplexInclusion (volume.restrict U) (((localRealCompression hU U P)^n) u) =
      ∑ w : Fin n → ((f.centers × Fin 3) ⊕ Unit) × Bool,
        (List.ofFn (fun j ↦ J (w j))).prod (l2ComplexInclusion (volume.restrict U) u) := by
  classical
  intro retarded J P
  rw [inclusion_localRealCompression_pow_of_star hU P (physicalPair_star _) n u,
    selectedFullResidual_measured_physicalPair_pow_eq_sum_words
      f hK L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU n,
    sum_apply]

/-- The literal real adjoint of a normalized full-residual power has all
reversed characteristic, elliptic and conjugate complex words after inclusion.
It retains the original measure, both masks,
and all conjugate letters (`app:ch_regular_base:eq:measured-adjoint`,
`app:ch_regular:lem:finite-chain`). -/
theorem selectedFullResidual_measured_real_pow_adjoint_eq_sum_words
    (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K) (L : ℝ)
    (Q : E → Fin (d+1) → Mat) (B : E → Mat)
    (W₁ : f.centers → TwoTimeAmplitude d (d+1))
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1)
    (hib : ∀ y, ‖f.inputMask y‖ ≤ 1) (hsupp : tsupport output ⊆ ball x f.physicalRadius)
    (R C : f.centers → ℝ)
    (hb : ∀ p, GraphNormalAmplitudeBounds
      (maskedPhysicalPDOCycleSymbol (chartOutputMask f p) (chartInputMask f p)
        (selectedAlgebraicSymbol f p (2*L) Q B 1)) (R p) (C p))
    (T : f.centers → H →L[ℂ] H)
    (μ ν : E → ℝ) (hμ : Continuous μ) (hν : Continuous ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1)
    {U : Set E} (hU : MeasurableSet U) (n : ℕ) (u : LocalL2 U RF) :
    let retarded := (sourceCutMultiplier output ho hob).comp
      ((finitePhysicalOperator (fun p ↦ (f.chart p).index) T).comp
        (sourceCutMultiplier f.inputMask f.inputMask_smooth.continuous hib))
    let J := fun a : ((f.centers × Fin 3) ⊕ Unit) × Bool ↦ localRetardedOperator hU U
      (measuredOperator μ ν hμ hν hμb hνb
        (selectedFullPhysicalResidualTerm f hK L Q B W₁ output ho hob hib T a))
    let P := physicalPairedSectorSum {()} (fun _ : Unit ↦
      measuredOperator μ ν hμ hν hμb hνb
        ((1 / 2 : ℂ) •
          (selectedFiniteDirectResidual f L Q B W₁ output ho hob retarded +
            (sourceCutMultiplier output ho hob).comp
              (EllipticComplement.ellipticResidual f hK L Q B))))
    l2ComplexInclusion (volume.restrict U) (((localRealCompression hU U P)^n).adjoint u) =
      ∑ w : Fin n → ((f.centers × Fin 3) ⊕ Unit) × Bool,
        ((List.ofFn (fun j ↦ J (w j))).reverse.map (fun S ↦ S.adjoint)).prod
          (l2ComplexInclusion (volume.restrict U) u) := by
  classical
  intro retarded J P
  have hPa : ∀ v, P.adjoint (star v) = star (P.adjoint v) := by
    intro v
    dsimp only [P]
    rw [physicalPairedSectorSum_adjoint_eq]
    exact physicalPair_star _ v
  have hreal : ((localRealCompression hU U P)^n).adjoint =
      (localRealCompression hU U P.adjoint)^n :=
    (star_pow (localRealCompression hU U P) n).trans
      (congrArg (fun S ↦ S^n) (localRealCompression_adjoint hU hU P))
  rw [hreal, inclusion_localRealCompression_pow_of_star hU P.adjoint hPa n u]
  have hcomplex : (localRetardedOperator hU U P.adjoint)^n =
      ((localRetardedOperator hU U P)^n).adjoint :=
    ((star_pow (localRetardedOperator hU U P) n).trans
      (congrArg (fun S ↦ S^n) (localRetardedOperator_adjoint hU hU P))).symm
  rw [hcomplex, selectedFullResidual_measured_physicalPair_pow_adjoint_eq_sum_words
      f hK L Q B W₁ output ho hob hib hsupp R C hb T μ ν hμ hν hμb hνb hU n,
    sum_apply]

end JanetCartan.RegularSector.FiniteResidual.FiniteIdentity
