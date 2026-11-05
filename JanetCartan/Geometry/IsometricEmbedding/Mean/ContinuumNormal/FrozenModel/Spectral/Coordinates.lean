module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumNormal.FrozenModel.Symbol
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SymbolGeometry

/-!
# The retained conic inverse at the physical origin

The frozen step of `app:ch_background:prop:bg-frame` uses the zero-position
restriction of the SAME canonical conic inverse. These definitions retain its
incidence variable, spectator, adapted slice coordinates, and input measure.
The domains extend freely in the two physical positions; the measurement
factors will supply their actual support in the full amplitude.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumNormal.FrozenModel
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ContinuumRow ContinuumRow.CanonicalCarrier ContinuumRow.CanonicalConic
open ActualComparison ContinuumNormalReduction TransportSymbol ConicChart

/-- Erase only the two positions in the original carrier input
(`new:lem:scaling`). -/
def originInput {n : ℕ} (p : InputVariables n) : InputVariables n := ((0, 0), p.2)

/-- Erase only the two positions in the symbol output, leaving both the physical
frequency and the Lebesgue spectator unchanged (`new:lem:scaling`). -/
def originOutput {n : ℕ} (p : Variables n × Euclidean 2) : Variables n × Euclidean 2 :=
  ((0, 0, p.1.2.2), p.2)

/-- The zero-position restriction is a smooth fixed coordinate map
(`app:ch_background:eq:bg-Psi`). -/
theorem originInput_smooth {n : ℕ} : ContDiff ℝ ∞ (@originInput n) :=
  contDiff_const.prodMk contDiff_snd

/-- The output restriction is smooth without changing frequency or spectator
(`app:ch_background:eq:bg-Psi`). -/
theorem originOutput_smooth {n : ℕ} : ContDiff ℝ ∞ (@originOutput n) :=
  (contDiff_const.prodMk (contDiff_const.prodMk contDiff_fst.snd.snd)).prodMk contDiff_snd

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The original supported cone at zero position, extended in the positions
only (`app:ch_background:eq:bg-Psi`, frozen step). -/
def frozenInputDomain (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    Set (InputVariables n) := originInput ⁻¹' symbolInputDomain z₀ ηb r a

/-- The SAME canonical conic image at zero position
(`app:ch_background:eq:bg-full-complex-amplitude`, frozen step). -/
def frozenSymbolDomain (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    Set (Variables n × Euclidean 2) := originOutput ⁻¹' symbolDomain T Q z₀ ηb r a

/-- The SAME canonical measurable inverse evaluated at zero physical positions
(`app:ch_background:eq:bg-Psi`, frozen step). -/
def frozenSymbolInverse (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    Variables n × Euclidean 2 → ℝ × Euclidean (n - 1) :=
  symbolInverse T Q z₀ ηb r a ∘ originOutput

/-- Exact position independence of the chosen frozen inverse
(`new:lem:scaling`). -/
theorem frozenSymbolInverse_position (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (r a : ℝ) (x y k : Euclidean n) (v : Euclidean 2) :
    frozenSymbolInverse T Q z₀ ηb r a ((x, y, k), v) =
      frozenSymbolInverse T Q z₀ ηb r a ((0, 0, k), v) := rfl

/-- The zero-position inverse domain has no residual physical restriction
(`new:lem:scaling`). -/
theorem frozenSymbolDomain_position (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (r a : ℝ) (x y k : Euclidean n) (v : Euclidean 2) :
    ((x, y, k), v) ∈ frozenSymbolDomain T Q z₀ ηb r a ↔
      ((0, 0, k), v) ∈ frozenSymbolDomain T Q z₀ ηb r a := Iff.rfl

/-- The retained input cone is open (`app:ch_background:eq:bg-Psi`). -/
theorem frozenInputDomain_open (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    IsOpen (frozenInputDomain z₀ ηb r a) :=
  (symbolInputDomain_open z₀ ηb r a).preimage originInput_smooth.continuous

/-- Positive output dilation preserves the frozen conic domain
(`app:ch_background:eq:bg-Psi`). -/
theorem frozenSymbolDomain_smul_iff (z₀ : Euclidean 3) (ηb : Euclidean (n - 1))
    (r a : ℝ) {t : ℝ} (ht : 0 < t) (p : Variables n × Euclidean 2) :
    (scaleFrequency t p.1, p.2) ∈ frozenSymbolDomain T Q z₀ ηb r a ↔
      p ∈ frozenSymbolDomain T Q z₀ ηb r a :=
  symbolDomain_smul_iff T Q ht (originOutput p)

variable {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a b cJ : ℝ}
    {V L : Set (ℝ × Euclidean (n - 1))}
    {G : (ℝ × Euclidean (n - 1)) ≃L[ℝ] (ℝ × Euclidean (n - 1))}
    (hηb : ηb ≠ 0) (hr : 0 < r)
    (hInv : BufferedPhaseInverse (adaptedTransportChart T Q) (physicalParameterSet z₀ a)
      (dataBox z₀ ηb r) (dataSet z₀ ηb (2 * r)) (dataBox z₀ ηb (2 * r)) V L b cJ G)
    (htrans : ∀ p ∈ physicalParameterSet z₀ a,
      ∀ u ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r),
        ‖(adaptedTransportChart T Q p u).2 - u.2‖ ≤ (angularWidth ηb r / 4) * ‖u.2‖)
include hηb hr hInv htrans

/-- Openness transfers from the constructed canonical conic image. The local
inputs are produced by `CanonicalConic.exists_actual_conic_inverse`
(`app:ch_background:eq:bg-Psi`). -/
theorem frozenSymbolDomain_open (hV : IsOpen V) (hLV : L ⊆ V) :
    IsOpen (frozenSymbolDomain T Q z₀ ηb r a) :=
  (symbolDomain_open T Q hηb hr hInv htrans hV hLV).preimage originOutput_smooth.continuous

/-- The frozen inverse is globally measurable with the SAME zero extension
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenSymbolInverse_measurable (hV : IsOpen V) (hLV : L ⊆ V) :
    Measurable (frozenSymbolInverse T Q z₀ ηb r a) :=
  (symbolInverse_measurable T Q hηb hr hInv htrans hV hLV).comp
    originOutput_smooth.continuous.measurable

/-- Joint smoothness on the frozen image follows from the retained inverse
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem frozenSymbolInverse_smooth (hLV : L ⊆ V) :
    ContDiffOn ℝ ∞ (frozenSymbolInverse T Q z₀ ηb r a)
      (frozenSymbolDomain T Q z₀ ηb r a) :=
  (symbolInverse_smooth T Q hηb hr hInv htrans hLV).comp originOutput_smooth.contDiffOn
    (fun _ hp ↦ hp)

/-- The chosen inverse stays in the original supported incidence/angular cone
(`app:ch_background:eq:bg-Psi`). -/
theorem frozenSymbolInverse_maps :
    MapsTo (inverseCoordinates (frozenSymbolInverse T Q z₀ ηb r a))
      (frozenSymbolDomain T Q z₀ ηb r a) (frozenInputDomain z₀ ηb r a) := by
  intro p hp
  exact symbolInverse_maps T Q hηb hr hInv htrans hp

/-- The original incidence variable is degree zero and the input covector is
degree one in physical output frequency, for the retained frozen inverse
(`app:ch_background:eq:bg-Psi`). -/
theorem frozenSymbolInverse_smul {p : Variables n × Euclidean 2}
    (hp : p ∈ frozenSymbolDomain T Q z₀ ηb r a) {t : ℝ} (ht : 0 < t) :
    frozenSymbolInverse T Q z₀ ηb r a (scaleFrequency t p.1, p.2) =
      ((frozenSymbolInverse T Q z₀ ηb r a p).1,
        t • (frozenSymbolInverse T Q z₀ ηb r a p).2) :=
  symbolInverse_smul T Q hηb hr hInv htrans hp ht

omit T Q hηb hInv htrans in
/-- The original carrier labels remain inside the constructed seed parameter
buffer on the frozen input cone (`app:ch_background:eq:bg-Psi`). -/
theorem carrierInterior_of_frozenInputDomain (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {p : InputVariables n} (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    parameter p.2.1 ∈ parameterInterior (3 * P.radius / 2) :=
  hcarrier ⟨(ball_subset_closedBall.trans (closedBall_subset_closedBall har)) hp.1.1,
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))) hp.2.1⟩

omit hηb hInv htrans in
/-- The actual carrier buffer supplies the phase-domain condition throughout
the frozen input cone. These are the same buffer inequalities returned by
`CanonicalConic.exists_actual_conic_inverse` (`new:lem:scaling`). -/
theorem phaseBuffer_of_frozenInputDomain {c C : ℝ} (hP : P.IsValid c C)
    (har : a ≤ 3 * r)
    (hcarrier : closedBall (spectatorCenter z₀) (3 * r) ×ˢ closedBall (z₀ 0) (3 * r) ⊆
      carrierParameters ⁻¹' parameterInterior (3 * P.radius / 2))
    {p : InputVariables n} (hp : p ∈ frozenInputDomain z₀ ηb r a) :
    T.reference.spatialPatch (parameter p.2.1) ∈
      ball (ActualPhase.covectorCenter T) T.family.radius := by
  apply spatialPatch_mem_phaseBuffer T hP
  exact fun i ↦ (carrierInterior_of_frozenInputDomain hr har hcarrier hp i).le

end JanetCartan.ContinuumNormal.FrozenModel
