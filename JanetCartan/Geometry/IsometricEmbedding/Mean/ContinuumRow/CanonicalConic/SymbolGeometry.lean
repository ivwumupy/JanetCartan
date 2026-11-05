module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.CanonicalConic.SliceCoordinates

/-!
# The same conic inverse in the transport-symbol variables

This leaf only reorders the original variables and applies the retained
orthogonal output coordinates. It proves the augmented inverse identities,
open joint domain, measurable inverse and homogeneity used by the global
carrier producer. Its local hypotheses are the actual outputs instantiated
in `exists_actual_conic_inverse`, not assumed operator conclusions.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.ContinuumRow.CanonicalConic
open ActualCarriers FrozenMenu CurrentFullPhase FullPhaseCharts
open ActualComparison CanonicalCarrier ContinuumNormalReduction TransportSymbol ConicChart

variable {n : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Original symbol variables in the retained adapted output coordinates
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def symbolOutputCoordinates (p : Variables n × Euclidean 2) :
    (Euclidean 2 × Euclidean n × Euclidean n) × (ℝ × Euclidean (n - 1)) :=
  ((p.2, p.1.1, p.1.2.1), (adaptedSliceCoordinates T).equiv p.1.2.2)

/-- Smoothness of the fixed reordering and orthogonal coordinate map
(`app:ch_background:eq:bg-Psi`). -/
theorem symbolOutputCoordinates_smooth : ContDiff ℝ ∞ (symbolOutputCoordinates T) :=
  (contDiff_snd.prodMk (contDiff_fst.fst.prodMk contDiff_fst.snd.fst)).prodMk
    ((adaptedSliceCoordinates T).equiv.contDiff.comp contDiff_fst.snd.snd)

/-- The original input cone, keeping the original initial product coordinates
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def symbolInputDomain (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    Set (InputVariables n) :=
  {p | (p.2.1.2, p.1.1, p.1.2) ∈ physicalParameterSet z₀ a ∧
    (p.2.1.1, p.2.2) ∈ supportedCone z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)}

/-- The genuine original-variable input domain is open
(`app:ch_background:eq:bg-Psi`). -/
theorem symbolInputDomain_open (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    IsOpen (symbolInputDomain z₀ ηb r a) :=
  ((physicalParameterSet_open (n := n) z₀ a).preimage
    (continuous_snd.fst.snd.prodMk (continuous_fst.fst.prodMk continuous_fst.snd))).inter
      ((supportedCone_open z₀ (NormedSpace.normalize ηb) r (angularWidth ηb r)).preimage
        (continuous_snd.fst.fst.prodMk continuous_snd.snd))

variable (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress n) < T.family.threshold})

/-- The actual joint conic image in the symbol's original physical variables
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def symbolDomain (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    Set (Variables n × Euclidean 2) :=
  symbolOutputCoordinates T ⁻¹' supportedOutput T Q z₀ ηb r a

/-- The same measurable conic inverse in the original output variables
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def symbolInverse (z₀ : Euclidean 3) (ηb : Euclidean (n - 1)) (r a : ℝ) :
    Variables n × Euclidean 2 → ℝ × Euclidean (n - 1) :=
  conicInverse T Q z₀ ηb r a ∘ symbolOutputCoordinates T

/-- The actual symbol domain is invariant under positive frequency dilation
(`app:ch_background:eq:bg-Psi`). -/
theorem symbolDomain_smul_iff {z₀ : Euclidean 3} {ηb : Euclidean (n - 1)} {r a : ℝ}
    {t : ℝ} (ht : 0 < t) (p : Variables n × Euclidean 2) :
    (scaleFrequency t p.1, p.2) ∈ symbolDomain T Q z₀ ηb r a ↔
      p ∈ symbolDomain T Q z₀ ηb r a := by
  have he : symbolOutputCoordinates T (scaleFrequency t p.1, p.2) =
      ((symbolOutputCoordinates T p).1, t • (symbolOutputCoordinates T p).2) := by
    simp only [symbolOutputCoordinates, scaleFrequency, map_smul]
  change symbolOutputCoordinates T (scaleFrequency t p.1, p.2) ∈
    supportedOutput T Q z₀ ηb r a ↔ symbolOutputCoordinates T p ∈ supportedOutput T Q z₀ ηb r a
  rw [he]
  exact supportedOutput_smul_iff T Q ht _

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

/-- Openness required by the global carrier producer, for the actual physical
conic output domain (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem symbolDomain_open (hV : IsOpen V) (hLV : L ⊆ V) :
    IsOpen (symbolDomain T Q z₀ ηb r a) :=
  (supportedOutput_open T Q hηb hr hInv htrans hV hLV).preimage
    (symbolOutputCoordinates_smooth T).continuous

/-- Joint smoothness in both physical positions, output and spectator for the
same constructed inverse (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem symbolInverse_smooth (hLV : L ⊆ V) :
    ContDiffOn ℝ ∞ (symbolInverse T Q z₀ ηb r a) (symbolDomain T Q z₀ ηb r a) :=
  (conicInverse_smooth T Q hηb hr hInv htrans hLV).comp
    (symbolOutputCoordinates_smooth T).contDiffOn (fun _ hp ↦ hp)

/-- The original-variable inverse is globally measurable, as required for the
literal Lebesgue substitution (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem symbolInverse_measurable (hV : IsOpen V) (hLV : L ⊆ V) :
    Measurable (symbolInverse T Q z₀ ηb r a) :=
  (conicInverse_measurable T Q hηb hr hInv htrans hV hLV).comp
    (symbolOutputCoordinates_smooth T).continuous.measurable

/-- The complete inverse substitution lands in the actual input cone,
including both original positions and the unchanged spectator (`bg-Psi`). -/
theorem symbolInverse_maps : MapsTo (inverseCoordinates (symbolInverse T Q z₀ ηb r a))
    (symbolDomain T Q z₀ ηb r a) (symbolInputDomain z₀ ηb r a) := by
  intro p hp
  have hp' : symbolOutputCoordinates T p ∈ supportedOutput T Q z₀ ηb r a := hp
  refine ⟨hp'.1, ?_⟩
  change conicInverse T Q z₀ ηb r a (symbolOutputCoordinates T p) ∈ _
  rw [conicInverse_eq T Q hp']
  exact localConicInverse_mem T Q hηb hr hInv htrans hp'

/-- The inverse solves the literal physical averaged-gradient equation;
there is no substitution identity among the hypotheses (`bg-Psi`). -/
theorem transportAveragedGradient_symbolInverse
    {p : Variables n × Euclidean 2} (hp : p ∈ symbolDomain T Q z₀ ηb r a) :
    transportAveragedGradient (transportPosition T Q)
      (inverseCoordinates (symbolInverse T Q z₀ ηb r a) p) = p.1.2.2 := by
  have hp' : symbolOutputCoordinates T p ∈ supportedOutput T Q z₀ ηb r a := hp
  apply (adaptedSliceCoordinates T).equiv.injective
  have hh := map_localConicInverse T Q hηb hr hInv htrans hp'
  rw [← conicInverse_eq T Q hp'] at hh
  exact hh

/-- The actual augmented right-inverse identity consumed by the primitive
inverse-jet producer (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem augmentedTransportGradient_symbolInverse :
    EqOn (augmentedTransportGradient (transportPosition T Q) ∘
      inverseCoordinates (symbolInverse T Q z₀ ηb r a)) id (symbolDomain T Q z₀ ηb r a) :=
  augmentedTransportGradient_inverseCoordinates _ _
    (fun _ hp ↦ transportAveragedGradient_symbolInverse T Q hηb hr hInv htrans hp)

/-- The original input is recovered from its actual physical output. Both
positions and the spectator are retained (`app:ch_background:eq:bg-Psi`). -/
theorem symbolInverse_augmentedTransportGradient
    {p : InputVariables n} (hp : p ∈ symbolInputDomain z₀ ηb r a) :
    inverseCoordinates (symbolInverse T Q z₀ ηb r a)
      (augmentedTransportGradient (transportPosition T Q) p) = p := by
  have hq : symbolOutputCoordinates T (augmentedTransportGradient (transportPosition T Q) p) ∈
      supportedOutput T Q z₀ ηb r a := ⟨hp.1, (p.2.1.1, p.2.2), hp.2, rfl⟩
  have he : symbolInverse T Q z₀ ηb r a
      (augmentedTransportGradient (transportPosition T Q) p) = (p.2.1.1, p.2.2) := by
    change conicInverse T Q z₀ ηb r a _ = _
    rw [conicInverse_eq T Q hq]
    exact localConicInverse_map T Q hηb hr hInv htrans
      (p := (p.2.1.2, p.1.1, p.1.2)) (u := (p.2.1.1, p.2.2)) hp.1 hp.2
  simp only [augmentedTransportGradient] at he
  simp only [inverseCoordinates, augmentedTransportGradient, he]

/-- The symbol domain is exactly the actual augmented image of the supported
input cone (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem symbolDomain_eq_image :
    symbolDomain T Q z₀ ηb r a =
      augmentedTransportGradient (transportPosition T Q) '' symbolInputDomain z₀ ηb r a := by
  apply Subset.antisymm
  · intro p hp
    exact ⟨inverseCoordinates (symbolInverse T Q z₀ ηb r a) p,
      symbolInverse_maps T Q hηb hr hInv htrans hp,
      augmentedTransportGradient_symbolInverse T Q hηb hr hInv htrans hp⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨hp.1, (p.2.1.1, p.2.2), hp.2, rfl⟩

/-- Positive frequency homogeneity for the SAME symbol inverse, with the
incidence and spectator labels fixed (`app:ch_background:eq:bg-Psi`). -/
theorem symbolInverse_smul {p : Variables n × Euclidean 2}
    (hp : p ∈ symbolDomain T Q z₀ ηb r a) {t : ℝ} (ht : 0 < t) :
    symbolInverse T Q z₀ ηb r a (scaleFrequency t p.1, p.2) =
      ((symbolInverse T Q z₀ ηb r a p).1, t • (symbolInverse T Q z₀ ηb r a p).2) := by
  have hp' : symbolOutputCoordinates T p ∈ supportedOutput T Q z₀ ηb r a := hp
  have hpt : symbolOutputCoordinates T (scaleFrequency t p.1, p.2) ∈
      supportedOutput T Q z₀ ηb r a := (symbolDomain_smul_iff T Q ht p).mpr hp
  simp only [symbolInverse, Function.comp_apply]
  rw [conicInverse_eq T Q hp', conicInverse_eq T Q hpt]
  have he : symbolOutputCoordinates T (scaleFrequency t p.1, p.2) =
      ((symbolOutputCoordinates T p).1, t • (symbolOutputCoordinates T p).2) := by
    simp only [symbolOutputCoordinates, scaleFrequency, map_smul]
  rw [he]
  exact localConicInverse_smul T Q hηb hr hInv htrans hp' ht

end JanetCartan.ContinuumRow.CanonicalConic
