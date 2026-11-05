module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.AmplitudeProfiles.Geometry.ComponentBounds
public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.PhaseExtension.Profiles.Interpolation

/-!
# Global geometric-component profiles for the canonical adjoint

This supplies `hc` and `C₀` for
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
The exact extended geometric normal uses the literal canonical normal completion,
carrier gradient and retained nullvector, with the scalar and flow removed. The
original quadratic stress detector is preserved. No composite amplitude, normal,
detector or adjoint bound is assumed.

The derivative reserve is `2 * (n + 1) + 6`, independent of `s`. A primitive
immersion norm at that fixed order and the separate metric/normal gaps determine
all constants before the varying immersion, projected stress or null column.
The one high norm has order `s + 2 * (n + 1) + 6`; any larger common budget works,
including when `s = 0`.

The fixed geometric inputs are explicit. The parent may shrink the retained
coefficient radius to place its closed ball inside the state/phase domain;
nullvector smoothness and norms restrict by `cNorm_mono_set_of_contDiffAt`. It restricts
an open product chart `X × V` into that ball and takes a positive norm radius `σ`
with `12a ≤ σ` inside the product chart. For instance `σ = 12a` and open product
balls of radius `16a` work once the supported chart of radius `32a` lies in the
coefficient ball. `closedBall_chartCenter_subset_supportedChart` and
`exists_supportedChart_flowCylinder_cap`, followed by the retained amplitude
buffer map, give that containment by a further fixed restriction on `a`.
`exists_supportedChart_initialBuffer_cap` supplies the simultaneous flow/scalar
buffer. The parent must instantiate these fixed containments for its same data
using the retained coefficient radius; no extra stress threshold is required.

The nullvector smoothness and bounds are the corresponding projections of
`NullTransport.exists_projected_local_positive_amplitude`; all other terms in
that producer's coefficient sum are nonnegative. `SupportedData` transfers the
component below unchanged to the parent's extended carrier data.

Sources: `app:ch_background:prop:bg-adjoint`, `app:ch_background:eq:bg-T`,
`app:ch_waves:eq:joint-tame`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Metric
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
open ContinuumRow ActualCarriers FrozenMenu CurrentFullPhase NullTransport
open LeadingWave AmbientResponse ProjectedStressFrame DerivativeKernels PhaseExtension

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)

/-- Global smoothness and the exact `C₀` reserve profiles for the ACTUAL canonical
carrier's geometric component. All constants precede the varying data; only a
fixed primitive low norm, one high immersion norm, separate geometric gaps and
the retained nullvector coefficients are used. The scalar and flow are arbitrary
and do not enter this component. This is the geometric input of `bg-adjoint`,
not an unconditional adjoint or existence theorem. -/
theorem exists_carrierChartGeometryComponent_profiles {c C : ℝ} (hP : P.IsValid c C)
    {K : Set (Euclidean n)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hball : closedBall (0 : Euclidean n) T.data.localReference.stateRadius ⊆ K)
    (z : Euclidean 3) {ρ σ a : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (ha : 0 < a)
    (haσ : 12 * a ≤ σ)
    (hx : MapsTo Prod.fst (closedBall ((0 : Euclidean n), z) ρ)
      (closedBall (0 : Euclidean n) T.data.localReference.stateRadius))
    (hcρ : closedBall ((0 : Euclidean n), z) ρ ⊆
      ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius))
    {X : Set (Euclidean n)} {V : Set CarrierParameter}
    (hX : IsOpen X) (hV : IsOpen V) (hXU : X ⊆ U)
    (hσX : closedBall (0 : Euclidean n) σ ⊆ X)
    (hσV : closedBall (chartCenter (n := n) z).2 σ ⊆ V)
    (hσK : closedBall (0 : Euclidean n) σ ⊆ K)
    (hcoef : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (closedBall ((0 : Euclidean n), z) ρ))
    (A : ℕ → ℝ) (hA : ∀ j, 0 < A j)
    {M κmet κ : ℝ} (hM : 0 ≤ M) (hκmet : 0 < κmet) (hκ : 0 < κ) :
    ∀ s : ℕ, ∃ C₀ : Fin n → ℕ → ℝ, (∀ j i, 0 ≤ C₀ j i) ∧
      ∀ (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
        cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
          (Q - fun _ ↦ cubeStress n) < T.family.threshold})
        (F : Euclidean n → Euclidean N), Q.1 = projectedStress F →
      ContDiffOn ℝ ∞ F U → IsImmersionOn F U → HasFullNormalRankOn F U →
      cNorm K (2 * (n + 1) + 6) F ≤ M →
      (∀ x ∈ K, ∀ v, κmet * ‖v‖ ^ 2 ≤ ‖fderiv ℝ F x v‖ ^ 2) →
      (∀ x ∈ K, ∀ w ∈ normalSpace F x,
        κ * ‖w‖ ≤ ‖normalPairing F (fun _ ↦ w) x‖) →
      ∀ col : Fin n,
      (∀ w ∈ closedBall ((0 : Euclidean n), z) ρ,
        ContDiffAt ℝ ∞ (carrierNullvector T Q col) w) →
      (∀ m, cNorm (closedBall ((0 : Euclidean n), z) ρ) m (carrierNullvector T Q col) ≤
        A m * (1 + cNorm K (m + 5) F)) →
      ContDiff ℝ ∞ (extendedGeometricNormal T Q F col z ha) ∧
      ∀ (row : Fin n)
        (Φ Y : ℝ × (Euclidean (n - 1) × Euclidean 3) → Euclidean (n - 1) × Euclidean 3)
        (initial : Euclidean (n - 1) × Euclidean 3 → ℝ) (hcell : 4 * a < 1 / 2)
        (angular : CarrierParameter → Euclidean (n - 1) → ℝ) (high : ℝ → ℝ),
      let d := CanonicalCarrier.data T Q F row col Φ Y initial ha hcell angular high
      let ν := extendedGeometricNormal T Q F col z ha
      (∀ j, ContDiff ℝ ∞ (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j)) ∧
      ∀ H : ℝ, 1 + cNorm K (s + 2 * (n + 1) + 6) F ≤ H →
      ∀ j p, ∀ i ≤ s + 2 * (n + 1),
        ‖iteratedFDeriv ℝ i (carrierChartGeometryComponent d (FixedCutoffs.physical ha 1) ν j) p‖ ≤
          C₀ j i * H ^ (((i - 2 * (n + 1) : ℕ) : ℝ) / (max s 1 : ℕ)) := by
  obtain ⟨B, hB, hb⟩ := exists_physicalGeometryComponent_bounds T (N := N) hP
    hK hKU hball z hρ hσ ha hx hcρ hX hV hXU hσX hσV hσK hcoef A hA hM hκmet hκ
  intro s
  let b := 2 * (n + 1)
  choose C₀ hC₀ hprofile using fun j ↦ exists_closedBall_reserve_profile (F := ℂ)
    (chartCenter (n := n) z) hσ b s (B j b * (1 + M)) (B j (b + s))
  refine ⟨C₀, hC₀, ?_⟩
  intro Q F hQ hF hi hrank hFM hmet hnormal col hnull hnullB
  let L := closedBall (chartCenter (n := n) z) σ
  have hLXV : L ⊆ X ×ˢ V := by
    rw [show L = closedBall (chartCenter z) σ from rfl,
      ← closedBall_prod_same (chartCenter (n := n) z).1 (chartCenter (n := n) z).2 σ]
    exact Set.prod_mono hσX hσV
  have hsuppL : tsupport (chartBump (n := n) z ha) ⊆ L := by
    rw [(chartBump z ha).tsupport_eq]
    exact closedBall_subset_closedBall haσ
  have hc : MapsTo (fun p : Euclidean n × CarrierParameter ↦
      (p.1, CanonicalCarrier.parameter p.2)) (X ×ˢ V)
      (ball (0 : Euclidean n) T.physicalRadius ×ˢ parameterInterior (2 * P.radius)) :=
    fun p hp ↦ hcρ (hcoef hp)
  obtain ⟨hν, hcomponent⟩ := extendedGeometricNormal_and_component_contDiff T Q hP
    hF hi hrank col hX hV hXU hc z ha hcoef (hsuppL.trans hLXV) hnull
  have hlow6 : cNorm K 6 F ≤ M := (cNorm_mono_order (by omega)).trans hFM
  have hbound := hb Q F hQ hF hi hrank hlow6 hmet hnormal col hnull hnullB
  have hglobal (H : ℝ) (hhigh : 1 + cNorm K (s + b + 6) F ≤ H)
      (j : Fin n) (i : ℕ) (hi : i ≤ b + s) (p : Euclidean n × CarrierParameter) :
      ‖iteratedFDeriv ℝ i (physicalGeometryComponent T Q F col z ha j) p‖ ≤
        C₀ j i * H ^ (((i - b : ℕ) : ℝ) / (max s 1 : ℕ)) := by
    have hH : 1 ≤ H := le_trans (by linarith [cNorm_nonneg K (s + b + 6) F]) hhigh
    by_cases hp : p ∈ L
    · have hlo : cNorm L b (physicalGeometryComponent T Q F col z ha j) ≤ B j b * (1 + M) :=
        (hbound j b).trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl 1) hFM) (hB j b).le)
      have hhi : cNorm L (b + s) (physicalGeometryComponent T Q F col z ha j) ≤ B j (b + s) * H := by
        apply (hbound j (b + s)).trans
        apply mul_le_mul_of_nonneg_left _ (hB j (b + s)).le
        simpa only [Nat.add_comm b s] using hhigh
      exact hprofile j _ (hcomponent j) hlo H hH hhi i hi p hp
    · have hz : iteratedFDeriv ℝ i (physicalGeometryComponent T Q F col z ha j) p = 0 := by
        by_contra hn
        exact hp (hsuppL ((physicalGeometryComponent_tsupport_subset T Q F col z ha j)
          (support_iteratedFDeriv_subset i hn)))
      rw [hz, norm_zero]
      exact mul_nonneg (hC₀ j i) (Real.rpow_nonneg (zero_le_one.trans hH) _)
  refine ⟨hν, ?_⟩
  intro row Φ Y initial hcell angular high
  dsimp only
  constructor
  · intro j
    rw [carrierChartGeometryComponent_eq_physicalGeometryComponent]
    exact (hcomponent j).comp (contDiff_snd.prodMk contDiff_fst)
  · intro H hH j p i hi
    rw [carrierChartGeometryComponent_eq_physicalGeometryComponent]
    have hswap := (LinearIsometryEquiv.prodComm ℝ CarrierParameter (Euclidean n)).norm_iteratedFDeriv_comp_right
      (physicalGeometryComponent T Q F col z ha j) p i
    apply hswap.trans_le
    exact hglobal H hH j i (by dsimp [b]; omega) (p.2, p.1)

end JanetCartan.ContinuumAdjoint.Canonical.AmplitudeProfiles
