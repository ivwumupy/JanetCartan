module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.MeasuredAmplitude.SupportedNormal
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.MaskProfiles.Detector

/-!
# Global coefficients for the actual measured sampling kernel

`RawKernel.bandKernelData` needs globally continuous phase and carrier maps.
The retained Hamilton fields are smooth on their original buffered domains.
These explicit extensions agree there, and the measured polynomial already
has its fixed compact extension. No new phase, minor or transport solution is
selected. The consumers are the actual kernel construction and its literal
raw integral identification (`app:ch_waves:eq:sampling-prefix-normal`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.Sampling.MeasuredAmplitude
open ActualCarriers FrozenMenu CurrentFullPhase LeadingWave.FullModulation RawKernel
open FullPhaseCharts.ActualPhase

private theorem contDiff_cutoff_extension
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a : E} (b : ContDiffBump a) {O : Set E} (hO : IsOpen O)
    (hb : closedBall a b.rOut ⊆ O) {f : E → V} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiff ℝ ∞ (fun x ↦ b x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ closedBall a b.rOut
  · exact b.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds (hb hx)))
  · have hz : (b : E → ℝ) =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (by simpa only [b.tsupport_eq] using hx)
    apply (contDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [Pi.zero_apply] at hy
    simp only [hy, zero_smul]

variable {m N : ℕ}
variable {P : Patch (m + 1)} {U : Set (Euclidean (m + 1))} {hU : IsOpen U}
  (T : PatchQuantitativeFamily P U hU)
  (Q : {Q : Euclidean (m + 1) → Fin (m + 1) → MetricTensor (m + 1) //
    ContDiffOn ℝ ∞ Q U ∧
    cNorm (closedBall (0 : Euclidean (m + 1)) T.data.localReference.stateRadius) 6
      (Q - fun _ ↦ cubeStress (m + 1)) < T.family.threshold})

/-- Fixed full-phase cutoff, equal to one on the complete retained phase
domain and supported inside its proved smooth enlargement
(`app:ch_waves:setup:oscillatory`). -/
def retainedPhaseCutoff : ContDiffBump ((0 : Euclidean (m + 1)), covectorCenter T) :=
  ⟨T.family.radius, 3 * T.family.radius / 2, T.family.radius_pos,
    by linarith [T.family.radius_pos]⟩

/-- The SAME Hamilton phase with a global smooth extension. Its value on
`phaseDomain T` is unchanged (`app:ch_waves:eq:sampling-prefix-normal`). -/
def extendedRetainedPhase (x : Euclidean (m + 1)) (ξ : Euclidean ((m + 1) - 1)) : ℝ :=
  retainedPhaseCutoff T (x, ξ) * phase T Q x ξ

/-- Global smoothness required by the literal `BandKernelData` constructor
is proved from the Hamilton phase, rather than assumed
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem contDiff_extendedRetainedPhase :
    ContDiff ℝ ∞ (Function.uncurry (extendedRetainedPhase T Q)) := by
  exact contDiff_cutoff_extension (retainedPhaseCutoff T) isOpen_ball
    (closedBall_subset_ball (by
      change 3 * T.family.radius / 2 < 2 * T.family.radius
      linarith [T.family.radius_pos])) (phase_smooth T Q)

/-- Pointwise agreement on the original full phase domain, with no change
to the current Hamilton chart (`app:ch_waves:setup:oscillatory`). -/
theorem extendedRetainedPhase_eq {x : Euclidean (m + 1)} {ξ : Euclidean ((m + 1) - 1)}
    (h : (x, ξ) ∈ phaseDomain T) : extendedRetainedPhase T Q x ξ = phase T Q x ξ := by
  rw [extendedRetainedPhase, (retainedPhaseCutoff T).one_of_mem_closedBall
    (ball_subset_closedBall h), one_mul]

/-- Carrier cutoff on the SAME retained raw cell
(`app:ch_waves:eq:individual-representation`). -/
def retainedCarrierCutoff (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ) : ContDiffBump z₀ :=
  ⟨ρ, 3 * ρ / 2, hρ, by linarith⟩

/-- Global extension of the original frozen carrier covector. This is used
only to make the sampling kernel globally continuous; its value on the raw
amplitude support is unchanged (`app:ch_waves:eq:sampling-prefix-normal`). -/
def extendedRetainedCarrier (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (z : Euclidean 3) : Euclidean ((m + 1) - 1) :=
  retainedCarrierCutoff z₀ hρ z • T.reference.spatialPatch z

/-- Smoothness of the explicit carrier extension follows from the original
patch smoothness on its buffered neighborhood
(`app:ch_waves:setup:oscillatory`). -/
theorem contDiff_extendedRetainedCarrier {c C : ℝ} (hP : P.IsValid c C)
    (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (hz : closedBall z₀ (2 * ρ) ⊆ parameterInterior (2 * P.radius)) :
    ContDiff ℝ ∞ (extendedRetainedCarrier T z₀ hρ) := by
  apply contDiff_cutoff_extension (retainedCarrierCutoff z₀ hρ)
    (isOpen_parameterInterior _)
    ((closedBall_subset_closedBall (by dsimp [retainedCarrierCutoff]; linarith)).trans hz)
  exact T.reference.spatialPatch_smooth hP

/-- The carrier extension agrees on every retained raw cell
(`app:ch_waves:eq:individual-representation`). -/
theorem extendedRetainedCarrier_eq (z₀ : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    {z : Euclidean 3} (hz : z ∈ closedBall z₀ ρ) :
    extendedRetainedCarrier T z₀ hρ z = T.reference.spatialPatch z := by
  rw [extendedRetainedCarrier, (retainedCarrierCutoff z₀ hρ).one_of_mem_closedBall hz,
    one_smul]

variable (F : Euclidean (m + 1) → Euclidean N) (row col : Fin (m + 1))
  (Φ Y : ℝ × (Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) →
    Euclidean ((m + 1) - 1) × (Euclidean 3 × Euclidean ((m + 1) - 1)))
  (r : Euclidean ((m + 1) - 1) × Euclidean 3 → ℝ)
  (measurement : Euclidean (m + 1) → Matrix (Fin N) (Fin (m + 1)) ℂ →L[ℂ] EuclideanSpace ℂ (Fin (m + 1)))
  (χ : Euclidean (m + 1) → ℝ)
  (a : Euclidean (m + 1) × (Euclidean 3 × Euclidean ((m + 1) - 1))) {ρ : ℝ} (hρ : 0 < ρ)

/-- A nonzero extended measured coefficient is inside the original raw
cutoff's support. This gives both the physical support and the carrier
plateau needed by the actual kernel (`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem supportedMeasuredDerivativePolynomial_mem_ball
    {τ : ℝ} {z : Euclidean 3} {x : Euclidean (m + 1)} {ξ : Euclidean ((m + 1) - 1)}
    (h : supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
      τ z x ξ ≠ 0) : (x, (z, ξ)) ∈ ball a (3 * ρ / 4) := by
  have hc : retainedAmplitudeCutoff a hρ (x, (z, ξ)) ≠ 0 := by
    intro hc
    apply h
    simp only [supportedMeasuredDerivativePolynomial, hc, zero_smul]
  have hm : (x, (z, ξ)) ∈ Function.support (retainedAmplitudeCutoff a hρ) := hc
  rw [ContDiffBump.support_eq] at hm
  exact hm

/-- Fixed physical support of the actual extended measured coefficient,
independent of the carrier, frequency, color and band count
(`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem supportedMeasuredDerivativePolynomial_eq_zero_off_physical
    (τ : ℝ) (z : Euclidean 3) (x : Euclidean (m + 1)) (ξ : Euclidean ((m + 1) - 1))
    (hx : x ∉ closedBall a.1 ρ) :
    supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
      τ z x ξ = 0 := by
  by_contra hn
  have hw := supportedMeasuredDerivativePolynomial_mem_ball T Q F row col Φ Y r
    measurement χ a hρ hn
  rw [← ball_prod_same] at hw
  exact hx (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hw.1))

/-- The small raw covector displacement stays in the SAME extension plateau.
This is the unnormalized version of the band homotopy's support calculation
(`app:ch_waves:setup:oscillatory`). -/
theorem retained_shift_mem_plateau {z : Euclidean 3} {x : Euclidean (m + 1)}
    {d : Euclidean (m + 1 - 1)}
    (hx : x ∈ closedBall a.1 (ρ / 2))
    (hz : (z, T.reference.spatialPatch z) ∈ closedBall a.2 (ρ / 4))
    (hd : ‖d‖ ≤ ρ / 4) :
    (x, (z, T.reference.spatialPatch z + d)) ∈ closedBall a (ρ / 2) := by
  have hρ' : 0 ≤ ρ := by linarith [norm_nonneg d]
  rw [← closedBall_prod_same] at hz ⊢
  refine ⟨hx, ?_⟩
  rw [← closedBall_prod_same]
  refine ⟨closedBall_subset_closedBall (by linarith) hz.1, ?_⟩
  rw [mem_closedBall_iff_norm]
  calc
    ‖T.reference.spatialPatch z + d - a.2.2‖ =
        ‖(T.reference.spatialPatch z - a.2.2) + d‖ := by congr 1; abel
    _ ≤ ‖T.reference.spatialPatch z - a.2.2‖ + ‖d‖ := norm_add_le _ _
    _ ≤ ρ / 4 + ρ / 4 := add_le_add (mem_closedBall_iff_norm.mp hz.2) hd
    _ = ρ / 2 := by ring

/-- On the measured raw field the fixed polynomial extension can be removed
pointwise, including at zero inverse frequency
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem supportedMeasuredDerivativePolynomial_eq_raw
    (hχ : Function.support χ ⊆ closedBall a.1 (ρ / 2))
    {z : Euclidean 3}
    (hz : (z, T.reference.spatialPatch z) ∈ closedBall a.2 (ρ / 4))
    (τ : ℝ) (x : Euclidean (m + 1)) (η : Euclidean (m + 1 - 1))
    (hd : ‖τ • η‖ ≤ ρ / 4) :
    supportedMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ a hρ
      τ z x (T.reference.spatialPatch z + τ • η) =
      fullMeasuredDerivativePolynomial T Q F row col Φ Y r measurement χ
        τ z x (T.reference.spatialPatch z + τ • η) := by
  by_cases hx : χ x = 0
  · simp only [supportedMeasuredDerivativePolynomial, fullMeasuredDerivativePolynomial,
      hx, Complex.ofReal_zero, zero_smul, smul_zero]
  · rw [supportedMeasuredDerivativePolynomial,
      retainedAmplitudeCutoff_one a hρ (retained_shift_mem_plateau T a (hχ hx) hz hd),
      one_smul]

include hρ in
/-- The explicit global phase has exactly the original raw quotient on the
common measured buffer. Both evaluations of the full phase are retained;
the quotient is not replaced by its principal approximation
(`app:ch_waves:eq:sampling-prefix-normal`). -/
theorem extendedRetainedPhase_difference_eq
    (hphase : closedBall a (2 * ρ) ⊆ domain T)
    {z : Euclidean 3} {x : Euclidean (m + 1)}
    (hx : x ∈ closedBall a.1 (ρ / 2))
    (hz : (z, T.reference.spatialPatch z) ∈ closedBall a.2 (ρ / 4))
    (τ : ℝ) (η : Euclidean (m + 1 - 1)) (hd : ‖τ • η‖ ≤ ρ / 4) :
    rawPrimaryPhaseDifference (extendedRetainedPhase T Q) (T.reference.spatialPatch z)
      τ x η = rawPrimaryPhaseDifference (phase T Q) (T.reference.spatialPatch z) τ x η := by
  have hpoint' : (x, (z, T.reference.spatialPatch z + τ • η)) ∈ domain T :=
    hphase (closedBall_subset_closedBall (by linarith)
      (retained_shift_mem_plateau T a hx hz hd))
  have hpoint : (x, T.reference.spatialPatch z + τ • η) ∈ phaseDomain T := hpoint'
  have hbase : (x, T.reference.spatialPatch z) ∈ phaseDomain T := by
    have hh : (x, (z, T.reference.spatialPatch z + 0)) ∈ domain T :=
      hphase (closedBall_subset_closedBall (by linarith : ρ / 2 ≤ 2 * ρ)
        (retained_shift_mem_plateau T a hx hz (d := 0) (by simp; positivity)))
    change (x, T.reference.spatialPatch z + 0) ∈ phaseDomain T at hh
    simpa only [add_zero] using hh
  simp only [rawPrimaryPhaseDifference, extendedRetainedPhase_eq T Q hpoint,
    extendedRetainedPhase_eq T Q hbase]

end JanetCartan.Sampling.MeasuredAmplitude
