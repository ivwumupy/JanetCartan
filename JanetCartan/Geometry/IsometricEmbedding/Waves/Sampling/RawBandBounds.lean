module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.RawKernel
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.WideBandIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.BandOperator
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.SliceBounds.CoordinateTransfer.Coordinates

/-!
# Matching the sampling bands to the actual raw slice integral

The SAME measured amplitude, detector, radial band, half derivative and Fourier
scalar occur on both sides. These identities are the connection needed to
apply the sharp slice estimate to `hband` in
`exists_threshold_refinedKernelPrefix_realization`. The actual raw-family
primitive normal data and its common budgets still require their producer.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set

namespace JanetCartan.Sampling.RawKernel
open SamplingKernelBounds RawInputPartition NormalComparison MeanNormalBound
open MeanNormalBound.NormalizedFullPhase RawPrimary.SliceBounds

variable {n J : ℕ} {P : Type*} [TopologicalSpace P]
  [FirstCountableTopology P] [LocallyCompactSpace P]

section Constructed

variable
    (S : P → Euclidean n → Euclidean (n - 1) → ℝ)
    (A : P → Euclidean n → Euclidean (n - 1) → EuclideanSpace ℂ (Fin n))
    (ζ : P → Euclidean (n - 1)) (τ : P → ℝ) (d : Euclidean (n - 1) → ℂ)
    (hS : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      S q.1.1 q.1.2 q.2))
    (hA : Continuous (fun q : (P × Euclidean n) × Euclidean (n - 1) ↦
      A q.1.1 q.1.2 q.2))
    (hζ : Continuous ζ) (hτ : Continuous τ) (hτ₀ : ∀ p, τ p ≠ 0)
    (hd : Continuous d) (K : Set (Euclidean n)) (hK : IsCompact K)
    (hAK : ∀ p x η, x ∉ K → A p x η = 0)
    (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hAM : ∀ p x η, ‖A p x η‖ ≤ M) (hdB : ∀ η, ‖d η‖ ≤ B)

local notation "D" => bandKernelData (J := J) S A ζ τ d hS hA hζ hτ hτ₀ hd
  K hK hAK M B hM hB hAM hdB

omit [FirstCountableTopology P] [LocallyCompactSpace P] in
/-- Exact pointwise kernel matching to the original measured raw summand.
The smooth radial mask is retained; no sharp restriction is part of the
amplitude (`app:ch_waves:eq:individual-raw-slice`). -/
theorem bandKernelData_kernel (j : Fin J) (p : P)
    (x : Euclidean n) (η : Euclidean (n - 1)) :
    (D).kernel (j, p) η x =
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) : ℝ) •
        ((Real.sqrt ‖η‖ : ℂ) * weightedRadialBand d j.val η) •
          (Complex.exp (Complex.I * (rawPrimaryPhaseDifference (S p) (ζ p) (τ p) x η : ℂ)) •
            A p x (ζ p + τ p • η)) := by
  simp only [BandKernelData.kernel, bandKernel, bandKernelData, measuredBandAmplitude,
    weightedRadialBand, RCLike.real_smul_eq_coe_smul (K := ℂ),
    Complex.ofReal_mul, smul_smul]
  congr 1
  ac_rfl

/-- Actual forward action of the constructed wide sampling band. The
representative is the original raw integral with its explicit physical
Fourier normalization (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem bandKernelData_wideOperator_ae_rawIntegral
    (j : Fin J) (p : P) (f : WideBandL2 n j.val) :
    wideBandKernelOperator D j.val (j, p) f =ᵐ[volume] fun x ↦
      (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        rawSliceBandIntegral (n := n) (S p) (A p) (fun _ ↦ 1) (ζ p) (τ p)
          (weightedRadialBand d j.val) j.val f x := by
  have h := wideBandKernelOperator_ae_integral D j.val (j, p) (fun η hη x ↦ by
    simp only [BandKernelData.kernel, bandKernel]
    change _ • measuredBandAmplitude A ζ τ (((j, p), η), x) = 0
    rw [measuredBandAmplitude_eq_zero_off_wideBand A ζ τ j p η x hη, smul_zero]) f
  refine h.trans (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [rawSliceBandIntegral, Complex.ofReal_one, one_smul, rawPrimaryDemodulatedIntegral]
  rw [← integral_smul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun η hη ↦ by
    rw [bandKernelData_kernel]
    simp [weightedRadialBand_eq_zero_off_wideBand d hη])]
  apply integral_congr_ae
  filter_upwards [] with η
  rw [bandKernelData_kernel]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  congr 1
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- The actual wide sampling operator is the physical transfer of any slice
operator realizing the SAME raw integral. This is an equality of bounded maps,
not an assumed kernel or normal identity. The slice producer supplies `hR`
by its proved integral formula (`app:ch_waves:eq:individual-raw-slice`). -/
theorem bandKernelData_wideOperator_eq_adapted
    {ξ : Euclidean n} (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)
    (j : Fin J) (p : P)
    (R : WideBandL2 n j.val →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin n)) 2 (volume : Measure (ℝ × Euclidean (n - 1))))
    (hR : ∀ f, R f =ᵐ[volume] fun q ↦
      (2 * Real.pi) ^ (-(n : ℝ) / 2) •
        rawSliceBandIntegral (n := n)
          (fun q η ↦ S p (adaptedPhysicalCoordinates sec q) η)
          (fun q η ↦ A p (adaptedPhysicalCoordinates sec q) η)
          (fun _ ↦ 1) (ζ p) (τ p) (weightedRadialBand d j.val) j.val f q) :
    wideBandKernelOperator D j.val (j, p) =
      (adaptedL2Equiv sec (EuclideanSpace ℂ (Fin n))).toContinuousLinearEquiv.toContinuousLinearMap.comp R := by
  ext1 f
  apply Lp.ext
  filter_upwards [bandKernelData_wideOperator_ae_rawIntegral S A ζ τ d hS hA hζ hτ hτ₀ hd
    K hK hAK M B hM hB hAM hdB j p f,
    adaptedL2Equiv_coeFn sec (EuclideanSpace ℂ (Fin n)) (R f),
    (adaptedPhysicalCoordinates_symm_measurePreserving sec).quasiMeasurePreserving.ae (hR f)]
    with x hx hy hz
  change _ = adaptedL2Equiv sec (EuclideanSpace ℂ (Fin n)) (R f) x
  rw [hx, hy, Function.comp_apply, hz]
  simp only [rawSliceBandIntegral, rawPrimaryDemodulatedIntegral, rawPrimaryPhaseDifference,
    MeasurableEquiv.apply_symm_apply]

end Constructed
/-- A single constant from the proved slice theorem controls the literal
constructed sampling kernel and both sharp refinements. It is chosen before
the band ceiling, coefficients, carrier labels and primitive slice data. The
phase/amplitude equations below concern those primitive data, not operator
matching or an assumed sharp bound. The actual `RawPrimary` family must still
supply these SAME data and common budgets before the sampling theorem is
complete (`app:ch_waves:eq:sampling-operator-bounds`). -/
theorem exists_bandKernelData_sharp_bound {m : ℕ} {ξ : Euclidean (m + 1)}
    (sec : ActualCarriers.FrozenPhaseReference.AdaptedSection ξ)
    (G : UniformNormalGeometry m (m + 1)) (C : ℕ → ℝ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ C_op > 0, ∀ (J : ℕ)
      (S : P → Euclidean (m + 1) → Euclidean m → ℝ)
      (A : P → Euclidean (m + 1) → Euclidean m → EuclideanSpace ℂ (Fin (m + 1)))
      (ζ : P → Euclidean m) (τ : P → ℝ) (d : Euclidean m → ℂ)
      (hS : Continuous (fun q : (P × Euclidean (m + 1)) × Euclidean m ↦ S q.1.1 q.1.2 q.2))
      (hA : Continuous (fun q : (P × Euclidean (m + 1)) × Euclidean m ↦ A q.1.1 q.1.2 q.2))
      (hζ : Continuous ζ) (hτ : Continuous τ) (hτ₀ : ∀ p, τ p ≠ 0)
      (hd : Continuous d) (K : Set (Euclidean (m + 1))) (hK : IsCompact K)
      (hAK : ∀ p x η, x ∉ K → A p x η = 0)
      (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
      (hAM : ∀ p x η, ‖A p x η‖ ≤ M) (hdB : ∀ η, ‖d η‖ ≤ B),
      (∀ x ∈ K, ((adaptedPhysicalCoordinates sec).symm x).1 ∈ Ioo a b) →
      ∀ (j : Fin J) (p : P) (F : (t : ℝ) → t ∈ Ioo a b → UniformNormalData G C),
      τ p * (2 : ℝ) ^ j.val ∈ Icc 0 G.ε₀ →
      let S₀ := fun q η ↦ S p (adaptedPhysicalCoordinates sec q) η
      let A₀ := fun q η ↦ A p (adaptedPhysicalCoordinates sec q) η
      let amp := rawSliceBandAmplitude (n := m + 1) A₀ (fun _ ↦ 1) (ζ p) (τ p)
        (weightedRadialBand (n := m + 1) d j.val) j.val
      (∀ t (ht : t ∈ Ioo a b) y u,
        rawPrimaryPhaseDifference S₀ (ζ p) (τ p * (2 : ℝ) ^ j.val) (t, y) u =
          (F t ht).phase (τ p * (2 : ℝ) ^ j.val) y u) →
      (∀ t (ht : t ∈ Ioo a b) y u i,
        amp (t, y) u i = (F t ht).amplitude (τ p * (2 : ℝ) ^ j.val) y u i) →
      let D := bandKernelData (J := J) S A ζ τ d hS hA hζ hτ hτ₀ hd
        K hK hAK M B hM hB hAM hdB
      ‖wideBandKernelOperator D j.val (j, p)‖ ^ 2 ≤ C_op * (2 : ℝ) ^ j.val ∧
      ∀ q : Fin 2, ‖D.operator (refinedRadius (j, q)) (j, p)‖ ^ 2 ≤
        C_op * refinedRadius (j, q) := by
  obtain ⟨C_op, hC_op, hband⟩ := exists_rawSliceBandOperator G C a b hab
  refine ⟨C_op, hC_op, ?_⟩
  intro J S A ζ τ d hS hA hζ hτ hτ₀ hd K hK hAK M B hM hB hAM hdB
    htime j p F hε S₀ A₀ amp hphase hamp D
  have hc : Continuous (adaptedPhysicalCoordinates sec) := by
    change Continuous (fun q : ℝ × Euclidean m ↦ q.1 • sec.normal + sec.embedding q.2)
    fun_prop
  have ha : Continuous (Function.uncurry amp) := by
    have hAc : Continuous (fun q : (ℝ × Euclidean m) × Euclidean m ↦
        A p (adaptedPhysicalCoordinates sec q.1) (ζ p + (τ p * (2 : ℝ) ^ j.val) • q.2)) :=
      hA.comp (f := fun q : (ℝ × Euclidean m) × Euclidean m ↦
        ((p, adaptedPhysicalCoordinates sec q.1), ζ p + (τ p * (2 : ℝ) ^ j.val) • q.2))
        (by fun_prop)
    have hr : Continuous (radialBand (m + 1) j.val) :=
      (contDiff_radialBand (m + 1) j.val (r := 0)).continuous
    dsimp only [amp, rawSliceBandAmplitude, Function.uncurry_def, A₀]
    simp only [weightedRadialBand, Complex.ofReal_one, one_mul]
    exact ((Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp continuous_snd.norm)).mul
      ((hd.mul (Complex.continuous_ofReal.comp hr)).comp
        (show Continuous (fun q : (ℝ × Euclidean m) × Euclidean m ↦
          (2 : ℝ) ^ j.val • q.2) from by fun_prop))).smul hAc
  have ht : ∀ t ∉ Ioo a b, ∀ (y u : Euclidean m), amp (t, y) u = 0 := by
    intro t ht y u
    have hx : adaptedPhysicalCoordinates sec (t, y) ∉ K := by
      intro hx
      apply ht
      simpa only [MeasurableEquiv.symm_apply_apply] using htime _ hx
    change _ • A p (adaptedPhysicalCoordinates sec (t, y))
      (ζ p + (τ p * (2 : ℝ) ^ j.val) • u) = 0
    rw [hAK p _ _ hx, smul_zero]
  have hs : HasCompactSupport (Function.uncurry amp) := by
    apply HasCompactSupport.intro ((isCompact_Icc.prod G.compact_X₀).prod G.compact_D₀)
    intro q hq
    rcases q with ⟨⟨t, y⟩, u⟩
    by_cases htab : t ∈ Ioo a b
    · have hnot : (y, u) ∉ G.X₀ ×ˢ G.D₀ := fun h ↦
        hq ⟨⟨⟨htab.1.le, htab.2.le⟩, h.1⟩, h.2⟩
      have hz : (F t htab).amplitude (τ p * (2 : ℝ) ^ j.val) y u = 0 := by
        by_contra hn
        exact hnot ((F t htab).amplitude_support _ hε hn)
      apply PiLp.ext
      intro i
      change amp (t, y) u i = 0
      rw [hamp t htab, hz]
      rfl
    · exact ht t htab y u
  have hp : Continuous (Function.uncurry
      (rawPrimaryPhaseDifference S₀ (ζ p) (τ p * (2 : ℝ) ^ j.val))) := by
    have hleft : Continuous (fun q : (ℝ × Euclidean m) × Euclidean m ↦
        S p (adaptedPhysicalCoordinates sec q.1) (ζ p + (τ p * (2 : ℝ) ^ j.val) • q.2)) :=
      hS.comp (f := fun q : (ℝ × Euclidean m) × Euclidean m ↦
        ((p, adaptedPhysicalCoordinates sec q.1), ζ p + (τ p * (2 : ℝ) ^ j.val) • q.2))
        (by fun_prop)
    have hright : Continuous (fun q : (ℝ × Euclidean m) × Euclidean m ↦
        S p (adaptedPhysicalCoordinates sec q.1) (ζ p)) :=
      hS.comp (f := fun q : (ℝ × Euclidean m) × Euclidean m ↦
        ((p, adaptedPhysicalCoordinates sec q.1), ζ p)) (by fun_prop)
    exact (hleft.sub hright).div_const _
  obtain ⟨R, hR, hnorm, _⟩ := hband j.val (τ p) (hτ₀ p) F hε S₀ A₀
    (fun _ ↦ 1) (ζ p) (weightedRadialBand (n := m + 1) d j.val)
    (fun η hη ↦ weightedRadialBand_eq_zero_off_wideBand (n := m + 1) d hη)
    ha hs (fun q _ ↦ hp.continuousAt) ht hphase hamp
  have he := bandKernelData_wideOperator_eq_adapted S A ζ τ d hS hA hζ hτ hτ₀ hd
    K hK hAK M B hM hB hAM hdB sec j p R hR
  have hb : ‖wideBandKernelOperator D j.val (j, p)‖ ^ 2 ≤ C_op * (2 : ℝ) ^ j.val := by
    rw [he, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp]
    exact hnorm
  refine ⟨hb, ?_⟩
  intro q
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_annularOperator_le_wideBand D j.val (j, p) q) 2).trans
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ hC_op.le
  exact pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _)

end JanetCartan.Sampling.RawKernel
