module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.RawCutoffBounds.Auxiliary
public import JanetCartan.Geometry.IsometricEmbedding.Mean.ContinuumRow.Image
public import JanetCartan.Geometry.IsometricEmbedding.Mean.AuxiliaryRealization.Tangential

/-!
# The ordered auxiliary source and covector

The input of `app:ch_background:eq:bg-Vaux` is arbitrary real torus L² data.
The Fourier square precedes source multiplication, and the Bessel inverse is
literally the operator used by the image channel. The explicit Fourier-series
representative and its physical lift are fixed once, independently of the
Sobolev order. Its smoothness and L² identification are proved in `SmoothCovector`.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace JanetCartan.AuxiliaryRawBand

open ContinuumRow

variable {n N : ℕ}

/-- The smooth ordered source `χ_src π_K² h_im`
(`app:ch_background:eq:bg-Vaux`). -/
def rawSource (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :
    Torus n → Euclidean n :=
  fun x ↦ χsrc x • AuxiliaryRealization.squaredCutoff K h x

/-- The actual L² source, with the raw cutoff first
(`app:ch_background:eq:bg-Vaux`). -/
def rawSourceL2 (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) : OutputL2 n :=
  cutoffMultiplier χsrc (RawCutoffBounds.auxiliarySquaredCutoff K h)

/-- The ordered source has its literal smooth representative
(`app:ch_background:eq:bg-Vaux`). -/
theorem rawSourceL2_coeFn (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :
    rawSourceL2 χsrc K h =ᵐ[volume] rawSource χsrc K h := by
  filter_upwards [cutoffMultiplier_coeFn χsrc
    (RawCutoffBounds.auxiliarySquaredCutoff K h),
    RawCutoffBounds.auxiliarySquaredCutoff_coeFn K h] with x hc hr
  exact hc.trans (congrArg (fun v ↦ χsrc x • v) hr)

/-- Smooth source multiplication follows the finite Fourier cut
(`app:ch_background:eq:bg-Vaux`). -/
theorem isSmoothPeriodic_rawSource (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) :
    IsSmoothPeriodic (rawSource χsrc K h) :=
  ⟨hχ.1.smul (AuxiliaryRealization.isSmoothPeriodic_squaredCutoff K h).1,
    hχ.2.smul (AuxiliaryRealization.isSmoothPeriodic_squaredCutoff K h).2⟩

/-- Literal chart agreement for the ordered source, with no change of measure
(`app:ch_background:eq:bg-Vaux`). -/
theorem periodicLift_rawSource (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :
    periodicLift (rawSource χsrc K h) =
      AuxiliaryRealization.sourceCutInput (periodicLift χsrc) K h := rfl

/-- The covector at the H¹ level used by the actual image channel
(`app:ch_background:eq:bg-Vaux`). -/
def rawCovectorH1 (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :
    PeriodicSobolevSpace n (Euclidean n) 1 :=
  periodicBesselLift (rawSourceL2 χsrc K h)

/-- The underlying covector is the same Bessel inverse at every order
(`app:ch_background:eq:bg-Vaux`). -/
def rawCovectorL2 (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) : OutputL2 n :=
  periodicBesselInverse (rawSourceL2 χsrc K h)

/-- Compatibility of the H¹ and L² covectors (`app:ch_background:eq:bg-Vaux`). -/
@[simp] theorem toL2_rawCovectorH1 (χsrc : C(Torus n, ℝ)) (K : ℝ)
    (h : OutputL2 n) :
    PeriodicSobolevSpace.toL2 1 (rawCovectorH1 χsrc K h) = rawCovectorL2 χsrc K h :=
  toL2_periodicBesselLift _

/-- One fixed Fourier-series representative, never chosen anew at each order
(`app:ch_background:eq:bg-Vaux`). `SmoothCovector` proves smoothness and
agreement with `rawCovectorL2`. -/
def rawCovector (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :
    Torus n → Euclidean n := fun x ↦
  ∑' k : Fin n → ℤ, periodicBesselSymbol k •
    periodicFourierModeOfParts k (periodicFourierCoeff (rawSource χsrc K h) k).1
      (periodicFourierCoeff (rawSource χsrc K h) k).2 x

/-- The unique ordered physical field, including the final physical cutoff and
literal half tangent lift (`app:ch_background:eq:bg-Vaux`). -/
def physicalField (G : Euclidean n → Euclidean N) (χout : Euclidean n → ℝ)
    (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) : Euclidean n → Euclidean N :=
  fun x ↦ χout x • AuxiliaryRealization.tangentialField G
    (periodicLift (rawCovector χsrc K h)) x

/-- The full geometric strain of the same physical field, including cutoff
derivatives (`app:ch_background:prop:bg-mixed-physical`). -/
def physicalStrain (G : Euclidean n → Euclidean N) (χout : Euclidean n → ℝ)
    (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n) :=
  linearizedMetric G (physicalField G χout χsrc K h)

/-- The ordered source is bounded from arbitrary L² data, uniformly in `K ≥ 1`
(`app:ch_background:eq:bg-Vaux-raw-band`, order zero). -/
theorem norm_rawSourceL2_le (χsrc : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K)
    (h : OutputL2 n) : ‖rawSourceL2 χsrc K h‖ ≤ ‖χsrc‖ * ‖h‖ := by
  have hcut : ‖RawCutoffBounds.auxiliarySquaredCutoff K h‖ ≤ ‖h‖ := by
    have hb := RawCutoffBounds.auxiliarySquaredCutoff_band hK h 0
    simpa only [pow_zero, one_mul, (periodicSobolevScale n (Euclidean n)).gradeNorm_zero] using hb
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul (cutoffMultiplier_norm_le χsrc) hcut (norm_nonneg _) (norm_nonneg _))

/-- The source-to-covector step gains the derivative needed for the full strain
without any regularity assumption on the raw datum
(`app:ch_background:eq:bg-Vaux-raw-band`, order zero). -/
theorem norm_rawCovectorH1_le (χsrc : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K)
    (h : OutputL2 n) : ‖rawCovectorH1 χsrc K h‖ ≤ ‖χsrc‖ * ‖h‖ := by
  rw [rawCovectorH1, norm_periodicBesselLift]
  exact norm_rawSourceL2_le χsrc hK h

/-- L² bound for the same covector (`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem norm_rawCovectorL2_le (χsrc : C(Torus n, ℝ)) {K : ℝ} (hK : 1 ≤ K)
    (h : OutputL2 n) : ‖rawCovectorL2 χsrc K h‖ ≤ ‖χsrc‖ * ‖h‖ :=
  (norm_periodicBesselInverse_apply_le _).trans (norm_rawSourceL2_le χsrc hK h)

/-- Every smooth source level represents the same ordered L² source
(`app:ch_background:eq:bg-Vaux`). -/
theorem toL2_ofSmooth_rawSource (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) (s : ℕ) :
    PeriodicSobolevSpace.toL2 s (PeriodicSobolevSpace.ofSmooth s
      (rawSource χsrc K h) (isSmoothPeriodic_rawSource χsrc hχ K h)) =
        rawSourceL2 χsrc K h := by
  apply Lp.ext
  exact (PeriodicSobolevSpace.toL2_ofSmooth_ae _ _ _).trans (rawSourceL2_coeFn _ _ _).symm

/-- All higher Bessel gains have the same underlying covector; this supplies
the common input to every field/strain estimate (`app:ch_background:eq:bg-Vaux`). -/
theorem toL2_gain_rawSource (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) (s : ℕ) :
    PeriodicSobolevSpace.toL2 (s + 1) (periodicBesselGain s
      (PeriodicSobolevSpace.ofSmooth s (rawSource χsrc K h)
        (isSmoothPeriodic_rawSource χsrc hχ K h))) = rawCovectorL2 χsrc K h := by
  rw [toL2_periodicBesselGain, toL2_ofSmooth_rawSource χsrc hχ K h s]
  rfl

/-- Actual Sobolev membership of the ordered Bessel output at every order,
before choosing a smooth representative (`app:ch_background:eq:bg-Vaux`). -/
theorem rawCovectorL2_mem_succ (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) (s : ℕ) :
    rawCovectorL2 χsrc K h ∈ periodicSobolevLevel n (Euclidean n) (s + 1) := by
  rw [← toL2_gain_rawSource χsrc hχ K h s]
  exact PeriodicSobolevSpace.toL2_mem _ _

/-- Exact one-order norm gain for this particular ordered source; downstream
product estimates must bound the source rather than assuming an auxiliary
operator bound (`app:ch_background:eq:bg-Vaux-raw-band`). -/
theorem norm_gain_rawSource (χsrc : C(Torus n, ℝ))
    (hχ : IsSmoothPeriodic (χsrc : Torus n → ℝ)) (K : ℝ) (h : OutputL2 n) (s : ℕ) :
    ‖periodicBesselGain s (PeriodicSobolevSpace.ofSmooth s (rawSource χsrc K h)
      (isSmoothPeriodic_rawSource χsrc hχ K h))‖ =
        periodicSobolevNorm s (rawSource χsrc K h) := by
  rw [norm_periodicBesselGain, PeriodicSobolevSpace.norm_eq]
  simp only [periodicSobolevNorm,
    periodicFourierCoeff_congr_ae (PeriodicSobolevSpace.toL2_ofSmooth_ae _ _ _)]

/-- Exact coefficients of the ordered L² covector, used to identify its single
Fourier-series representative (`app:ch_background:eq:bg-Vaux`). -/
theorem rawCovectorL2_coeff (χsrc : C(Torus n, ℝ)) (K : ℝ) (h : OutputL2 n)
    (k : Fin n → ℤ) :
    periodicL2FourierCoeff k (rawCovectorL2 χsrc K h) =
      periodicBesselSymbol k • periodicL2FourierCoeff k (rawSourceL2 χsrc K h) :=
  periodicL2FourierCoeff_besselInverse _ _

end JanetCartan.AuxiliaryRawBand
