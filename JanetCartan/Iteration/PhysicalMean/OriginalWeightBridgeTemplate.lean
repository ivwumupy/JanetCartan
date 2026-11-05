module

public import JanetCartan.Iteration.PhysicalMean.CanonicalSource
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.WholeSource
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.OriginalConicMasks
public import JanetCartan.Iteration.PhysicalSampling.OriginalExternalWeights
public import JanetCartan.Iteration.PhysicalSampling.ParameterCutoff
public import JanetCartan.Iteration.PhysicalSamplingShells.Native
public import JanetCartan.Geometry.IsometricEmbedding.Waves.Sampling.BackgroundQuadrature.Enumeration
public import JanetCartan.Geometry.IsometricEmbedding.Waves.SamplingRealization.Family
public meta import JanetCartan.Iteration.PhysicalInitialization.OriginalProtectedTemplate

/-!
# Restore the original carrier factor in the complete physical source

Consumers: the outer-weight original application and
`app:ch_mean_pairs:eq:mean-current-canonical`. The carrier factor acts on the
FULL raw Fourier density before the fixed whole-source response. The original
positive initial scalar and the unmodulated zero atom are not scaled. In
particular, restoring the factor in both Graw and the measured component A
scales D=Graw A* Q₀ by its SQUARE, not by the factor itself. No inverse weight,
new inverse, shell-diagonal replacement or cancellation premise occurs here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set MeasureTheory Metric NormedSpace
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.PhysicalMean.OriginalWeightBridge
open RawInputPartition RawPrimary CanonicalAtomRealization
open ActualCarriers FrozenMenu CurrentFullPhase CurrentMean CanonicalChange
open SmoothPeriodicFamily ContinuumRow CanonicalCarrier

/-- The carrier factor multiplies the WHOLE original Fourier density, retaining
`√‖η‖`, every smooth radial band and the original raw representatives, including
zero factors (`app:ch_mean_pairs:defn:mean-wave-input`). -/
theorem weightedWideDensity_carrierFactor {n J : ℕ} (a : ℝ)
    (d : Euclidean (n-1) → ℂ) (v : WideInput n J) (η : Euclidean (n-1)) :
    weightedWideDensity (fun ξ ↦ (a : ℂ)*d ξ) v η =
      (a : ℂ)*weightedWideDensity d v η := by
  simp only [weightedWideDensity, weightedRadialBand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

open Sampling CanonicalConic

private theorem original_mask_factor {n : ℕ} (zRoot : Euclidean 3)
    {ρ rη : ℝ} (hρ : 0 < ρ) {ηb : Euclidean (n-1)}
    (hηb : ηb ≠ 0) (hrη : 0 < rη) (q : CarrierParameter)
    (hi : Euclidean (n-1) → ℂ) (ξ : Euclidean (n-1)) :
    (angularMask zRoot (normalize ηb) hρ (angularWidth_spec hηb hrη).1 q
        (normalize ξ) : ℂ)*hi ξ =
      ((incidenceMask zRoot hρ q.1*spectatorMask zRoot hρ q.2 : ℝ) : ℂ)*
        (originalConicDetector hηb hrη ξ*hi ξ) := by
  have hf := originalConicCarrierWeight_sqrt_mul_direction zRoot hρ hηb hrη q (normalize ξ)
  rw [originalConicCarrierWeight, carrierSamplingEquiv.symm_apply_apply,
    Real.sqrt_sq (mul_nonneg (ContDiffBump.nonneg _) (ContDiffBump.nonneg _))] at hf
  rw [← hf]
  simp only [Complex.ofReal_mul, originalConicDetector, mul_assoc]

open CorrectedAtoms ResponseSourceExtension

private theorem full_strain_real_smul {n N : ℕ} (F : Euclidean n → Euclidean N)
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) (a : ℝ) (x : Euclidean n) :
    WKB.complexLinearizedMetric F (a • W) x = a • WKB.complexLinearizedMetric F W x := by
  have hf : fderiv ℝ (a • W) x = a • fderiv ℝ W x :=
    congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := W) a) x
  ext i j
  simp only [WKB.complexLinearizedMetric, partialDeriv, hf,
    _root_.smul_apply, PiLp.smul_apply, Matrix.smul_apply]
  simp only [mul_smul_comm, smul_mul_assoc, ← smul_add, ← Finset.smul_sum]

private theorem full_atomicSource_real_smul {n N : ℕ} (F : Euclidean n → Euclidean N)
    (χ : Euclidean n → ℝ) (W : Euclidean n → EuclideanSpace ℂ (Fin N)) (a : ℝ) :
    complexAtomicSource F χ (a • W) = a • complexAtomicSource F χ W := by
  funext x
  change χ x • WKB.complexLinearizedMetric F (a • W) x =
    a • (χ x • WKB.complexLinearizedMetric F W x)
  rw [full_strain_real_smul]
  exact smul_comm _ _ _

private theorem full_correctedAtom_real_smul {n N : ℕ} (F : Euclidean n → Euclidean N)
    (χ : Euclidean n → ℝ) (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (W : Euclidean n → EuclideanSpace ℂ (Fin N)) (a : ℝ) :
    complexCorrectedAtom F χ B (a • W) = a • complexCorrectedAtom F χ B W := by
  unfold complexCorrectedAtom
  rw [full_atomicSource_real_smul]
  have hb : complexifyResponse B (a • complexAtomicSource F χ W) =
      a • complexifyResponse B (complexAtomicSource F χ W) :=
    ((complexifyResponse B).restrictScalars ℝ).map_smul a _
  rw [hb, smul_sub]

section Physical

variable {n N J : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q-fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1))) →
      Euclidean (n-1) × (Euclidean 3 × Euclidean (n-1)))
    (r : Euclidean (n-1) × Euclidean 3 → ℝ) (τ : ℝ) (z : Euclidean 3)

/-- Literal primary synthesis with the restored carrier mask. The SAME positive
initial scalar r, phase, full atom, high-pass and radial masks are retained;
this does not scale the separate zero atom (`app:ch_waves:eq:WKB-W`). -/
theorem fullPrimaryWave_carrierFactor (a : ℝ) (d : Euclidean (n-1) → ℂ)
    (v : WideInput n J) (x : Euclidean n) :
    fullPrimaryWave T Q F row col Φ Y τ r z (fun ξ ↦ (a : ℂ)*d ξ) v x =
      a • fullPrimaryWave T Q F row col Φ Y τ r z d v x := by
  unfold fullPrimaryWave wideSuperposition
  simp_rw [weightedWideDensity_carrierFactor, mul_smul]
  rw [integral_smul]
  exact IsScalarTower.algebraMap_smul ℂ a _

/-- Moving the SAME carrier factor onto the original raw Hilbert input is an
exact integral identity, not division by a sample weight. Only the detector's
actual measurability and bound enter (`app:ch_mean_pairs:defn:mean-lag-input`). -/
theorem fullPrimaryWave_carrierFactor_eq_scaledInput (a : ℝ)
    {d : Euclidean (n-1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hb : ∀ ξ, ‖d ξ‖ ≤ M) (v : WideInput n J) :
    fullPrimaryWave T Q F row col Φ Y τ r z (fun ξ ↦ (a : ℂ)*d ξ) v =
      fullPrimaryWave T Q F row col Φ Y τ r z d (a • v) := by
  funext x
  rw [fullPrimaryWave_carrierFactor]
  have hv : ((a : ℂ) • v : WideInput n J) = a • v :=
    IsScalarTower.algebraMap_smul ℂ a v
  have hs := fullPrimaryWave_smul T Q F row col Φ Y r τ z hd hb (a : ℂ) v x
  rw [hv] at hs
  exact ((IsScalarTower.algebraMap_smul ℂ a _).symm.trans hs.symm)

/-- The carrier factor is restored BEFORE applying the fixed response to the
entire raw source. No response is moved through a band integral and no source
cutoff or response operator changes (`app:ch_lag:eq:lag-recurrence`). -/
theorem wholeSourceCorrectedWave_carrierFactor (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (a : ℝ)
    {d : Euclidean (n-1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hb : ∀ ξ, ‖d ξ‖ ≤ M) (v : WideInput n J) :
    wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z
        (fun ξ ↦ (a : ℂ)*d ξ) v =
      wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d (a • v) := by
  unfold wholeSourceCorrectedWave
  rw [fullPrimaryWave_carrierFactor_eq_scaledInput T Q F row col Φ Y r τ z a hd hb]

/-- The actual demodulated derivative of the complete corrected source has the
same restored-mask identity. This is equality of the literal physical fields,
not a conclusion inferred from equality of normal operators
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem wholeSourceCorrectedDerivative_carrierFactor (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (a : ℝ)
    {d : Euclidean (n-1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hb : ∀ ξ, ‖d ξ‖ ≤ M) (v : WideInput n J) (x : Euclidean n) :
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B τ z
        (fun ξ ↦ (a : ℂ)*d ξ) v x =
      wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B τ z d (a • v) x := by
  unfold wholeSourceCorrectedDerivative
  rw [wholeSourceCorrectedWave_carrierFactor T Q F row col Φ Y r τ z χ B a hd hb]

/-- The actual original full angular mask, not an abstract weighted surrogate,
restores the incidence/spectator factor outside the complete primary integral.
The high-pass multiplier, positive initial scalar, phase and spatial parameter
are identical on both sides (`app:ch_mean_pairs:defn:mean-wave-input`). -/
theorem originalAngular_fullPrimaryWave (zRoot : Euclidean 3)
    {ρ rη : ℝ} (hρ : 0 < ρ) {ηb : Euclidean (n-1)}
    (hηb : ηb ≠ 0) (hrη : 0 < rη) (q : CarrierParameter)
    (hi : Euclidean (n-1) → ℂ) (v : WideInput n J) (x : Euclidean n) :
    fullPrimaryWave T Q F row col Φ Y τ r (parameter q)
        (fun ξ ↦ (angularMask zRoot (normalize ηb) hρ
          (angularWidth_spec hηb hrη).1 q (normalize ξ) : ℂ)*hi ξ) v x =
      (incidenceMask zRoot hρ q.1*spectatorMask zRoot hρ q.2) •
        fullPrimaryWave T Q F row col Φ Y τ r (parameter q)
          (fun ξ ↦ originalConicDetector hηb hrη ξ*hi ξ) v x := by
  simp_rw [original_mask_factor (n := n) zRoot hρ hηb hrη q hi]
  exact fullPrimaryWave_carrierFactor T Q F row col Φ Y r τ (parameter q) _ _ v x

/-- Literal original-mask restoration for the full corrected source. The SAME
fixed source response acts AFTER the entire primary wave; the detector-only
right side is evaluated on the actually scaled raw Hilbert input
(`app:ch_lag:eq:lag-recurrence`). -/
theorem originalAngular_correctedWave (χsrc : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (zRoot : Euclidean 3)
    {ρ rη : ℝ} (hρ : 0 < ρ) {ηb : Euclidean (n-1)}
    (hηb : ηb ≠ 0) (hrη : 0 < rη) (q : CarrierParameter)
    (hi : Euclidean (n-1) → ℂ) {M : ℝ}
    (hd : Measurable (fun ξ ↦ originalConicDetector hηb hrη ξ*hi ξ))
    (hb : ∀ ξ, ‖originalConicDetector hηb hrη ξ*hi ξ‖ ≤ M) (v : WideInput n J) :
    wholeSourceCorrectedWave T Q F row col Φ Y r χsrc B τ (parameter q)
        (fun ξ ↦ (angularMask zRoot (normalize ηb) hρ
          (angularWidth_spec hηb hrη).1 q (normalize ξ) : ℂ)*hi ξ) v =
      wholeSourceCorrectedWave T Q F row col Φ Y r χsrc B τ (parameter q)
        (fun ξ ↦ originalConicDetector hηb hrη ξ*hi ξ)
        ((incidenceMask zRoot hρ q.1*spectatorMask zRoot hρ q.2) • v) := by
  simp_rw [original_mask_factor (n := n) zRoot hρ hηb hrη q hi]
  exact wholeSourceCorrectedWave_carrierFactor T Q F row col Φ Y r τ (parameter q)
    χsrc B _ hd hb v

/-- Full original physical derivative factorization, including the entire
corrected source and every Fourier band. Together with the real linear source
realization this proves Gfull=a Gdetector, including a=0; no Gram equality is
used (`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem originalAngular_correctedDerivative (χsrc : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (zRoot : Euclidean 3)
    {ρ rη : ℝ} (hρ : 0 < ρ) {ηb : Euclidean (n-1)}
    (hηb : ηb ≠ 0) (hrη : 0 < rη) (q : CarrierParameter)
    (hi : Euclidean (n-1) → ℂ) {M : ℝ}
    (hd : Measurable (fun ξ ↦ originalConicDetector hηb hrη ξ*hi ξ))
    (hb : ∀ ξ, ‖originalConicDetector hηb hrη ξ*hi ξ‖ ≤ M)
    (v : WideInput n J) (x : Euclidean n) :
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χsrc B τ (parameter q)
        (fun ξ ↦ (angularMask zRoot (normalize ηb) hρ
          (angularWidth_spec hηb hrη).1 q (normalize ξ) : ℂ)*hi ξ) v x =
      wholeSourceCorrectedDerivative T Q F row col Φ Y r χsrc B τ (parameter q)
        (fun ξ ↦ originalConicDetector hηb hrη ξ*hi ξ)
        ((incidenceMask zRoot hρ q.1*spectatorMask zRoot hρ q.2) • v) x := by
  simp_rw [original_mask_factor (n := n) zRoot hρ hηb hrη q hi]
  exact wholeSourceCorrectedDerivative_carrierFactor T Q F row col Φ Y r τ (parameter q)
    χsrc B _ hd hb v x

/-- The literal whole-source corrected wave scales by the restored carrier
factor globally. The response is real linear and the total derivative commutes
with constant real scaling even at zero; no arbitrary analytic premise is added
(`app:ch_response:cor:current-atoms`). -/
theorem wholeSourceCorrectedWave_carrierFactor_smul (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (a : ℝ)
    (d : Euclidean (n-1) → ℂ) (v : WideInput n J) :
    wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z (fun ξ ↦ (a : ℂ)*d ξ) v =
      a • wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d v := by
  have hw : fullPrimaryWave T Q F row col Φ Y τ r z (fun ξ ↦ (a : ℂ)*d ξ) v =
      a • fullPrimaryWave T Q F row col Φ Y τ r z d v := by
    funext x
    exact fullPrimaryWave_carrierFactor T Q F row col Φ Y r τ z a d v x
  unfold wholeSourceCorrectedWave
  rw [hw, full_correctedAtom_real_smul]

/-- The derivative of the complete corrected physical wave, including its
fixed demodulation, has exactly one restored carrier factor. This proves the
full Graw factor from formulas, not a normal-operator comparison
(`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem wholeSourceCorrectedDerivative_carrierFactor_smul (χ : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (a : ℝ)
    (d : Euclidean (n-1) → ℂ) (v : WideInput n J) (x : Euclidean n) :
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B τ z
        (fun ξ ↦ (a : ℂ)*d ξ) v x =
      a • wholeSourceCorrectedDerivative T Q F row col Φ Y r χ B τ z d v x := by
  unfold wholeSourceCorrectedDerivative
  rw [wholeSourceCorrectedWave_carrierFactor_smul]
  rw [show fderiv ℝ
      (a • wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d v) x =
      a • fderiv ℝ (wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d v) x from
    congrFun (fderiv_const_smul_field (𝕜 := ℝ)
      (f := wholeSourceCorrectedWave T Q F row col Φ Y r χ B τ z d v) a) x]
  rw [map_smul, smul_comm]

/-- Actual positive-τ full-angular Graw is the incidence/spectator scalar times
the detector-only Graw, on the SAME full positive initializer and fixed source
response. All source derivatives and all band interactions are retained
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem originalAngular_Graw_eq (χsrc : Euclidean n → ℝ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (zRoot : Euclidean 3)
    {ρ rη : ℝ} (hρ : 0 < ρ) {ηb : Euclidean (n-1)}
    (hηb : ηb ≠ 0) (hrη : 0 < rη) (q : CarrierParameter)
    (hi : Euclidean (n-1) → ℂ) (v : WideInput n J) (x : Euclidean n) :
    wholeSourceCorrectedDerivative T Q F row col Φ Y r χsrc B τ (parameter q)
        (fun ξ ↦ (angularMask zRoot (normalize ηb) hρ
          (angularWidth_spec hηb hrη).1 q (normalize ξ) : ℂ)*hi ξ) v x =
      (incidenceMask zRoot hρ q.1*spectatorMask zRoot hρ q.2) •
        wholeSourceCorrectedDerivative T Q F row col Φ Y r χsrc B τ (parameter q)
          (fun ξ ↦ originalConicDetector hηb hrη ξ*hi ξ) v x := by
  simp_rw [original_mask_factor (n := n) zRoot hρ hηb hrη q hi]
  exact wholeSourceCorrectedDerivative_carrierFactor_smul T Q F row col Φ Y r τ
    (parameter q) χsrc B _ _ v x

end Physical

section Canonical

variable {n : ℕ} {ι m : Type*} [Fintype ι] [Fintype m]
    {Raw : ι → Type*} [∀ i, NormedAddCommGroup (Raw i)]
    [∀ i, InnerProductSpace ℝ (Raw i)] [∀ i, CompleteSpace (Raw i)]
    (a : ι → ℝ)
    (A : ∀ i, Raw i →L[ℝ] OutputL2 n)
    (G : ∀ i, Raw i →ₗ[ℝ] SmoothPeriodicFamily n Unit (Matrix m (Fin n) ℂ))
    (Q₀ : OutputL2 n →L[ℝ] OutputL2 n)

omit [Fintype ι] in
/-- Restoring the original carrier factor in BOTH the raw physical source and
its real measured adjoint gives Dfull=a² Ddetector on the SAME original inverse.
This holds also at a=0 (`app:ch_mean_pairs:eq:mean-current-canonical`). -/
theorem fixedSourceDerivative_carrierFactor (e : SmoothResidual n)
    (x : Torus n) (i : ι) :
    (fixedSourceDerivative (fun i ↦ a i • A i) (fun i ↦ a i • G i) Q₀ e).val x i =
      (a i)^2 • (fixedSourceDerivative A G Q₀ e).val x i := by
  change ((a i • G i) ((a i • A i).adjoint (Q₀ (smoothResidualToL2 n e)))).val x () =
    (a i)^2 • (G i ((A i).adjoint (Q₀ (smoothResidualToL2 n e)))).val x ()
  simp only [smul_apply, LinearMap.smul_apply, map_smul,
    Submodule.coe_smul, Pi.smul_apply, smul_smul, pow_two]

omit A Q₀ [Fintype ι] [∀ i, CompleteSpace (Raw i)] in
/-- The SAME full positive background is left UNSCALED. Its actual real cross
response gains exactly one carrier factor when Graw does; the factor two is
unchanged (`app:ch_mean_pairs:defn:mean-canonical`). -/
theorem smoothRawCrossResponse_carrierFactor
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (i : ι) :
    smoothRawCrossResponse base C hC (fun i ↦ a i • G i) i =
      a i • smoothRawCrossResponse base C hC G i := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  funext x u
  cases u
  simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
    smoothRawCrossResponse_apply]
  change C x ((2 : ℝ) • hermitianBilinear (base.val x i) (a i • (G i v).val x ())) =
    a i • C x ((2 : ℝ) • hermitianBilinear (base.val x i) ((G i v).val x ()))
  rw [map_smul]
  simp only [map_smul, smul_comm (2 : ℝ) (a i)]

omit Q₀ [Fintype ι] [∀ i, CompleteSpace (Raw i)] in
/-- An already constructed detector component's genuine raw action transfers
to the full-angular physical component. This is a pointwise action identity,
not a new analytic assumption or an equality of Gram matrices
(`main:eq:canonical-identity`). -/
theorem rawAction_carrierFactor
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (hraw : ∀ i v, smoothResidualToL2 n (smoothRawCrossResponse base C hC G i v) = A i v)
    (i : ι) (v : Raw i) :
    smoothResidualToL2 n
        (smoothRawCrossResponse base C hC (fun i ↦ a i • G i) i v) =
      (a i • A i) v := by
  rw [smoothRawCrossResponse_carrierFactor]
  simp only [LinearMap.smul_apply, map_smul, hraw, smul_apply]

/-- The linear response uses the restored squared carrier mass, but the SAME
unscaled full background. Thus an inner-weight normal comparison can transfer
to the outer-weight physical linear term, without changing the uncut inverse
(`app:ch_mean_pairs:eq:mean-operators`). -/
theorem smoothCanonicalResponse_carrierFactor (μ : ι → ℝ)
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ))
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (e : OutputL2 n) :
    smoothCanonicalResponse μ (fun i ↦ a i • A i)
        (smoothRawCrossResponse base C hC (fun i ↦ a i • G i)) Q₀ e =
      smoothCanonicalResponse (fun i ↦ μ i*(a i)^2) A
        (smoothRawCrossResponse base C hC G) Q₀ e := by
  simp only [smoothCanonicalResponse, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
  apply Finset.sum_congr rfl
  intro i _
  rw [smoothRawCrossResponse_carrierFactor]
  simp only [LinearMap.smul_apply, map_smul, smul_apply, smul_smul, pow_two]

/-- The actual bilinear quadratic source has the FOURTH carrier power relative
to the outer physical mass. It is not the old inner-weight quadratic source:
when μinner=μouter*a² its mass is μinner*a². Both inputs use the SAME Q₀
(`app:ch_mean_pairs:eq:mean-operators`). -/
theorem fixedSourceQuadratic_carrierFactor (μ : ι → ℝ)
    (C : Torus n → Matrix (Fin n) (Fin n) ℝ →L[ℝ] Euclidean n) (hC : IsSmoothPeriodic C)
    (u v : SmoothResidual n) :
    fixedSourceQuadratic μ C hC (fun i ↦ a i • A i) (fun i ↦ a i • G i) Q₀ u v =
      fixedSourceQuadratic (fun i ↦ μ i*(a i)^4) C hC A G Q₀ u v := by
  apply Subtype.ext
  funext x b
  change C x (∑ i, μ i • hermitianBilinear
      ((fixedSourceDerivative (fun i ↦ a i • A i) (fun i ↦ a i • G i) Q₀ u).val x i)
      ((fixedSourceDerivative (fun i ↦ a i • A i) (fun i ↦ a i • G i) Q₀ v).val x i)) =
    C x (∑ i, (μ i*(a i)^4) • hermitianBilinear
      ((fixedSourceDerivative A G Q₀ u).val x i) ((fixedSourceDerivative A G Q₀ v).val x i))
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [fixedSourceDerivative_carrierFactor, fixedSourceDerivative_carrierFactor]
  simp only [map_smul, LinearMap.smul_apply, smul_smul]
  congr 1
  ring

/-- Exact full physical Hermitian increment under carrier restoration. The
baseline retains μouter and the original full positive B; the linear and
quadratic increments use μouter*a² and μouter*a⁴ respectively. This squares the
ENTIRE canonical derivative, preserving all original band cross terms
(`app:ch_mean_pairs:eq:mean-exact-self-change`). -/
theorem fullHermitian_increment_carrierFactor (μ : ι → ℝ)
    (base : SmoothPeriodicFamily n ι (Matrix m (Fin n) ℂ)) (e : SmoothResidual n) :
    weightedHermitianTensor μ
        (base+fixedSourceDerivative (fun i ↦ a i • A i) (fun i ↦ a i • G i) Q₀ e).val -
        weightedHermitianTensor μ base.val =
      (2 : ℝ) • weightedHermitianBilinear (fun i ↦ μ i*(a i)^2) base.val
        (fixedSourceDerivative A G Q₀ e).val +
      weightedHermitianTensor (fun i ↦ μ i*(a i)^4) (fixedSourceDerivative A G Q₀ e).val := by
  change weightedHermitianTensor μ
      (base.val+(fixedSourceDerivative (fun i ↦ a i • A i) (fun i ↦ a i • G i) Q₀ e).val) -
      weightedHermitianTensor μ base.val = _
  rw [weightedHermitianTensor_add_sub]
  congr 1
  · congr 1
    funext x
    change (∑ i, μ i • hermitianBilinear (base.val x i)
      ((fixedSourceDerivative (fun i ↦ a i • A i) (fun i ↦ a i • G i) Q₀ e).val x i)) =
      ∑ i, (μ i*(a i)^2) • hermitianBilinear (base.val x i)
        ((fixedSourceDerivative A G Q₀ e).val x i)
    apply Finset.sum_congr rfl
    intro i _
    rw [fixedSourceDerivative_carrierFactor]
    simp only [map_smul, smul_smul]
  · funext x
    apply Finset.sum_congr rfl
    intro i _
    rw [← mixedHermitianTensor_self, ← mixedHermitianTensor_self,
      fixedSourceDerivative_carrierFactor]
    change μ i • hermitianBilinear
      ((a i)^2 • (fixedSourceDerivative A G Q₀ e).val x i)
      ((a i)^2 • (fixedSourceDerivative A G Q₀ e).val x i) =
      (μ i*(a i)^4) • hermitianBilinear
        ((fixedSourceDerivative A G Q₀ e).val x i) ((fixedSourceDerivative A G Q₀ e).val x i)
    simp only [map_smul, LinearMap.smul_apply, smul_smul]
    congr 1
    ring

end Canonical

section NormalBenchmark
open SeparatedSampling Sampling.Realization SamplingKernelBounds
open PhysicalSampling.OriginalExternalWeights

/-- The original incidence/spectator factor in sampling coordinates. Its square
is the retained inner weight; the full physical Graw contains the factor itself
(`app:ch_mean_pairs:eq:mean-current-canonical`). -/
def carrierFactor (zRoot : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (z : Point) : ℝ :=
  incidenceMask zRoot hρ (carrierSamplingEquiv.symm z).1 *
    spectatorMask zRoot hρ (carrierSamplingEquiv.symm z).2

private theorem carrierFactor_sq (zRoot : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (z : Point) : (carrierFactor zRoot hρ z)^2 = originalConicCarrierWeight zRoot hρ z := rfl

private theorem carrierFactor_range (zRoot : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (z : Point) : carrierFactor zRoot hρ z ∈ Icc (0 : ℝ) 1 := by
  refine ⟨mul_nonneg (ContDiffBump.nonneg _) (ContDiffBump.nonneg _), ?_⟩
  exact (mul_le_of_le_one_left (ContDiffBump.nonneg _) (ContDiffBump.le_one _)).trans
    (ContDiffBump.le_one _)

private theorem carrierFactor_sqrt (zRoot : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (z : Point) : carrierFactor zRoot hρ z = Real.sqrt (originalConicCarrierWeight zRoot hρ z) := by
  rw [← carrierFactor_sq, Real.sqrt_sq (carrierFactor_range zRoot hρ z).1]

/-- Continuity of the literal carrier factor used by the restored scalar kernel
in the SAME-event amplitude test (`new:eq:amplitude-test`). -/
theorem carrierFactor_continuous (zRoot : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (carrierFactor zRoot hρ) := by
  convert Real.continuous_sqrt.comp (contDiff_originalConicCarrierWeight zRoot hρ).continuous using 1
  funext z
  exact carrierFactor_sqrt zRoot hρ z

/-- The restored factor is a contraction, including inactive labels; this is
the scalar-kernel input of the SAME-event test (`new:eq:amplitude-test`). -/
theorem carrierFactor_abs_le_one (zRoot : Euclidean 3) {ρ : ℝ} (hρ : 0 < ρ)
    (z : Point) : |carrierFactor zRoot hρ z| ≤ 1 := by
  rw [abs_of_nonneg (carrierFactor_range zRoot hρ z).1]
  exact (carrierFactor_range zRoot hρ z).2

/-- The native scalar kernel with its literal restored carrier factor. This is
not a new sampler: its outer norm is transferred from the SAME original event
(`new:eq:amplitude-test`). -/
def originalScalarCarrierKernel {n J p : ℕ}
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r)
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p+1)) × Point)) n) :
    BandKernelData (Fin J × ((Fin 3 → Fin (p+1)) × Point)) n :=
  PhysicalSampling.parameterCutKernel D (fun q ↦ carrierFactor zRoot hr q.2.2)
    ((carrierFactor_continuous zRoot hr).comp (continuous_snd.comp continuous_snd))
    (fun q ↦ carrierFactor_abs_le_one zRoot hr q.2.2)

private theorem originalScalarCarrierKernel_kernel {n J p : ℕ}
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r)
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p+1)) × Point)) n)
    (j : Fin J) (c : Fin 3 → Fin (p+1)) (z : Point)
    (η : Euclidean (n-1)) (x : Euclidean n) :
    (originalScalarCarrierKernel zRoot hr D).kernel (j,c,z) η x =
      (carrierFactor zRoot hr z : ℂ) • D.kernel (j,c,z) η x := by
  exact PhysicalSampling.parameterCutKernel_kernel D _ _ _ (j,c,z) η x

private theorem originalScalarCarrierKernel_scalar {n J p : ℕ}
    (hn : 1 ≤ n) (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r)
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p+1)) × Point)) n)
    (j : Fin J) (c : Fin 3 → Fin (p+1)) (z : Point)
    (x : Euclidean n) (η : Euclidean (n-1)) :
    PhysicalSamplingShells.scalarBandKernel hn (originalScalarCarrierKernel zRoot hr D) (j,c,z) x η =
      (carrierFactor zRoot hr z : ℂ) * PhysicalSamplingShells.scalarBandKernel hn D (j,c,z) x η := by
  simp only [PhysicalSamplingShells.scalarBandKernel, originalScalarCarrierKernel_kernel,
    PiLp.smul_apply, smul_eq_mul]

private theorem originalScalarCarrierKernel_prefix {n J p : ℕ}
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r)
    (D : BandKernelData (Fin J × ((Fin 3 → Fin (p+1)) × Point)) n)
    (L : ℕ) (c : Fin 3 → Fin (p+1)) (z : Point) :
    refinedKernelPrefix (originalScalarCarrierKernel zRoot hr D) L (c,z) =
      carrierFactor zRoot hr z • refinedKernelPrefix D L (c,z) := by
  calc
    _ = (carrierFactor zRoot hr z : ℂ) • refinedKernelPrefix D L (c,z) := by
      simpa only [originalScalarCarrierKernel] using
        PhysicalSampling.parameterCutKernel_refinedKernelPrefix D
          (fun q : (Fin 3 → Fin (p+1)) × Point ↦ carrierFactor zRoot hr q.2)
          ((carrierFactor_continuous zRoot hr).comp continuous_snd)
          (fun q ↦ carrierFactor_abs_le_one zRoot hr q.2) L (c,z)
    _ = _ := (RCLike.real_smul_eq_coe_smul (K := ℂ)
      (carrierFactor zRoot hr z) (refinedKernelPrefix D L (c,z))).symm

private theorem original_factor_zero_of_inner_weight_zero
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r) (χ : CarrierParameter → ℝ)
    (hχ : ∀ q ∈ carrierSupport zRoot (r := r), χ q = 1)
    (w : ℝ → ℝ) (h : ℝ) (U : Lattice → Point) (a : Sample)
    (ho : weight (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U a ≠ 0)
    (hi : weight (originalConicCarrierWeight zRoot hr) w h U a = 0) :
    carrierFactor zRoot hr (node h U a) = 0 := by
  rw [weight_eq_carrier_weight_mul_external zRoot hr χ hχ] at hi
  have hφ : originalConicCarrierWeight zRoot hr (node h U a) = 0 :=
    (mul_eq_zero.mp hi).resolve_right ho
  rw [carrierFactor_sqrt, hφ, Real.sqrt_zero]

private theorem patchMeanNormal_eq_of_weighted_atoms {E H : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : ℕ} {w : ℝ → ℝ} {W Bi Bo Pi Po h : ℝ} {ψi ψo : Point → ℝ}
    (hw : WindowBounds p w W) (hi : PatchBounds ψi Bi Pi) (ho : PatchBounds ψo Bo Po)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (Ti To : (Fin 3 → Fin (p+1)) → Point → E →L[ℂ] H)
    (he : ∀ c z, ψo z • atomNormal (To c z) = ψi z • atomNormal (Ti c z)) :
    patchMeanNormal p Bo ψo w h To = patchMeanNormal p Bi ψi w h Ti := by
  let Fo := fun q : Lattice ↦ ∫ z : Point, blockWeight w h q z • (ψo z • atomNormal (To (color p q) z))
  let Fi := fun q : Lattice ↦ ∫ z : Point, blockWeight w h q z • (ψi z • atomNormal (Ti (color p q) z))
  have hFo : HasSum Fo (patchMeanNormal p Bo ψo w h To) := by
    simpa only [Fo, patchMeanNormal, smul_smul, mul_comm] using
      BackgroundQuadrature.hasSum_blockIntegrals hw ho hh hh₁ (fun c z ↦ atomNormal (To c z))
  have hFi : HasSum Fi (patchMeanNormal p Bi ψi w h Ti) := by
    simpa only [Fi, patchMeanNormal, smul_smul, mul_comm] using
      BackgroundQuadrature.hasSum_blockIntegrals hw hi hh hh₁ (fun c z ↦ atomNormal (Ti c z))
  have hef : Fo = Fi := by
    funext q
    change (∫ z : Point, blockWeight w h q z • (ψo z • atomNormal (To (color p q) z))) = _
    change _ = ∫ z : Point, blockWeight w h q z • (ψi z • atomNormal (Ti (color p q) z))
    apply integral_congr_ae
    filter_upwards [] with z
    rw [he (color p q) z]
  rw [hef] at hFo
  exact hFo.unique hFi

private theorem atomNormal_real_factor {E H : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (t : ℝ) (T : E →L[ℂ] H) : atomNormal (t • T) = t^2 • atomNormal T := by
  have hadj := map_smulₛₗ (ContinuousLinearMap.adjoint (𝕜 := ℂ)) (t : ℂ) T
  rw [show starRingEnd ℂ (t : ℂ) = (t : ℂ) from Complex.conj_ofReal t] at hadj
  have hadj' : (t • T).adjoint = t • T.adjoint := by
    simpa only [Complex.coe_smul] using hadj
  unfold atomNormal
  rw [hadj']
  ext x
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.map_smul_of_tower, smul_smul, pow_two]

private theorem original_normal_mean {E H : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r) (χ : CarrierParameter → ℝ)
    (hχ : ∀ q ∈ carrierSupport zRoot (r := r), χ q = 1)
    {p : ℕ} {w : ℝ → ℝ} {W Bi Bo h : ℝ}
    (hw : WindowBounds p w W)
    (hi : PatchBounds (originalConicCarrierWeight zRoot hr) Bi 1)
    (ho : PatchBounds (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) Bo 1)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (T : (Fin 3 → Fin (p+1)) → Point → E →L[ℂ] H) :
    patchMeanNormal p Bo (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h
        (fun c z ↦ carrierFactor zRoot hr z • T c z) =
      patchMeanNormal p Bi (originalConicCarrierWeight zRoot hr) w h T := by
  apply patchMeanNormal_eq_of_weighted_atoms hw hi ho hh hh₁
  intro c z
  rw [atomNormal_real_factor, smul_smul, carrierFactor_sq, mul_comm]
  rw [carrier_weight_mul_external_sq zRoot hr χ hχ z]

private theorem original_normal_sample {E H : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r) (χ : CarrierParameter → ℝ)
    (hχ : ∀ q ∈ carrierSupport zRoot (r := r), χ q = 1)
    {p : ℕ} {w : ℝ → ℝ} {W Bi Bo h : ℝ}
    (hw : WindowBounds p w W)
    (hi : PatchBounds (originalConicCarrierWeight zRoot hr) Bi 1)
    (ho : PatchBounds (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) Bo 1)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (T : (Fin 3 → Fin (p+1)) → Point → E →L[ℂ] H)
    (U : Lattice → Point) (hU : ∀ q c, 0 ≤ U q c ∧ U q c < h) :
    patchSampleNormal p Bo (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h
        (fun c z ↦ carrierFactor zRoot hr z • T c z) U =
      patchSampleNormal p Bi (originalConicCarrierWeight zRoot hr) w h T U := by
  unfold patchSampleNormal
  calc
    _ = ∑ a ∈ samples p Bo (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U,
        weight (originalConicCarrierWeight zRoot hr) w h U a •
          atomNormal (T (color p a.1) (node h U a)) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [atomNormal_real_factor, smul_smul, carrierFactor_sq,
        weight_eq_carrier_weight_mul_external zRoot hr χ hχ]
      rw [mul_comm]
    _ = _ := by
      symm
      apply Finset.sum_subset (samples_subset_external zRoot hr χ hχ hw hi ho hh hh₁ U hU)
      intro a _ ha
      have hz : weight (originalConicCarrierWeight zRoot hr) w h U a = 0 := by
        by_contra hne
        exact ha ((mem_samples_iff hw hi hh hh₁ hU).mpr hne)
      rw [hz, zero_smul]

private theorem original_outer_scalar_bound {I : Type} [fI : Fintype I] {n J p : ℕ}
    (hn : 1 ≤ n) (zRoot : I → Euclidean 3) (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (χ : I → CarrierParameter → ℝ)
    (hχ : ∀ i q, q ∈ carrierSupport (zRoot i) (r := r i) → χ i q = 1)
    {w : ℝ → ℝ} {W Bi Bo h : ℝ} (hw : WindowBounds p w W)
    (hi : ∀ i, PatchBounds (originalConicCarrierWeight (zRoot i) (hr i)) Bi 1)
    (ho : ∀ i, PatchBounds (fun z ↦ (χ i (carrierSamplingEquiv.symm z))^2) Bo 1)
    (hh : 0 < h) (hh₁ : h ≤ 1) (ξ : I → ShiftSpace p Bi h)
    (hU : ∀ i q c, 0 ≤ extendedShift (ξ i) q c ∧ extendedShift (ξ i) q c < h)
    (D : I → BandKernelData (Fin J × ((Fin 3 → Fin (p+1)) × Point)) n) (L : ℕ)
    {C t : ℝ}
    (hevent : ‖familyDeviation p Bi (fun i ↦ originalConicCarrierWeight (zRoot i) (hr i)) w h
      (fun i c z ↦ refinedKernelPrefix (D i) L (c,z)) ξ‖ ≤ t)
    (hmean : ‖∑ i, patchMeanNormal p Bi (originalConicCarrierWeight (zRoot i) (hr i)) w h
      (fun c z ↦ refinedKernelPrefix (D i) L (c,z))‖ ≤ C) :
    ‖PhysicalSamplingShells.nativeScalarOperator hn Bo
      (fun i z ↦ (χ i (carrierSamplingEquiv.symm z))^2) w h
      (fun i ↦ extendedShift (ξ i))
      (fun i ↦ originalScalarCarrierKernel (zRoot i) (hr i) (D i)) L‖ ≤ Real.sqrt (C+t) := by
  let U := fun i ↦ extendedShift (ξ i)
  let φ := fun i ↦ originalConicCarrierWeight (zRoot i) (hr i)
  let ψ := fun i z ↦ (χ i (carrierSamplingEquiv.symm z))^2
  let Dout := fun i ↦ originalScalarCarrierKernel (zRoot i) (hr i) (D i)
  have hμi (a : CanonicalRowComparison.SampleIndex p Bi φ w h U) :
      0 ≤ CanonicalRowComparison.sampleWeight Bi φ w h U a :=
    weight_nonneg hw (hi a.1) hh.le a.2
  have hμo (a : CanonicalRowComparison.SampleIndex p Bo ψ w h U) :
      0 ≤ CanonicalRowComparison.sampleWeight Bo ψ w h U a :=
    weight_nonneg hw (ho a.1) hh.le a.2
  have hnormal : NormalPerturbation.normal
      (PhysicalSamplingShells.sampledRefinedRow Bo ψ w h U Dout L) =
      NormalPerturbation.normal
        (PhysicalSamplingShells.sampledRefinedRow Bi φ w h U D L) := by
    rw [PhysicalSamplingShells.sampledRefinedRow_normal Bo ψ w h U Dout L hμo,
      PhysicalSamplingShells.sampledRefinedRow_normal Bi φ w h U D L hμi]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Dout, originalScalarCarrierKernel_prefix, Complex.coe_smul] using
      original_normal_sample (zRoot i) (hr i) (χ i) (hχ i) hw (hi i) (ho i)
        hh hh₁ (fun c z ↦ refinedKernelPrefix (D i) L (c,z)) (U i) (hU i)
  have hnorm : ‖PhysicalSamplingShells.sampledRefinedRow Bo ψ w h U Dout L‖ =
      ‖PhysicalSamplingShells.sampledRefinedRow Bi φ w h U D L‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← NormalPerturbation.norm_normal, hnormal, NormalPerturbation.norm_normal]
  rw [PhysicalSamplingShells.norm_nativeScalarOperator_eq]
  apply (norm_scalarOutputProjection_comp_le hn _).trans
  change ‖PhysicalSamplingShells.sampledRefinedRow Bo ψ w h U Dout L‖ ≤ _
  rw [hnorm]
  exact PhysicalSamplingShells.norm_sampledRefinedRow_le_of_common_event
    Bi φ w h ξ D L hμi hevent hmean

private theorem original_real_normal_sample {n : ℕ}
    {Raw : Sample → Type} [∀ a, NormedAddCommGroup (Raw a)]
    [∀ a, InnerProductSpace ℝ (Raw a)] [∀ a, CompleteSpace (Raw a)]
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r) (χ : CarrierParameter → ℝ)
    (hχ : ∀ q ∈ carrierSupport zRoot (r := r), χ q = 1)
    {p : ℕ} {w : ℝ → ℝ} {W Bi Bo h : ℝ}
    (hw : WindowBounds p w W)
    (hi : PatchBounds (originalConicCarrierWeight zRoot hr) Bi 1)
    (ho : PatchBounds (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) Bo 1)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q c, 0 ≤ U q c ∧ U q c < h)
    (A : ∀ a, Raw a →L[ℝ] OutputL2 n) :
    let si := samples p Bi (originalConicCarrierWeight zRoot hr) w h U
    let so := samples p Bo (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U
    let innerRow := CanonicalRow.weightedRow
      (fun a : si ↦ weight (originalConicCarrierWeight zRoot hr) w h U a.val)
      (fun a : si ↦ A a.val)
    let outerRow := CanonicalRow.weightedRow
      (fun a : so ↦ weight (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U a.val)
      (fun a : so ↦ carrierFactor zRoot hr (node h U a.val) • A a.val)
    outerRow.comp outerRow.adjoint = innerRow.comp innerRow.adjoint := by
  intro si so innerRow outerRow
  have hwi : ∀ a : si, 0 ≤ weight (originalConicCarrierWeight zRoot hr) w h U a.val :=
    fun a ↦ weight_nonneg hw hi hh.le a.val
  have hwo : ∀ a : so, 0 ≤ weight (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U a.val :=
    fun a ↦ weight_nonneg hw ho hh.le a.val
  apply ContinuousLinearMap.ext
  intro e
  change outerRow (outerRow.adjoint e) = innerRow (innerRow.adjoint e)
  dsimp only [outerRow, innerRow]
  rw [CanonicalRow.weightedRow_normal_apply _ hwo,
    CanonicalRow.weightedRow_normal_apply _ hwi]
  let term := fun a : Sample ↦ weight (originalConicCarrierWeight zRoot hr) w h U a •
    A a ((A a).adjoint e)
  calc
    _ = ∑ a : so, term a.val := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [term]
      simp only [map_smul, smul_apply, smul_smul]
      rw [weight_eq_carrier_weight_mul_external zRoot hr χ hχ,
        ← carrierFactor_sq]
      congr 1
      ring
    _ = ∑ a ∈ so, term a := Finset.sum_coe_sort so term
    _ = ∑ a ∈ si, term a := by
      symm
      apply Finset.sum_subset (samples_subset_external zRoot hr χ hχ hw hi ho hh hh₁ U hU)
      intro a _ ha
      have hz : weight (originalConicCarrierWeight zRoot hr) w h U a = 0 := by
        by_contra hne
        exact ha ((mem_samples_iff hw hi hh hh₁ hU).mpr hne)
      dsimp only [term]
      rw [hz, zero_smul]
    _ = _ := (Finset.sum_coe_sort si term).symm

private theorem original_weighted_source {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r) (χ : CarrierParameter → ℝ)
    (hχ : ∀ q ∈ carrierSupport zRoot (r := r), χ q = 1)
    {p : ℕ} {w : ℝ → ℝ} {W Bi Bo h : ℝ}
    (hw : WindowBounds p w W)
    (hi : PatchBounds (originalConicCarrierWeight zRoot hr) Bi 1)
    (ho : PatchBounds (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) Bo 1)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q c, 0 ≤ U q c ∧ U q c < h)
    (H : Sample → V) :
    (∑ a ∈ samples p Bo (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U,
      Real.sqrt (weight (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U a) •
        (carrierFactor zRoot hr (node h U a) • H a)) =
      ∑ a ∈ samples p Bi (originalConicCarrierWeight zRoot hr) w h U,
        Real.sqrt (weight (originalConicCarrierWeight zRoot hr) w h U a) • H a := by
  calc
    _ = ∑ a ∈ samples p Bo (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U,
        Real.sqrt (weight (originalConicCarrierWeight zRoot hr) w h U a) • H a := by
      apply Finset.sum_congr rfl
      intro a _
      rw [sqrt_weight_eq_carrier_cutoff_mul_external zRoot hr χ hχ, smul_smul]
      change (_ * carrierFactor zRoot hr (node h U a)) • H a =
        (carrierFactor zRoot hr (node h U a) * _) • H a
      rw [mul_comm]
    _ = _ := by
      symm
      apply Finset.sum_subset (samples_subset_external zRoot hr χ hχ hw hi ho hh hh₁ U hU)
      intro a _ ha
      have hz : weight (originalConicCarrierWeight zRoot hr) w h U a = 0 := by
        by_contra hne
        exact ha ((mem_samples_iff hw hi hh hh₁ hU).mpr hne)
      rw [hz, Real.sqrt_zero, zero_smul]

private theorem finiteHermitian_of_inner_sum {n N : ℕ} {I : Type}
    (si so : Finset I) (μi μo φ : I → ℝ)
    (hsum : ∀ H : I → Matrix (Fin n) (Fin n) ℝ,
      (∑ a ∈ si, μi a • H a) = ∑ a ∈ so, μo a • (φ a • H a))
    (base D : I → Matrix (Fin N) (Fin n) ℂ) :
    (∑ a ∈ so, μo a • hermitianTensor (base a + φ a • D a)) -
      (∑ a ∈ so, μo a • hermitianTensor (base a)) =
      (2 : ℝ) • (∑ a ∈ si, μi a • hermitianBilinear (base a) (D a)) +
        ∑ a ∈ si, μi a • (φ a • hermitianTensor (D a)) := by
  rw [hsum (fun a ↦ hermitianBilinear (base a) (D a)),
    hsum (fun a ↦ φ a • hermitianTensor (D a)),
    ← Finset.sum_sub_distrib, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← smul_sub, hermitianTensor_add_sub, ← mixedHermitianTensor_eq_symmetricPart]
  have hcross : mixedHermitianTensor (base a) (φ a • D a) =
      φ a • hermitianBilinear (base a) (D a) :=
    (hermitianBilinear (base a)).map_smul (φ a) (D a)
  have hquad : hermitianTensor (φ a • D a) = φ a • (φ a • hermitianTensor (D a)) := by
    rw [← mixedHermitianTensor_self, mixedHermitianTensor_smul_left]
    rw [mixedHermitianTensor_comm (D a) (φ a • D a)]
    rw [mixedHermitianTensor_smul_left, mixedHermitianTensor_self]
  rw [hcross, hquad, smul_add, smul_comm (μo a) (2 : ℝ)]

private theorem original_sampled_Hermitian {n N : ℕ}
    (zRoot : Euclidean 3) {r : ℝ} (hr : 0 < r) (χ : CarrierParameter → ℝ)
    (hχ : ∀ q ∈ carrierSupport zRoot (r := r), χ q = 1)
    {p : ℕ} {w : ℝ → ℝ} {W Bi Bo h : ℝ}
    (hw : WindowBounds p w W)
    (hi : PatchBounds (originalConicCarrierWeight zRoot hr) Bi 1)
    (ho : PatchBounds (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) Bo 1)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (U : Lattice → Point) (hU : ∀ q c, 0 ≤ U q c ∧ U q c < h)
    (base D : Sample → Matrix (Fin N) (Fin n) ℂ) :
    (∑ a ∈ samples p Bo (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U,
      weight (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U a •
        hermitianTensor (base a + originalConicCarrierWeight zRoot hr (node h U a) • D a)) -
      (∑ a ∈ samples p Bo (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U,
        weight (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U a • hermitianTensor (base a)) =
      (2 : ℝ) • (∑ a ∈ samples p Bi (originalConicCarrierWeight zRoot hr) w h U,
        weight (originalConicCarrierWeight zRoot hr) w h U a • hermitianBilinear (base a) (D a)) +
      ∑ a ∈ samples p Bi (originalConicCarrierWeight zRoot hr) w h U,
        weight (originalConicCarrierWeight zRoot hr) w h U a •
          (originalConicCarrierWeight zRoot hr (node h U a) • hermitianTensor (D a)) := by
  apply finiteHermitian_of_inner_sum
  intro H
  calc
    _ = ∑ a ∈ samples p Bo (fun z ↦ (χ (carrierSamplingEquiv.symm z))^2) w h U,
        weight (originalConicCarrierWeight zRoot hr) w h U a • H a := by
      apply Finset.sum_subset (samples_subset_external zRoot hr χ hχ hw hi ho hh hh₁ U hU)
      intro a _ ha
      have hz : weight (originalConicCarrierWeight zRoot hr) w h U a = 0 := by
        by_contra hne
        exact ha ((mem_samples_iff hw hi hh hh₁ hU).mpr hne)
      rw [hz, zero_smul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [weight_eq_carrier_weight_mul_external zRoot hr χ hχ, mul_comm, mul_smul]

end NormalBenchmark

end JanetCartan.PhysicalMean.OriginalWeightBridge
end

public meta section
namespace JanetCartan.PhysicalMean.OriginalWeightBridgeTemplate
open Lean Meta Elab Command
open PhysicalInitialization.OriginalProtectedTemplate

private partial def specializeInputsAux (source : Name) (type : Expr)
    (args bound : Array Expr) (remaining : Array (Name × Expr)) : MetaM Expr := do
  let type ← whnf type
  if let .forallE name domain body bi := type then
    let short := name.eraseMacroScopes
    if let some (_, value) := remaining.find? (fun p ↦ p.1 == short) then
      unless ← isDefEq (← inferType value) domain do
        throwError "original weight bridge: wrong original specialization {source}.{short}"
      specializeInputsAux source (body.instantiate1 value) (args.push value) bound
        (remaining.filter (fun p ↦ p.1 != short))
    else
      withLocalDecl name bi domain fun x ↦
        specializeInputsAux source (body.instantiate1 x) (args.push x) (bound.push x) remaining
  else
    unless remaining.isEmpty do
      throwError "original weight bridge: unmatched fixed input for {source}"
    mkLambdaFVars bound (mkAppN (mkConst source) args)

private def specializeInputs (source : Name) (fixed : Array (Name × Expr)) : MetaM Expr := do
  let info ← getConstInfo source
  unless info.levelParams.isEmpty do
    throwError "original weight bridge: unexpected universe-polymorphic static input {source}"
  specializeInputsAux source info.type #[] #[] fixed

/-- Actual original22 mask and weight application. The full physical arguments
remain explicit and SAME on both sides; analytic realization/profile producers
are not assumed to have been completed by these algebraic identities. -/
elab "construct_original_weight_bridge" : command => liftTermElabM do
  let ns := `JanetCartan.PhysicalMean.OriginalWeightBridge.Original
  let outer := `JanetCartan.PhysicalSampling.OriginalOuterWeights
  let inner := `JanetCartan.PhysicalSampling.OriginalWeights
  let indexName := inner ++ `Index
  let info ← getConstInfo indexName
  forallTelescope info.type fun all result ↦ do
    unless all.size == 22 && result.isSort do
      throwError "original weight bridge: expected exact original22 index ABI"
    let n := (← inferType all[1]!).getAppArgs.back!
    unless ← isDefEq n (mkApp (mkConst ``Nat.succ) all[0]!) do
      throwError "original weight bridge: same physical dimension guard failed"
    let merged := mkAppN (mkConst `JanetCartan.PhysicalSampling.samplingCappedExtra)
      #[all[0]!, all[1]!, all[2]!, all[21]!]
    let capped := mkAppN (mkConst `JanetCartan.PhysicalNormalInverse.strongCappedExtra)
      #[n, all[1]!, merged]
    let native := (#[n, all[1]!] ++ all[3:22].toArray).set! 20 capped
    let index := mkAppN (mkConst indexName) all
    let sourceIndex := mkAppN (mkConst (outer ++ `Index)) all
    unless ← isDefEq index sourceIndex do
      throwError "original weight bridge: outer and original finite indices differ"
    discard <| store (ns ++ `index_eq_outer) all (← mkEqRefl index)
      false (some (← mkEq index sourceIndex))
    let ofield (name : Name) := mkAppN (mkConst (outer ++ name)) all
    let ifield (name : Name) := mkAppN (mkConst (inner ++ name)) all
    let selected (name : Name) :=
      mkAppN (mkConst (`JanetCartan.PhysicalSeed.SelectedBoundary ++ name)) native
    let hOne ← mkAppM ``Nat.succ_le_succ #[mkApp (mkConst ``Nat.zero_le) all[0]!]
    let fI ← synthInstance (← mkAppM ``Fintype #[index])
    let scalarFamilyFields : Array (Name × Expr) := #[(`I,index), (`fI,fI),
      (`n,n), (`p,all[2]!), (`hn,hOne), (`zRoot,ofield `root), (`r,ofield `a),
      (`hr,selected `ha'), (`χ,ofield `χ), (`hχ,ofield `χ_on_carrier),
      (`Bi,ifield `B), (`Bo,ofield `B), (`hi,ifield `patchBounds), (`ho,ofield `patchBounds)]
    discard <| store (ns ++ `outer_scalar_common_event_bound) all
      (← specializeInputs ``OriginalWeightBridge.original_outer_scalar_bound scalarFamilyFields)
    withLocalDeclD `i index fun i ↦ do
      let save (name : Name) (proof : Expr) : MetaM Unit := do
        discard <| store (ns ++ name) all (← mkLambdaFVars #[i] proof)
      let root := mkApp (ofield `root) i
      let ρ := mkApp (ofield `a) i
      let hρ := mkApp (selected `ha') i
      let scalarFields : Array (Name × Expr) := #[(`n,n), (`p,all[2]!),
        (`zRoot,root), (`r,ρ), (`hr,hρ)]
      let scalarKernel ← specializeInputs ``OriginalWeightBridge.originalScalarCarrierKernel scalarFields
      discard <| store (ns ++ `scalarKernel) all (← mkLambdaFVars #[i] scalarKernel) true
      save `scalarKernel_factor
        (← specializeInputs ``OriginalWeightBridge.originalScalarCarrierKernel_kernel scalarFields)
      save `scalarKernel_prefix_factor
        (← specializeInputs ``OriginalWeightBridge.originalScalarCarrierKernel_prefix scalarFields)
      save `scalarKernel_coordinate_factor
        (← specializeInputs ``OriginalWeightBridge.originalScalarCarrierKernel_scalar
          (scalarFields.push (`hn,hOne)))
      let ηnonzero := mkApp (selected `hηb) i
      let ηtype ← Core.betaReduce (← zetaReduce (← inferType ηnonzero))
      unless ηtype.isAppOfArity ``Ne 3 do
        throwError "original weight bridge: native nonzero transverse projection changed"
      let ηb := ηtype.getAppArgs[1]!
      let rη := mkApp (selected `r') i
      let hrη := mkApp (selected `hr') i
      let physical : Array (Name × Expr) := #[(`n,n), (`zRoot,root), (`ρ,ρ), (`hρ,hρ),
        (`rη,rη), (`ηb,ηb), (`hηb,ηnonzero), (`hrη,hrη)]
      for (name, theoremName) in #[
          (`fullPrimaryWave_eq, ``OriginalWeightBridge.originalAngular_fullPrimaryWave),
          (`wholeCorrectedWave_eq, ``OriginalWeightBridge.originalAngular_correctedWave),
          (`wholeCorrectedDerivative_eq, ``OriginalWeightBridge.originalAngular_correctedDerivative),
          (`Graw_eq, ``OriginalWeightBridge.originalAngular_Graw_eq)] do
        save name (← specializeInputs theoremName physical)
      let χ := mkApp (ofield `χ) i
      let hχ := mkApp (ofield `χ_on_carrier) i
      let weights : Array (Name × Expr) := #[(`zRoot,root), (`r,ρ), (`hr,hρ),
        (`χ,χ), (`hχ,hχ), (`p,all[2]!), (`Bi,ifield `B), (`Bo,ofield `B),
        (`hi,mkApp (ifield `patchBounds) i), (`ho,mkApp (ofield `patchBounds) i)]
      save `factor_zero_of_inner_weight_zero
        (← specializeInputs ``OriginalWeightBridge.original_factor_zero_of_inner_weight_zero
          #[(`zRoot,root), (`r,ρ), (`hr,hρ), (`χ,χ), (`hχ,hχ)])
      save `normal_mean_eq (← specializeInputs ``OriginalWeightBridge.original_normal_mean weights)
      save `normal_sample_eq (← specializeInputs ``OriginalWeightBridge.original_normal_sample weights)
      save `real_normal_sample_eq (← specializeInputs ``OriginalWeightBridge.original_real_normal_sample
        (weights.push (`n,n)))
      save `weighted_full_source_eq (← specializeInputs ``OriginalWeightBridge.original_weighted_source weights)
      save `fullHermitian_increment_eq (← specializeInputs ``OriginalWeightBridge.original_sampled_Hermitian
        (weights.push (`n,n)))
      save `factor_range (← mkAppM ``OriginalWeightBridge.carrierFactor_range #[root,hρ])
      save `factor_eq_sqrt_inner (← mkAppM ``OriginalWeightBridge.carrierFactor_sqrt #[root,hρ])
      let fac ← mkAppM ``OriginalWeightBridge.carrierFactor #[root,hρ]
      discard <| store (ns ++ `factor) all (← mkLambdaFVars #[i] fac) true
      let square ← mkAppM ``OriginalWeightBridge.carrierFactor_sq #[root,hρ]
      let originalWeight := mkApp (ifield `φ) i
      let point := mkConst `JanetCartan.SeparatedSampling.Point
      withLocalDeclD `z point fun z ↦ do
        let lhs ← mkAppM ``HPow.hPow #[mkApp fac z,mkNatLit 2]
        let goal ← mkEq lhs (mkApp originalWeight z)
        unless ← isDefEq (← inferType (mkApp square z)) goal do
          throwError "original weight bridge: literal factor square is not original φ"
        discard <| store (ns ++ `factor_sq_eq_inner) all
          (← mkLambdaFVars #[i,z] (mkApp square z)) false (some (← mkForallFVars #[i,z] goal))
  logInfo "original22 weight bridge: literal original angular Graw/full corrected wave, SAME unscaled positive initializer/whole response, outer74 χ and old innerφ normal means/samples on SAME nodes; no new χ/ξ/Q₀"

end JanetCartan.PhysicalMean.OriginalWeightBridgeTemplate
end
