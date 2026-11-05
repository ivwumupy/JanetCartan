module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Assembly
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportKernel.Positivity
public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.HighFrequency

/-!
# Identification with the smooth spectator symbol

For `app:ch_background:eq:bg-full-complex-amplitude`, the carrier kernel and
the symbol use the same primitive coefficients, inverse, and absolute Jacobian.
The identities below compare their literal formulas, without identifying the
torus output measure with physical Lebesgue measure. The compact spectator
integrability proof is local in the two positions and covector, so it also
applies to the homogeneous diagonal away from zero.
-/

@[expose] public noncomputable section
open MeasureTheory Set Function
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumRow.TransportKernel
open ContinuumNormalReduction
variable {n N : ℕ}

local instance : TopologicalSpace (Matrix (Fin n) (Fin n) ℝ) :=
  (Matrix.frobeniusNormedAddCommGroup (m := Fin n) (n := Fin n)
    (α := ℝ)).toUniformSpace.toTopologicalSpace

/-- The actual carrier primitives in the shared symbol convention. The physical
measurement function must agree with the torus cutoff at the chart points;
this definition makes no measure-transport assertion
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def coefficientsOfCarrier (d : CarrierData n N) (measurement : Euclidean n → ℝ) :
    TransportSymbol.Coefficients n N where
  measurement := measurement
  angular := fun p ↦ d.angularCutoff p.1 p.2
  high := d.highCutoff
  normal := fun p ↦ d.normalField p.1 p.2
  reduced := fun p ↦ fun i ↦ reducedCovector d p.1 (d.covector p.1 p.2) i

/-- Entrywise identification of the two zero-extended densities, with the
radial regularization squared. All matching hypotheses concern primitive
coordinates or coefficients, not the resulting density
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem inverseDensityEntry_eq_extendedDensity
    (d : CarrierData n N) (measurement : Euclidean n → ℝ)
    (radial : ℝ → ℝ) (R : ℝ) (x y : Torus n)
    (e : Euclidean n ≃ᵐ SliceVariable n)
    (D : Euclidean 2 → Set (Euclidean n))
    (Ψ U : Euclidean 2 → Euclidean n → Euclidean n)
    (J : Euclidean 2 → Euclidean n → Euclidean n →L[ℝ] Euclidean n)
    (jac : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (v : Euclidean 2) (k : Euclidean n)
    (hx : measurement (d.chartPoint x) = d.measurementCutoff x)
    (hy : measurement (d.chartPoint y) = d.measurementCutoff y)
    (hΩ : ((d.chartPoint x, d.chartPoint y, k), v) ∈ Ω ↔ k ∈ Ψ v '' D v)
    (hu : u ((d.chartPoint x, d.chartPoint y, k), v) = e (U v k))
    (hJ : jac (TransportSymbol.inverseCoordinates u ((d.chartPoint x, d.chartPoint y, k), v)) =
      |(J v (U v k)).det|) (i j : Fin n) :
    inverseDensityEntry d (fun z ↦ radial (‖z.2‖ / R)) x y e D Ψ U J v k i j =
      TransportSymbol.extendedDensity (TransportSymbol.regularizedCoefficients
        (coefficientsOfCarrier d measurement) radial R) jac u Ω
          ((d.chartPoint x, d.chartPoint y, k), v) i j := by
  classical
  by_cases hk : k ∈ Ψ v '' D v
  · simp only [inverseDensityEntry, indicator_of_mem hk, TransportSymbol.extendedDensity,
      indicator_of_mem (hΩ.mpr hk), TransportSymbol.inputDensity, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul, TransportSymbol.inputWeight, hJ]
    simp only [TransportSymbol.inverseCoordinates, TransportSymbol.regularizedCoefficients,
      coefficientsOfCarrier, hu, hx, hy, normalDensityEntry, chartCarrierVariable]
    ring
  · simp [inverseDensityEntry, TransportSymbol.extendedDensity, hk, hΩ]

section SpectatorRegularity
variable (a : TransportSymbol.Coefficients n N) (jac : TransportSymbol.InputVariables n → ℝ)
  (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
  (F : TransportSymbol.InputVariables n → TransportSymbol.Variables n × Euclidean 2)
  {Ω : Set (TransportSymbol.Variables n × Euclidean 2)} {W L : Set (TransportSymbol.InputVariables n)}
  (p : TransportSymbol.Variables n)
  (hΩ : IsOpen Ω) (h : TransportSymbol.PrimitiveRegularity a jac W)
  (hu : ContDiffOn ℝ ∞ u Ω)
  (hmap : MapsTo (TransportSymbol.inverseCoordinates u) Ω W)
  (hright : ∀ q ∈ Ω, F (TransportSymbol.inverseCoordinates u q) = q)
  (hs : ∀ q ∈ W, a.measurement q.1.1 ≠ 0 → a.measurement q.1.2 ≠ 0 →
    a.angular (q.2.1, ‖q.2.2‖⁻¹ • q.2.2) ≠ 0 → a.high ‖q.2.2‖ ≠ 0 → q ∈ L)
  (hclosed : IsClosed {v : Euclidean 2 | (p, v) ∈ F '' L})
  (hbuffer : ∀ v, (p, v) ∈ F '' L → (p, v) ∈ Ω)

include hΩ h hu hmap hright hs hclosed hbuffer in
/-- Smoothness in the spectator at fixed positions and frequency follows from
primitive regularity and a buffer on that slice. This does not demand global
smoothness of the homogeneous amplitude at frequency zero
(`app:ch_background:eq:bg-symbol`). -/
theorem spectatorDensity_contDiff :
    ContDiff ℝ ∞ (fun v ↦ TransportSymbol.extendedDensity a jac u Ω (p, v)) := by
  apply Localization.contDiff_of_contDiffOn_support_neighborhood
    (hΩ.preimage (by fun_prop : Continuous (fun v : Euclidean 2 ↦ (p, v))))
  · have hi := (TransportSymbol.inputDensity_contDiffOn h).comp
      (TransportSymbol.inverseCoordinates_contDiffOn hu) hmap
    apply (hi.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun _ hv ↦ hv)).congr
    intro v hv
    exact Set.indicator_of_mem (show (p, v) ∈ Ω from hv) _
  · apply (closure_minimal (s := Function.support
      (fun v ↦ TransportSymbol.extendedDensity a jac u Ω (p, v))) ?_ hclosed).trans
      (fun v hv ↦ hbuffer v hv)
    intro v hv
    exact TransportSymbol.support_extendedDensity_subset a jac u F hmap hright hs hv

/-- Original angular support implies compact support of the spectator density;
no transformed-support hypothesis is introduced
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem spectatorDensity_hasCompactSupport {K : Set (Euclidean 2)} (hK : IsCompact K)
    (hangular : ∀ z η, z.2 ∉ K → a.angular (z, η) = 0) :
    HasCompactSupport (fun v ↦ TransportSymbol.extendedDensity a jac u Ω (p, v)) := by
  apply HasCompactSupport.intro hK
  intro v hv
  by_cases hq : (p, v) ∈ Ω
  · simp [TransportSymbol.extendedDensity, hq, TransportSymbol.inputDensity, TransportSymbol.inputWeight,
      TransportSymbol.inverseCoordinates, hangular ((u (p, v)).1, v) _ hv]
  · simp [TransportSymbol.extendedDensity, hq]

include hΩ h hu hmap hright hs hclosed hbuffer in
/-- Compact angular support and primitive smoothness discharge pointwise
spectator integrability, including for homogeneous coefficients at nonzero
frequency. This is the analytic input to the diagonal positivity comparison
(`app:ch_background:eq:bg-real-symbol`). -/
theorem integrable_spectatorDensity {K : Set (Euclidean 2)} (hK : IsCompact K)
    (hangular : ∀ z η, z.2 ∉ K → a.angular (z, η) = 0) :
    Integrable (fun v ↦ TransportSymbol.extendedDensity a jac u Ω (p, v)) :=
  (spectatorDensity_contDiff a jac u F p hΩ h hu hmap hright hs hclosed hbuffer).continuous.integrable_of_hasCompactSupport
      (spectatorDensity_hasCompactSupport a jac u p hK hangular)

end SpectatorRegularity

/-- Continuous entry evaluation for the real Frobenius matrices in
`app:ch_background:eq:bg-full-complex-amplitude`; used to pass integrals and
derivatives to the scalar PDO calculus. -/
def realMatrixEntry (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ A i j
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The matrix spectator integral agrees entrywise with the scalar integrals.
This uses continuity of matrix evaluation, so it remains valid for the shared
Frobenius norm (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem amplitude_entry_eq_integral
    (a : TransportSymbol.Coefficients n N) (jac : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (p : TransportSymbol.Variables n)
    (hangular : ∀ z η, z.2 ∉ K → a.angular (z, η) = 0)
    (hi : Integrable (fun v ↦ TransportSymbol.extendedDensity a jac u Ω (p, v))) (i j : Fin n) :
    TransportSymbol.amplitude a jac u Ω K p i j = ∫ v, TransportSymbol.extendedDensity a jac u Ω (p, v) i j := by
  rw [TransportSymbol.amplitude_eq_integral a jac u Ω K p (fun v hv ↦ ?_)]
  · exact ((realMatrixEntry i j).integral_comp_comm hi).symm
  · by_cases hq : (p, v) ∈ Ω
    · simp [TransportSymbol.extendedDensity, hq, TransportSymbol.inputDensity, TransportSymbol.inputWeight,
        TransportSymbol.inverseCoordinates, hangular ((u (p, v)).1, v) _ hv]
    · simp [TransportSymbol.extendedDensity, hq]

/-- Primitive matching and smooth chart data connecting the exact kernel to
the symbol in `app:ch_background:eq:bg-full-complex-amplitude`. The actual
phase-chart and leading-wave owners supply these fields. In particular, there
is no density identity, integrability statement, or operator bound in this
record. Slice buffers allow homogeneous coefficients away from zero. -/
structure SymbolInputs {d : CarrierData n N} {m : CarrierVariable n → ℝ}
    {x y : Torus n} (c : ChartInputs d m x y) where
  measurement : Euclidean n → ℝ
  radial : ℝ → ℝ
  radius : ℝ
  mask_eq : m = fun z ↦ radial (‖z.2‖ / radius)
  measurement_left : measurement (d.chartPoint x) = d.measurementCutoff x
  measurement_right : measurement (d.chartPoint y) = d.measurementCutoff y
  jacobian : TransportSymbol.InputVariables n → ℝ
  inverse : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n
  forward : TransportSymbol.InputVariables n → TransportSymbol.Variables n × Euclidean 2
  domain : Set (TransportSymbol.Variables n × Euclidean 2)
  inputDomain : Set (TransportSymbol.InputVariables n)
  inputSupport : Set (TransportSymbol.InputVariables n)
  spectatorSupport : Set (Euclidean 2)
  domain_open : IsOpen domain
  compact_spectator : IsCompact spectatorSupport
  angular_support : ∀ z η, z.2 ∉ spectatorSupport → d.angularCutoff z η = 0
  domain_eq : ∀ v k, ((d.chartPoint x, d.chartPoint y, k), v) ∈ domain ↔
    k ∈ c.phaseMap v '' c.domain v
  inverse_eq : ∀ v k, inverse ((d.chartPoint x, d.chartPoint y, k), v) =
    c.coordinates (c.inverse v k)
  jacobian_eq : ∀ v k,
    jacobian (TransportSymbol.inverseCoordinates inverse
      ((d.chartPoint x, d.chartPoint y, k), v)) = |(c.derivative v (c.inverse v k)).det|
  regularity : TransportSymbol.PrimitiveRegularity
    (TransportSymbol.regularizedCoefficients (coefficientsOfCarrier d measurement) radial radius)
    jacobian inputDomain
  inverse_smooth : ContDiffOn ℝ ∞ inverse domain
  inverse_maps : MapsTo (TransportSymbol.inverseCoordinates inverse) domain inputDomain
  right_inverse : ∀ p ∈ domain, forward (TransportSymbol.inverseCoordinates inverse p) = p
  primitive_support : ∀ p ∈ inputDomain,
    measurement p.1.1 ≠ 0 → measurement p.1.2 ≠ 0 →
    d.angularCutoff p.2.1 (‖p.2.2‖⁻¹ • p.2.2) ≠ 0 →
    d.highCutoff ‖p.2.2‖ * radial (‖p.2.2‖ / radius) ≠ 0 → p ∈ inputSupport
  slice_closed : ∀ k, IsClosed {v : Euclidean 2 |
    ((d.chartPoint x, d.chartPoint y, k), v) ∈ forward '' inputSupport}
  slice_buffer : ∀ k v, ((d.chartPoint x, d.chartPoint y, k), v) ∈ forward '' inputSupport →
    ((d.chartPoint x, d.chartPoint y, k), v) ∈ domain

namespace SymbolInputs
variable {d : CarrierData n N} {m : CarrierVariable n → ℝ} {x y : Torus n}
  {c : ChartInputs d m x y} (s : SymbolInputs c)

/-- The shared regularized primitive coefficients for the literal carrier
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
def coefficients : TransportSymbol.Coefficients n N :=
  TransportSymbol.regularizedCoefficients (coefficientsOfCarrier d s.measurement)
    s.radial s.radius

/-- Equality of the actual conic density and the shared smooth zero extension
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem density_eq (v : Euclidean 2) (k : Euclidean n) (i j : Fin n) :
    inverseDensityEntry d m x y c.coordinates c.domain c.phaseMap c.inverse c.derivative v k i j =
      TransportSymbol.extendedDensity s.coefficients s.jacobian s.inverse s.domain
        ((d.chartPoint x, d.chartPoint y, k), v) i j := by
  conv_lhs => arg 2; rw [s.mask_eq]
  exact inverseDensityEntry_eq_extendedDensity d s.measurement s.radial s.radius x y
    c.coordinates c.domain c.phaseMap c.inverse c.derivative s.jacobian s.inverse
    s.domain v k s.measurement_left s.measurement_right (s.domain_eq v k)
    (s.inverse_eq v k) (s.jacobian_eq v k) i j

/-- Pointwise detector integrability is deduced from primitive regularity and
compact angular support (`app:ch_background:eq:bg-real-symbol`). -/
theorem integrable_density (k : Euclidean n) :
    Integrable (fun v ↦ TransportSymbol.extendedDensity s.coefficients s.jacobian
      s.inverse s.domain ((d.chartPoint x, d.chartPoint y, k), v)) :=
  integrable_spectatorDensity s.coefficients s.jacobian s.inverse s.forward
    (d.chartPoint x, d.chartPoint y, k) s.domain_open s.regularity s.inverse_smooth
    s.inverse_maps s.right_inverse s.primitive_support (s.slice_closed k) (s.slice_buffer k)
    s.compact_spectator s.angular_support

/-- The full scalar kernel entries are the entries of the shared matrix symbol.
Both sides retain the compact Lebesgue spectator integral
(`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem amplitude_eq (k : Euclidean n) (i j : Fin n) :
    c.amplitude k i j = TransportSymbol.amplitude s.coefficients s.jacobian
      s.inverse s.domain s.spectatorSupport (d.chartPoint x, d.chartPoint y, k) i j := by
  rw [amplitude_entry_eq_integral _ _ _ _ _ _ s.angular_support (s.integrable_density k)]
  exact integral_congr_ae (Filter.Eventually.of_forall (fun v ↦ s.density_eq v k i j))

include s in
/-- Entrywise detector integrability for the original conic formula; the
previously separate hypothesis in diagonal positivity is now discharged
(`app:ch_background:eq:bg-real-symbol`). -/
theorem integrable_inverseDensityEntry (k : Euclidean n) (i j : Fin n) :
    Integrable (fun v ↦ inverseDensityEntry d m x y c.coordinates c.domain c.phaseMap
      c.inverse c.derivative v k i j) := by
  have hi := (realMatrixEntry i j).integrable_comp (s.integrable_density k)
  exact hi.congr (Filter.Eventually.of_forall (fun v ↦ (s.density_eq v k i j).symm))

/-- Identification of the compact carrier kernel with the shared symbol.
The finite-band bounds supply frequency integrability and the chart supplies
the actual Jacobian substitution (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem normalEntry_eq_symbol (h : FiniteCarrierKernelBounds d m)
    (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart) (i j : Fin n) :
    regularizedNormalEntry d m x y i j = ∫ k, NormalComparison.oscillatoryFactor 1
      (inner ℝ (d.chartPoint x - d.chartPoint y) k) *
        (TransportSymbol.amplitude s.coefficients s.jacobian s.inverse s.domain
          s.spectatorSupport (d.chartPoint x, d.chartPoint y, k) i j : ℂ) := by
  rw [c.normalEntry_eq h hx hy]
  simp_rw [s.amplitude_eq]

/-- Positivity of the literal diagonal follows solely from its primitive
coefficient and chart data; detector integrability is proved internally
(`app:ch_background:eq:bg-real-symbol`). -/
theorem diagonal_posSemidef {c : ChartInputs d m x x} (s : SymbolInputs c)
    (k : Euclidean n) : Matrix.PosSemidef (fun i j ↦ c.amplitude k i j) :=
  fullAmplitudeEntry_diagonal_posSemidef d m x c.coordinates c.domain c.phaseMap
    c.inverse c.derivative k (s.integrable_inverseDensityEntry k)

end SymbolInputs

/-- The normalized real two-position amplitude. Its frequency reflection comes
from the checked real-quadrature kernel identity, with no even-mask assumption
(`app:ch_background:eq:bg-real-symbol`). -/
def reflectedSymbolAmplitude
    (a : TransportSymbol.Coefficients n N) (jac : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (p : TransportSymbol.Variables n) : Matrix (Fin n) (Fin n) ℝ :=
  (2 * (2 * Real.pi) ^ n) •
    (TransportSymbol.amplitude a jac u Ω K p +
      TransportSymbol.amplitude a jac u Ω K (p.1, p.2.1, -p.2.2))

/-- The real kernel of the actual compact carrier is the normalized oscillatory
integral of the shared reflected matrix amplitude. All frequency and spectator
integrability used in reflection is deduced from the finite-band and primitive
inputs (`app:ch_background:eq:bg-real-symbol`). -/
theorem SymbolInputs.realNormalEntry_eq_symbol
    {d : CarrierData n N} {m : CarrierVariable n → ℝ} {x y : Torus n}
    {c : ChartInputs d m x y} (s : SymbolInputs c)
    (h : FiniteCarrierKernelBounds d m) (hx : x ∈ d.outputChart) (hy : y ∈ d.outputChart)
    (i j : Fin n) :
    ((4 * (regularizedNormalEntry d m x y i j).re : ℝ) : ℂ) =
      ((2 * Real.pi) ^ n : ℂ)⁻¹ * ∫ k, NormalComparison.oscillatoryFactor 1
        (inner ℝ (d.chartPoint x - d.chartPoint y) k) *
          (reflectedSymbolAmplitude s.coefficients s.jacobian s.inverse s.domain
            s.spectatorSupport (d.chartPoint x, d.chartPoint y, k) i j : ℂ) := by
  rw [c.realNormalEntry_eq_normalized h hx hy]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with k
  rw [s.amplitude_eq k, s.amplitude_eq (-k)]
  simp only [reflectedSymbolAmplitude, Matrix.smul_apply, Matrix.add_apply,
    smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

/-- The large-frequency diagonal is exactly the reflected homogeneous matrix
in `app:ch_background:eq:bg-real-symbol`. The high-cutoff discrepancy is
therefore confined to bounded frequency; no smoothness at zero is asserted. -/
theorem reflectedSymbolAmplitude_diagonal_eq_homogeneous
    (a : TransportSymbol.Coefficients n N) (jac : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (Ω : Set (TransportSymbol.Variables n × Euclidean 2)) (K : Set (Euclidean 2))
    (hhigh : ∀ r : ℝ, 2 ≤ r → a.high r = 1) {C : ℝ} (hC : 0 < C)
    (hcomparison : ∀ p ∈ Ω, ‖p.1.2.2‖ ≤ C * ‖(u p).2‖)
    (x k : Euclidean n) (hk : 2 * C ≤ ‖k‖) :
    reflectedSymbolAmplitude a jac u Ω K (x, x, k) =
      reflectedDiagonalMatrix (TransportSymbol.homogeneousDiagonal a jac u Ω K x) k := by
  unfold reflectedSymbolAmplitude reflectedDiagonalMatrix TransportSymbol.homogeneousDiagonal
  rw [TransportSymbol.amplitude_eq_homogeneous_of_large_frequency a jac u Ω K
    hhigh hC hcomparison (x, x, k) hk,
    TransportSymbol.amplitude_eq_homogeneous_of_large_frequency a jac u Ω K
      hhigh hC hcomparison (x, x, -k) (by simpa using hk)]

/-- Smoothness of the reflected full matrix amplitude follows from the actual
primitive smoothness and buffers. This is the input used by full-amplitude
diagonal reduction (`app:ch_background:eq:bg-real-symbol`). -/
theorem reflectedSymbolAmplitude_contDiff
    (a : TransportSymbol.Coefficients n N) (jac : TransportSymbol.InputVariables n → ℝ)
    (u : TransportSymbol.Variables n × Euclidean 2 → SliceVariable n)
    (F : TransportSymbol.InputVariables n → TransportSymbol.Variables n × Euclidean 2)
    {Ω : Set (TransportSymbol.Variables n × Euclidean 2)}
    {W L : Set (TransportSymbol.InputVariables n)}
    (hΩ : IsOpen Ω) (h : TransportSymbol.PrimitiveRegularity a jac W)
    (hu : ContDiffOn ℝ ∞ u Ω) (hmap : MapsTo (TransportSymbol.inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (TransportSymbol.inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ L)
    (hclosed : IsClosed (F '' L)) (hbuffer : F '' L ⊆ Ω)
    {K : Set (Euclidean 2)} (hK : IsCompact K) :
    ContDiff ℝ ∞ (reflectedSymbolAmplitude a jac u Ω K) := by
  have ha := TransportSymbol.amplitude_contDiff a jac u F hΩ h hu hmap hright hs
    hclosed hbuffer hK
  exact (ha.add (ha.comp
    (contDiff_fst.prodMk (contDiff_snd.fst.prodMk contDiff_snd.snd.neg)))).const_smul _

/-- The homogeneous literal diagonal satisfies the manuscript's positive
comparison from primitive smoothness and compact detector support, with no
separate detector-integrability assumption (`app:ch_background:eq:bg-real-symbol`). -/
theorem homogeneousDiagonalMatrix_reflected_comparison_of_symbolInputs
    (d : CarrierData n N) (x : Torus n)
    (c : ChartInputs { d with highCutoff := fun _ ↦ 1 } (fun _ ↦ 1) x x)
    (s : SymbolInputs c) (k : Euclidean n) :
    (reflectedDiagonalMatrix
      (homogeneousDiagonalMatrix d x c.coordinates c.domain c.phaseMap c.inverse c.derivative) k -
        (2 * (2 * Real.pi) ^ n) • homogeneousDiagonalMatrix d x c.coordinates c.domain
          c.phaseMap c.inverse c.derivative k).PosSemidef :=
  homogeneousDiagonalMatrix_reflected_comparison d x c.coordinates c.domain c.phaseMap
    c.inverse c.derivative k (s.integrable_inverseDensityEntry (-k))

end JanetCartan.ContinuumRow.TransportKernel
