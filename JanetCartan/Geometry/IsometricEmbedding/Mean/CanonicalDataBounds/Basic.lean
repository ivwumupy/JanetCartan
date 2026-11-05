module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawInputRealization
public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalChange

/-!
# The actual canonical initial datum

The definitions in `app:ch_mean_pairs:eq:mean-current-canonical` and
`main:eq:old-canonical`, on the shared Lebesgue annular Hilbert space. The
physical map acts on the same inverse Fourier datum; spatial initial cutoffs
belong inside that map. The original zero atom is not modified here.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff

namespace JanetCartan.CanonicalDataBounds

open RawInputRealization

variable {n : ℕ} {ι : Type*} [Fintype ι] {radius : ι → ℝ}
  {Output : Type*} [NormedAddCommGroup Output] [InnerProductSpace ℝ Output]
  [CompleteSpace Output]

/-- The actual real Hilbert adjoint input in `main:eq:old-canonical`. -/
def adjointInput (A : Input n radius →L[ℝ] Output) (Q0 : Output →L[ℝ] Output)
    (r : Output) : Input n radius := A.adjoint (Q0 r)

/-- The Fourier density before spatial cutoffs in
`app:ch_mean_pairs:eq:mean-current-canonical`. -/
def fourierDensity (β : ι → Euclidean (n - 1) → ℂ)
    (A : Input n radius →L[ℝ] Output) (Q0 : Output →L[ℝ] Output) (r : Output) :
    Euclidean (n - 1) → ℂ := density β (adjointInput A Q0 r)

/-- The canonical datum `B_in A* Q0 r` of `main:eq:old-canonical`, using the
shared radian inverse Fourier integral on Lebesgue initial variables. -/
def initialDatum (β : ι → Euclidean (n - 1) → ℂ)
    (A : Input n radius →L[ℝ] Output) (Q0 : Output →L[ℝ] Output) (r : Output) :
    Euclidean (n - 1) → ℂ := field β (adjointInput A Q0 r)

/-- The physical change in `app:ch_mean_pairs:eq:mean-current-canonical` is
the supplied current wave map applied to this very same initial datum. -/
def physicalChange {Physical : Type*}
    (G : (Euclidean (n - 1) → ℂ) → Physical)
    (β : ι → Euclidean (n - 1) → ℂ)
    (A : Input n radius →L[ℝ] Output) (Q0 : Output →L[ℝ] Output) (r : Output) :
    Physical := G (initialDatum β A Q0 r)

/-- The input support assertion of `app:ch_mean_pairs:eq:mean-canonical-bounds`
holds for the literal density representative, before spatial cutoff. -/
theorem fourierDensity_eq_zero_above_ceiling (β : ι → Euclidean (n - 1) → ℂ)
    (A : Input n radius →L[ℝ] Output) (Q0 : Output →L[ℝ] Output) (r : Output)
    {R : ℝ} (hR : ∀ i, radius i ≤ R) {η : Euclidean (n - 1)} (hη : R < ‖η‖) :
    fourierDensity β A Q0 r η = 0 :=
  density_eq_zero_above_ceiling β _ hR hη

/-- Integrability of the actual canonical density, needed for the Fourier
variation in `main:eq:variation`. -/
theorem integrable_fourierDensity {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : ∀ i η, ‖β i η‖ ≤ M)
    (A : Input n radius →L[ℝ] Output) (Q0 : Output →L[ℝ] Output) (r : Output) :
    Integrable (fourierDensity β A Q0 r) volume := integrable_density hβ hM _

/-- Smoothness of the datum in `app:ch_mean_pairs:eq:mean-current-canonical`. -/
theorem contDiff_initialDatum {β : ι → Euclidean (n - 1) → ℂ}
    (hβ : ∀ i, Measurable (β i)) {M : ℝ} (hM : ∀ i η, ‖β i η‖ ≤ M)
    (A : Input n radius →L[ℝ] Output) (Q0 : Output →L[ℝ] Output) (r : Output)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ i, radius i ≤ R) :
    ContDiff ℝ ∞ (initialDatum β A Q0 r) := contDiff_field hβ hM _ hR0 hR

/-- Transfer a raw size bound to the individual canonical datum, retaining the
precise extra half power in `app:ch_mean_pairs:eq:mean-canonical-bounds`.
The individual operator and continuum inverse bounds are explicit inputs. -/
theorem size_adjointInput_le (A : Input n radius →L[ℝ] Output)
    (Q0 : Output →L[ℝ] Output) (size : Input n radius → ℝ)
    {B CA CQ K e : ℝ} (hB : 0 ≤ B) (hCA : 0 ≤ CA) (hK : 0 < K)
    (hA : ‖A‖ ≤ CA * Real.sqrt K) (hQ : ‖Q0‖ ≤ CQ)
    (hraw : ∀ v, size v ≤ B * K ^ e * ‖v‖) (r : Output) :
    size (adjointInput A Q0 r) ≤ (B * CA * CQ) * K ^ (e + 1 / 2) * ‖r‖ := by
  calc
    _ ≤ (B * K ^ e) * (CA * Real.sqrt K) * ‖Q0‖ * ‖r‖ :=
      CanonicalChange.size_adjoint_inverse_le A Q0 size (by positivity) hA hraw r
    _ ≤ (B * K ^ e) * (CA * Real.sqrt K) * CQ * ‖r‖ := by gcongr
    _ = _ := by rw [Real.rpow_add hK, Real.sqrt_eq_rpow]; ring

end JanetCartan.CanonicalDataBounds
