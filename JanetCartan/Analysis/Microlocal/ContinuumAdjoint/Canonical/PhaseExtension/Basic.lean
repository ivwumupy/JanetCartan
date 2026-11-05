module

public import JanetCartan.Analysis.Microlocal.ContinuumAdjoint.Canonical.Phase
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport

/-!
# Affine extensions and their rectangular derivative fields

Shared formulas for the geometric inputs of
`DerivativeKernels.exists_scalarTransportCarrierAdjoint_periodic_raw_bound`.
Only the perturbation of a fixed linear transported position is cut off.
Consequently the reference spatial derivative survives outside the chart.
The actual quantitative rank gap is a separate construction obligation.

Source: `app:ch_background:eq:bg-derivative-trade`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
open ContinuumRow

variable {n : ℕ}

/-- Extend a transported position by cutting off its difference from a fixed
linear reference, for `app:ch_background:eq:bg-derivative-trade`. -/
def affineExtension (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    (χ : Euclidean n × CarrierParameter → ℝ)
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (p : Euclidean n × CarrierParameter) : Euclidean (n - 1) :=
  A p.1 + χ p • (Y p - A p.1)

/-- The phase of an extended transported position, in the exact argument order
of the raw adjoint endpoint (`app:ch_background:eq:bg-derivative-trade`). -/
def phase (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (z : CarrierParameter) (x : Euclidean n) (η : Euclidean (n - 1)) : ℝ :=
  inner ℝ (Y (x, z)) η

/-- The transpose of the spatial derivative of the transported position.
For the actual Hamilton position this is the published rectangular mixed
phase matrix (`app:ch_background:eq:bg-derivative-trade`). -/
def spatialMatrix (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (z : CarrierParameter) (x : Euclidean n) : TransverseMatrix n :=
  fun i j ↦ (fderiv ℝ (fun y ↦ Y (y, z)) x (EuclideanSpace.single i 1)) j

/-- The physical vector field obtained from the transpose of the Gram left
inverse. Its right-inverse identity must be proved from the rank gap
(`app:ch_background:eq:bg-derivative-trade`). -/
def initialField (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (z : CarrierParameter) (x : Euclidean n) (h : Euclidean (n - 1)) : Euclidean n :=
  WithLp.toLp 2 ((transverseLeftInverse (spatialMatrix Y z x))ᵀ *ᵥ (fun j ↦ h j))

/-- The carrier trade retains the full derivative in all original carrier
labels, as required in `app:ch_background:eq:bg-derivative-trade`. -/
def carrierField (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    (z : CarrierParameter) (x : Euclidean n) (h : CarrierParameter) : Euclidean n :=
  initialField Y z x (fderiv ℝ (fun w ↦ Y (x, w)) z h)

/-- The localized correction is globally smooth when its closed support lies
in the actual smoothness domain (`app:ch_background:eq:bg-derivative-trade`). -/
theorem affineExtension_contDiff
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    {O : Set (Euclidean n × CarrierParameter)} (hO : IsOpen O)
    (hχ : ContDiff ℝ ∞ χ) (hY : ContDiffOn ℝ ∞ Y O) (hs : tsupport χ ⊆ O) :
    ContDiff ℝ ∞ (affineExtension A χ Y) := by
  apply (A.contDiff.comp contDiff_fst).add
  apply Localization.contDiff_of_contDiffOn_support_neighborhood hO
  · exact hχ.contDiffOn.smul (hY.sub (A.contDiff.comp contDiff_fst).contDiffOn)
  · exact (tsupport_smul_subset_left χ (fun p ↦ Y p - A p.1)).trans hs

/-- A cutoff plateau gives agreement on a neighborhood, hence preserves all
jets on the complete supported chart (`app:ch_background:eq:bg-derivative-trade`). -/
theorem affineExtension_eventuallyEq
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    {p : Euclidean n × CarrierParameter} (hp : p ∈ interior {q | χ q = 1}) :
    affineExtension A χ Y =ᶠ[𝓝 p] Y := by
  filter_upwards [isOpen_interior.mem_nhds hp] with q hq
  have hχq : χ q = 1 := (interior_subset hq : q ∈ {q | χ q = 1})
  simp only [affineExtension, hχq, one_smul]
  abel

/-- Off the closed cutoff support, the extension retains the reference on a
whole neighborhood (`app:ch_background:eq:bg-derivative-trade`). -/
theorem affineExtension_eventuallyEq_reference
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    {p : Euclidean n × CarrierParameter} (hp : p ∉ tsupport χ) :
    affineExtension A χ Y =ᶠ[𝓝 p] (fun q ↦ A q.1) := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
  change χ q = 0 at hq
  simp only [affineExtension, hq, zero_smul, add_zero]

/-- In particular the spatial derivative is the reference derivative outside
the chart, rather than zero (`app:ch_background:eq:bg-derivative-trade`). -/
theorem fderiv_affineExtension_outside
    (A : Euclidean n →L[ℝ] Euclidean (n - 1))
    {χ : Euclidean n × CarrierParameter → ℝ}
    (Y : Euclidean n × CarrierParameter → Euclidean (n - 1))
    {x : Euclidean n} {z : CarrierParameter} (hp : (x, z) ∉ tsupport χ) :
    fderiv ℝ (fun y ↦ affineExtension A χ Y (y, z)) x = A := by
  have he := (affineExtension_eventuallyEq_reference A Y hp).comp_tendsto
    (continuousAt_id.prodMk continuousAt_const).tendsto
  exact he.fderiv_eq.trans (A.fderiv)

/-- Global smoothness of the scalar phase supplied to `hΦ` of the scalar
transport endpoint (`app:ch_background:prop:bg-adjoint`). -/
theorem phase_contDiff
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n × Euclidean (n - 1) ↦
      phase Y p.1 p.2.1 p.2.2) :=
  (hY.comp (contDiff_snd.fst.prodMk contDiff_fst)).inner ℝ contDiff_snd.snd

/-- Global smoothness of the exact graph supplied to `hY` of the scalar
transport endpoint (`app:ch_background:prop:bg-adjoint`). -/
theorem graph_contDiff
    {Y : Euclidean n × CarrierParameter → Euclidean (n - 1)}
    (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (fun p : CarrierParameter × Euclidean n ↦ (p.1, Y (p.2, p.1))) :=
  contDiff_fst.prodMk (hY.comp (contDiff_snd.prodMk contDiff_fst))

end JanetCartan.ContinuumAdjoint.Canonical.PhaseExtension
