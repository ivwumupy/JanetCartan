module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.QuadratureSource

/-!
# The inner inverse cutoff on the original real quadratures

The input of the fixed Neumann inverse is a physical multiplication on the
restricted real datum. It equals the quadrature of the complex source with the
product of the two original cutoffs, with no change of phase, measure or
frequency (`app:ch_regular:eq:inverse-remainder`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped NNReal ENNReal
namespace JanetCartan.ResponseTransfer.SourceNegative
open RegularSector.Characteristic.RetardedLocalization SmallSupport
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local instance : Fact (1 ≤ ((2 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual inner bump in `correctedSource` multiplies the original source
cutoff on either real quadrature. The equality is in the original restricted
L² space; the two cutoffs need no plateau relation
(`app:ch_response:eq:response-actual-solver-formula`,
`app:ch_regular:eq:inverse-remainder`). -/
theorem bumpL2_restrict_modulatedSource_quadrature
    (W : Set E) {x : E} (χ₂ : ContDiffBump x) (χ φ : E → ℝ)
    (f : E → F) (lam : ℝ)
    (hm : MemLp (modulatedSource χ φ f lam) 2 volume)
    (hloc : MemLp (modulatedSource ((χ₂ : E → ℝ) * χ) φ f lam) 2 volume)
    (ζ : ℂ) :
    bumpL2 (p := 2) le_rfl χ₂
        (l2RealPart (volume.restrict W) (ζ • restrictL2 W (hm.toLp _))) =
      l2RealPart (volume.restrict W) (ζ • restrictL2 W (hloc.toLp _)) := by
  let u := restrictL2 W (hm.toLp _)
  let v := restrictL2 W (hloc.toLp _)
  apply Lp.ext
  filter_upwards [bumpL2_coeFn (p := 2) le_rfl χ₂ (l2RealPart (volume.restrict W) (ζ • u)),
    euclideanRealPart.coeFn_compLpL (ζ • u), euclideanRealPart.coeFn_compLpL (ζ • v),
    Lp.coeFn_smul ζ u, Lp.coeFn_smul ζ v, restrictL2_coeFn W (hm.toLp _),
    restrictL2_coeFn W (hloc.toLp _), ae_restrict_of_ae hm.coeFn_toLp,
    ae_restrict_of_ae hloc.coeFn_toLp] with y hb hru hrv hsu hsv hu hv hmu hmv
  change (l2RealPart (volume.restrict W) (ζ • u)) y = euclideanRealPart ((ζ • u) y) at hru
  change (l2RealPart (volume.restrict W) (ζ • v)) y = euclideanRealPart ((ζ • v) y) at hrv
  change u y = _ at hu
  change v y = _ at hv
  change (bumpL2 (p := 2) le_rfl χ₂ (l2RealPart (volume.restrict W) (ζ • u))) y =
    (l2RealPart (volume.restrict W) (ζ • v)) y
  rw [hb, hru, hrv, hsu, hsv, Pi.smul_apply, Pi.smul_apply, hu, hv, hmu, hmv]
  simp only [modulatedSource, Pi.mul_apply, mul_smul, ← map_smul]
  rw [smul_comm (χ₂ y) ζ]

end JanetCartan.ResponseTransfer.SourceNegative
