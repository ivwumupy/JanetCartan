module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.Basic
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Restriction

/-!
# The original source under restriction and zero extension

The complete cutoff source is the zero extension of its restriction to any
measured domain containing that same cutoff support. This identifies the
source used by the local inverse with the original Fourier class, without
truncating its amplitude or changing Lebesgue measure.
Source: `app:ch_regular:eq:inverse-remainder`.
-/

@[expose] public noncomputable section
open Set MeasureTheory
namespace JanetCartan.ResponseTransfer.SourceNegative
open RegularSector.Characteristic.RetardedLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
local notation "F" => EuclideanSpace ℂ (Fin q)

/-- Restricting the ORIGINAL modulated source and extending it by zero gives
exactly its original L² class. The actual source cutoff supplies support, so
no additional source projection or analytic output premise is required.
Consumer: the source norm of `ArbitraryAccuracy.inverse_remainder_restrictionSobolev`
(`app:ch_regular:eq:inverse-remainder`). -/
theorem zeroExtend_restrictL2_modulatedSource
    {W : Set E} (hW : MeasurableSet W) (χ φ : E → ℝ)
    (f : E → F) (lam : ℝ) (hs : tsupport χ ⊆ W)
    (hm : MemLp (modulatedSource χ φ f lam) 2 volume) :
    SmallSupport.zeroExtend hW (restrictL2 W (hm.toLp (modulatedSource χ φ f lam))) =
      hm.toLp (modulatedSource χ φ f lam) := by
  apply Lp.ext
  have hr := (ae_restrict_iff' hW).mp (restrictL2_coeFn W (hm.toLp _))
  filter_upwards [SmallSupport.zeroExtend_coeFn hW (restrictL2 W (hm.toLp _)),
    hr, hm.coeFn_toLp] with x hx hr hf
  rw [hx]
  by_cases hxW : x ∈ W
  · exact (indicator_of_mem hxW _).trans (hr hxW)
  · rw [indicator_of_notMem hxW, hf]
    have hχ : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hxW (hs h))
    simp only [modulatedSource, hχ, zero_smul]

end JanetCartan.ResponseTransfer.SourceNegative
