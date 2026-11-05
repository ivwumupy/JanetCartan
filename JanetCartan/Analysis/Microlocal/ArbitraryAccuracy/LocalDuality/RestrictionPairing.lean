module

public import JanetCartan.Analysis.Sobolev.Local.Basic
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Local L² pairing and genuine weak extensions

The representative and infimum steps needed to apply the whole-space Fourier
pairing to `app:ch_regular_base:eq:negative-duality`. Zero extension is used only
for the source; the test function uses a genuine weak Sobolev extension.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {W : Set (EuclideanSpace ℝ (Fin n))} {N : ℕ} {v : LocalL2 W F}

/-- The whole-space L² class of a genuine weak extension, used in
`app:ch_regular_base:eq:negative-duality`. -/
def SobolevExtension.toL2 (e : SobolevExtension W N v) :
    Lp (α := EuclideanSpace ℝ (Fin n)) F 2 := e.memLp_fun.toLp e.toFun

/-- The L² class retains the weak extension's representative a.e.
(`app:ch_regular_base:eq:negative-duality`). -/
theorem SobolevExtension.toL2_coeFn (e : SobolevExtension W N v) :
    e.toL2 =ᵐ[volume] e.toFun := e.memLp_fun.coeFn_toLp

/-- The whole-space class restricts to the original test function
(`app:ch_regular_base:eq:negative-duality`). -/
theorem SobolevExtension.toL2_restrict (e : SobolevExtension W N v) :
    e.toL2 =ᵐ[volume.restrict W] v := by
  have he : e.toL2 =ᵐ[volume.restrict W] e.toFun := ae_restrict_of_ae e.toL2_coeFn
  exact he.trans e.restrict_eq

/-- Descend a uniform bound over genuine extensions to their infimum, including
a zero coefficient. This is the final infimum step of
`app:ch_regular_base:eq:negative-duality`. -/
theorem le_mul_restrictionSobolevNorm_of_extensions (hv : MemRestrictionSobolev W N v)
    {a c : ℝ} (hc : 0 ≤ c)
    (he : ∀ e : SobolevExtension W N v, a ≤ c * e.jetNorm) :
    a ≤ c * restrictionSobolevNorm W N v := by
  obtain rfl | hc := hc.eq_or_lt
  · simpa using he hv.some
  rw [mul_comm c]
  apply (div_le_iff₀ hc).mp
  unfold restrictionSobolevNorm
  refine le_csInf ?_ ?_
  · exact ⟨hv.some.jetNorm, hv.some, rfl⟩
  rintro _ ⟨e, rfl⟩
  exact (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using he e)

end JanetCartan.LocalSobolev

namespace JanetCartan.LocalSobolev

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {W : Set (EuclideanSpace ℝ (Fin n))} {N : ℕ} {v : LocalL2 W F}

/-- Pairing against a zero extension is the actual local pairing whenever the
whole-space test agrees on the domain (`app:ch_regular_base:eq:negative-duality`). -/
theorem inner_zeroExtend_eq_of_restrict
    (hW : MeasurableSet W) (h v : LocalL2 W F)
    (V : Lp (α := EuclideanSpace ℝ (Fin n)) F 2)
    (hV : V =ᵐ[volume.restrict W] v) :
    inner ℝ (SmallSupport.zeroExtend hW h) V = inner ℝ h v := by
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ x, W.indicator (fun y ↦ inner ℝ (h y) (V y)) x := by
      apply integral_congr_ae
      filter_upwards [SmallSupport.zeroExtend_coeFn hW h] with x hx
      rw [hx]
      by_cases hxW : x ∈ W <;> simp [hxW]
    _ = ∫ x in W, inner ℝ (h x) (V x) := integral_indicator hW
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hV] with x hx
      rw [hx]

/-- The test function's genuine extension has exactly the local pairing with
the zero-extended source (`app:ch_regular_base:eq:negative-duality`). -/
theorem SobolevExtension.inner_zeroExtend
    (hW : MeasurableSet W) (h : LocalL2 W F) (e : SobolevExtension W N v) :
    inner ℝ (SmallSupport.zeroExtend hW h) e.toL2 = inner ℝ h v :=
  inner_zeroExtend_eq_of_restrict hW h v e.toL2 e.toL2_restrict

end JanetCartan.LocalSobolev
