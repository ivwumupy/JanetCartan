module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.ImageNormal.PeriodicComparison.OneFactor.WeakAction.BesselRepresentative.SmoothLift

/-!
# Pointwise localization of the smooth Bessel representative

The actual real L² comparison gives equality almost everywhere after the
output mask. Both sides have continuous representatives on Euclidean space:
the output mask lies strictly inside the cell, and the remainder kernel is
smooth with compact support. This supplies the pointwise identity consumed
by `exists_smooth_localized_periodicBesselLift` in
`app:ch_background:prop:bg-frame`, Step 1.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ContDiff SchwartzMap
open JanetCartan.PeriodicLocalL2
open JanetCartan.Pseudodifferential.DifferentialChart
open JanetCartan.ContinuumNormal

namespace JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison.BesselRepresentative

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The smooth representative of the actual lift satisfies the literal
localized comparison, including the nonzero-lattice remainder integral
(`app:ch_background:prop:bg-frame`, Step 1). The smooth representative is
constructed by `exists_smooth_periodicBesselLift`. -/
theorem localized_comparison_of_smooth_lift
    {r R : ℝ} (hr : r < 1 / 2) (hR₀ : 0 < R) (hrR : r < R) (hR : R < 1 / 2)
    (χ ρ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hρ : ContDiff ℝ ∞ ρ)
    (hχs : tsupport χ ⊆ chartBox r) (hρs : tsupport ρ ⊆ chartBox R)
    (v : Fin d → 𝓢(E, ℂ)) (f : EuclideanL2 d E)
    (hf : l2ComplexInclusion volume f =ᵐ[volume]
      fun x ↦ WithLp.toLp 2 (fun j ↦ v j x))
    (w : Torus d → E) (hw : IsSmoothPeriodic w)
    (hlift : ContinuumRow.periodicBesselLift
      (ContinuumRow.cutoffMultiplier (periodizedCutoff hr χ hχ hχs) (toTorus (𝕜 := ℝ) f)) =
      PeriodicSobolevSpace.ofSmooth 1 w hw) :
    ∀ x j, (ρ x : ℂ) * (periodicLift w x j : ℂ) =
      (ρ x : ℂ) * imageBesselSchwartzCLM
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) (v j)) x +
      ∫ y, (localizedImageBesselRemainder ρ χ x y : ℂ) * v j y := by
  have hχR : ∀ x, χ x ≠ 0 → ∀ i, |x i| ≤ R :=
    fun x hx i ↦ (hχs (subset_tsupport χ hx) i).trans hrR.le
  have hρR : ∀ x, ρ x ≠ 0 → ∀ i, |x i| ≤ R :=
    fun x hx ↦ hρs (subset_tsupport ρ hx)
  let hχc := hasCompactSupport_of_imageBessel_cube_support χ hχR
  let hρc := hasCompactSupport_of_imageBessel_cube_support ρ hρR
  let Mχ := realImageCutoffOperator (I := Fin d) χ hχ.continuous hχc
  let Mρ := realImageCutoffOperator (I := Fin d) ρ hρ.continuous hρc
  let g := ContinuumRow.periodicBesselInverse (toTorus (𝕜 := ℝ) (Mχ f))
  have hg : g =ᵐ[volume] w := by
    have he := DFunLike.congr_fun (toTorus_realImageCutoffOperator hr χ hχ hχs) f
    change toTorus (𝕜 := ℝ) (Mχ f) =
      ContinuumRow.cutoffMultiplier (periodizedCutoff hr χ hχ hχs) (toTorus (𝕜 := ℝ) f) at he
    have h := congrArg (PeriodicSobolevSpace.toL2 1) hlift
    rw [ContinuumRow.toL2_periodicBesselLift, ← he] at h
    change g = _ at h
    rw [h]
    exact PeriodicSobolevSpace.toL2_ofSmooth_ae 1 w hw
  have hloc : Mρ (toEuclidean (𝕜 := ℝ) g) =
      Mρ (realImageBesselL2Operator (Mχ f)) +
      realLocalizedImageBesselRemainderOperator hR ρ χ hρ hχ hρR hχR f :=
    DFunLike.congr_fun
      (periodicBesselInverse_localized_eq_add_remainder hR₀.le hR ρ χ hρ hχ hρR hχR) f
  intro x j
  let b := imageBesselSchwartzCLM
    (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) (v j))
  let B := freezingPhysicalMultiplier ρ hρ.continuous hρc (b.toLp 2)
  let Q := localizedImageBesselRemainderOperator hR ρ χ hρ hχ hρR hχR ((v j).toLp 2)
  have hc : complexifiedL2Coordinate volume j (Mρ (toEuclidean (𝕜 := ℝ) g)) = B + Q := by
    rw [hloc, map_add]
    rw [complexifiedL2Coordinate_realImageCutoffOperator,
      complexifiedL2Coordinate_realImageBesselL2Operator,
      cutoff_coordinate_eq_toLp χ hχ hχc v f hf,
      complexifiedL2Coordinate_realLocalizedImageBesselRemainderOperator,
      coordinate_eq_toLp v f hf, imageBesselL2Operator_toLp]
    simp only [B, Q, b, imageBesselSchwartzCLM_apply]
  have hglift := (ae_restrict_iff' measurableSet_halfOpenCell).mp
    (measurePreserving_quotient.quasiMeasurePreserving.ae_eq_comp hg)
  have hleft : complexifiedL2Coordinate volume j (Mρ (toEuclidean (𝕜 := ℝ) g)) =ᵐ[volume]
      fun z ↦ (ρ z : ℂ) * (periodicLift w z j : ℂ) := by
    filter_upwards [complexifiedL2Coordinate_coe volume j (Mρ (toEuclidean (𝕜 := ℝ) g)),
      realImageCutoffOperator_coe ρ hρ.continuous hρc (toEuclidean (𝕜 := ℝ) g),
      toEuclidean_coe (𝕜 := ℝ) g, hglift] with z hz hm he hg'
    rw [hz, hm, he]
    by_cases hρz : ρ z = 0
    · simp [hρz]
    · have hcell : z ∈ halfOpenCell d := chartBox_subset_cell hR
        (hρs (subset_tsupport ρ hρz))
      rw [Set.indicator_of_mem hcell]
      change ((ρ z * g (torusQuotient z) j : ℝ) : ℂ) = _
      have hgz : g (torusQuotient z) = w (torusQuotient z) := hg' hcell
      rw [Complex.ofReal_mul, hgz]
      rfl
  have hrem : Q =ᵐ[volume] fun z ↦
      ∫ y, (localizedImageBesselRemainder ρ χ z y : ℂ) * v j y := by
    filter_upwards [localizedImageBesselRemainderOperator_ae_integral
      hR ρ χ hρ hχ hρR hχR ((v j).toLp 2)] with z hz
    rw [hz]
    apply integral_congr_ae
    filter_upwards [(v j).coeFn_toLp 2] with y hy
    rw [hy]
  have hright : B + Q =ᵐ[volume] fun z ↦ (ρ z : ℂ) * b z +
      ∫ y, (localizedImageBesselRemainder ρ χ z y : ℂ) * v j y := by
    filter_upwards [Lp.coeFn_add B Q,
      freezingPhysicalMultiplier_coeFn ρ hρ.continuous hρc (b.toLp 2),
      b.coeFn_toLp 2, hrem] with z hz hb hb' hq
    rw [hz, Pi.add_apply, hb, hb', hq, Complex.real_smul]
  rw [hc] at hleft
  have hae := hleft.symm.trans hright
  have hK : ContDiff ℝ ∞ (fun p : E × E ↦ localizedImageBesselRemainder ρ χ p.1 p.2) :=
    contDiff_localizedImageBesselRemainder hR ρ χ hρ hχ hρR hχR
  have hKc : HasCompactSupport (fun p : E × E ↦ localizedImageBesselRemainder ρ χ p.1 p.2) :=
    hasCompactSupport_localizedImageBesselRemainder_of_cube_support ρ χ hρR hχR
  have hremc : Continuous (fun z ↦ ∫ y, (localizedImageBesselRemainder ρ χ z y : ℂ) * v j y) :=
    (show Differentiable ℝ _ from fun z ↦ differentiableAt_imageNormal_kernel_integral
      _ hK hKc (v j) ((v j).smooth ⊤) z).continuous
  have hlc : Continuous (fun z ↦ (ρ z : ℂ) * (periodicLift w z j : ℂ)) :=
    (Complex.continuous_ofReal.comp hρ.continuous).mul
      (Complex.continuous_ofReal.comp ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d ↦ ℝ) j).continuous.comp hw.2.continuous))
  have hrc : Continuous (fun z ↦ (ρ z : ℂ) * b z +
      ∫ y, (localizedImageBesselRemainder ρ χ z y : ℂ) * v j y) :=
    ((Complex.continuous_ofReal.comp hρ.continuous).mul b.continuous).add hremc
  exact congrFun ((Continuous.ae_eq_iff_eq volume hlc hrc).mp hae) x

end JanetCartan.ContinuumNormalReduction.ImageNormal.PeriodicComparison.BesselRepresentative
