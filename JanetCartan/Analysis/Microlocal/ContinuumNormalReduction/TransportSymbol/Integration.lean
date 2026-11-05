module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Smooth

/-!
# Differentiating the compact spectator integral

All parameter jets commute with the fixed Lebesgue spectator integral in
`app:ch_background:eq:bg-full-complex-amplitude`. Compactness and joint
smoothness supply domination; no interchange assumption is introduced.
-/

@[expose] public noncomputable section
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Every joint derivative passes through the compact spectator integral in
`app:ch_background:eq:bg-full-complex-amplitude`. The auxiliary Banach target
allows the induction to apply to derivatives, including matrix-valued ones. -/
theorem iteratedFDeriv_spectatorIntegral {K : Set (Euclidean 2)} (hK : IsCompact K)
    (j : ℕ) {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : Variables n × Euclidean 2 → G} (hf : ContDiff ℝ ∞ f) (x : Variables n) :
    iteratedFDeriv ℝ j (fun y ↦ ∫ v in K, f (y, v)) x =
      ∫ v in K, iteratedFDeriv ℝ j (fun y ↦ f (y, v)) x := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  induction j generalizing G with
  | zero =>
    let L := (continuousMultilinearCurryFin0 ℝ (Variables n) G).symm
    exact (L.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ j ih =>
    let g : Variables n × Euclidean 2 → Variables n →L[ℝ] G :=
      fun p ↦ fderiv ℝ (fun y ↦ f (y, p.2)) p.1
    have hg : ContDiff ℝ ∞ g := by
      apply contDiffOn_univ.mp
      simpa only [univ_prod_univ] using
        contDiffOn_parameterFDeriv (U := univ) (V := univ) isOpen_univ isOpen_univ
          hf.contDiffOn
    have he : fderiv ℝ (fun y ↦ ∫ v in K, f (y, v)) =
        fun y ↦ ∫ v in K, g (y, v) := by
      funext y
      exact fderiv_compactParameterIntegral (U := univ) (V := univ)
        isOpen_univ isOpen_univ hK (subset_univ K) hf.contDiffOn (mem_univ y)
    rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, he, ih hg]
    let L := (continuousMultilinearCurryRightEquiv' ℝ j (Variables n) G).symm
    change L (∫ v in K, iteratedFDeriv ℝ j (fun y ↦ g (y, v)) x) = _
    calc
      _ = ∫ v in K, L (iteratedFDeriv ℝ j (fun y ↦ g (y, v)) x) :=
        (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ)
          (E := Variables n [×j]→L[ℝ] Variables n →L[ℝ] G)
          (F := Variables n [×(j + 1)]→L[ℝ] G) L.toContinuousLinearEquiv _).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with v
        exact (iteratedFDeriv_succ_eq_comp_right (f := fun y ↦ f (y, v))).symm

section PrimitiveInputs
variable (a : Coefficients n N) (J : InputVariables n → ℝ)
  (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
  (F : InputVariables n → Variables n × Euclidean 2)
  {Ω : Set (Variables n × Euclidean 2)} {W L : Set (InputVariables n)}
  (hΩ : IsOpen Ω) (h : PrimitiveRegularity a J W) (hu : ContDiffOn ℝ ∞ u Ω)
  (hmap : MapsTo (inverseCoordinates u) Ω W)
  (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
  (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
    a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ L)
  (hclosed : IsClosed (F '' L)) (hbuffer : F '' L ⊆ Ω)
  {K : Set (Euclidean 2)} (hK : IsCompact K)

include hΩ h hu hmap hright hs hclosed hbuffer hK

/-- The actual spectator amplitude is globally smooth, including the boundary
of the inverse chart, from primitive regularity and the support buffers.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem amplitude_contDiff : ContDiff ℝ ∞ (amplitude a J u Ω K) := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  apply contDiffOn_univ.mp
  exact contDiffOn_compactParameterIntegral isOpen_univ isOpen_univ hK (subset_univ K)
    (extendedDensity_contDiff a J u F hΩ h hu hmap hright hs hclosed hbuffer).contDiffOn

/-- All actual amplitude jets equal the integrals of the density jets.
The primitive geometric inputs and buffers imply all domination and
integrability needed for this identity (`app:ch_background:eq:bg-full-complex-amplitude`). -/
theorem iteratedFDeriv_amplitude (j : ℕ) (x : Variables n) :
    iteratedFDeriv ℝ j (amplitude a J u Ω K) x =
      ∫ v in K, iteratedFDeriv ℝ j (fun y ↦ extendedDensity a J u Ω (y, v)) x :=
  iteratedFDeriv_spectatorIntegral hK j
    (extendedDensity_contDiff a J u F hΩ h hu hmap hright hs hclosed hbuffer) x

end PrimitiveInputs
end JanetCartan.ContinuumNormalReduction.TransportSymbol
