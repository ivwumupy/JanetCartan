module

public import JanetCartan.Analysis.Microlocal.ContinuumNormalReduction.TransportSymbol.Basic
public import JanetCartan.Analysis.Calculus.CompactParameterIntegral
public import JanetCartan.Analysis.Microlocal.Localization.CompactSupport

/-!
# Smooth buffered spectator amplitudes

For Step 1 of `app:ch_background:prop:bg-frame`, smoothness and support of the
literal amplitude follow from the original primitive functions and the inverse
identity. No smoothness of the transformed density or its zero extension is
assumed. The actual chart and coefficient producers must supply these inputs.
-/

@[expose] public noncomputable section
open Set Function Filter MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.ContinuumNormalReduction.TransportSymbol
variable {n N : ℕ}

/-- Primitive regularity on the original chart in
`app:ch_background:eq:bg-full-complex-amplitude`. The hypotheses concern only
masks, the normal field, the reduced covector, and the absolute Jacobian;
they contain no transformed-amplitude regularity or estimate. -/
structure PrimitiveRegularity (a : Coefficients n N) (J : InputVariables n → ℝ)
    (W : Set (InputVariables n)) : Prop where
  leftMeasurement : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦ a.measurement p.1.1) W
  rightMeasurement : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦ a.measurement p.1.2) W
  angular : ContDiff ℝ ∞ a.angular
  high : ContDiff ℝ ∞ a.high
  leftNormal : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦ a.normal (p.1.1, p.2.1)) W
  rightNormal : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦ a.normal (p.1.2, p.2.1)) W
  leftReduced : ∀ i, ContDiffOn ℝ ∞
    (fun p : InputVariables n ↦ a.reduced (p.1.1, p.2.1) i) W
  rightReduced : ∀ i, ContDiffOn ℝ ∞
    (fun p : InputVariables n ↦ a.reduced (p.1.2, p.2.1) i) W
  jacobian : ContDiffOn ℝ ∞ J W
  jacobian_ne_zero : ∀ p ∈ W, J p ≠ 0
  covector_ne_zero : ∀ p ∈ W, p.2.2 ≠ 0

private theorem matrix_contDiffOn_of_entries {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {W : Set E} {f : E → Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i j, ContDiffOn ℝ ∞ (fun p ↦ f p i j) W) : ContDiffOn ℝ ∞ f W := by
  let e : (Fin n × Fin n → ℝ) ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := fun g i j ↦ g (i, j)
      invFun := fun A ij ↦ A ij.1 ij.2
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact e.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (contDiffOn_pi.mpr fun ij ↦ h ij.1 ij.2)

/-- Smoothness of the explicit original density follows from primitive
regularity and the two nonvanishing conditions. Source:
`app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem inputDensity_contDiffOn {a : Coefficients n N} {J : InputVariables n → ℝ}
    {W : Set (InputVariables n)} (h : PrimitiveRegularity a J W) :
    ContDiffOn ℝ ∞ (inputDensity a J) W := by
  have hnorm : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦ ‖p.2.2‖) W :=
    contDiffOn_snd.snd.norm ℝ h.covector_ne_zero
  have hdir : ContDiffOn ℝ ∞ (fun p : InputVariables n ↦ ‖p.2.2‖⁻¹ • p.2.2) W :=
    (hnorm.inv (fun p hp ↦ norm_ne_zero_iff.mpr (h.covector_ne_zero p hp))).smul
      contDiffOn_snd.snd
  have hweight : ContDiffOn ℝ ∞ (inputWeight a J) W :=
    (((((h.leftMeasurement.mul h.rightMeasurement).mul
      ((h.angular.comp_contDiffOn (contDiffOn_snd.fst.prodMk hdir)).pow 2)).mul
      ((h.high.comp_contDiffOn hnorm).pow 2)).mul hnorm).div h.jacobian
      h.jacobian_ne_zero).mul (h.leftNormal.norm_sq ℝ) |>.mul (h.rightNormal.norm_sq ℝ)
  apply matrix_contDiffOn_of_entries
  intro i j
  exact hweight.mul ((h.leftReduced i).mul (h.rightReduced j))

/-- Joint inverse substitution is smooth when the actual inverse is smooth.
Source: `app:ch_background:eq:bg-full-complex-amplitude`. -/
theorem inverseCoordinates_contDiffOn
    {u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1)}
    {Ω : Set (Variables n × Euclidean 2)} (hu : ContDiffOn ℝ ∞ u Ω) :
    ContDiffOn ℝ ∞ (inverseCoordinates u) Ω :=
  (contDiffOn_fst.fst.prodMk contDiffOn_fst.snd.fst).prodMk
    ((hu.fst.prodMk contDiffOn_snd).prodMk hu.snd)

/-- The support of the literal zero extension is transported from the
primitive masks, using the actual right-inverse identity. No support property
of the transformed amplitude is assumed (`app:ch_background:prop:bg-frame`). -/
theorem support_extendedDensity_subset
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} {W L : Set (InputVariables n)}
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ L) :
    support (extendedDensity a J u Ω) ⊆ F '' L := by
  intro p hp
  have hpΩ : p ∈ Ω := by
    by_contra h
    exact hp (by simp [extendedDensity, h])
  have hn : inputDensity a J (inverseCoordinates u p) ≠ 0 := by
    simpa only [mem_support, extendedDensity, indicator_of_mem hpΩ] using hp
  have hleft : a.measurement (inverseCoordinates u p).1.1 ≠ 0 := by
    intro hz
    exact hn (by simp [inputDensity, inputWeight, hz])
  have hright' : a.measurement (inverseCoordinates u p).1.2 ≠ 0 := by
    intro hz
    exact hn (by simp [inputDensity, inputWeight, hz])
  have hang : a.angular ((inverseCoordinates u p).2.1,
      ‖(inverseCoordinates u p).2.2‖⁻¹ • (inverseCoordinates u p).2.2) ≠ 0 := by
    intro hz
    exact hn (by simp [inputDensity, inputWeight, hz])
  have hhi : a.high ‖(inverseCoordinates u p).2.2‖ ≠ 0 := by
    intro hz
    exact hn (by simp [inputDensity, inputWeight, hz])
  exact ⟨inverseCoordinates u p, hs _ (hmap hpΩ) hleft hright' hang hhi, hright p hpΩ⟩

/-- Smooth zero extension follows from the input masks, the output buffer and
primitive regularity, even for an unbounded conic chart. Source:
`app:ch_background:prop:bg-frame`, Step 1. -/
theorem extendedDensity_contDiff
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} {W L : Set (InputVariables n)}
    (hΩ : IsOpen Ω) (h : PrimitiveRegularity a J W) (hu : ContDiffOn ℝ ∞ u Ω)
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ L)
    (hclosed : IsClosed (F '' L)) (hbuffer : F '' L ⊆ Ω) :
    ContDiff ℝ ∞ (extendedDensity a J u Ω) := by
  apply Localization.contDiff_of_contDiffOn_support_neighborhood hΩ
  · apply ((inputDensity_contDiffOn h).comp (inverseCoordinates_contDiffOn hu) hmap).congr
    intro p hp
    exact indicator_of_mem hp _
  · exact (closure_minimal
      (support_extendedDensity_subset a J u F hmap hright hs) hclosed).trans hbuffer

/-- Every jet off the inverse chart vanishes because of the closed output
buffer. Smoothness of the extended amplitude is not needed for this fact.
Source: `app:ch_background:prop:bg-frame`, Step 1. -/
theorem iteratedFDeriv_extendedDensity_eq_zero
    (a : Coefficients n N) (J : InputVariables n → ℝ)
    (u : Variables n × Euclidean 2 → ℝ × Euclidean (n - 1))
    (F : InputVariables n → Variables n × Euclidean 2)
    {Ω : Set (Variables n × Euclidean 2)} {W L : Set (InputVariables n)}
    (hmap : MapsTo (inverseCoordinates u) Ω W)
    (hright : ∀ p ∈ Ω, F (inverseCoordinates u p) = p)
    (hs : ∀ p ∈ W, a.measurement p.1.1 ≠ 0 → a.measurement p.1.2 ≠ 0 →
      a.angular (p.2.1, ‖p.2.2‖⁻¹ • p.2.2) ≠ 0 → a.high ‖p.2.2‖ ≠ 0 → p ∈ L)
    (hclosed : IsClosed (F '' L)) (hbuffer : F '' L ⊆ Ω)
    {p : Variables n × Euclidean 2} (hp : p ∉ Ω) (j : ℕ) :
    iteratedFDeriv ℝ j (extendedDensity a J u Ω) p = 0 := by
  have hsupport : tsupport (extendedDensity a J u Ω) ⊆ Ω :=
    (closure_minimal (support_extendedDensity_subset a J u F hmap hright hs) hclosed).trans
      hbuffer
  have he := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hp (hsupport h))
  simpa using (he.iteratedFDeriv ℝ j).eq_of_nhds

end JanetCartan.ContinuumNormalReduction.TransportSymbol
