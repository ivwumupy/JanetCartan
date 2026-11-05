module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.FixedSolverAtoms
public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.SourceEnvelope
public import JanetCartan.Geometry.IsometricEmbedding.Response.SignedProductEstimates.ReducedSources
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.SourceNegative.LocalizedQuadratures

/-!
# The smooth solver's admitted datum for the complete primary atom

The two real data used by the smooth solver are the restricted quadratures of
one complex L² class. Its envelope is the half stress contraction of the
literal full strain on the original row, with both physical cutoffs. This
identifies the datum in `app:ch_regular:eq:inverse-remainder` for the response
in `app:ch_response:eq:response-actual-solver-formula`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric MeasureTheory
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CompatibleResponse
open ActualCarriers FrozenMenu CurrentFullPhase RawPrimary LeadingWave.FullModulation
open ResponseTransfer ResponseTransfer.SourceNegative ResponseSourceExtension ResponsePrimarySources
open CorrectedAtoms PrimarySourceAdmission FixedDomainInverse LocalSobolev
open Sampling.BackgroundModulation RegularSector.Characteristic.RetardedLocalization
variable {d N : ℕ} {P : Patch (d + 1)} {U : Set (Euclidean (d + 1))} {hU : IsOpen U}
local notation "E" => Euclidean (d + 1)
local notation "V" => EuclideanSpace ℂ (Fin (d + 1))
local notation "Par" => Euclidean 3 × Euclidean d

/-- Rotation of the complete tensor source commutes with its physical stress
projection, including the half and both original cutoffs
(`app:ch_response:eq:response-full-map`). -/
private theorem cutoffStress_rotated_modulatedSource
    (Q : E → Fin (d + 1) → MetricTensor (d + 1)) (χ η φ : E → ℝ)
    (a : E → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (lam : ℝ) (ζ : ℂ) :
    euclideanCutoffStressSource Q η (tensorFieldRealPart (ζ • modulatedSource χ φ a lam)) =
      fun y ↦ euclideanRealPart (ζ • modulatedSource χ φ
        (fun x ↦ η x • ((1 / 2 : ℝ) • complexStressContraction (Q x) (a x))) lam y) := by
  have he : ζ • modulatedSource χ φ a lam = modulatedSource χ φ (ζ • a) lam := by
    funext y
    simp only [Pi.smul_apply, modulatedSource]
    rw [smul_comm ζ (χ y), smul_comm ζ (carrier lam φ y)]
  rw [he]
  exact (SignedProductEstimates.cutoff_stressSource_real_modulated_eq Q χ η φ (ζ • a) lam).trans
    (by
      funext y
      simp only [modulatedSource, Pi.smul_apply, map_smul]
      rw [smul_comm ζ (χ y), smul_comm ζ (carrier lam φ y), smul_comm ζ (η y),
        smul_comm ζ (1 / 2 : ℝ)]
      exact (euclideanRealPart.map_smul (χ y) _).symm)

/-- Identify both actual admitted smooth sources with the original modulated
reduced source on the inverse's measured domain. Its L² membership is proved
from the two smooth compact quadratures. The independent covector, frequency
`τ⁻¹`, row, strain envelope and both physical cutoffs are unchanged. This is the
source identification for the finite inverse expansion in
`app:ch_response:eq:response-graded-reduced` and for `CorrectedAtoms`. -/
theorem fullPrimary_cutoffStressSmoothSource_quadratures
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : E → Fin (d + 1) → MetricTensor (d + 1) // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : E) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress (d + 1)) < T.family.threshold})
    (F : E → Euclidean N) (row col : Fin (d + 1))
    (Φ Y : ℝ × (Euclidean d × Par) → Euclidean d × Par)
    (r : Euclidean d × Euclidean 3 → ℝ) {Ω : Set (E × Par)} (hΩ : IsOpen Ω)
    (hspace : ∀ w ∈ Ω, w.1 ∈ U) (hphase : ∀ w ∈ Ω, (w.1,w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U) (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hn : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    {core chart : Set E} (χenv : OutputCutoff core chart)
    (χ η : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hη : ContDiff ℝ ∞ η)
    (hs : tsupport χ ⊆ core) (τ : ℝ) (c : Par) (hΩc : ∀ x ∈ tsupport χ, (x,c) ∈ Ω) :
    let atom := complexAtomicSource F χ (fun y ↦ fullPrimaryAtom T Q F row col Φ Y τ r c.1 (y,c.2))
    let a := fullStrainEnvelope T Q F row col Φ Y r χenv τ c
    let reduced := modulatedSource χ (fun y ↦ phase T Q y c.2)
      (fun y ↦ η y • ((1 / 2 : ℝ) • complexStressContraction (Q.1 y) (a y))) τ⁻¹
    ∃ (hre : tensorFieldRealPart atom ∈ compactSmoothSources (tsupport χ))
      (him : tensorFieldImagPart atom ∈ compactSmoothSources (tsupport χ))
      (hm : MemLp reduced 2 volume), ∀ W : Set E,
      let admit := cutoffStressSmoothSource (W := W) Q.1 η hU
        (fun i ↦ contDiffOn_pi.mp Q.property.1 i) hη (fun x hx ↦ hspace (x,c) (hΩc x hx))
      let u := restrictL2 W (hm.toLp reduced)
      (admit ⟨_, hre⟩ : LocalL2 W E) = l2RealPart (volume.restrict W) u ∧
      (admit ⟨_, him⟩ : LocalL2 W E) = l2RealPart (volume.restrict W) (-Complex.I • u) := by
  intro atom a reduced
  have hQU i := contDiffOn_pi.mp Q.property.1 i
  have hSU : tsupport χ ⊆ U := fun x hx ↦ hspace (x,c) (hΩc x hx)
  have hw := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ hΩ hspace hphase
    hF hi hrank hα hn
  obtain ⟨hr, hi'⟩ := fullPrimaryAtom_source_mem T Q F row col Φ Y r hΩ hspace hF τ hw
    c.1 c.2 χ hχ hc hΩc
  let realSource : compactSmoothSources (tsupport χ) := ⟨tensorFieldRealPart atom, hr⟩
  let imagSource : compactSmoothSources (tsupport χ) := ⟨tensorFieldImagPart atom, hi'⟩
  let R := euclideanCutoffStressSource Q.1 η realSource
  let I := euclideanCutoffStressSource Q.1 η imagSource
  have hraw : atom = modulatedSource χ (fun y ↦ phase T Q y c.2) a τ⁻¹ :=
    cutoff_fullPrimaryStrain_eq_modulatedSource T Q F row col Φ Y r χenv χ hs τ c
  have hrot (ζ : ℂ) : euclideanCutoffStressSource Q.1 η (tensorFieldRealPart (ζ • atom)) =
      fun x ↦ euclideanRealPart (ζ • reduced x) := by
    rw [hraw]
    exact cutoffStress_rotated_modulatedSource Q.1 χ η _ a τ⁻¹ ζ
  have hrEq : R = fun x ↦ euclideanRealPart (reduced x) := by
    simpa only [one_smul] using hrot 1
  have himag : tensorFieldImagPart atom = tensorFieldRealPart (-Complex.I • atom) := by
    ext x i j
    change (atom x i j).im = (-Complex.I * atom x i j).re
    simp
  have hiEq : I = fun x ↦ euclideanRealPart (-Complex.I • reduced x) := by
    change euclideanCutoffStressSource Q.1 η (tensorFieldImagPart atom) = _
    rw [himag, hrot]
  have hmR : MemLp R 2 volume := memLp_euclideanCutoffStressSource Q.1 η hU hQU hη hSU realSource
  have hmI : MemLp I 2 volume := memLp_euclideanCutoffStressSource Q.1 η hU hQU hη hSU imagSource
  have hm : MemLp reduced 2 volume := by
    apply ((euclideanComplexInclusion.comp_memLp' hmR).add
      ((euclideanComplexInclusion.comp_memLp' hmI).const_smul Complex.I)).ae_eq
    filter_upwards with x
    ext i
    change ((R x i : ℝ) : ℂ) + Complex.I * ((I x i : ℝ) : ℂ) = reduced x i
    rw [hrEq, hiEq]
    simp [Complex.ext_iff]
  refine ⟨hr, hi', hm, ?_⟩
  intro W admit u
  constructor
  · apply Lp.ext
    filter_upwards [cutoffStressSmoothSource_coeFn (W := W) Q.1 η hU hQU hη hSU realSource,
      euclideanRealPart.coeFn_compLpL u, restrictL2_coeFn W (hm.toLp reduced),
      ae_restrict_of_ae hm.coeFn_toLp] with y h1 h2 h3 h4
    exact h1.trans ((congrFun hrEq y).trans ((congrArg euclideanRealPart (h3.trans h4)).symm.trans h2.symm))
  · apply Lp.ext
    filter_upwards [cutoffStressSmoothSource_coeFn (W := W) Q.1 η hU hQU hη hSU imagSource,
      euclideanRealPart.coeFn_compLpL (-Complex.I • u), Lp.coeFn_smul (-Complex.I) u,
      restrictL2_coeFn W (hm.toLp reduced), ae_restrict_of_ae hm.coeFn_toLp] with y h1 h2 h3 h4 h5
    change (-Complex.I • u) y = -Complex.I • u y at h3
    have hpoint : (-Complex.I • u) y = -Complex.I • reduced y :=
      h3.trans (congrArg (fun v : V ↦ -Complex.I • v) (h4.trans h5))
    exact h1.trans ((congrFun hiEq y).trans ((congrArg euclideanRealPart hpoint).symm.trans h2.symm))

end JanetCartan.CompatibleResponse
