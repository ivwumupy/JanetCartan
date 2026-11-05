module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.JointRegularity

/-!
# Joint regularity of the actual full primary source

For `app:ch_response:cor:current-atoms`, the source is the complete strain of
`fullPrimaryAtom`, cut off afterwards by the original fixed source cutoff.
The physical source is globally smooth jointly with the retained parameters
on any open parameter chart whose entire source support stays in the raw chart.
No regularity of the response output is used.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius JanetCartan.TensorFrobenius

namespace JanetCartan.ResponseSmoothParameters
open ResponseSourceExtension PrimarySourceAdmission CorrectedAtoms
open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- The full physical strain is jointly smooth with the source parameters
(`app:ch_waves:eq:exact-half-strain`). Its derivatives are physical derivatives
of the SAME joint field, with the parameters held fixed. -/
theorem contDiffOn_jointComplexStrain
    {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N} {W : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    {U : Set (Euclidean n)} {Ω : Set (Euclidean n × Z)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W Ω) :
    ContDiffOn ℝ ∞
      (fun w ↦ WKB.complexLinearizedMetric F (fun x ↦ W (x, w.2)) w.1) Ω := by
  let L : (Fin n → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.id
  let C : (Fin n → Fin n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  apply C.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  have hf (i : Fin n) (k : Fin N) :
      ContDiffOn ℝ ∞ (fun w : Euclidean n × Z ↦ (partialDeriv F w.1 i k : ℂ)) Ω :=
    (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_euclidean.mp (contDiffOn_partialDeriv hU hF i) k)).comp
        contDiffOn_fst hspace
  have hw (i : Fin n) (k : Fin N) :
      ContDiffOn ℝ ∞
        (fun w : Euclidean n × Z ↦ partialDeriv (fun x ↦ W (x, w.2)) w.1 i k) Ω := by
    have hh := (contDiffOn_piLp 2).mp
      ((hW.fderiv_of_isOpen hΩ (m := ∞) (by simp)).clm_apply
        (contDiffOn_const (c := (EuclideanSpace.single i 1, (0 : Z))))) k
    apply hh.congr
    intro w hw
    have hd := ((hW.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp)).hasFDerivAt.comp w.1
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) w.1 w.2)
    exact congrArg (fun D ↦ D (EuclideanSpace.single i 1) k) hd.fderiv
  exact ContDiffOn.sum (s := Finset.univ) (fun k _ ↦
    ((hf i k).mul (hw j k)).add ((hw i k).mul (hf j k)))

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)

/-- The literal full primary source is jointly smooth on the whole physical
space and the retained parameter chart. The original cutoff is applied after
the complete strain and is never shrunk (`app:ch_response:cor:current-atoms`).
The raw regularity premise is discharged from the retained geometry. -/
theorem contDiffOn_fullPrimaryAtom_source
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {V : Set (Euclidean 3 × Euclidean (n - 1))} (_hV : IsOpen V)
    (hsrc : ∀ c ∈ V, ∀ x ∈ tsupport χ, (x, c) ∈ Ω) (τ : ℝ) :
    ContDiffOn ℝ ∞
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        complexAtomicSource F χ
          (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1)
      (univ ×ˢ V) := by
  have hw := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
    hΩ hspace hphase hF hi hrank hα hnonzero
  have hs := contDiffOn_jointComplexStrain hU hΩ hspace hF hw
  intro w hwV
  by_cases hx : w.1 ∈ tsupport χ
  · exact ((hχ.contDiffAt.comp w contDiffAt_fst).smul
      (hs.contDiffAt (hΩ.mem_nhds (hsrc w.2 hwV.2 w.1 hx)))).contDiffWithinAt
  · apply ContDiffAt.contDiffWithinAt
    apply (contDiffAt_const (c := (0 : Matrix (Fin n) (Fin n) ℂ))).congr_of_eventuallyEq
    have he : (fun z : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦ χ z.1)
        =ᶠ[𝓝 w] (fun _ ↦ 0) :=
      (notMem_tsupport_iff_eventuallyEq.mp hx).comp_tendsto (continuous_fst.tendsto w)
    filter_upwards [he]
      with z hz
    simp only [complexAtomicSource, hz, zero_smul]

/-- Both real source quadratures have joint regularity on the same chart
(`app:ch_response:cor:current-atoms`). This feeds the real fixed response; no
complex response or independent quadrature inverse is selected. -/
theorem contDiffOn_fullPrimaryAtom_source_quadratures
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ)
    {V : Set (Euclidean 3 × Euclidean (n - 1))} (hV : IsOpen V)
    (hsrc : ∀ c ∈ V, ∀ x ∈ tsupport χ, (x, c) ∈ Ω) (τ : ℝ) :
    ContDiffOn ℝ ∞
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        tensorFieldRealPart (complexAtomicSource F χ
          (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2))) w.1)
      (univ ×ˢ V) ∧
    ContDiffOn ℝ ∞
      (fun w : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) ↦
        tensorFieldImagPart (complexAtomicSource F χ
          (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2))) w.1)
      (univ ×ˢ V) := by
  have hs := contDiffOn_fullPrimaryAtom_source T Q F row col Φ Y r hΩ hspace
    hphase hF hi hrank hα hnonzero χ hχ hV hsrc τ
  let R : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] MetricTensor n :=
    { toFun := fun A i j ↦ (A i j).re
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  let I : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] MetricTensor n :=
    { toFun := fun A i j ↦ (A i j).im
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  exact ⟨(⟨R, R.continuous_of_finiteDimensional⟩ : _ →L[ℝ] _).contDiff.comp_contDiffOn hs,
    (⟨I, I.continuous_of_finiteDimensional⟩ : _ →L[ℝ] _).contDiff.comp_contDiffOn hs⟩

end JanetCartan.ResponseSmoothParameters
