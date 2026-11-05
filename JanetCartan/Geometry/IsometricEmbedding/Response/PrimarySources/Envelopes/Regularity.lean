module

public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmbientStrain.Exact

/-!
# Smoothness of the complete primary strain

The source in `app:ch_response:cor:current-atoms` is the full linearized metric
of the retained primary atom. Its demodulated amplitude is jointly smooth on
the original leading-wave domain, including the scalar and carrier labels.
No strain regularity or strain estimate is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped ContDiff Matrix.Norms.Frobenius

namespace JanetCartan.ResponsePrimarySources

private theorem contDiffOn_joint_complexLinearizedMetric
    {n N : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : Euclidean n → Euclidean N}
    {W : Euclidean n × Z → EuclideanSpace ℂ (Fin N)}
    {U : Set (Euclidean n)} {Ω : Set (Euclidean n × Z)}
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hspace : MapsTo Prod.fst Ω U)
    (hF : ContDiffOn ℝ ∞ F U) (hW : ContDiffOn ℝ ∞ W Ω) :
    ContDiffOn ℝ ∞
      (fun w ↦ WKB.complexLinearizedMetric F (fun x ↦ W (x, w.2)) w.1) Ω := by
  have hdF (i : Fin n) (k : Fin N) :
      ContDiffOn ℝ ∞ (fun w : Euclidean n × Z ↦ (partialDeriv F w.1 i k : ℂ)) Ω :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (((contDiffOn_piLp 2).mp (contDiffOn_partialDeriv hU hF i) k).comp
        contDiffOn_fst hspace)
  have hdW (i : Fin n) (k : Fin N) : ContDiffOn ℝ ∞
      (fun w ↦ partialDeriv (fun x ↦ W (x, w.2)) w.1 i k) Ω := by
    have hd := (contDiffOn_piLp 2).mp
      ((hW.fderiv_of_isOpen hΩ (m := ∞) (by simp)).clm_apply
        (contDiffOn_const (c := (EuclideanSpace.single i 1, (0 : Z))))) k
    apply hd.congr
    intro w hw
    have he := (hW.contDiffAt (hΩ.mem_nhds hw)).differentiableAt (by simp)
    have hc := (he.hasFDerivAt.comp w.1
      ((hasFDerivAt_id (𝕜 := ℝ) w.1).prodMk (hasFDerivAt_const w.2 w.1))).fderiv
    exact congrArg (fun D : Euclidean n →L[ℝ] EuclideanSpace ℂ (Fin N) ↦
      D (EuclideanSpace.single i 1) k) hc
  let L : (Fin n → Fin n → ℂ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := LinearMap.id
  let C : (Fin n → Fin n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    ⟨L, L.continuous_of_finiteDimensional⟩
  apply C.contDiff.comp_contDiffOn
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  change ContDiffOn ℝ ∞ (fun w ↦ ∑ k : Fin N,
    ((partialDeriv F w.1 i k : ℂ) * partialDeriv (fun x ↦ W (x, w.2)) w.1 j k +
      partialDeriv (fun x ↦ W (x, w.2)) w.1 i k * (partialDeriv F w.1 j k : ℂ))) Ω
  exact ContDiffOn.sum fun k _ ↦ ((hdF i k).mul (hdW j k)).add
    ((hdW i k).mul (hdF j k))

open RawPrimary LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase

/-- Joint smoothness of the literal complete demodulated strain, derived from
the same retained leading outputs. Consumer: the compact source envelope for
`app:ch_response:cor:current-atoms`. This adds no quantitative reserve. -/
theorem contDiffOn_fullPrimaryStrainAmplitude_of_leading_outputs
    {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (Metric.closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) (τ : ℝ)
    {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (hnonzero : ∀ w ∈ Ω,
      nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0) :
    ContDiffOn ℝ ∞ (fullPrimaryStrainAmplitude T Q F row col Φ Y r τ) Ω := by
  have hW := contDiffOn_fullPrimaryAtom_of_leading_outputs
    T Q F row col Φ Y r τ hΩ hspace hphase hF hi hrank hα hnonzero
  have hs := contDiffOn_joint_complexLinearizedMetric hU hΩ
    (fun _ hw ↦ hspace _ hw) hF hW
  have hc : ContDiffOn ℝ ∞
      (fun w ↦ Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 : ℂ) / (τ : ℂ))) Ω :=
    ((contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_fullPhase T Q hphase))).div_const (τ : ℂ)).cexp
  exact hc.smul hs

end JanetCartan.ResponsePrimarySources
