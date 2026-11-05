module

public import JanetCartan.Geometry.IsometricEmbedding.Response.CorrectedAtoms.Amplitudes
public import JanetCartan.Geometry.IsometricEmbedding.Waves.RawPrimary.AmplitudeGrades.Polynomial.Formulas

/-!
# Joint amplitude maps on the original scalar span

The consumer is `app:ch_response:eq:current-density-lipschitz`. Physical
differentiation preserves the scalar linearity already proved for the SAME raw
atoms and response. The auxiliary joint cutoff only realizes chart amplitudes
as globally defined linear maps; it does not change the response or its source.
On its plateau all joint jets agree with the literal amplitudes.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius

namespace JanetCartan.CorrectedAtoms
open RawPrimary LeadingWave LeadingWave.FullModulation ActualCarriers FrozenMenu CurrentFullPhase
open ResponseSourceExtension PrimarySourceAdmission RawPrimary.AmplitudeGrades.Polynomial

/-- Local scalar linearity passes through the physical derivative in
`app:ch_response:cor:current-atoms`. This helper never differentiates the inverse
operator with respect to a carrier parameter. -/
private def fieldDerivativeLinearMap {S E G : Type*} [AddCommGroup S] [Module ℝ S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    (W : S → E → G) (L : S →ₗ[ℝ] (O → G)) (hL : ∀ r y, L r y = W r y)
    (hW : ∀ r, DifferentiableAt ℝ (W r) x) : S →ₗ[ℝ] (E →L[ℝ] G) where
  toFun r := fderiv ℝ (W r) x
  map_add' r s := by
    have he : W (r + s) =ᶠ[𝓝 x] W r + W s := by
      filter_upwards [hO.mem_nhds hx] with y hy
      have hh := congrFun (L.map_add r s) ⟨y, hy⟩
      simpa only [hL, Pi.add_apply] using hh
    exact he.fderiv_eq.trans (fderiv_add (hW r) (hW s))
  map_smul' a r := by
    have he : W (a • r) =ᶠ[𝓝 x] a • W r := by
      filter_upwards [hO.mem_nhds hx] with y hy
      have hh := congrFun (L.map_smul a r) ⟨y, hy⟩
      simpa only [hL, Pi.smul_apply] using hh
    exact he.fderiv_eq.trans (fderiv_const_smul (hW r) a)

/-- A fixed chart cutoff preserves pointwise scalar linearity
(`app:ch_response:eq:current-density-lipschitz`). Its literal values, not chosen
linear representatives, define the family. -/
private def cutoffFamilyLinearMap {S D E : Type*} [AddCommGroup S] [Module ℝ S]
    [TopologicalSpace D] [AddCommGroup E] [Module ℝ E]
    (ψ : D → ℝ) (f : S → D → E)
    (h : ∀ x ∈ tsupport ψ, ∃ L : S →ₗ[ℝ] E, ∀ r, L r = f r x) :
    S →ₗ[ℝ] (D → E) where
  toFun r x := ψ x • f r x
  map_add' r s := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · obtain ⟨L, hL⟩ := h x hx
      change ψ x • f (r + s) x = ψ x • f r x + ψ x • f s x
      rw [← hL, ← hL, ← hL, map_add, smul_add]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  map_smul' a r := by
    funext x
    by_cases hx : x ∈ tsupport ψ
    · obtain ⟨L, hL⟩ := h x hx
      change ψ x • f (a • r) x = a • (ψ x • f r x)
      rw [← hL, ← hL, map_smul]
      exact smul_comm _ _ _
    · simp [image_eq_zero_of_notMem_tsupport hx]

/-- The leading tensor is linear in the leading covector, with its original
negative sign (`app:ch_waves:eq:arbitrary-b-amplitudes`). -/
private def principalMatrixLinearMap {n N : ℕ} (L : MetricTensor n →ₗ[ℝ] Euclidean N)
    (ξ : Euclidean n) : Euclidean n →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ where
  toFun b := (principalMatrix (principalNormal L ξ b) ξ).map Complex.ofReal
  map_add' b c := by
    have he : symmetricProduct ξ (b + c) = symmetricProduct ξ b + symmetricProduct ξ c := by
      ext i j
      simp only [symmetricProduct, PiLp.add_apply, Matrix.add_apply]
      ring
    ext i j
    simp only [principalNormal, he, map_add, principalMatrix, Matrix.map_apply,
      PiLp.add_apply, Matrix.add_apply, add_mul, neg_add_rev, Complex.ofReal_add,
      Complex.ofReal_neg, Complex.ofReal_mul]
    ring
  map_smul' a b := by
    ext i j
    simp only [principalNormal_smul, principalMatrix, Matrix.map_apply, PiLp.smul_apply,
      Matrix.smul_apply, smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_mul,
      RingHom.id_apply, Complex.real_smul]
    ring

variable {n N : ℕ} {P : Patch n} {U : Set (Euclidean n)} {hU : IsOpen U}
    (T : PatchQuantitativeFamily P U hU)
    (Q : {Q : Euclidean n → Fin n → MetricTensor n // ContDiffOn ℝ ∞ Q U ∧
      cNorm (closedBall (0 : Euclidean n) T.data.localReference.stateRadius) 6
        (Q - fun _ ↦ cubeStress n) < T.family.threshold})
    (F : Euclidean n → Euclidean N) (row col : Fin n)
    (Φ Y : ℝ × (Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1))) →
      Euclidean (n - 1) × (Euclidean 3 × Euclidean (n - 1)))

/-- The SAME leading matrix as a real-linear map of the original scalar,
jointly in physical and carrier variables
(`app:ch_response:eq:current-density-lipschitz`). -/
def fullLeadingPrincipalMatrixLinearMap : (Euclidean (n - 1) × Euclidean 3 → ℝ) →ₗ[ℝ]
    (Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Matrix (Fin N) (Fin n) ℂ) where
  toFun := fullLeadingPrincipalMatrix T Q F row col Φ Y
  map_add' r s := by
    funext w
    change principalMatrixLinearMap (AmbientResponse.canonicalNormalCompletion F w.1)
      (phaseGradient T Q w.1 w.2.2) (fullLeadingCovectorLinearMap T Q F row col Φ Y (r + s) w) =
      principalMatrixLinearMap (AmbientResponse.canonicalNormalCompletion F w.1)
        (phaseGradient T Q w.1 w.2.2) (fullLeadingCovectorLinearMap T Q F row col Φ Y r w) +
      principalMatrixLinearMap (AmbientResponse.canonicalNormalCompletion F w.1)
        (phaseGradient T Q w.1 w.2.2) (fullLeadingCovectorLinearMap T Q F row col Φ Y s w)
    simp only [map_add, Pi.add_apply]
  map_smul' a r := by
    funext w
    change principalMatrixLinearMap (AmbientResponse.canonicalNormalCompletion F w.1)
      (phaseGradient T Q w.1 w.2.2) (fullLeadingCovectorLinearMap T Q F row col Φ Y (a • r) w) =
      a • principalMatrixLinearMap (AmbientResponse.canonicalNormalCompletion F w.1)
        (phaseGradient T Q w.1 w.2.2) (fullLeadingCovectorLinearMap T Q F row col Φ Y r w)
    simp only [map_smul, Pi.smul_apply]

/-- The linear leading map has the literal retained values, without choosing
another leading tensor (`app:ch_response:cor:current-atoms`). -/
@[simp] theorem fullLeadingPrincipalMatrixLinearMap_apply
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ) :
    fullLeadingPrincipalMatrixLinearMap T Q F row col Φ Y r =
      fullLeadingPrincipalMatrix T Q F row col Φ Y r := rfl

variable {Ω : Set (Euclidean n × (Euclidean 3 × Euclidean (n - 1)))}
    (hΩ : IsOpen Ω) (hspace : ∀ w ∈ Ω, w.1 ∈ U)
    (hphase : ∀ w ∈ Ω, (w.1, w.2.2) ∈ phaseDomain T)
    (hF : ContDiffOn ℝ ∞ F U) (hi : IsImmersionOn F U)
    (hrank : HasFullNormalRankOn F U)
    (hnonzero : ∀ w ∈ Ω, nullvector T Q col w ≠ 0 ∧ conullvector T Q row w ≠ 0)

include hΩ hspace hphase hF hi hrank hnonzero

/-- The original raw derivative amplitude is the demodulated physical
derivative on the retained chart. This specializes the checked corrected-field
identity at the zero response, solely to establish raw scalar linearity
(`app:ch_waves:eq:individual-representation`). -/
theorem fullDerivativeAmplitude_eq_demodulated
    (r : Euclidean (n - 1) × Euclidean 3 → ℝ)
    (hα : ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    {τ : ℝ} (hτ : τ ≠ 0)
    {w : Euclidean n × (Euclidean 3 × Euclidean (n - 1))} (hw : w ∈ Ω) :
    fullDerivativeAmplitude T Q F row col Φ Y r τ w =
      Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ)) •
        (fun i j ↦ partialDeriv
          (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1 j i) := by
  have hzero : fullPrimaryResponse T Q F row col Φ Y 0 0 τ r w.2 = 0 := by
    ext x i
    simp [fullPrimaryResponse, complexifyResponse]
  have hcorr : fullCorrectedPrimaryAtom T Q F row col Φ Y 0 0 τ r w.2 =
      (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) := by
    change (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) -
      fullPrimaryResponse T Q F row col Φ Y 0 0 τ r w.2 = _
    rw [hzero, sub_zero]
  have hy : fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y 0 0 r τ w = 0 := by
    simp [fullPrimaryResponseDerivativeAmplitude, hzero, partialDeriv]
    rfl
  have hh := fullCorrectedDerivativeAmplitude_eq_demodulated T Q F row col Φ Y 0 0 r
    hΩ hspace hphase hF hi hrank hα hnonzero hτ hw
    (by rw [hzero]; exact differentiableAt_const _)
  simpa only [fullCorrectedDerivativeAmplitude, hy, sub_zero, hcorr] using hh

/-- The raw and leading amplitudes have linear realizations on the original
scalar span without requiring a response estimate. This is the raw input to
`app:ch_response:eq:current-density-lipschitz`; only the given chart cutoff is
used, and the literal amplitudes are unchanged on its plateau. -/
theorem exists_cutoffRawAmplitudeLinearMaps
    {z₀ : Euclidean 3} {R Mᵣ m : ℝ}
    (hα : ∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (ψ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ)
    (hψ : tsupport ψ ⊆ Ω) {τ : ℝ} (hτ : τ ≠ 0) :
    ∃ Apr A₀ : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
        (Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Matrix (Fin N) (Fin n) ℂ),
      ∀ r, Apr r = (fun w ↦ ψ w • fullDerivativeAmplitude T Q F row col Φ Y r τ w) ∧
        A₀ r = (fun w ↦ ψ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w) := by
  let S := initialScalarSpan (n := n) z₀ R Mᵣ m
  have hαspan (r : S) :=
    contDiffOn_scalarAmplitude_of_mem_initialScalarSpan T Q F row col Φ Y hα r.property
  have hpoint (w) (hw : w ∈ tsupport ψ) :
      ∃ A : S →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ,
        ∀ r, A r = fullDerivativeAmplitude T Q F row col Φ Y r τ w := by
    let O : Set (Euclidean n) := {x | (x, w.2) ∈ Ω}
    have ho : IsOpen O := hΩ.preimage (continuous_id.prodMk continuous_const)
    let W : S →ₗ[ℝ] (O → EuclideanSpace ℂ (Fin N)) :=
      { toFun r x := fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)
        map_add' r s := by
          funext x
          exact fullPrimaryAtom_initial_add T Q F row col Φ Y hΩ hspace hphase
            hF hi hnonzero τ (r := r) (s := s) (hαspan r) (hαspan s)
            (w := (x, w.2)) x.property
        map_smul' c r := by
          funext x
          exact fullPrimaryAtom_initial_smul T Q F row col Φ Y hΩ hspace hphase
            hF hi hnonzero τ (r := r) (hαspan r) c (w := (x, w.2)) x.property }
    have hd (r : S) : DifferentiableAt ℝ
        (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1 := by
      have hh := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
        hΩ hspace hphase hF hi hrank (hαspan r) hnonzero
      exact (((hh.contDiffAt (hΩ.mem_nhds (hψ hw))).comp w.1
        (f := fun x : Euclidean n ↦ (x, w.2))
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
    let Dpr := fieldDerivativeLinearMap ho (hψ hw)
      (fun (r : S) x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2))
      W (fun _ _ ↦ rfl) hd
    let c := Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ))
    refine ⟨c • ((RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N).toLinearMap.comp Dpr), ?_⟩
    intro r
    exact (fullDerivativeAmplitude_eq_demodulated T Q F row col Φ Y
      hΩ hspace hphase hF hi hrank hnonzero r (hαspan r) hτ (hψ hw)).symm
  let Apr := cutoffFamilyLinearMap ψ
    (fun (r : S) ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ) hpoint
  let A₀ := cutoffFamilyLinearMap ψ
    (fun (r : S) ↦ fullLeadingPrincipalMatrix T Q F row col Φ Y r)
    (fun w _ ↦ by
      let ev : (Euclidean n × (Euclidean 3 × Euclidean (n - 1)) →
          Matrix (Fin N) (Fin n) ℂ) →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ :=
        { toFun f := f w
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      exact ⟨ev.comp ((fullLeadingPrincipalMatrixLinearMap T Q F row col Φ Y).comp
        (initialScalarSpan (n := n) z₀ R Mᵣ m).subtype), fun _ ↦ rfl⟩)
  exact ⟨Apr, A₀, fun _ ↦ ⟨rfl, rfl⟩⟩

/-- Real-linear realizations of the literal raw, leading and response derivative
amplitudes on ONE joint cutoff. The cutoff is supplied before the scalar and
frequency; it only extends the chart amplitudes for the density estimate. The
same `B` appears in every source and every derivative. Only physical response
differentiability is needed here, as supplied by
`contDiff_fullPrimaryResponse_ambientExtension`; joint regularity and quantitative
response bounds remain with their analytic producer
(`app:ch_response:eq:current-density-lipschitz`). -/
theorem exists_cutoffFullAmplitudeLinearMaps
    {z₀ : Euclidean 3} {R Mᵣ m : ℝ}
    (hα : ∀ r ∈ primitiveInitialScalars (n := n) z₀ R Mᵣ m,
      ContDiffOn ℝ ∞ (scalarAmplitude T Q F row col Φ Y r) Ω)
    (χ : Euclidean n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N))
    (ψ : Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → ℝ)
    (hψ : tsupport ψ ⊆ Ω)
    (hsrc : ∀ w ∈ tsupport ψ, ∀ x ∈ tsupport χ, (x, w.2) ∈ Ω)
    {τ : ℝ} (hτ : τ ≠ 0)
    (hB : ∀ (r : initialScalarSpan (n := n) z₀ R Mᵣ m), ∀ w ∈ tsupport ψ,
      DifferentiableAt ℝ (fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2) w.1) :
    ∃ Apr A₀ Yresp : initialScalarSpan (n := n) z₀ R Mᵣ m →ₗ[ℝ]
        (Euclidean n × (Euclidean 3 × Euclidean (n - 1)) → Matrix (Fin N) (Fin n) ℂ),
      ∀ r, Apr r = (fun w ↦ ψ w • fullDerivativeAmplitude T Q F row col Φ Y r τ w) ∧
        A₀ r = (fun w ↦ ψ w • fullLeadingPrincipalMatrix T Q F row col Φ Y r w) ∧
        Yresp r = (fun w ↦ ψ w • fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ w) := by
  let S := initialScalarSpan (n := n) z₀ R Mᵣ m
  have hαspan (r : S) :=
    contDiffOn_scalarAmplitude_of_mem_initialScalarSpan T Q F row col Φ Y hα r.property
  have hpoint (w) (hw : w ∈ tsupport ψ) :
      ∃ A Yresp : S →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ,
        ∀ r, A r = fullDerivativeAmplitude T Q F row col Φ Y r τ w ∧
          Yresp r = fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ w := by
    obtain ⟨V, W, hV, hW⟩ := exists_fullCorrectedPrimaryLinearMaps T Q F row col Φ Y χ B
      hΩ hspace hphase hF hi hrank hnonzero hα hχ hc τ w.2 (hsrc w hw)
    let O : Set (Euclidean n) := {x | (x, w.2) ∈ Ω}
    have ho : IsOpen O := hΩ.preimage (continuous_id.prodMk continuous_const)
    let res : (Euclidean n → EuclideanSpace ℂ (Fin N)) →ₗ[ℝ]
        (O → EuclideanSpace ℂ (Fin N)) :=
      { toFun f x := f x
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    have hraw (r : S) (x : O) : (W + res.comp V) r x =
        fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2) := by
      change W r x + V r x = _
      rw [hW, hV]
      change (fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2) -
        fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 x) +
          fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2 x = _
      exact sub_add_cancel _ _
    have hd (r : S) : DifferentiableAt ℝ
        (fun x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2)) w.1 := by
      have hh := contDiffOn_fullPrimaryAtom_of_leading_outputs T Q F row col Φ Y r τ
        hΩ hspace hphase hF hi hrank (hαspan r) hnonzero
      exact (((hh.contDiffAt (hΩ.mem_nhds (hψ hw))).comp w.1
        (f := fun x : Euclidean n ↦ (x, w.2))
        (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp))
    let Dpr := fieldDerivativeLinearMap ho (hψ hw)
      (fun (r : S) x ↦ fullPrimaryAtom T Q F row col Φ Y τ r w.2.1 (x, w.2.2))
      (W + res.comp V) hraw hd
    let Dresp := fieldDerivativeLinearMap ho (hψ hw)
      (fun (r : S) ↦ fullPrimaryResponse T Q F row col Φ Y χ B τ r w.2)
      (res.comp V) (fun r x ↦ congrFun (hV r) x) (fun r ↦ hB r w hw)
    let a := Complex.exp (-Complex.I * (phase T Q w.1 w.2.2 / τ : ℝ))
    refine ⟨a • ((RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N).toLinearMap.comp Dpr),
      a • ((RawPrimary.AmplitudeGrades.Polynomial.differentialMatrix n N).toLinearMap.comp Dresp), ?_⟩
    intro r
    exact ⟨(fullDerivativeAmplitude_eq_demodulated T Q F row col Φ Y
      hΩ hspace hphase hF hi hrank hnonzero r (hαspan r) hτ (hψ hw)).symm, rfl⟩
  let Apr := cutoffFamilyLinearMap ψ
    (fun (r : S) ↦ fullDerivativeAmplitude T Q F row col Φ Y r τ)
    (fun w hw ↦ by
      obtain ⟨A, _, hA⟩ := hpoint w hw
      exact ⟨A, fun r ↦ (hA r).1⟩)
  let Yresp := cutoffFamilyLinearMap ψ
    (fun (r : S) ↦ fullPrimaryResponseDerivativeAmplitude T Q F row col Φ Y χ B r τ)
    (fun w hw ↦ by
      obtain ⟨_, A, hA⟩ := hpoint w hw
      exact ⟨A, fun r ↦ (hA r).2⟩)
  let A₀ := cutoffFamilyLinearMap ψ
    (fun (r : S) ↦ fullLeadingPrincipalMatrix T Q F row col Φ Y r)
    (fun w _ ↦ by
      let ev : (Euclidean n × (Euclidean 3 × Euclidean (n - 1)) →
          Matrix (Fin N) (Fin n) ℂ) →ₗ[ℝ] Matrix (Fin N) (Fin n) ℂ :=
        { toFun f := f w
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      exact ⟨ev.comp ((fullLeadingPrincipalMatrixLinearMap T Q F row col Φ Y).comp
        (initialScalarSpan (n := n) z₀ R Mᵣ m).subtype), fun _ ↦ rfl⟩)
  exact ⟨Apr, A₀, Yresp, fun _ ↦ ⟨rfl, rfl, rfl⟩⟩

end JanetCartan.CorrectedAtoms
