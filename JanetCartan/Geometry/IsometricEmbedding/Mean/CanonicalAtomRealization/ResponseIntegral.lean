module

public import JanetCartan.Geometry.IsometricEmbedding.Mean.CanonicalAtomRealization.SobolevIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Response.SmoothParameters.TensorResponse

/-!
# The same response before and after source integration

For `app:ch_lag:eq:lag-recurrence`, the shared Hilbert extension agrees with
one supplied response on every original supported source. Apply it to the
proved Sobolev source integral, then assemble the tensor entries in the fixed
physical coordinates. Both quadratures, the source support, and the raw density
are unchanged. The only response input is its existing finite source-norm bound,
owned by the fixed-inverse producer, not the desired interchange identity.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.TensorFrobenius
namespace JanetCartan.CanonicalAtomRealization
open RawPrimary RawInputPartition RetardedSobolev.Spaces ResponseSmoothParameters

variable {n J d₀ : ℕ} {V : Set (Euclidean (n - 1))}
    (hV : IsOpen V) (hceil : Metric.closedBall 0 ((2 : ℝ) ^ J) ⊆ V)
    {S : Set (ℝ × (Fin d₀ → ℝ))} (hS : IsCompact S)
    (f : Euclidean (n - 1) → supportedTests S)
    (hf : ContDiffOn ℝ ∞
      (fun z : (ℝ × (Fin d₀ → ℝ)) × Euclidean (n - 1) ↦ (f z.2).val.val z.1)
      (univ ×ˢ V))
    {d : Euclidean (n - 1) → ℂ} {M : ℝ}
    (hd : Measurable d) (hM : 0 ≤ M) (hb : ∀ η, ‖d η‖ ≤ M)
    {G : Type} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (B : supportedTests S →ₗ[ℂ] G) (s : ℕ)
    (hB : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : supportedTests S,
      ‖B u‖ ≤ C * ‖ofTest s volume u.val‖)

include hV hceil hS hf hd hM hb hB in
/-- The original weighted responses are Bochner integrable, from the SAME
fixed response's source norm bound (`app:ch_lag:eq:lag-Y-envelope`). -/
theorem integrable_wideSourceResponse (v : WideInput n J) :
    Integrable (fun η ↦ weightedWideDensity d v η • B (f η)) := by
  have hc : ContinuousOn (fun η ↦ B (f η)) V := by
    intro η hη
    exact (contDiffAt_supportedResponse hV hS (B.restrictScalars ℝ) s hB f
      (hf.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
        (fun _ hz ↦ ⟨mem_univ _, hz.1⟩)) 0 hη).continuousAt.continuousWithinAt
  exact integrable_wideSuperposition (U := (univ : Set ℝ)) hceil
    (hc.comp continuous_snd.continuousOn (fun _ hz ↦ hz.2)) hd hM hb v (mem_univ 0)

include hB in
/-- The SAME bounded response commutes with canonical source synthesis.
The Sobolev integral identity is proved from the literal atomic sources;
the Hilbert extension agrees with the response on every admitted source
(`app:ch_lag:eq:lag-recurrence`, `app:ch_response:prop:response-graded`). -/
theorem response_wideSourceTest_eq_integral (v : WideInput n J) :
    B (wideSourceTest hV hceil hS f hf hd hM hb v) =
      ∫ η, weightedWideDensity d v η • B (f η) := by
  let H := PiLp 2 (fun _ : JetIndex d₀ s ↦
    Lp ℂ 2 (volume : Measure ((Fin d₀ → ℝ) × ℝ)))
  let L : Sobolev s (volume : Measure ((Fin d₀ → ℝ) × ℝ)) →L[ℂ] H :=
    ((PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap).comp
      (sobolevSubmodule s volume).subtypeL
  let j : supportedTests S →ₗ[ℂ] H :=
    L.toLinearMap.comp ((ofTest s volume).comp (supportedTests S).subtype)
  have hjnorm (u : supportedTests S) : ‖ofTest s volume u.val‖ ≤ ‖j u‖ := by
    change ‖(ofTest s volume u.val).val‖ ≤ _
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
      (fun i ↦ PiLp.norm_apply_le (j u) i)
  have hbnd : ∃ C : ℝ, ∀ u : supportedTests S, ‖B u‖ ≤ C * ‖j u‖ := by
    obtain ⟨C, hC, hCb⟩ := hB
    exact ⟨C, fun u ↦ (hCb u).trans (mul_le_mul_of_nonneg_left (hjnorm u) hC)⟩
  obtain ⟨A, hA⟩ := exists_response_extension_of_hilbert_bound
    (V := supportedTests S) (H := H) (G := G)
    (j.restrictScalars ℝ) (B.restrictScalars ℝ) hbnd
  change ∀ u, A (j u) = B u at hA
  have hi := integrable_wideSourceSobolev hV hceil hS f hf hd hM hb s v
  have hj : j (wideSourceTest hV hceil hS f hf hd hM hb v) =
      ∫ η, j (weightedWideDensity d v η • f η) := by
    change L (ofTest s volume (wideSourceTest hV hceil hS f hf hd hM hb v).val) = _
    rw [ofTest_wideSourceTest_eq_integral, ← L.integral_comp_comm hi]
    apply integral_congr_ae
    filter_upwards [] with η
    simp only [j, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.subtype_apply, map_smul]
  have hji : Integrable (fun η ↦ j (weightedWideDensity d v η • f η)) := by
    simpa only [j, LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      Submodule.subtype_apply, Submodule.coe_smul, map_smul] using L.integrable_comp hi
  rw [← hA, hj, ← A.integral_comp_comm hji]
  apply integral_congr_ae
  filter_upwards [] with η
  rw [show A (j (weightedWideDensity d v η • f η)) =
      B (weightedWideDensity d v η • f η) from hA _]
  exact B.map_smul _ _

section Tensor
open ResponseSourceExtension

variable {N : ℕ}

include hV hceil hd hM hb in
/-- The same real tensor response, complexified on the original quadratures,
commutes with finite-band source synthesis. The finite-component source
decomposition and its integral are proved in the original physical chart
(`app:ch_lag:eq:lag-recurrence`). -/
theorem complexifyResponse_wideIntegral
    (e : (ℝ × (Fin d₀ → ℝ)) ≃L[ℝ] Euclidean n)
    {S : Set (Euclidean n)} (hS : IsCompact S)
    (B : MetricField n →ₗ[ℝ] (Euclidean n → Euclidean N)) (x : Euclidean n)
    (hB : ∀ i j : Fin n, ∃ s : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : supportedTests (e ⁻¹' S),
        ‖tensorComponentResponse e S B i j u x‖ ≤ C * ‖ofTest s volume u.val‖)
    (A : Euclidean (n - 1) → Euclidean n → Matrix (Fin n) (Fin n) ℂ)
    (hA : ContDiffOn ℝ ∞ (fun w : Euclidean n × Euclidean (n - 1) ↦ A w.2 w.1)
      (univ ×ˢ V))
    (hs : ∀ η ∈ V, tsupport (A η) ⊆ S) (v : WideInput n J) :
    complexifyResponse B (fun y ↦ ∫ η, weightedWideDensity d v η • A η y) x =
      ∫ η, weightedWideDensity d v η • complexifyResponse B (A η) x := by
  classical
  obtain ⟨g, hg, he⟩ := exists_supported_tensor_components e hS A hA hs
  have hK : IsCompact (e ⁻¹' S) := e.toHomeomorph.isCompact_preimage.mpr hS
  have hgt (ij : Fin n × Fin n) : ContDiffOn ℝ ∞
      (fun w : (ℝ × (Fin d₀ → ℝ)) × Euclidean (n - 1) ↦ (g ij w.2).val.val w.1)
      (univ ×ˢ V) :=
    (hg ij).comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun _ hw ↦ ⟨hw.2, mem_univ _⟩)
  let W (ij : Fin n × Fin n) := wideSourceTest hV hceil hK (g ij) (hgt ij) hd hM hb v
  let single (ij : Fin n × Fin n) : ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    (Matrix.singleLinearMap ℂ ij.1 ij.2).toContinuousLinearMap
  have hscalar (ij : Fin n × Fin n) (y : Euclidean n) :
      Integrable (fun η ↦ weightedWideDensity d v η • (g ij η).val.val (e.symm y)) :=
    integrable_wideSuperposition hceil (hgt ij).continuousOn hd hM hb v (mem_univ _)
  have hi (ij : Fin n × Fin n) (y : Euclidean n) : Integrable
      (fun η ↦ weightedWideDensity d v η • tensorTestSource e ij.1 ij.2 (g ij η).val y) := by
    apply ((single ij).integrable_comp (hscalar ij y)).congr
    filter_upwards [] with η
    exact (single ij).map_smul _ _
  have hw (ij : Fin n × Fin n) (y : Euclidean n) :
      tensorTestSource e ij.1 ij.2 (W ij).val y =
        ∫ η, weightedWideDensity d v η • tensorTestSource e ij.1 ij.2 (g ij η).val y := by
    change single ij (∫ η, weightedWideDensity d v η • (g ij η).val.val (e.symm y)) = _
    rw [← (single ij).integral_comp_comm (hscalar ij y)]
    simp only [map_smul]
    rfl
  have hzero {η : Euclidean (n - 1)} (hη : η ∉ V) : weightedWideDensity d v η = 0 := by
    apply wideDensity_eq_zero_of_ceiling_le
    have hn : η ∉ Metric.closedBall 0 ((2 : ℝ) ^ J) := fun h ↦ hη (hceil h)
    exact le_of_lt (by simpa using hn)
  have hwhole : (fun y ↦ ∫ η, weightedWideDensity d v η • A η y) =
      ∑ ij : Fin n × Fin n, tensorTestSource e ij.1 ij.2 (W ij).val := by
    funext y
    simp only [Finset.sum_apply, hw]
    rw [← integral_finsetSum _ (fun ij _ ↦ hi ij y)]
    apply integral_congr_ae
    filter_upwards [] with η
    by_cases hη : η ∈ V
    · rw [he η hη]
      simp only [Finset.sum_apply, Finset.smul_sum]
    · simp [hzero hη]
  let Bc (ij : Fin n × Fin n) : supportedTests (e ⁻¹' S) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin N) :=
    (LinearMap.proj x).comp (((complexifyResponse B).comp
      (tensorTestSource e ij.1 ij.2)).comp (supportedTests (e ⁻¹' S)).subtype)
  have hr (ij : Fin n × Fin n) :
      Bc ij (W ij) = ∫ η, weightedWideDensity d v η • Bc ij (g ij η) := by
    obtain ⟨s, C, hC, hCb⟩ := hB ij.1 ij.2
    exact response_wideSourceTest_eq_integral hV hceil hK (g ij) (hgt ij)
      hd hM hb (Bc ij) s ⟨C, hC, hCb⟩ v
  have hri (ij : Fin n × Fin n) :
      Integrable (fun η ↦ weightedWideDensity d v η • Bc ij (g ij η)) := by
    obtain ⟨s, C, hC, hCb⟩ := hB ij.1 ij.2
    exact integrable_wideSourceResponse hV hceil hK (g ij) (hgt ij)
      hd hM hb (Bc ij) s ⟨C, hC, hCb⟩ v
  rw [hwhole, map_sum, Finset.sum_apply]
  change (∑ ij : Fin n × Fin n, Bc ij (W ij)) = _
  simp_rw [hr]
  rw [← integral_finsetSum _ (fun ij _ ↦ hri ij)]
  apply integral_congr_ae
  filter_upwards [] with η
  by_cases hη : η ∈ V
  · rw [he η hη, map_sum, Finset.sum_apply, Finset.smul_sum]
    rfl
  · simp [hzero hη]

end Tensor
end JanetCartan.CanonicalAtomRealization
