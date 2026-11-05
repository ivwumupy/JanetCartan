module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.PrimitiveRealization.Locality
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.PrimitiveInputs

/-!
# Full graph families from the original buffered phase

The whole-image inverse geometry, normalized inverse and Jacobian bounds,
transported closed supports and smooth auxiliary phase are constructed from
original phase data. The full-amplitude low theorem then supplies one family,
its literal adjoints and a common cutoff sequence. Locality removes the auxiliary
phase from every exported operator and kernel. This is the low realization
producer for supported integer Sobolev transfer in actual-calculus Steps 1--3.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 3200000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
open SourceExpansion LowBounds NormalComparison FrequencyCutoff AmplitudeBound
open FullLowBounds WholeImageGeometry FullAmplitudePrimitiveBudget FirstOutputJets
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- Full graph realization with no inverse-geometry or operator premises.
The original phase is smooth only near the closed buffered chart. Its finite
normalized phase jets, mixed second-jet bound, injective averaged gradient,
determinant gap, homogeneity and positive frequency collar produce all whole-image
normal estimates. The low reserve is `fullLowReserve n = 3*n+4`, before any
Sobolev order. Every original full amplitude with that reserve has its literal
forward and adjoint strong limits, and every weighted modified amplitude has
the low bound and distributional realization needed by supported transfer.
Source: `app:ch_regular_base:thm:actual-calculus`, Steps 1--3. -/
theorem exists_fullGraphFamily_of_wholeImage_phase
    (hn : 0 < n) (R ℓ B₀ Bφ : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ a > 0, ∃ b > a, ∃ C > 0,
      ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ →
        (∀ y ∈ Y₀, ∀ i : Fin n, |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
      ∃ χ : ℕ → E → ℂ,
        (∀ j, ContDiff ℝ ∞ (χ j)) ∧ (∀ j, HasCompactSupport (χ j)) ∧
        (∀ j, (0 : E) ∉ tsupport (χ j)) ∧
        (∀ (A : FullAmplitude n r), (∀ x y η, η ∉ F₀ → A x y η = 0) →
          ∀ j, frequencyCutFullAmplitude (χ j) A =
            frequencyCutFullAmplitude (complexPhysicalCutoff j) A) ∧
      ∀ (X D : Set E) (O : Set (E × E)) (S : E → E → ℝ),
        IsOpen X → IsOpen D → Convex ℝ X → IsOpen O →
        closure (X ×ˢ D) ⊆ O → ContDiffOn ℝ ∞ (Function.uncurry S) O →
        (∀ x ∈ X, ∀ u ∈ D, ∀ t : ℝ, 0 < t → t • u ∈ D →
          S x (t • u) = t * S x u) →
        (∀ x ∈ X, ∀ u ∈ D,
          ‖fderiv ℝ (fun v ↦ fderiv ℝ (fun z ↦ S z v) x) u‖ ≤ B₀) →
        (∀ x ∈ X, ∀ y ∈ X, InjOn (averagedGradient S x y) D) →
        (∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D, δ ≤ |(averagedJacobian S x y u).det|) →
        (∀ u ∈ D, ε < ‖u‖) →
        (∀ j : ℕ, ∀ z ∈ X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b,
          ∀ k ≤ wholeImagePhaseReserve n, ‖iteratedFDeriv ℝ k
            (Function.uncurry (normalizedPhase ((2 : ℝ)^j) S)) z‖ ≤ Bφ) →
        (∀ x ∈ X, ‖x‖ ≤ R) → X₀ ⊆ X → F₀ ⊆ D →
      (∀ (A : FullAmplitude n r), ForwardAmplitudeAdmissible X₀ Y₀ F₀ A →
        ∀ B : ℝ, HasFullSourceSymbolBound A (fullLowReserve n) B →
        ∃ Treg : ℕ → H →L[ℂ] H,
          ‖fullGraphOperator S A‖ ≤ C * B ∧ ‖(fullGraphOperator S A).adjoint‖ ≤ C * B ∧
          (∀ j, ‖Treg j‖ ≤ C * B) ∧
          (∀ j u, Treg j (graphTestToLp u) =ᵐ[volume]
            graphTestOutput S (frequencyCutFullAmplitude (χ j) A) u) ∧
          (∀ j (u : graphTestSpace n r), (Treg j).adjoint (graphTestToLp u) =ᵐ[volume]
            fun y ↦ WithLp.toLp 2 (reverseGraphOperator S
              (frequencyCutFullAmplitude (fun η ↦ star (χ j η))
                (fun x y η ↦ (A x y η).conjTranspose)) (fun x ↦ (u.val x).ofLp) y)) ∧
          (∀ u, Tendsto (fun j ↦ Treg j u) atTop (𝓝 (fullGraphOperator S A u))) ∧
          (∀ u, Tendsto (fun j ↦ (Treg j).adjoint u) atTop
            (𝓝 ((fullGraphOperator S A).adjoint u))) ∧
          (∀ u, fullGraphOperator S A (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) ∧
          GraphDistributionalRealization (graphOperator S) χ A (fullGraphOperator S A) ∧
          GraphDistributionalRealization (reverseGraphOperator S) (fun j η ↦ star (χ j η))
            (fun x y η ↦ (A x y η).conjTranspose) (fullGraphOperator S A).adjoint) ∧
      (∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) → (∀ η, ‖η‖ ≤ ρ η) →
        ∀ (G : FullAmplitude n r), ForwardAmplitudeAdmissible X₀ Y₀ F₀ G →
        ∀ B : ℝ, 0 ≤ B →
        (∀ w : List (Coordinate n), w.length ≤ fullLowReserve n →
          ∀ x y η, (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ B) →
        ‖fullGraphOperator S G‖ ≤ C * B ∧
          GraphDistributionalRealization (graphOperator S) χ G (fullGraphOperator S G)) ∧
      (∀ (ρ : E → ℝ), (∀ η, 1 ≤ ρ η) → (∀ η, ‖η‖ ≤ ρ η) →
        ∀ (K₀ : Set (E × E)), K₀ ⊆ X₀ ×ˢ Y₀ →
        ∀ (G : FullAmplitude n r), ReverseAmplitudeAdmissible K₀ G →
        (∀ x y η, η ∉ F₀ → G x y η = 0) →
        ∀ B : ℝ, 0 ≤ B →
        (∀ w : List (Coordinate n), w.length ≤ fullLowReserve n →
          ∀ x y η, (ρ η) ^ frequencyOrder w * ‖jet w G x y η‖ ≤ B) →
        ‖reverseFullGraphOperator S G‖ ≤ C * B ∧
          GraphDistributionalRealization (reverseGraphOperator S) (fun j η ↦ star (χ j η))
            G (reverseFullGraphOperator S G)) := by
  obtain ⟨F, hF, Cfreq, hCfreq, a, ha, b, hab, hfrequency⟩ :=
    exists_wholeImage_frequency_comparison_and_shell_range (n := n) B₀ hδ hε
  obtain ⟨M, _hM, L, _hL, hjets⟩ :=
    exists_normalizedWholeImage_jet_bounds (n := n) (primitiveNormalReserve n) Bφ b hδ
  let c := max 1 a⁻¹
  have hc : 1 ≤ c := le_max_left _ _
  obtain ⟨C, hC, hfamily⟩ := exists_fullGraphFamily_of_primitive_inputs
    (r := r) hn R ℓ M L c hℓ hRcell hδ hF.le hc
  refine ⟨a, ha, b, hab, C, hC, ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
  obtain ⟨χ, hχ, hχcompact, hχzero, hχpreserve, hfamily⟩ :=
    hfamily X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
  refine ⟨χ, hχ, hχcompact, hχzero, hχpreserve, ?_⟩
  intro X D O S hX hD hcX hO hbuffer hS hhom hmix hinj hgap hcollar hphase hR hX₀ hF₀
  have hSlocal := hS.mono (subset_trans subset_closure hbuffer)
  obtain ⟨hcompare, hmap⟩ :=
    hfrequency S X D hX hD hcX hSlocal hhom hmix hgap hcollar
  have hj := hjets S X D hX hD hcX hSlocal hinj hgap a ha hab hphase hmap
  have chart := averagedGradientChart hX hD hcX hSlocal hinj hδ hgap
  obtain ⟨S', hS', he'⟩ := exists_smooth_phase_extension S isClosed_closure hO hbuffer hS
  have he : EqOn (Function.uncurry S') (Function.uncurry S) (X ×ˢ D) :=
    fun _ hq ↦ (he' _ (subset_closure hq)).eq_of_nhds
  have hdom := bufferedNormalDomain_phase_congr hX hcX he
  have hforward := normalForwardCoordinates_phase_congr hX hcX he
  let K : Set (NormalVariables n) := X₀ ×ˢ (X₀ ×ˢ F₀)
  have hKclosed : IsClosed K := hXcompact.isClosed.prod (hXcompact.isClosed.prod hFclosed)
  have hKsub : K ⊆ X ×ˢ (X ×ˢ D) := fun _ hq ↦ ⟨hX₀ hq.1, hX₀ hq.2.1, hF₀ hq.2.2⟩
  have himage : normalForwardCoordinates S' '' K = normalForwardCoordinates S '' K :=
    Set.image_congr (fun _ hq ↦ hforward (hKsub hq))
  have hUopen := isOpen_bufferedNormalDomain hX hD hcX hSlocal hinj hδ hgap
  let V : ℕ → Set (NormalVariables n) := fun j ↦
    X ×ˢ (X ×ˢ normalizedSourceBand D ((2 : ℝ)^j) a b)
  have hscale : ∀ j z, z ∈ V j →
      (2 : ℝ)^j ≤ c * (1 + ‖(2 : ℝ)^j • z.2.2‖) := by
    intro j z hz
    have hρ : 0 ≤ (2 : ℝ)^j := by positivity
    have haz : a ≤ ‖z.2.2‖ := hz.2.2.2.1.le
    calc
      (2 : ℝ)^j = a⁻¹ * ((2 : ℝ)^j * a) := by field_simp
      _ ≤ a⁻¹ * ((2 : ℝ)^j * ‖z.2.2‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left haz hρ) (inv_nonneg.mpr ha.le)
      _ = a⁻¹ * ‖(2 : ℝ)^j • z.2.2‖ := by rw [norm_smul, Real.norm_of_nonneg hρ]
      _ ≤ c * ‖(2 : ℝ)^j • z.2.2‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
      _ ≤ c * (1 + ‖(2 : ℝ)^j • z.2.2‖) :=
        mul_le_mul_of_nonneg_left (by linarith) (zero_le_one.trans hc)
  obtain ⟨hconstruct, hweighted, hreverse⟩ := hfamily S' hS'
    (W := X ×ˢ (X ×ˢ D)) (K := K)
    (chart.congr_phase hX hcX he)
    (hdom.symm ▸ hUopen)
    (hdom.symm ▸ wholeImageInverse_contDiffOn hX hD hcX hSlocal hinj hδ hgap)
    (hdom.symm ▸ (mapsTo_wholeImageInverse (S := S) (X := X) (D := D)))
    (averagedJacobian_contDiffOn hX hD hcX hSlocal)
    (fun q hq ↦ abs_pos.mp (hδ.trans_le (hgap _ hq.1 _ hq.2.1 _ hq.2.2)))
    (fun q hq ↦ by
      have hq' : q ∈ bufferedNormalDomain X D S := hdom ▸ hq
      rw [hforward (mapsTo_wholeImageInverse hq')]
      exact normalForward_wholeImageInverse hq')
    (fun _ _ hx hy hη ↦ ⟨hx, hy, hη⟩)
    (by
      rw [himage]
      exact isClosed_normalForward_image_of_frequency_bound
        hX hD hcX hSlocal hKclosed hKsub hCfreq.le
        (fun x hx y hy u hu ↦ (hcompare x hx y hy u hu).2))
    (by rw [himage, hdom]; exact normalForward_image_subset_bufferedNormalDomain hKsub)
    hR
    (fun x hx y hy u hu ↦ by
      rw [averagedGradient_phase_congr hX hcX he hx hy hu]
      exact (hcompare x hx y hy u hu).1.trans
        (mul_le_mul_of_nonneg_left (by linarith) hF.le))
    V (fun j ↦ hdom.symm ▸ isOpen_normalDyadicShell hUopen j)
    (fun j ↦ hX.prod (hX.prod (isOpen_normalizedSourceBand hD _ a b)))
    (fun j ↦ hdom.symm ▸ normalizedWholeImageInverse_contDiffOn_shell
      hX hD hcX hSlocal hinj hδ hgap j)
    (fun j ↦ hdom.symm ▸ hmap j)
    (fun j ↦ normalizedAveragedJacobian_contDiffOn_band hX hD hcX hSlocal _ a b)
    (fun _ z hz ↦ hgap _ hz.1 _ hz.2.1 _ hz.2.2.1)
    (fun j ↦ (hj j).1) (fun j ↦ hdom.symm ▸ (hj j).2) hscale hX₀ hF₀
  have hagree (A : FullAmplitude n r) (hA : ForwardAmplitudeAdmissible X₀ Y₀ F₀ A) :
      ∀ x y η, A x y η ≠ 0 → S' x η = S x η := by
    intro x y η hne
    apply he (x := (x, η))
    constructor
    · apply hX₀
      by_contra hx
      exact hne (hA.support x y η (Or.inl hx))
    · apply hF₀
      by_contra hη
      exact hne (hA.support x y η (Or.inr (Or.inr hη)))
  refine ⟨?_, ?_, ?_⟩
  · intro A hA B hb
    obtain ⟨Treg, ht, hta, htr, hr, hra, hl, hal, hf, hreal, har⟩ := hconstruct A hA B hb
    have heA := hagree A hA
    have hop := FullLowBounds.fullGraphOperator_phase_congr S S' A heA
    have heAc : ∀ x y η, (A x y η).conjTranspose ≠ 0 → S' x η = S x η :=
      fun x y η h ↦ heA x y η (fun hz ↦ h (by simp [hz]))
    rw [hop] at ht hta hl hal hf hreal har
    refine ⟨Treg, ht, hta, htr, ?_, ?_, hl, hal, ?_,
      (graphDistributionalRealization_phase_congr S S' χ A _ heA).mp hreal,
      (reverseGraphDistributionalRealization_phase_congr S S' _ _ _ heAc).mp har⟩
    · intro j u
      have hecut : ∀ x y η, frequencyCutFullAmplitude (χ j) A x y η ≠ 0 →
          S' x η = S x η := fun x y η h ↦ heA x y η
            (fun hz ↦ h (by simp [frequencyCutFullAmplitude, hz]))
      simpa only [graphTestOutput_phase_congr S S' _ hecut] using hr j u
    · intro j u
      have hecut : ∀ x y η,
          frequencyCutFullAmplitude (fun η ↦ star (χ j η))
            (fun x y η ↦ (A x y η).conjTranspose) x y η ≠ 0 → S' x η = S x η :=
        fun x y η h ↦ heAc x y η (fun hz ↦ h (by simp [frequencyCutFullAmplitude, hz]))
      simpa only [reverseGraphOperator_phase_congr S S' _ hecut] using hra j u
    · intro u
      simpa only [graphTestOutput_phase_congr S S' A heA] using hf u
  · intro ρ hρ hηρ G hG B hB hb
    obtain ⟨hbound, hreal⟩ := hweighted ρ hρ hηρ G hG B hB hb
    have heG := hagree G hG
    rw [FullLowBounds.fullGraphOperator_phase_congr S S' G heG] at hbound hreal
    exact ⟨hbound, (graphDistributionalRealization_phase_congr S S' χ G _ heG).mp hreal⟩
  · intro ρ hρ hηρ K₀ hK₀ G hG hfreq B hB hb
    obtain ⟨hbound, hreal⟩ := hreverse ρ hρ hηρ K₀ hK₀ G hG hfreq B hB hb
    have hGbox : ReverseAmplitudeAdmissible (X₀ ×ˢ Y₀) G :=
      ⟨hG.smooth, fun _ hp ↦ hK₀ (hG.support hp)⟩
    have heG := hagree G (forwardAmplitudeAdmissible_of_reverse hGbox hFclosed hFzero hfreq)
    rw [FullLowBounds.reverseFullGraphOperator_phase_congr S S' G heG] at hbound hreal
    exact ⟨hbound, (reverseGraphDistributionalRealization_phase_congr S S' _ G _ heG).mp hreal⟩

end JanetCartan.FourierIntegral
