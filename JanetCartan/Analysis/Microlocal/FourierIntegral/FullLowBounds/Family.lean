module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Uniform
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Operators
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.WeightedJets
public import JanetCartan.Analysis.Microlocal.FourierIntegral.WholeImageGeometry.Basic

/-!
# Uniform full graph families for integer Sobolev transfer

The same bounded full graph family, its literal Hilbert adjoints and a single
carrier-preserving cutoff sequence serve every complete modified amplitude.
The low reserve is `3 * n + 4`, independent of the requested Sobolev order.
All amplitude inputs are original smooth symbols and supports; the operators,
coefficient bounds, strong limits and both weak realizations are constructed.
Only the explicit whole-image inverse/Jacobian/support geometry remains for
the parent to instantiate. Source: `app:ch_regular_base:thm:actual-calculus`,
Step 1, and `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open SourceExpansion LowBounds NormalComparison FrequencyCutoff AmplitudeBound
open FullAmplitudePrimitiveBudget FirstOutputJets
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

private theorem continuous_normalForward_of_smooth (S : E → E → ℝ)
    (hS : ContDiff ℝ ∞ (Function.uncurry S)) : Continuous (normalForwardCoordinates S) := by
  have h := WholeImageGeometry.averagedGradient_contDiffOn
    (X := Set.univ) (D := Set.univ) isOpen_univ isOpen_univ (convex_univ : Convex ℝ (Set.univ : Set E))
    hS.contDiffOn
  simp only [Set.univ_prod_univ, contDiffOn_univ] at h
  exact continuous_fst.prodMk (continuous_snd.fst.prodMk h.continuous)

/-- Actual operator families with one fixed finite low reserve and one common
cutoff sequence, including the exact low-reserve premises of
`exists_graph_integer_sobolev_constant` and `exists_adjoint_integer_sobolev_constant`.
The weighted clauses apply to every admissible modified amplitude as soon as
its finite primitive jet budget is supplied. The reverse clause uses the
actual Hilbert adjoint of the forward construction on the conjugate transpose.
There are no operator, convergence, coefficient-budget or realization premises.
Geometric instantiation on the whole averaged-gradient image remains with the
parent. Source: `app:ch_regular_base:thm:actual-calculus`, Steps 1 and 3. -/
theorem exists_fullGraphFamily_of_primitive_inputs
    (hn : 0 < n) (R ℓ M L c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c) :
    ∃ C > 0, ∀ (X₀ Y₀ F₀ : Set E), IsCompact X₀ →
      (∀ y ∈ Y₀, ∀ i : Fin n, |y i| ≤ R) → IsClosed F₀ → (0 : E) ∉ F₀ →
    ∃ χ : ℕ → E → ℂ,
      (∀ j, ContDiff ℝ ∞ (χ j)) ∧ (∀ j, HasCompactSupport (χ j)) ∧
      (∀ j, (0 : E) ∉ tsupport (χ j)) ∧
      (∀ (A : FullAmplitude n r), (∀ x y η, η ∉ F₀ → A x y η = 0) →
        ∀ j, frequencyCutFullAmplitude (χ j) A =
          frequencyCutFullAmplitude (complexPhysicalCutoff j) A) ∧
    ∀
    (S : E → E → ℝ) (_hS : ContDiff ℝ ∞ (Function.uncurry S))
    {X D : Set E} {η : E → E → E → E} {J : E → E → E → E →L[ℝ] E}
    {W K : Set (NormalVariables n)}
    (_chart : AveragedGradientChart S X D η J δ)
    (_hopen : IsOpen (bufferedNormalDomain X D S))
    (_hηinput : ContDiffOn ℝ ∞ (normalInverseCoordinates η) (bufferedNormalDomain X D S))
    (_hmapinput : MapsTo (normalInverseCoordinates η) (bufferedNormalDomain X D S) W)
    (_hJinput : ContDiffOn ℝ ∞ (fun q : NormalVariables n ↦ J q.1 q.2.1 q.2.2) W)
    (_hgapinput : ∀ q ∈ W, (J q.1 q.2.1 q.2.2).det ≠ 0)
    (_hrightInverse : ∀ q ∈ bufferedNormalDomain X D S,
      normalForwardCoordinates S (normalInverseCoordinates η q) = q)
    (_hcarrier : ∀ q ∈ W, q.1 ∈ X₀ → q.2.1 ∈ X₀ → q.2.2 ∈ F₀ → q ∈ K)
    (_hclosed : IsClosed (normalForwardCoordinates S '' K))
    (_hbuffer : normalForwardCoordinates S '' K ⊆ bufferedNormalDomain X D S)
    (_hR : ∀ x ∈ X, ‖x‖ ≤ R)
    (_hgrowth : ∀ x ∈ X, ∀ y ∈ X, ∀ u ∈ D,
      ‖averagedGradient S x y u‖ ≤ F * (1 + ‖u‖))
    (V : ℕ → Set (NormalVariables n))
    (_hUopen : ∀ l, IsOpen (normalDyadicShell (bufferedNormalDomain X D S) l))
    (_hVopen : ∀ l, IsOpen (V l))
    (_hη : ∀ l, ContDiffOn ℝ ∞
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D S) l))
    (_hmap : ∀ l, MapsTo
      (normalInverseCoordinates (normalizedNormalInverse ((2 : ℝ)^l) η))
      (normalDyadicShell (bufferedNormalDomain X D S) l) (V l))
    (_hJ : ∀ l, ContDiffOn ℝ ∞
      (fun q : NormalVariables n ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) (V l))
    (_hgap : ∀ l z, z ∈ V l → δ ≤ |(normalizedNormalJacobian
      ((2 : ℝ)^l) J z.1 z.2.1 z.2.2).det|)
    (_hJjet : ∀ l z, z ∈ V l → ∀ i ≤ primitiveNormalReserve n,
      ‖iteratedFDeriv ℝ i (fun q : NormalVariables n ↦
        normalizedNormalJacobian ((2 : ℝ)^l) J q.1 q.2.1 q.2.2) z‖ ≤ M)
    (_hηjet : ∀ l z, z ∈ normalDyadicShell (bufferedNormalDomain X D S) l →
      ∀ i, 1 ≤ i → i ≤ primitiveNormalReserve n →
      ‖iteratedFDeriv ℝ i (normalInverseCoordinates
        (normalizedNormalInverse ((2 : ℝ)^l) η)) z‖ ≤ L)
    (_hscale : ∀ l z, z ∈ V l →
      (2 : ℝ)^l ≤ c * (1 + ‖(2 : ℝ)^l • z.2.2‖))
    (_hX₀ : X₀ ⊆ X) (_hF₀ : F₀ ⊆ D),
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
  obtain ⟨C₀, hC₀, hbuild⟩ := exists_fullGraphL2_of_primitive_inputs
    (r := r) hn R ℓ M L c hℓ hRcell hδ hF hc
  let N := fullLowReserve n
  refine ⟨C₀ * (2 : ℝ)^N, mul_pos hC₀ (by positivity), ?_⟩
  intro X₀ Y₀ F₀ hXcompact hYbox hFclosed hFzero
  obtain ⟨χ, hχ, hχcompact, hχzero, hχstar, hχpreserve⟩ :=
    exists_compatiblePhysicalCutoff (r := r) hFclosed hFzero
  refine ⟨χ, hχ, hχcompact, hχzero, hχpreserve, ?_⟩
  intro S hS X D η J W K chart hopen hηinput hmapinput hJinput hgapinput
    hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
    hgap hJjet hηjet hscale hX₀ hF₀
  have hconstruct (A : FullAmplitude n r) (hA : ForwardAmplitudeAdmissible X₀ Y₀ F₀ A)
      (B : ℝ) (hb : HasFullSourceSymbolBound A N B) :
      ∃ Treg : ℕ → H →L[ℂ] H,
        ‖fullGraphOperator S A‖ ≤ C₀ * B ∧ ‖(fullGraphOperator S A).adjoint‖ ≤ C₀ * B ∧
        (∀ j, ‖Treg j‖ ≤ C₀ * B) ∧
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
          (fun x y η ↦ (A x y η).conjTranspose) (fullGraphOperator S A).adjoint := by
    have hmem (x y ξ : E) (h : A x y ξ ≠ 0) : x ∈ X₀ ∧ y ∈ Y₀ ∧ ξ ∈ F₀ := by
      refine ⟨?_, ?_, ?_⟩
      · by_contra hx
        exact h (hA.support x y ξ (Or.inl hx))
      · by_contra hy
        exact h (hA.support x y ξ (Or.inr (Or.inl hy)))
      · by_contra hξ
        exact h (hA.support x y ξ (Or.inr (Or.inr hξ)))
    have hs : ∀ x ξ i j, SupportedInCenteredBox R (fun y ↦ A x y ξ i j) := by
      intro x ξ i j y hy
      have hm : A x y ξ ≠ 0 := fun h ↦ hy (by simp [h])
      exact hYbox y (hmem x y ξ hm).2.1
    have hcar : ∀ q ∈ W, (∃ y, A q.1 y q.2.2 ≠ 0) →
        (∃ y, A q.2.1 y q.2.2 ≠ 0) → q ∈ K := by
      intro q hq ⟨y, hy⟩ ⟨z, hz⟩
      exact hcarrier q hq (hmem _ _ _ hy).1 (hmem _ _ _ hz).1 (hmem _ _ _ hy).2.2
    have hsd : ∀ x y ξ, x ∉ X ∨ ξ ∉ D → A x y ξ = 0 := by
      intro x y ξ hh
      rcases hh with hx | hξ
      · exact hA.support x y ξ (Or.inl fun h ↦ hx (hX₀ h))
      · exact hA.support x y ξ (Or.inr (Or.inr fun h ↦ hξ (hF₀ h)))
    obtain ⟨T, Treg, ht, hta, htr, hr, hlim, halim, hfull, _hfwd, _hpair,
        hradj, _hrev, _hunique⟩ :=
      hbuild A hs hA.smooth hb S hS chart hopen hηinput hmapinput hJinput hgapinput
        hrightInverse hcar hclosed hbuffer hR hgrowth V hUopen hVopen hη hmap hJ
        hgap hJjet hηjet hscale hXcompact (fun x y ξ hx ↦ hA.support x y ξ (Or.inl hx))
        hsd (fun _ ↦ (continuous_normalForward_of_smooth S hS).continuousOn)
    have he := fullGraphOperator_eq_of_realizes S A T hfull
    rw [← he] at ht hta hlim halim hfull
    have hfreq : ∀ x y ξ, ξ ∉ F₀ → A x y ξ = 0 :=
      fun x y ξ hξ ↦ hA.support x y ξ (Or.inr (Or.inr hξ))
    have hr' : ∀ j u, Treg j (graphTestToLp u) =ᵐ[volume]
        graphTestOutput S (frequencyCutFullAmplitude (χ j) A) u := by
      intro j u
      rw [hχpreserve A hfreq j]
      exact hr j u
    have hra' : ∀ j (u : graphTestSpace n r), (Treg j).adjoint (graphTestToLp u) =ᵐ[volume]
        fun y ↦ WithLp.toLp 2 (reverseGraphOperator S
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x y ξ ↦ (A x y ξ).conjTranspose)) (fun x ↦ (u.val x).ofLp) y) := by
      intro j u
      have hcut := hχpreserve (fun x y ξ ↦ (A x y ξ).conjTranspose)
        (fun x y ξ hξ ↦ by simp [hfreq x y ξ hξ]) j
      simp only [hχstar]
      rw [hcut]
      have hstar : (fun ξ : E ↦ star (complexPhysicalCutoff j ξ)) =
          complexPhysicalCutoff j := by
        funext ξ
        simp [complexPhysicalCutoff]
      simpa only [hstar] using hradj j u
    exact ⟨Treg, ht, hta, htr, hr', hra', hlim, halim, hfull,
      graphDistributionalRealization_of_strong_limit (graphOperator S) χ A
        (fullGraphOperator S A) Treg hr' hlim,
      graphDistributionalRealization_of_strong_limit (reverseGraphOperator S)
        (fun j ξ ↦ star (χ j ξ)) (fun x y ξ ↦ (A x y ξ).conjTranspose)
        (fullGraphOperator S A).adjoint (fun j ↦ (Treg j).adjoint) hra' halim⟩
  refine ⟨?_, ?_, ?_⟩
  · intro A hA B hb
    obtain ⟨Treg, ht, hta, htr, hrest⟩ := hconstruct A hA B hb
    have hB : 0 ≤ B := by
      have h := hb [] [] (by simp) 0 0 0
      exact (norm_nonneg _).trans (by simpa [coefficientCovectorWeight] using h)
    have hbound : C₀ * B ≤ C₀ * (2 : ℝ)^N * B :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC₀.le (one_le_pow₀ (by norm_num))) hB
    exact ⟨Treg, ht.trans hbound, hta.trans hbound, fun j ↦ (htr j).trans hbound, hrest⟩
  · intro ρ hρ hηρ G hG B hB hb
    have hj := hasFullSourceSymbolBound_of_weighted_jets hG.smooth N ρ
      (c := 2) (by norm_num) hB (fun ξ ↦ by have := hρ ξ; have := hηρ ξ; linarith) hb
    obtain ⟨Treg, ht, _hta, _htr, _hr, _hra, _hl, _hal, _hf, hreal, _har⟩ :=
      hconstruct G hG ((2 : ℝ)^N * B) hj
    exact ⟨by simpa only [mul_assoc] using ht, hreal⟩
  · intro ρ hρ hηρ K₀ hK₀ G hG hfreq B hB hb
    have hGbox : ReverseAmplitudeAdmissible (X₀ ×ˢ Y₀) G :=
      ⟨hG.smooth, fun _ hp ↦ hK₀ (hG.support hp)⟩
    have hg := forwardAmplitudeAdmissible_of_reverse hGbox hFclosed hFzero hfreq
    have hj := hasFullSourceSymbolBound_of_weighted_jets hg.smooth N ρ
      (c := 2) (by norm_num) hB (fun ξ ↦ by have := hρ ξ; have := hηρ ξ; linarith) hb
    obtain ⟨Treg, _ht, hta, _htr, _hr, _hra, _hl, _hal, _hf, _hreal, har⟩ :=
      hconstruct (fun x y ξ ↦ (G x y ξ).conjTranspose)
        (forwardAmplitudeAdmissible_conjTranspose hg) ((2 : ℝ)^N * B)
        (hasFullSourceSymbolBound_conjTranspose hj)
    refine ⟨by simpa only [reverseFullGraphOperator, mul_assoc] using hta, ?_⟩
    simpa only [Matrix.conjTranspose_conjTranspose, reverseFullGraphOperator] using har

end JanetCartan.FourierIntegral.FullLowBounds
