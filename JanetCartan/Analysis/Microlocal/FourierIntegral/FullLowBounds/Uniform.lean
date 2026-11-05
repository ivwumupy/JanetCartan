module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.SourceSeries
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.Distributional
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.CoefficientGeometry
public import JanetCartan.Analysis.Microlocal.FourierIntegral.FullLowBounds.LiteralAdjoint

/-!
# The uniform full-amplitude low reserve

The bounded full graph is constructed from the primitive normal geometry and
original full-symbol jets in `app:ch_regular_base:thm:actual-calculus`, Step 1.
The constant is fixed before the amplitude and its budget, including zero.
The same theorem can therefore be instantiated for every modified amplitude
in `app:ch_regular_base:eq:graph-derivative-transfer`.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped ContDiff Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral.FullLowBounds
open SourceExpansion LowBounds NormalComparison FrequencyCutoff AmplitudeBound
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The primitive full-symbol budget bounds its actual seminorm, including
budget zero. Consumer: `exists_fullGraphL2_of_primitive_inputs`, in
`app:ch_regular_base:thm:actual-calculus`, Step 1. -/
theorem fullSourceSymbolSeminorm_le_of_bound
    {A : FullAmplitude n r} {N : ℕ} {B : ℝ}
    (hb : HasFullSourceSymbolBound A N B) : fullSourceSymbolSeminorm A N ≤ B := by
  have hB : 0 ≤ B := by
    have h := hb [] [] (by simp) (0 : E) (0 : E) (0 : E)
    exact (norm_nonneg _).trans (by simpa [coefficientCovectorWeight] using h)
  apply csSup_le (Set.insert_nonempty _ _)
  intro b hb'
  rcases hb' with rfl | ⟨is, js, hij, x, y, η, rfl⟩
  · exact hB
  · exact hb is js hij x y η

/-- The actual full graph, its actual Hilbert adjoint, and the SAME literal
frequency regularizations from primitive geometry and the original symbol jets.
The positive constant is chosen before all amplitudes and budgets. The whole
averaged-gradient image and the normalized inverse-range scale comparison are
explicit geometric inputs; their instantiation belongs to the geometry parent.
No coefficient operators, coefficient norm estimates, full graph bounds or
convergence hypotheses are assumed. Source:
`app:ch_regular_base:thm:actual-calculus`, Step 1, and
`app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem exists_fullGraphL2_of_primitive_inputs
    (hn : 0 < n) (R ℓ M L c : ℝ) (hℓ : 0 < ℓ) (hRcell : R / ℓ < 1 / 2)
    {δ F : ℝ} (hδ : 0 < δ) (hF : 0 ≤ F) (hc : 1 ≤ c) :
    ∃ C > 0, ∀
    (A : FullAmplitude n r)
    (_hs : ∀ x η i j, SupportedInCenteredBox R (fun y ↦ A x y η i j))
    (_hA : ContDiff ℝ ∞ (fun p : E × E × E ↦ A p.1 p.2.1 p.2.2))
    {B : ℝ} (_hb : HasFullSourceSymbolBound A
      (primitiveNormalReserve n + lowReserve n) B)
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
    (_hcarrier : ∀ q ∈ W, (∃ y, A q.1 y q.2.2 ≠ 0) →
      (∃ y, A q.2.1 y q.2.2 ≠ 0) → q ∈ K)
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
    {Kout : Set E} (_hKout : IsCompact Kout)
    (_hsout : ∀ x y ξ, x ∉ Kout → A x y ξ = 0)
    (_hsdomain : ∀ x y ξ, x ∉ X ∨ ξ ∉ D → A x y ξ = 0)
    (_hforward : ∀ k, ContinuousOn (normalForwardCoordinates S)
      (jointNormalCarrier (matrixCoefficient ℓ A k) (matrixCoefficient ℓ A k))),
    ∃ T : H →L[ℂ] H, ∃ Treg : ℕ → H →L[ℂ] H,
      ‖T‖ ≤ C * B ∧ ‖T.adjoint‖ ≤ C * B ∧
      (∀ j, ‖Treg j‖ ≤ C * B) ∧
      (∀ j u, Treg j (graphTestToLp u) =ᵐ[volume]
        graphTestOutput S (fun x y η ↦ complexPhysicalCutoff j η • A x y η) u) ∧
      (∀ u, Tendsto (fun j ↦ Treg j u) atTop (𝓝 (T u))) ∧
      (∀ u, Tendsto (fun j ↦ (Treg j).adjoint u) atTop (𝓝 (T.adjoint u))) ∧
      (∀ u, T (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) ∧
      GraphDistributionalRealization (graphOperator S) complexPhysicalCutoff A T ∧
      (∀ (u : graphTestSpace n r) (w : H),
        Integrable (fun x ↦ inner ℂ (graphTestOutput S A u x) (w x)) ∧
        inner ℂ (graphTestToLp u) (T.adjoint w) =
          ∫ x, inner ℂ (graphTestOutput S A u x) (w x)) ∧
      (∀ j (u : graphTestSpace n r), (Treg j).adjoint (graphTestToLp u) =ᵐ[volume]
        fun y ↦ WithLp.toLp 2 (reverseGraphOperator S
          (frequencyCutFullAmplitude (fun η ↦ star (complexPhysicalCutoff j η))
            (fun x y η ↦ (A x y η).conjTranspose)) (fun x ↦ (u.val x).ofLp) y)) ∧
      GraphDistributionalRealization (reverseGraphOperator S)
        (fun j η ↦ star (complexPhysicalCutoff j η))
        (fun x y η ↦ (A x y η).conjTranspose) T.adjoint ∧
      ∀ U : H →L[ℂ] H,
        (∀ u, U (graphTestToLp u) =ᵐ[volume] graphTestOutput S A u) → U = T := by
  obtain ⟨C₀, hC₀, hcoeff⟩ := exists_coefficientGraphL2_of_fullSourceBound
    (r := r) hn R M L hδ hF
  let C := sourceOperatorConstant n r ℓ
    (C₀ * normalizedCoefficientJetConstant n (primitiveNormalReserve n) c)
  have hC : 0 ≤ C := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg hC₀.le
        (normalizedCoefficientJetConstant_pos (primitiveNormalReserve n) hc).le)
        (mul_nonneg (sq_nonneg _) (coefficientConstant_pos _ _ _).le)
    · exact tsum_nonneg fun k ↦ inv_nonneg.mpr
        (pow_nonneg (by linarith [frequencyNorm_nonneg k]) _)
  refine ⟨C + 1, by positivity, ?_⟩
  intro A hs hA B hb S hS X D η J W K chart hopen hηinput hmapinput hJinput
    hgapinput hrightInverse hcarrier hclosed hbuffer hR hgrowth V hUopen hVopen
    hη hmap hJ hgap hJjet hηjet hscale Kout hKout hsout hsdomain hforward
  have hscoef : ∀ k x ξ, x ∉ Kout → matrixCoefficient ℓ A k x ξ = 0 := by
    intro k x ξ hx
    exact matrixCoefficient_eq_zero_of_fiber ℓ A k x ξ (fun y ↦ hsout x y ξ hx)
  have hgeom := primitiveNormalGeometry_matrixCoefficient ℓ A hA S X D η J W K
    hopen hηinput hmapinput hJinput hgapinput hrightInverse hcarrier hclosed hbuffer hsdomain
  have hco := hcoeff hℓ hRcell A hs hA hb S hS.continuous hc chart hgeom hR
    hgrowth V hUopen hVopen hη hmap hJ hgap hJjet hηjet hscale hKout hsout
    hscoef hsdomain hforward
  obtain ⟨G, β, T, Treg, _hsum, _hasum, hT, hTa, hTr, hr, ht, hta,
      hfull, _hmem, hp, _hpl, huniq⟩ :=
    exists_literalSourceFourierExpansion_of_coefficientGraphs hn hℓ hRcell A hs hA hb
      S hS hKout hscoef c C₀ hc hC₀ hco
  have hB : 0 ≤ B := by
    have h := hb [] [] (by simp) (0 : E) (0 : E) (0 : E)
    exact (norm_nonneg _).trans (by simpa [coefficientCovectorWeight] using h)
  have hbound : C * fullSourceSymbolSeminorm A
      (primitiveNormalReserve n + lowReserve n) ≤ (C + 1) * B :=
    (mul_le_mul_of_nonneg_left (fullSourceSymbolSeminorm_le_of_bound hb) hC).trans
      (mul_le_mul_of_nonneg_right (by linarith) hB)
  obtain ⟨β⟩ := nonempty_sourceCutoff (n := n) hℓ hRcell
  have hsupport : ∀ x y ξ, x ∉ Kout ∨ y ∉ tsupport β.toFun → A x y ξ = 0 := by
    intro x y ξ h
    rcases h with hx | hy
    · exact hsout x y ξ hx
    · by_contra hAxy
      have hone := β.one_on_amplitude A hs x ξ y hAxy
      have hzero := image_eq_zero_of_notMem_tsupport hy
      rw [hone] at hzero
      exact one_ne_zero hzero
  have hadj := fun j u ↦ compactFullGraph_adjoint_ae S hS A hA hKout β.compact
    hsupport (complexPhysicalCutoff j) (complexPhysicalCutoff_contDiff j)
    (complexPhysicalCutoff_hasCompactSupport j) (Treg j) (hr j) u
  exact ⟨T, Treg, hT.trans hbound, hTa.trans hbound, fun j ↦ (hTr j).trans hbound,
    hr, ht, hta, hfull, graphDistributionalRealization_of_strong_limit
      (graphOperator S) complexPhysicalCutoff A T Treg hr ht, hp, hadj,
    graphDistributionalRealization_of_strong_limit (reverseGraphOperator S)
      (fun j η ↦ star (complexPhysicalCutoff j η))
      (fun x y η ↦ (A x y η).conjTranspose) T.adjoint
      (fun j ↦ (Treg j).adjoint) hadj hta, huniq⟩

end JanetCartan.FourierIntegral.FullLowBounds
