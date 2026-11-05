module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.ElapsedKernels

/-!
# Strong measurability from the actual compact graph kernels

The conditional passage to uncut operators uses the precise test realizations
and strong limits exported by `exists_fullGraphFamily_of_wholeImage_phase`.
The parent retarded construction must instantiate that producer on the elapsed
phases, with common cutoffs and bounds. Measurability of the finite kernels is
proved here, rather than included among those hypotheses.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.Frobenius

namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification

open FourierIntegral

variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)

/-- The literal compact graph test realization gives datum-wise strong
measurability by density. The realization is precisely a finite-cutoff output
of `exists_fullGraphFamily_of_wholeImage_phase`. Consumer:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem aestronglyMeasurable_compact_graph_apply
    (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude n q)
    (hS : Continuous (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2))
    (hA : Continuous (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2))
    {X Y K : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hK : IsCompact K)
    (hs : ∀ r x z ξ, x ∉ X ∨ z ∉ Y ∨ ξ ∉ K → A r x z ξ = 0)
    (T : ℝ → H →L[ℂ] H) (μ : Measure ℝ)
    (hreal : ∀ u : graphTestSpace n q, ∀ᵐ r ∂μ,
      T r (graphTestToLp u) =ᵐ[volume] graphTestOutput (S r) (A r) u)
    (u : H) : AEStronglyMeasurable (fun r ↦ T r u) μ := by
  apply aestronglyMeasurable_apply_of_dense graphTestToLp denseRange_graphTestToLp μ _ u
  intro v
  exact aestronglyMeasurable_L2_of_compact_representative _
    (fun r ↦ graphTestOutput (S r) (A r) v) μ
    (continuous_compact_graphTestOutput S A hS hA hY hK
      (fun r x z ξ h ↦ hs r x z ξ (Or.inr h)) v)
    hX (fun r x hx ↦ graphTestOutput_eq_zero_off_output (S r) (A r)
      (fun x z ξ hx ↦ hs r x z ξ (Or.inl hx)) v x hx) (hreal v)

/-- The reverse test formula exported by the same primitive constructor gives
strong measurability of adjoints, without commuting any factors. Consumer:
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem aestronglyMeasurable_compact_reverse_apply
    (S : ℝ → E → E → ℝ) (A : ℝ → FullAmplitude n q)
    (hS : Continuous (fun p : (ℝ × E) × E ↦ S p.1.1 p.1.2 p.2))
    (hA : Continuous (fun p : ((ℝ × E) × E) × E ↦ A p.1.1.1 p.1.1.2 p.1.2 p.2))
    {X Y K : Set E} (hX : IsCompact X) (hY : IsCompact Y) (hK : IsCompact K)
    (hs : ∀ r x z ξ, x ∉ X ∨ z ∉ Y ∨ ξ ∉ K → A r x z ξ = 0)
    (T : ℝ → H →L[ℂ] H) (μ : Measure ℝ)
    (hreal : ∀ u : graphTestSpace n q, ∀ᵐ r ∂μ,
      T r (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (S r) (A r) (fun x ↦ (u.val x).ofLp) z))
    (u : H) : AEStronglyMeasurable (fun r ↦ T r u) μ := by
  apply aestronglyMeasurable_apply_of_dense graphTestToLp denseRange_graphTestToLp μ _ u
  intro v
  exact aestronglyMeasurable_L2_of_compact_representative _
    (fun r z ↦ WithLp.toLp 2
      (reverseGraphOperator (S r) (A r) (fun x ↦ (v.val x).ofLp) z)) μ
    (continuous_compact_reverseGraphOutput S A hS hA hX hK
      (fun r x z ξ h ↦ hs r x z ξ (by tauto)) v)
    hY (fun r z hz ↦ reverseGraphOutput_eq_zero_off_source (S r) (A r)
      (fun x z ξ hz ↦ hs r x z ξ (Or.inr (Or.inl hz))) v z hz) (hreal v)

variable {d : ℕ}

/-- Strong measurability of the actual uncut elapsed graph from the primitive
constructor's finite test realizations and strong forward limits. All finite
kernel measurability is proved from the original continuous data and compact
masks. The parent must supply `hreal` and `hlim` by instantiating
`exists_fullGraphFamily_of_wholeImage_phase`; these are not asserted here.
Source: `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem aestronglyMeasurable_elapsedGraph_of_regularizations
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : (Euclidean (d + 1)) → ℂ)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (χ : ℕ → (Euclidean (d + 1)) → ℂ) (hχ : ∀ j, Continuous (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j)) (Δ : ℝ)
    (Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u))) (u : SpacetimeL2 d q) :
    AEStronglyMeasurable (fun r ↦ elapsedGraph Ψ b χout χsource β r u)
      (volume.restrict (Icc 0 Δ)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop (f := fun j r ↦ Treg j r u)
  · intro j
    apply aestronglyMeasurable_compact_graph_apply (elapsedPhase Ψ)
      (fun r ↦ frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r))
      (continuous_elapsedPhase Ψ hΨ)
      (continuous_cut_elapsedAmplitude b χout χsource β (χ j) hb ho hs hβ (hχ j))
      hocs hscs (hχcs j)
      (cut_elapsedAmplitude_eq_zero_off_support b χout χsource β (χ j))
      (Treg j) (volume.restrict (Icc 0 Δ)) _ u
    intro v
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hreal j r hr v
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hlim r hr u


variable (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : (Euclidean (d + 1)) → ℂ)
    (hΨ : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      Ψ p.1.1 p.1.2 p.2.1 p.2.2))
    (hb : Continuous (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
      b p.1.1 p.1.2 p.2.1 p.2.2))
    (ho : Continuous χout) (hs : Continuous χsource) (hβ : Continuous β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (χ : ℕ → (Euclidean (d + 1)) → ℂ) (hχ : ∀ j, Continuous (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j)) (Δ : ℝ)
    (Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)

include hΨ hb ho hs hβ hocs hscs hχ hχcs

/-- Measurability of every actual cutoff graph on every datum. The only operator
input is the finite test realization exported by
`exists_fullGraphFamily_of_wholeImage_phase`. Consumer: dominated convergence
in `app:ch_regular_base:eq:fixed-time-representation`. -/
theorem aestronglyMeasurable_elapsed_regularization
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (j : ℕ) (u : SpacetimeL2 d q) :
    AEStronglyMeasurable (fun r ↦ Treg j r u) (volume.restrict (Icc 0 Δ)) := by
  apply aestronglyMeasurable_compact_graph_apply (elapsedPhase Ψ)
    (fun r ↦ frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r))
    (continuous_elapsedPhase Ψ hΨ)
    (continuous_cut_elapsedAmplitude b χout χsource β (χ j) hb ho hs hβ (hχ j))
    hocs hscs (hχcs j)
    (cut_elapsedAmplitude_eq_zero_off_support b χout χsource β (χ j))
    (Treg j) (volume.restrict (Icc 0 Δ)) _ u
  intro v
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact hreal j r hr v

/-- Measurability of the literal cutoff adjoints from the primitive producer's
reverse test formula. In particular no operator-norm continuity of the adjoint
family is assumed. Consumer: `app:ch_regular_base:lem:retarded-kernel`. -/
theorem aestronglyMeasurable_elapsed_adjoint_regularization
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    (j : ℕ) (u : SpacetimeL2 d q) :
    AEStronglyMeasurable (fun r ↦ (Treg j r).adjoint u)
      (volume.restrict (Icc 0 Δ)) := by
  have ha := (continuous_cut_elapsedAmplitude b χout χsource β (χ j)
    hb ho hs hβ (hχ j)).matrix_conjTranspose
  simp only [frequencyCutFullAmplitude, Matrix.conjTranspose_smul] at ha
  apply aestronglyMeasurable_compact_reverse_apply (elapsedPhase Ψ)
    (fun r ↦ frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
      (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
    (continuous_elapsedPhase Ψ hΨ) ha hocs hscs (hχcs j) _
    (fun r ↦ (Treg j r).adjoint) (volume.restrict (Icc 0 Δ)) _ u
  · intro r x z ξ h
    have hz := congrArg Matrix.conjTranspose
      (cut_elapsedAmplitude_eq_zero_off_support b χout χsource β (χ j) r x z ξ h)
    simpa only [frequencyCutFullAmplitude, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_zero] using hz
  · intro v
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hrealAdj j r hr v

/-- The strong adjoint limits from `exists_fullGraphFamily_of_wholeImage_phase`
give datum-wise measurability of the actual uncut adjoints. The parent must
instantiate that constructor for the elapsed phases. Consumer:
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem aestronglyMeasurable_elapsedGraph_adjoint_of_regularizations
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u)))
    (u : SpacetimeL2 d q) :
    AEStronglyMeasurable (fun r ↦ (elapsedGraph Ψ b χout χsource β r).adjoint u)
      (volume.restrict (Icc 0 Δ)) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun j r ↦ (Treg j r).adjoint u)
  · exact fun j ↦ aestronglyMeasurable_elapsed_adjoint_regularization Ψ b χout χsource β
      hΨ hb ho hs hβ hocs hscs χ hχ hχcs Δ Treg hrealAdj j u
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hlimAdj r hr u

/-- The actual frequency regularizations converge after elapsed-time integration.
The hypotheses `hbound`, `hreal`, `hlim` are exactly the uniform LOW bound,
finite test realization and strong forward limit supplied by
`exists_fullGraphFamily_of_wholeImage_phase`. Their real instantiation belongs
to the parent construction. Source:
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem tendsto_integral_elapsedGraph_of_regularizations
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume]
        graphTestOutput (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    {C : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ C)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u))) (u : SpacetimeL2 d q) :
    Tendsto (fun j ↦ ∫ r in Icc 0 Δ, Treg j r u) atTop
      (𝓝 (elapsedGraphIntegral Δ Ψ b χout χsource β u)) :=
  tendsto_integral_apply_of_uniform_bound Treg
    (aestronglyMeasurable_elapsed_regularization Ψ b χout χsource β
      hΨ hb ho hs hβ hocs hscs χ hχ hχcs Δ Treg hreal) hbound hlim u

/-- Literal adjoint regularizations also commute with the time integral, using
the same LOW bound since adjunction preserves operator norm. The actual producer
of `hrealAdj`, `hbound`, `hlimAdj` is
`exists_fullGraphFamily_of_wholeImage_phase`. Consumer: the reversed kernel in
`app:ch_regular_base:lem:retarded-kernel`. -/
theorem tendsto_integral_elapsedGraph_adjoint_of_regularizations
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    {C : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ C)
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u)))
    (u : SpacetimeL2 d q) :
    Tendsto (fun j ↦ ∫ r in Icc 0 Δ, (Treg j r).adjoint u) atTop
      (𝓝 (∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u)) := by
  apply tendsto_integral_apply_of_uniform_bound (C := C) (fun j r ↦ (Treg j r).adjoint)
    (aestronglyMeasurable_elapsed_adjoint_regularization Ψ b χout χsource β
      hΨ hb ho hs hβ hocs hscs χ hχ hχcs Δ Treg hrealAdj) _ hlimAdj u
  intro j r hr
  simpa only [ContinuousLinearMap.adjoint.norm_map] using hbound j r hr

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
