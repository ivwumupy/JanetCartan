module

public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedLimits
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedRetarded
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification.SupportedReverse
/-!
# The uncut retarded operator as the strong limit of its literal kernels

The exact finite forward/adjoint test realizations, common LOW bound and strong
limits from `exists_fullGraphFamily_of_wholeImage_phase` suffice. Supported
primitive regularity proves measurability and the literal compact retarded
representatives, so dominated convergence identifies their uncut L² limits.
The parent must instantiate the primitive producer with its geometry and symbol
budgets; this conditional implication does not assert unconditional existence.
-/

@[expose] public noncomputable section
set_option maxHeartbeats 600000
open MeasureTheory Set Filter
open scoped Topology ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
open FourierIntegral
variable {d q : ℕ}
local notation "E" => Euclidean (d + 1)
/-- The datum-wise elapsed integral is the strong L² limit of the actual
masked physical retarded kernels, and its literal adjoint is the limit of the
reversed triangles with `Bβ*` to the left of `E_b*`. The compact representatives
are proved here, not assumed. Only `hreal`, `hrealAdj`, `hbound`, `hlim` and
`hlimAdj` are realization inputs; their exact producer is
`exists_fullGraphFamily_of_wholeImage_phase`. Its primitive instantiation is
an explicit obligation of the parent retarded construction.
Source: `app:ch_regular_base:lem:retarded-kernel` and
`app:ch_regular_base:eq:fixed-time-representation`. -/
theorem exists_retardedOperator_of_regularizations
    (Ψ : TwoTimePhase d) (b : TwoTimeAmplitude d q) (χout χsource β : E → ℂ)
    (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hΨ : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        Ψ p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (hb : ∀ r ∈ Icc 0 Δ, ∀ x ∈ tsupport χout, ∀ ξ ∈ tsupport β,
      ContinuousAt (fun p : (ℝ × ℝ) × (Euclidean d × Euclidean d) ↦
        b p.1.1 p.1.2 p.2.1 p.2.2) ((x 0, x 0 - r), (spatialPart x, spatialPart ξ)))
    (ho : Continuous χout) (hs : ContDiff ℝ ∞ χsource) (hβ : ContDiff ℝ ∞ β)
    (hocs : HasCompactSupport χout) (hscs : HasCompactSupport χsource)
    (χ : ℕ → E → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hχcs : ∀ j, HasCompactSupport (χ j))
    (Treg : ℕ → ℝ → SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q)
    (hreal : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      Treg j r (graphTestToLp u) =ᵐ[volume] graphTestOutput (elapsedPhase Ψ r)
        (frequencyCutFullAmplitude (χ j) (elapsedAmplitude b χout χsource β r)) u)
    (hrealAdj : ∀ j r, r ∈ Icc 0 Δ → ∀ u : graphTestSpace (d + 1) q,
      (Treg j r).adjoint (graphTestToLp u) =ᵐ[volume] fun z ↦ WithLp.toLp 2
        (reverseGraphOperator (elapsedPhase Ψ r)
          (frequencyCutFullAmplitude (fun ξ ↦ star (χ j ξ))
            (fun x z ξ ↦ (elapsedAmplitude b χout χsource β r x z ξ).conjTranspose))
          (fun x ↦ (u.val x).ofLp) z))
    {C : ℝ} (hbound : ∀ j r, r ∈ Icc 0 Δ → ‖Treg j r‖ ≤ C)
    (hlim : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ Treg j r u) atTop
      (𝓝 (elapsedGraph Ψ b χout χsource β r u)))
    (hlimAdj : ∀ r ∈ Icc 0 Δ, ∀ u, Tendsto (fun j ↦ (Treg j r).adjoint u) atTop
      (𝓝 ((elapsedGraph Ψ b χout χsource β r).adjoint u)))
    (a : ℝ) (hout : ∀ x, χout x ≠ 0 → x 0 ∈ Icc a (a + Δ))
    (hzero : ∀ t s y η, s ≤ a → b t s y η = 0) :
    (∀ u, AEStronglyMeasurable (fun r ↦ elapsedGraph Ψ b χout χsource β r u)
      (volume.restrict (Icc 0 Δ))) ∧
    (∀ u, AEStronglyMeasurable (fun r ↦ (elapsedGraph Ψ b χout χsource β r).adjoint u)
      (volume.restrict (Icc 0 Δ))) ∧
    ∃ Q : SpacetimeL2 d q →L[ℂ] SpacetimeL2 d q,
      ‖Q‖ ≤ Δ * C ∧
      (∀ u, Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u) ∧
      (∀ u, Q.adjoint u = ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u) ∧
      ∀ u : graphTestSpace (d + 1) q,
        ∃ R RAdj : ℕ → SpacetimeL2 d q,
          (∀ j, R j =ᵐ[volume] fun x ↦ WithLp.toLp 2
            (cutRetardedPhysical Ψ b χout χsource β (χ j) hs hβ (hχ j) (hχcs j) a u x)) ∧
          (∀ j, RAdj j =ᵐ[volume] fun z ↦ WithLp.toLp 2
            (cutReverseRetardedFourier Ψ b χout χsource β (χ j)
              (fun x ↦ (u.val x).ofLp) a (a + Δ) z)) ∧
          Tendsto R atTop (𝓝 (Q (graphTestToLp u))) ∧
          Tendsto RAdj atTop (𝓝 (Q.adjoint (graphTestToLp u))) := by
  have hm := supported_elapsedGraph_measurability_and_integral_limits Ψ b χout χsource β
    Δ hΔ hΨ hb ho hs.continuous hβ.continuous hocs hscs χ
    (fun j ↦ (hχ j).continuous) hχcs Treg hreal hrealAdj hbound hlim hlimAdj
  have hC : 0 ≤ C := (norm_nonneg (Treg 0 0)).trans (hbound 0 0 ⟨le_rfl, hΔ⟩)
  have hT : ∀ r ∈ Icc 0 Δ, ‖elapsedGraph Ψ b χout χsource β r‖ ≤ C := by
    intro r hr
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro u
    apply le_of_tendsto (hlim r hr u).norm
    exact Eventually.of_forall (fun j ↦ (Treg j r).le_opNorm u |>.trans
      (mul_le_mul_of_nonneg_right (hbound j r hr) (norm_nonneg u)))
  let Q := strongIntegral (elapsedGraph Ψ b χout χsource β) Δ C hm.1 hT
  have hQ (u : SpacetimeL2 d q) : Q u = elapsedGraphIntegral Δ Ψ b χout χsource β u := rfl
  have hQA (u : SpacetimeL2 d q) : Q.adjoint u =
      ∫ r in Icc 0 Δ, (elapsedGraph Ψ b χout χsource β r).adjoint u :=
    strongIntegral_adjoint_apply hm.1 hT hm.2.1 u
  refine ⟨hm.1, hm.2.1, Q, norm_strongIntegral_le hΔ hC hm.1 hT, hQ, hQA, ?_⟩
  intro u
  refine ⟨(fun j ↦ ∫ r in Icc 0 Δ, Treg j r (graphTestToLp u)),
    (fun j ↦ ∫ r in Icc 0 Δ, (Treg j r).adjoint (graphTestToLp u)), ?_, ?_, ?_, ?_⟩
  · intro j
    have he := (integral_elapsed_regularization_test_representatives Ψ b χout χsource β
      Δ hΔ hΨ hb ho hs.continuous hβ.continuous hocs hscs (χ j) (hχ j).continuous (hχcs j)
      (Treg j) (hreal j) (hrealAdj j) u).1
    apply he.trans
    exact Eventually.of_forall (fun x ↦ congrArg (WithLp.toLp 2)
      (integral_cut_elapsedGraph_eq_retardedPhysical_of_support Ψ b χout χsource β
        Δ hΔ hΨ hb ho hs hβ hocs hscs (χ j) (hχ j) (hχcs j) a hout hzero u x))
  · intro j
    have he := (integral_elapsed_regularization_test_representatives Ψ b χout χsource β
      Δ hΔ hΨ hb ho hs.continuous hβ.continuous hocs hscs (χ j) (hχ j).continuous (hχcs j)
      (Treg j) (hreal j) (hrealAdj j) u).2
    apply he.trans
    exact Eventually.of_forall (fun z ↦ congrArg (WithLp.toLp 2)
      (integral_cut_reverse_elapsedGraph_eq_reverseRetardedFourier_of_support
        Ψ b χout χsource β Δ hΔ hΨ hb ho hβ.continuous (χ j) (hχ j).continuous
        hocs (hχcs j) a (a + Δ) (by linarith) hout hzero
        (fun x ↦ (u.val x).ofLp) ((PiLp.continuous_ofLp 2 _).comp u.property.1.continuous) z))
  · simpa only [hQ] using hm.2.2.1 (graphTestToLp u)
  · simpa only [hQA] using hm.2.2.2 (graphTestToLp u)

end JanetCartan.RegularSector.Characteristic.EvolutionIntegral.KernelIdentification
