module

public import JanetCartan.Analysis.Microlocal.FourierIntegral.SobolevBounds.WeakTransfer.Realization

/-!
# Passing literal graph pairings to their supplied L² limits

This is the limit deduction in `app:ch_regular_base:eq:graph-derivative-transfer`.
The analytic input is an equality of actual compact-frequency integrals, which
must be proved by source and output integration by parts. It is displayed in
full, not replaced by an assumed derivative recurrence for the limiting operator.
The final weak-transfer assembly must discharge this input from phase smoothness,
homogeneity, the mixed inverse gap, and compact supports.
-/

@[expose] public noncomputable section
open MeasureTheory Filter LineDeriv
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.FourierIntegral
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "V" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp V 2 (volume : Measure E)

/-- The first weak derivative follows from the compact-frequency pairing
identity and precisely the distributional realization of its finitely many
terms. This is a conditional limit lemma; its pairing premise remains an
analytic obligation of the final assembly. Neither a derivative identity nor
any high-order estimate for the limiting L² operators is assumed.
Source: `app:ch_regular_base:eq:graph-derivative-transfer`. -/
theorem graph_distributional_derivative_of_regularized_pairings
    (K : FullAmplitude n r → (E → Fin r → ℂ) → E → Fin r → ℂ)
    (χ : ℕ → E → ℂ) (A R : FullAmplitude n r) (P : Fin n → FullAmplitude n r)
    (T U : H →L[ℂ] H) (W : Fin n → H →L[ℂ] H)
    (hT : GraphDistributionalRealization K χ A T)
    (hU : GraphDistributionalRealization K χ R U)
    (hW : ∀ j, GraphDistributionalRealization K χ (P j) (W j))
    (u : graphTestSpace n r) (i : Fin n)
    (hpair : ∀ k (φ : 𝓢(E, ℂ)),
      (∫ x, partialDeriv φ x i • WithLp.toLp 2
        (K (frequencyCutFullAmplitude (χ k) A) (fun y ↦ (u.val y).ofLp) x)) =
      -((∫ x, φ x • WithLp.toLp 2
          (K (frequencyCutFullAmplitude (χ k) R) (fun y ↦ (u.val y).ofLp) x)) +
        ∑ j, ∫ x, φ x • WithLp.toLp 2
          (K (frequencyCutFullAmplitude (χ k) (P j))
            (fun y ↦ ((graphTestPartialDeriv j u).val y).ofLp) x))) :
    lineDerivOp (EuclideanSpace.single i (1 : ℝ))
        (T (graphTestToLp u) : 𝓢'(E, V)) =
      (U (graphTestToLp u) : 𝓢'(E, V)) +
        ∑ j, (W j (graphTestToLp (graphTestPartialDeriv j u)) : 𝓢'(E, V)) := by
  ext φ : 1
  have hl := hT u (lineDerivOp (EuclideanSpace.single i (1 : ℝ)) φ)
  have hr := (hU u φ).add (tendsto_finsetSum Finset.univ
    (fun j _ ↦ hW j (graphTestPartialDeriv j u) φ))
  have heq := tendsto_nhds_unique hl (hr.neg.congr (fun k ↦ by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, partialDeriv] using
      (hpair k φ).symm))
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg]
  simp only [add_apply, sum_apply]
  exact neg_eq_iff_eq_neg.mpr heq

end JanetCartan.FourierIntegral
