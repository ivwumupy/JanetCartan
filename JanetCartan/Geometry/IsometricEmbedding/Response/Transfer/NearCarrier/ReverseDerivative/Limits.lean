module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ReverseDerivative.Weak
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative.Limits

/-!
# Limits of the reverse derivative transfer

The literal regularized identity passes to supplied distributional or strong L²
limits in `app:ch_response:eq:direct-envelope-profile`. These hypotheses name the
limits of each actual graph term; neither a derivative identity nor Sobolev
membership of the limiting output is supplied. `jc-response-near-carrier` must
instantiate the analytic inputs from `jc-finite-fio-calculus` and the geometry
from `jc-compatible-phase-geometry`.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer.ReverseDerivative
open LineDeriv
variable {n r : ℕ}

/-- The output derivative of a distributional limit is the sum of the limits of
the full remainder and datum-derivative graphs. Every convergence premise names
its literal normalized integral. Source:
`app:ch_response:eq:direct-envelope-profile`, reverse paragraph. -/
theorem envelopeGraph_distributional_limit_derivative
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (A : ℕ → FourierIntegral.FullAmplitude n r)
    (B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (f : Euclidean n → Fin r → ℂ) (j : Fin n)
    (hreg : ∀ k, TransferRegularization S ζ ρ (A k) B C f j)
    (F R : 𝓢'(Euclidean n, Fin r → ℂ)) (D : Fin n → 𝓢'(Euclidean n, Fin r → ℂ))
    (hF : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto
      (fun k ↦ ∫ y, φ y • envelopeGraph S ζ ρ (A k) f y) atTop (𝓝 (F φ)))
    (hR : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto
      (fun k ↦ ∫ y, φ y • envelopeGraph S ζ ρ (remainderAmplitude C (A k) j) f y)
      atTop (𝓝 (R φ)))
    (hD : ∀ (φ : 𝓢(Euclidean n, ℂ)) l, Tendsto
      (fun k ↦ ∫ y, φ y • envelopeGraph S ζ ρ (datumAmplitude C (A k) j l)
        (fun x ↦ partialDeriv f x l) y) atTop (𝓝 (D l φ))) :
    lineDerivOp (EuclideanSpace.single j (1 : ℝ)) F = R + ∑ l, D l := by
  ext φ : 1
  have hl := hF (lineDerivOp (EuclideanSpace.single j (1 : ℝ)) φ)
  have hr := (hR φ).add (tendsto_finsetSum Finset.univ (fun l _ ↦ hD φ l))
  have heq := tendsto_nhds_unique hl (hr.neg.congr (fun k ↦ by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, partialDeriv] using
      ((hreg k).weak_derivative φ).symm))
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg, add_apply, sum_apply]
  exact neg_eq_iff_eq_neg.mpr heq

/-- Strong L² limits give the reverse weak derivative, without assuming output
Sobolev membership. The three limits are of the actual normalized regularized
graphs over Euclidean volume. The pairing-continuity lemma is shared with the
forward deduction. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem envelopeGraph_L2_limit_derivative
    (S : Euclidean n → Euclidean n → ℝ) (ζ : Euclidean n) (ρ : ℝ)
    (A : ℕ → FourierIntegral.FullAmplitude n r)
    (B C : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (f : Euclidean n → Fin r → ℂ) (j : Fin n)
    (hreg : ∀ k, TransferRegularization S ζ ρ (A k) B C f j)
    (F R : Lp (Fin r → ℂ) 2 (volume : Measure (Euclidean n)))
    (D : Fin n → Lp (Fin r → ℂ) 2 (volume : Measure (Euclidean n)))
    (hmF : ∀ k, MemLp (envelopeGraph S ζ ρ (A k) f) 2)
    (hmR : ∀ k, MemLp (envelopeGraph S ζ ρ (remainderAmplitude C (A k) j) f) 2)
    (hmD : ∀ k l, MemLp (envelopeGraph S ζ ρ (datumAmplitude C (A k) j l)
      (fun x ↦ partialDeriv f x l)) 2)
    (hF : Tendsto (fun k ↦ (hmF k).toLp _) atTop (𝓝 F))
    (hR : Tendsto (fun k ↦ (hmR k).toLp _) atTop (𝓝 R))
    (hD : ∀ l, Tendsto (fun k ↦ (hmD k l).toLp _) atTop (𝓝 (D l))) :
    lineDerivOp (EuclideanSpace.single j (1 : ℝ)) (F : 𝓢'(Euclidean n, Fin r → ℂ)) =
      (R : 𝓢'(Euclidean n, Fin r → ℂ)) + ∑ l, (D l : 𝓢'(Euclidean n, Fin r → ℂ)) := by
  apply envelopeGraph_distributional_limit_derivative S ζ ρ A B C f j hreg
  · exact tendsto_forwardGraph_pairing_of_L2 _ hmF F hF
  · exact tendsto_forwardGraph_pairing_of_L2 _ hmR R hR
  · intro φ l
    exact tendsto_forwardGraph_pairing_of_L2 _ (fun k ↦ hmD k l) (D l) (hD l) φ

end JanetCartan.ResponseTransfer.ReverseDerivative
