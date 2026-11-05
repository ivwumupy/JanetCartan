module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.NearCarrier.ForwardDerivative.Weak

/-!
# Passage to actual distributional and L² limits

The weak identity for the literal frequency regularizations passes to supplied
limits of each of its actual graph terms. This is the limit step for the forward
paragraph of `app:ch_response:thm:response-literal-transfer`. In particular, no
output Sobolev membership is used to prove the derivative identity.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ContDiff SchwartzMap Topology Matrix.Norms.Frobenius
namespace JanetCartan.ResponseTransfer
open FourierIntegral LineDeriv
variable {n r : ℕ}

/-- Distributional limit of the actual forward derivative transfer identities.
All three convergence hypotheses refer to literal graph integrals, including
all full amplitudes. Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem forwardGraph_distributional_limit_derivative
    (Φ : Euclidean n → Euclidean n → ℝ) (A : ℕ → FullAmplitude n r)
    (B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (u : Euclidean n → Fin r → ℂ) (j : Fin n)
    (hreg : ∀ k, ForwardTransferRegularization Φ (A k) B u j)
    (F R : 𝓢'(Euclidean n, Fin r → ℂ)) (D : Fin n → 𝓢'(Euclidean n, Fin r → ℂ))
    (hF : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto
      (fun k ↦ ∫ x, φ x • graphOperator Φ (A k) u x) atTop (𝓝 (F φ)))
    (hR : ∀ φ : 𝓢(Euclidean n, ℂ), Tendsto
      (fun k ↦ ∫ x, φ x • graphOperator Φ (forwardRemainderAmplitude B (A k) j) u x)
      atTop (𝓝 (R φ)))
    (hD : ∀ (φ : 𝓢(Euclidean n, ℂ)) l, Tendsto
      (fun k ↦ ∫ x, φ x • graphOperator Φ (forwardDatumAmplitude B (A k) j l)
        (fun y ↦ partialDeriv u y l) x) atTop (𝓝 (D l φ))) :
    lineDerivOp (EuclideanSpace.single j (1 : ℝ)) F = R + ∑ l, D l := by
  ext φ : 1
  have hl := hF (lineDerivOp (EuclideanSpace.single j (1 : ℝ)) φ)
  have hr := (hR φ).add (tendsto_finsetSum Finset.univ (fun l _ ↦ hD φ l))
  have heq := tendsto_nhds_unique hl (hr.neg.congr (fun k ↦ by
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv, partialDeriv] using
      ((hreg k).weak_derivative φ).symm))
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg]
  simp only [add_apply, sum_apply]
  exact neg_eq_iff_eq_neg.mpr heq

/-- Strong L² convergence of actual functions gives convergence of their
Schwartz pairings. Used for the literal graph limits in
`app:ch_response:thm:response-literal-transfer`. -/
theorem tendsto_forwardGraph_pairing_of_L2
    (v : ℕ → Euclidean n → Fin r → ℂ) (hv : ∀ k, MemLp (v k) 2)
    (V : Lp (Fin r → ℂ) 2 (volume : Measure (Euclidean n)))
    (hV : Tendsto (fun k ↦ (hv k).toLp (v k)) atTop (𝓝 V))
    (φ : 𝓢(Euclidean n, ℂ)) :
    Tendsto (fun k ↦ ∫ x, φ x • v k x) atTop (𝓝 ((V : 𝓢'(Euclidean n, Fin r → ℂ)) φ)) := by
  let J := Lp.toTemperedDistributionCLM (Fin r → ℂ) (volume : Measure (Euclidean n)) 2
  let ev := PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) (Fin r → ℂ) φ
  have h := ((ev.comp J).continuous.tendsto V).comp hV
  apply h.congr
  intro k
  change ((hv k).toLp (v k) : 𝓢'(Euclidean n, Fin r → ℂ)) φ = _
  rw [Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [(hv k).coeFn_toLp] with x hx
  rw [hx]

/-- L² limit version of the forward transfer. The limits are those of the
actual regularized base, remainder and datum-derivative graphs. Only L²
membership is supplied, never output Sobolev membership.
Source: `app:ch_response:eq:direct-envelope-profile`. -/
theorem forwardGraph_L2_limit_derivative
    (Φ : Euclidean n → Euclidean n → ℝ) (A : ℕ → FullAmplitude n r)
    (B : Euclidean n → Euclidean n → Matrix (Fin n) (Fin n) ℝ)
    (u : Euclidean n → Fin r → ℂ) (j : Fin n)
    (hreg : ∀ k, ForwardTransferRegularization Φ (A k) B u j)
    (F R : Lp (Fin r → ℂ) 2 (volume : Measure (Euclidean n)))
    (D : Fin n → Lp (Fin r → ℂ) 2 (volume : Measure (Euclidean n)))
    (hmF : ∀ k, MemLp (graphOperator Φ (A k) u) 2)
    (hmR : ∀ k, MemLp (graphOperator Φ (forwardRemainderAmplitude B (A k) j) u) 2)
    (hmD : ∀ k l, MemLp (graphOperator Φ (forwardDatumAmplitude B (A k) j l)
      (fun y ↦ partialDeriv u y l)) 2)
    (hF : Tendsto (fun k ↦ (hmF k).toLp _) atTop (𝓝 F))
    (hR : Tendsto (fun k ↦ (hmR k).toLp _) atTop (𝓝 R))
    (hD : ∀ l, Tendsto (fun k ↦ (hmD k l).toLp _) atTop (𝓝 (D l))) :
    lineDerivOp (EuclideanSpace.single j (1 : ℝ)) (F : 𝓢'(Euclidean n, Fin r → ℂ)) =
      (R : 𝓢'(Euclidean n, Fin r → ℂ)) + ∑ l, (D l : 𝓢'(Euclidean n, Fin r → ℂ)) := by
  apply forwardGraph_distributional_limit_derivative Φ A B u j hreg
  · exact tendsto_forwardGraph_pairing_of_L2 _ hmF F hF
  · exact tendsto_forwardGraph_pairing_of_L2 _ hmR R hR
  · intro φ l
    exact tendsto_forwardGraph_pairing_of_L2 _ (fun k ↦ hmD k l) (D l) (hD l) φ

end JanetCartan.ResponseTransfer
