module

public import JanetCartan.Geometry.IsometricEmbedding.Reference.ActualCarriers.PencilContinuity
public import JanetCartan.Geometry.IsometricEmbedding.Reference.StressFrame.LocalComposition

/-!
# Literal incidence coefficients

The coefficient in Step 3 of `app:ch_seed:prop:seed-actual-menu` is the actual
covector differential of the determinant, evaluated on the testing covector.
Its polynomial smoothness includes singular pencils. These formulas are the
input to the quantitative estimates in `ActualCarriers/IncidenceBounds`.
-/

@[expose] public noncomputable section

open scoped ContDiff Matrix Matrix.Norms.Frobenius

namespace JanetCartan.ActualCarriers

/-- `app:ch_seed:prop:seed-actual-menu`, Step 3: the literal incidence coefficient
`k · d_ξ p(Q, ξ)`, with the covector represented in the shared Euclidean space. -/
def incidenceCoefficient {n : ℕ}
    (p : ((Fin n → MetricTensor n) × Euclidean n) × Euclidean n) : ℝ :=
  fderiv ℝ (determinant p.1.1) p.1.2 p.2

/-- `app:ch_seed:prop:seed-actual-menu`, Step 3: the incidence coefficient is a
polynomial cofactor contraction, even on the characteristic set. -/
theorem incidenceCoefficient_eq_trace {n : ℕ} (Q : Fin n → MetricTensor n)
    (ξ k : Euclidean n) :
    incidenceCoefficient ((Q, ξ), k) = ((pencil Q ξ).adjugate * pencil Q k).trace :=
  fderiv_determinant_apply Q ξ k

/-- `app:ch_seed:eq:seed-phase-tame`: joint smoothness of the fixed polynomial
coefficient. Together with compact primitive ranges this supplies all outer
coefficient bounds for the tame composition theorem. -/
theorem contDiff_incidenceCoefficient {n : ℕ} :
    ContDiff ℝ ∞ (incidenceCoefficient (n := n)) :=
  (contDiff_fderiv_determinant.comp contDiff_fst).clm_apply contDiff_snd

end JanetCartan.ActualCarriers
