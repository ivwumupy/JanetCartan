module
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.Physical

/-!
# Carrier conjugation on the original vector L² space

Unit-modulus multiplication preserves the norm, literal adjoint and strong
regularization limits. This is the demodulation step between the branch L²
constructor and the weak Sobolev proof of
`app:ch_response:eq:direct-envelope-profile`, following `new:eq:carrier-ibp`.
The physical operator and frequency remain fixed throughout.
-/

@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
open JanetCartan.ResponseTransfer.Complement
variable {n r : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin r)) 2 (volume : Measure E)

/-- The carrier has exactly unit modulus on the same physical L² space.
Source: restoration of the carrier following `new:eq:carrier-ibp`. -/
theorem norm_carrierMultiplication_apply (lam : ℝ) (φ : E → ℝ)
    (hφ : Continuous φ) (u : H) : ‖carrierMultiplication lam φ hφ u‖ = ‖u‖ := by
  have hb (ρ : ℝ) (v : H) : ‖carrierMultiplication ρ φ hφ v‖ ≤ ‖v‖ := by
    calc
      ‖carrierMultiplication ρ φ hφ v‖ ≤ 1 * ‖v‖ := by
        apply Lp.norm_le_mul_norm_of_ae_le_mul
        filter_upwards [carrierMultiplication_ae ρ φ hφ v] with x hx
        simp [hx, norm_smul, carrier, Complex.norm_exp]
      _ = ‖v‖ := one_mul _
  apply le_antisymm (hb lam u)
  simpa only [carrierMultiplication_neg_cancel] using hb (-lam) (carrierMultiplication lam φ hφ u)

/-- The literal Hilbert adjoint is multiplication by the opposite carrier,
as required by the reversed-phase case of `new:eq:carrier-ibp`. -/
theorem carrierMultiplication_adjoint (lam : ℝ) (φ : E → ℝ)
    (hφ : Continuous φ) :
    (carrierMultiplication (r := r) lam φ hφ).adjoint = carrierMultiplication (-lam) φ hφ := by
  have hi := (carrierMultiplication (r := r) lam φ hφ).norm_map_iff_adjoint_comp_self.mp
    (norm_carrierMultiplication_apply lam φ hφ)
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg (fun T : H →L[ℂ] H => T (carrierMultiplication (-lam) φ hφ u)) hi
  have hc : carrierMultiplication lam φ hφ (carrierMultiplication (-lam) φ hφ u) = u := by
    simpa only [neg_neg] using carrierMultiplication_neg_cancel (-lam) φ hφ u
  simpa only [ContinuousLinearMap.comp_apply, hc, one_apply_eq_self] using h

/-- Conjugation of the fixed physical operator by the SAME source and output
carrier (`app:ch_response:eq:direct-envelope-profile`). -/
def demodulatedL2Operator (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (carrierMultiplication (-lam) φ hφ).comp (T.comp (carrierMultiplication lam φ hφ))

/-- Demodulation has no frequency or scale cost in L². The actual low graph
constructor supplies the physical operator bound (`new:eq:carrier-ibp`). -/
theorem norm_demodulatedL2Operator_le (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (T : H →L[ℂ] H) : ‖demodulatedL2Operator lam φ hφ T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro u
  change ‖carrierMultiplication (-lam) φ hφ (T (carrierMultiplication lam φ hφ u))‖ ≤ _
  rw [norm_carrierMultiplication_apply]
  simpa only [norm_carrierMultiplication_apply] using T.le_opNorm (carrierMultiplication lam φ hφ u)

/-- Demodulation commutes with the literal Hilbert adjoint. No change of
amplitude or graph realization is made (`new:eq:carrier-ibp`). -/
theorem demodulatedL2Operator_adjoint (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (T : H →L[ℂ] H) :
    (demodulatedL2Operator lam φ hφ T).adjoint = demodulatedL2Operator lam φ hφ T.adjoint := by
  simp only [demodulatedL2Operator, ContinuousLinearMap.adjoint_comp,
    carrierMultiplication_adjoint, neg_neg, ContinuousLinearMap.comp_assoc]

/-- The actual regularizations converge strongly after carrier conjugation.
This also applies to the adjoints by `demodulatedL2Operator_adjoint`.
Source: passage to the realized graph in `app:ch_response:eq:direct-envelope-profile`. -/
theorem demodulatedL2Operator_strongLimit (lam : ℝ) (φ : E → ℝ) (hφ : Continuous φ)
    (Treg : ℕ → H →L[ℂ] H) (T : H →L[ℂ] H)
    (hlim : ∀ u, Tendsto (fun k => Treg k u) atTop (𝓝 (T u))) (u : H) :
    Tendsto (fun k => demodulatedL2Operator lam φ hφ (Treg k) u) atTop
      (𝓝 (demodulatedL2Operator lam φ hφ T u)) :=
  carrierMultiplication_tendsto (-lam) φ hφ (hlim (carrierMultiplication lam φ hφ u))

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularSobolev
