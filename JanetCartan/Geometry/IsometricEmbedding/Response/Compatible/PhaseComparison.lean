module

public import JanetCartan.Analysis.Microlocal.HamiltonPhase

/-!
# Compatibility of inverse charts for the same Hamilton flow

The inverse-coordinate uniqueness step of
`app:ch_response:thm:response-compatible-choice`. These theorems compare actual
charts of one flow; they do not assert that the independently constructed primary
Cauchy phase has yet been identified with that flow.
-/

@[expose] public noncomputable section

open JanetCartan.HamiltonPhase
open scoped InnerProductSpace

namespace JanetCartan.CompatibleResponse

variable {E U : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  {H : HomogeneousSymbol E} {Φ : HamiltonFlow H U}

/-- Any inverse base coordinate in the source of a projection chart is its
unique inverse there (`app:ch_response:thm:response-compatible-choice`). -/
theorem projection_coordinates_unique (C : ProjectionChart Φ)
    {z : E × (ℝ × U)} {q : ℝ × InitialData U} (hq : q ∈ C.source)
    (hposition : Φ.position q = z.1) (hparameter : q.2.2 = z.2) :
    C.coordinates z = (q.1, q.2.1) := by
  have hi := C.left_inverse q hq
  simpa only [hposition, hparameter, Prod.eta] using hi

/-- Two charts of the same flow have the same inverse coordinates wherever the
second inverse belongs to the first source
(`app:ch_response:thm:response-compatible-choice`). -/
theorem projection_coordinates_eq (C D : ProjectionChart Φ)
    {z : E × (ℝ × U)} (hz : z ∈ D.target)
    (hsource : chartLift D.coordinates z ∈ C.source) :
    C.coordinates z = D.coordinates z := by
  exact projection_coordinates_unique C hsource (D.right_inverse z hz) rfl

/-- The explicit section-energy phase is independent of the chosen inverse
chart on their compatible overlap
(`app:ch_response:thm:response-compatible-choice`). -/
theorem phase_eq_on_compatible_charts (C D : ProjectionChart Φ)
    {z : E × (ℝ × U)} (hz : z ∈ D.target)
    (hsource : chartLift D.coordinates z ∈ C.source) :
    phase C.coordinates z = phase D.coordinates z := by
  simp only [phase, projection_coordinates_eq C D hz hsource]

/-- At zero energy the phase is exactly `u′ · ζ` for the unique inverse
carrier; the Hamilton-time term vanishes
(`app:ch_response:thm:response-compatible-choice`). -/
theorem zero_energy_phase_eq (C : ProjectionChart Φ)
    {x : E} {ζ u : U} {t : ℝ}
    (hsource : (t, (u, (0, ζ))) ∈ C.source)
    (hposition : Φ.position (t, (u, (0, ζ))) = x) :
    phase C.coordinates (x, (0, ζ)) = ⟪u, ζ⟫_ℝ := by
  have hc := projection_coordinates_unique C (z := (x, (0, ζ))) hsource hposition rfl
  simp only [phase, hc, zero_mul, zero_add]

/-- In a compatible zero-energy chart, the physical derivatives agree as well
as the phases. Both derivatives are the momentum of the same inverse carrier
(`app:ch_response:thm:response-compatible-choice`). -/
theorem zero_energy_phase_fderiv_eq (C D : ProjectionChart Φ)
    {x : E} {ζ : U} (hC : (x, (0, ζ)) ∈ C.target)
    (hD : (x, (0, ζ)) ∈ D.target)
    (hsource : chartLift D.coordinates (x, (0, ζ)) ∈ C.source) :
    fderiv ℝ (fun y ↦ phase C.coordinates (y, (0, ζ))) x =
      fderiv ℝ (fun y ↦ phase D.coordinates (y, (0, ζ))) x := by
  have hc := C.hasFDerivAt_phase hC
  have hd := D.hasFDerivAt_phase hD
  have hi : HasFDerivAt (fun y : E ↦ (y, ((0 : ℝ), ζ)))
      ((ContinuousLinearMap.id ℝ E).prod 0) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const (0, ζ) x)
  have hc' := (hc.comp x hi).fderiv
  have hd' := (hd.comp x hi).fderiv
  simp only [Function.comp_def] at hc' hd'
  rw [hc', hd']
  simp only [phaseDifferential, chartLift, projection_coordinates_eq C D hD hsource]

end JanetCartan.CompatibleResponse
