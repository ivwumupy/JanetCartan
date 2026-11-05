module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.DirectEvolution.CompactTransfer.Terms

/-!
# Rescaling finite parameter words

The joint annular endpoints assume directions in the unit ball. This exact
rescaling supplies arbitrary finite words to the local domination input of
`orderedTransferAction_elapsedIntegral`, with no regularity hypothesis.
Source: the ordered parameter derivatives in `new:eq:carrier-ibp`.
-/

@[expose] public noncomputable section
namespace JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
open Pseudodifferential

/-- Every finite parameter word is a scalar multiple of a word of the same
length with directions in the unit ball. The identity holds for every function:
constant scalar multiplication commutes with the totalized Fréchet derivative.
Consumer: local domination from the unit-direction primitive joint endpoint
(`app:ch_response:lem:energy-carrier-jets`, `new:eq:carrier-ibp`). -/
theorem exists_unitParameterWord_rescaling {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (qs : List P) :
    ∃ us : List P, us.length = qs.length ∧ (∀ v ∈ us, ‖v‖ ≤ 1) ∧
      ∃ k : ℝ, ∀ f : P → F,
        orderedTransferAction (fun v g b ↦ fderiv ℝ g b v) qs f =
          k • orderedTransferAction (fun v g b ↦ fderiv ℝ g b v) us f := by
  induction qs with
  | nil => exact ⟨[], rfl, by simp, 1, fun _ ↦ (one_smul ℝ _).symm⟩
  | cons v qs ih =>
    obtain ⟨us, hlen, hus, k, he⟩ := ih
    let m : ℝ := max 1 ‖v‖
    have hm : 0 < m := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    let u : P := m⁻¹ • v
    have hu : ‖u‖ ≤ 1 := by
      dsimp only [u]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
      exact (inv_mul_le_one₀ hm).2 (le_max_right _ _)
    have hv : v = m • u := by
      simp [u, smul_smul, mul_inv_cancel₀ hm.ne']
    refine ⟨u :: us, by simp [hlen], ?_, m * k, ?_⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact hu
      · exact hus w hw
    · intro f
      funext b
      change fderiv ℝ (orderedTransferAction (fun v g b ↦ fderiv ℝ g b v) qs f) b v =
        (m * k) • fderiv ℝ (orderedTransferAction (fun v g b ↦ fderiv ℝ g b v) us f) b u
      rw [he f, fderiv_const_smul_field]
      simp only [Pi.smul_apply, smul_apply]
      calc
        _ = k • (fderiv ℝ (orderedTransferAction (fun v g b ↦ fderiv ℝ g b v) us f) b) (m • u) := by rw [← hv]
        _ = _ := by rw [map_smul, smul_smul, mul_comm k m]

end JanetCartan.ResponseTransfer.DirectEvolution.IntegratedEnvelope.Parameter
