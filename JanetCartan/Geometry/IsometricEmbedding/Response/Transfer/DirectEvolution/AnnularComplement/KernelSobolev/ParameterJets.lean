module

public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.GraphRealization.LocalIntegral
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.ParameterDerivatives.MixedGrades.OrderedSpatial

/-!
# Spatial bounds for actual parameter derivatives

The joint-order counting in `app:ch_response:lem:energy-carrier-jets` and
`app:ch_response:eq:fixed-factor-transfer`. Each parameter derivative costs
exactly one joint derivative. This deduction applies to the full integral,
including every output-carrier derivative when the supplied kernel is physical.
-/

@[expose] public noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
open Complement.ParameterDerivatives
open Complement.ParameterDerivatives.MixedGrades

variable {P X F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Joint smoothness of an evaluated actual parameter derivative in
`app:ch_response:lem:energy-carrier-jets`. The consuming Sobolev reconstruction
uses the spatial slice of this very function. -/
theorem contDiffOn_annularParameterJet {g : P × X → F} {U : Set P}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (U ×ˢ univ))
    (k : ℕ) (v : Fin k → P) :
    ContDiffOn ℝ ∞ (fun z : P × X ↦
      iteratedFDeriv ℝ k (fun c ↦ g (c, z.2)) z.1 v) (U ×ˢ univ) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ P) F v).contDiff.comp_contDiffOn
    (contDiffOn_parameterIteratedFDeriv hU hg k)

/-- Unit parameter directions consume precisely `k` joint orders, with no
frequency loss added by the conversion. Consumer: the physical and demodulated
Sobolev bounds in `app:ch_response:lem:energy-carrier-jets`. -/
theorem norm_annularParameterJet_joint_le {g : P × X → F} {U : Set P}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (U ×ˢ univ))
    (k : ℕ) (v : Fin k → P) (hv : ∀ a, ‖v a‖ ≤ 1)
    (j : ℕ) {z : P × X} (hz : z ∈ U ×ˢ univ) :
    ‖iteratedFDeriv ℝ j (fun w : P × X ↦
      iteratedFDeriv ℝ k (fun c ↦ g (c, w.2)) w.1 v) z‖ ≤
      ‖iteratedFDeriv ℝ (j + k) g z‖ := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    let H : P × X → F := fun w ↦ iteratedFDeriv ℝ k (fun c ↦ g (c, w.2)) w.1 (Fin.tail v)
    have hH : ContDiffOn ℝ ∞ H (U ×ˢ univ) :=
      contDiffOn_annularParameterJet hU hg k (Fin.tail v)
    have he : (fun w : P × X ↦ iteratedFDeriv ℝ (k + 1)
        (fun c ↦ g (c, w.2)) w.1 v) =ᶠ[𝓝 z]
        (fun w ↦ fderiv ℝ (fun c ↦ H (c, w.2)) w.1 (v 0)) := by
      filter_upwards [(hU.prod isOpen_univ).mem_nhds hz] with w hw
      have hs : ContDiffAt ℝ ∞ (fun c ↦ g (c, w.2)) w.1 :=
        (hg.contDiffAt ((hU.prod isOpen_univ).mem_nhds hw)).comp w.1
          (contDiffAt_id.prodMk contDiffAt_const)
      exact (hs.differentiableAt_iteratedFDeriv
        (by exact_mod_cast ENat.natCast_lt_top k : (k : ℕ∞ω) < ∞)).iteratedFDeriv_succ_apply_left'
    rw [(he.iteratedFDeriv ℝ j).eq_of_nhds]
    apply (norm_iteratedFDeriv_parameterFDeriv_le (hU.prod isOpen_univ) hH hz (v 0) j).trans
    apply (mul_le_of_le_one_left (norm_nonneg _) (hv 0)).trans
    have hi := ih (Fin.tail v) (fun a ↦ hv a.succ) (j + 1)
    have horder : j + 1 + k = j + (k + 1) := by omega
    rw [horder] at hi
    exact hi

/-- Freezing the parameter gives the spatial bound consumed by compact
Sobolev conversion, at total joint order `j+k`
(`app:ch_response:lem:energy-carrier-jets`). -/
theorem norm_annularParameterJet_spatial_le {g : P × X → F} {U : Set P}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g (U ×ˢ univ))
    (k : ℕ) (v : Fin k → P) (hv : ∀ a, ‖v a‖ ≤ 1)
    (j : ℕ) {c : P} (hc : c ∈ U) (x : X) :
    ‖iteratedFDeriv ℝ j (fun y ↦ iteratedFDeriv ℝ k (fun a ↦ g (a, y)) c v) x‖ ≤
      ‖iteratedFDeriv ℝ (j + k) g (c, x)‖ :=
  (norm_iteratedFDeriv_fixed_parameter_le hU
    (contDiffOn_annularParameterJet hU hg k v) hc x j).trans
      (norm_annularParameterJet_joint_le hU hg k v hv j ⟨hc, mem_univ x⟩)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
/-- Parameter derivatives retain the original compact output support by
locality in the open parameter set. No support assumption on differentiated
outputs is needed (`app:ch_response:lem:energy-carrier-jets`). -/
theorem annularParameterJet_eq_zero_off_support {g : P × X → F}
    {U : Set P} {S : Set X} (hU : IsOpen U)
    (hs : ∀ c ∈ U, ∀ x ∉ S, g (c, x) = 0)
    (k : ℕ) (v : Fin k → P) {c : P} (hc : c ∈ U) {x : X} (hx : x ∉ S) :
    iteratedFDeriv ℝ k (fun a ↦ g (a, x)) c v = 0 := by
  have he : (fun a ↦ g (a, x)) =ᶠ[𝓝 c] (fun _ ↦ (0 : F)) :=
    Filter.mem_of_superset (hU.mem_nhds hc) (fun a ha ↦ hs a ha x hx)
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  cases k <;> simp

end JanetCartan.ResponseTransfer.DirectEvolution.AnnularComplement
