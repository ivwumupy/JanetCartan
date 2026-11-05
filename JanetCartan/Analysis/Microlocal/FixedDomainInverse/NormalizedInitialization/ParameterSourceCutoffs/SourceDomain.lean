module

public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ParameterSourceCutoffs.FourierProfiles
public import JanetCartan.Analysis.Microlocal.FixedDomainInverse.NormalizedInitialization.ParameterSourceCutoffs.Support

/-!
# Extend the original supported source profile to every parameter

The fixed source is zero off its original closed parameter support. Every
parameter jet is consequently zero there. A Fourier profile proved on any
set containing that support therefore holds globally with the identical
constants and reserve. This is the input-domain bridge from the original
parameter neighborhood to each selected active sector in
`app:ch_response:eq:response-whole-source-partition`.
-/

@[expose] public noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace JanetCartan.FixedDomainInverse.ParameterSourceCutoffs

open Pseudodifferential ResponseTransfer ResponseTransfer.Complement

variable {X P F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every original parameter jet vanishes outside the closed parameter
support. No global estimate outside that support is an input
(`app:ch_response:cor:finite-jets`). -/
theorem parameter_jet_eq_zero_off_closed_support
    (a : X × P → F) {C : Set P} (hC : IsClosed C)
    (hs : ∀ q, q.2 ∉ C → a q = 0) {c : P} (hc : c ∉ C)
    (y : X) (l : ℕ) (w : Fin l → P) :
    iteratedFDeriv ℝ l (fun b ↦ a (y,b)) c w = 0 := by
  have he : (fun b ↦ a (y,b)) =ᶠ[𝓝 c] fun _ ↦ (0 : F) := by
    filter_upwards [hC.isOpen_compl.mem_nhds hc] with b hb
    exact hs (y,b) hb
  rw [(he.iteratedFDeriv (𝕜 := ℝ) l).eq_of_nhds]
  cases l with
  | zero => simp
  | succ l => simp

variable {n r : ℕ} {I : Type*}
local notation "E" => Euclidean n
local notation "Fibre" => EuclideanSpace ℂ (Fin r)
local notation "H" => Lp Fibre 2 (volume : Measure E)

/-- The original natural reserved source profile extends to every parameter
with the SAME constants. Outside the fixed closed parameter support all
source jets are identically zero. This lets the active-sector theorem receive
the cutoff source on its own neighborhood, without any new Fourier premise
(`app:ch_response:eq:response-whole-source-partition`). -/
theorem reserved_source_fourier_profile_global_of_closed_parameter_support
    {C V : Set P} (hC : IsClosed C) (hCV : C ⊆ V)
    (a : I → E × P → Fibre) (hs : ∀ i q, q.2 ∉ C → a i q = 0)
    (A K : I → ℝ) (hA : ∀ i, 0 ≤ A i) (hK : ∀ i, 0 ≤ K i)
    (reserve : ℕ) (Csource : ℕ → ℕ → ℝ) (hCsource : ∀ l s, 0 ≤ Csource l s)
    (hsource : ∀ i c, c ∈ V → ∀ l (w : Fin l → P), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
          Csource l s*A i*K i^(s+l-reserve)) :
    ∀ i c, ∀ l (w : Fin l → P), (∀ j, ‖w j‖ ≤ 1) → ∀ s : ℕ,
      let f := fun y ↦ iteratedFDeriv ℝ l (fun q ↦ a i (y,q)) c w
      ∃ hm : MemLp f 2 volume, MemVectorFourierSobolev (s : ℝ) (hm.toLp f) ∧
        vectorFourierSobolevNorm (s : ℝ) (hm.toLp f) ≤
          Csource l s*A i*K i^(s+l-reserve) := by
  intro i c l w hw s f
  by_cases hc : c ∈ C
  · exact hsource i c (hCV hc) l w hw s
  · have hf : f = 0 := funext fun y ↦
      parameter_jet_eq_zero_off_closed_support (a i) hC (hs i) hc y l w
    rw [hf]
    let G : GradedScale H := vectorFourierSobolevScale
    have hz : MemVectorFourierSobolev (s : ℝ) (0 : H) := (G.level s).zero_mem
    refine ⟨MemLp.zero,hz,?_⟩
    change vectorFourierSobolevNorm (s : ℝ) (0 : H) ≤ _
    rw [← vectorFourierSobolevScale_gradeNorm s hz]
    change G.gradeNorm s 0 ≤ _
    rw [G.gradeNorm_eq hz]
    change G.seminorm s 0 ≤ _
    rw [map_zero]
    exact mul_nonneg (mul_nonneg (hCsource l s) (hA i)) (pow_nonneg (hK i) _)

end JanetCartan.FixedDomainInverse.ParameterSourceCutoffs
