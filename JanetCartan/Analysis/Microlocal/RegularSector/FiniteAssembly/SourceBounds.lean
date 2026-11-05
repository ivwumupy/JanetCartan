module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceOperator
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.OperatorBounds
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.IdentityDefect.TerminalBounds.Ordinary

/-!
# The full source identity defect at the selected threshold

The source is the actual angular PDO of the same enlarged family. Its complete
defect, including the low-frequency shoulder, has an order-zero estimate in
both orientations. No gain is asserted for that defect. This is the remaining
order-zero summand of `selectedFiniteCompleteError` (`prop:complete-residual`,
`resolved-angular-tail`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic.EvolutionIntegral FiniteMasks FiniteMasks.ActualFamily
open FourierIntegral LowBounds Pseudodifferential
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "H" => SpacetimeL2 d (d+1)

/-- Construct the bound for the entire common-masked source defect from the
actual angular multiplier and the fixed output. The literal adjoint reverses
all physical masks. Its constants precede Q and B (`resolved-angular-tail`). -/
theorem exists_selectedFiniteSourcePDO_identity_defect_bounds
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) :
    ∃ cost : ℕ → ℝ, (∀ s, 0 ≤ cost s) ∧
    let D := (sourceCutMultiplier output ho.continuous hob).comp (selectedFiniteSourcePDO f L)-1
    ∀ s : ℕ, ∀ V : H →L[ℂ] H, (V = D ∨ V = D.adjoint) → ∀ u,
      MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ cost s*vectorFourierSobolevNorm (s : ℝ) u := by
  have hforward s := exists_actualAngularPDO_sub_identity_sobolev_bound
    (r := d+1) (withEnlargedThreshold f L hL) false s
  have hreverse s := exists_actualAngularPDO_sub_identity_sobolev_bound
    (r := d+1) (withEnlargedThreshold f L hL) true s
  choose Cf hCf hf using hforward
  choose Ca hCa ha using hreverse
  let C s := Cf s+Ca s+1
  have hC s : 0 ≤ C s := by dsimp [C]; linarith [hCf s, hCa s]
  have hsource (s : ℕ) (V : H →L[ℂ] H)
      (hV : V = selectedFiniteSourcePDO f L ∨ V = (selectedFiniteSourcePDO f L).adjoint)
      (u : H) (hu : MemVectorFourierSobolev (s : ℝ) u) :
      MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ C s*vectorFourierSobolevNorm (s : ℝ) u := by
    have hdefect : MemVectorFourierSobolev (s : ℝ) ((V-1) u) ∧
        vectorFourierSobolevNorm (s : ℝ) ((V-1) u) ≤
          (Cf s+Ca s)*vectorFourierSobolevNorm (s : ℝ) u := by
      rcases hV with rfl | rfl
      · rw [selectedFiniteSourcePDO_eq_actualAngularPDO f L hL]
        exact ⟨(hf s u hu).1, (hf s u hu).2.trans (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (hCa s)) (norm_nonneg _))⟩
      · rw [selectedFiniteSourcePDO_eq_actualAngularPDO f L hL]
        exact ⟨(ha s u hu).1, (ha s u hu).2.trans (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (hCf s)) (norm_nonneg _))⟩
    obtain ⟨hm, hn⟩ := TerminalBounds.add_bound hdefect.1 hu
    have he : (V-1) u+u = V u := by simp
    rw [he] at hm hn
    refine ⟨hm, hn.trans ?_⟩
    calc
      _ ≤ (Cf s+Ca s)*vectorFourierSobolevNorm (s : ℝ) u+
          vectorFourierSobolevNorm (s : ℝ) u := add_le_add hdefect.2 le_rfl
      _ = C s*vectorFourierSobolevNorm (s : ℝ) u := by dsimp [C]; ring
  obtain ⟨Dm, hDm, hmask⟩ := exists_outputMask_sobolev_constants (q := d+1) output ho hoc hob
  refine ⟨fun s ↦ Dm s*C s*Dm s+1,
    fun s ↦ add_nonneg (mul_nonneg (mul_nonneg (zero_le_one.trans (hDm s)) (hC s))
      (zero_le_one.trans (hDm s))) zero_le_one, ?_⟩
  intro D s V hV u hu
  have hm := hmask (selectedFiniteSourcePDO f L) s s (C s) 0 (hC s) le_rfl
    (by simpa only [zero_mul, add_zero] using hsource s)
  have hid (W : H →L[ℂ] H) (hW : W = 1 ∨ W = (1 : H →L[ℂ] H).adjoint) (v : H)
      (hv : MemVectorFourierSobolev (s : ℝ) v) :
      MemVectorFourierSobolev (s : ℝ) (W v) ∧
      vectorFourierSobolevNorm (s : ℝ) (W v) ≤
        1*(vectorFourierSobolevNorm (s : ℝ) v+0*‖v‖) := by
    rcases hW with rfl | rfl <;> simpa using And.intro hv (le_refl (vectorFourierSobolevNorm (s : ℝ) v))
  have hneg := direct_sobolev_unit_smul (1 : H →L[ℂ] H) (-1) (by simp)
    s s 1 0 hid
  have hb := direct_sobolev_add _ _ s s (Dm s*C s*Dm s) 1 0 hm hneg
  have hv : V = (sourceCutMultiplier output ho.continuous hob).comp
      (selectedFiniteSourcePDO f L)+(-1 : ℂ) • (1 : H →L[ℂ] H) ∨
      V = ((sourceCutMultiplier output ho.continuous hob).comp
        (selectedFiniteSourcePDO f L)+(-1 : ℂ) • (1 : H →L[ℂ] H)).adjoint := by
    have he : (-1 : ℂ) • (1 : H →L[ℂ] H) = -1 := by ext u; simp
    simpa only [D, he, sub_eq_add_neg] using hV
  simpa only [zero_mul, add_zero] using hb V hv u hu

end JanetCartan.RegularSector.FiniteAssembly
