module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.OperatorBounds

/-!
# External half-normalization of the fixed-shift estimates

The actual complete assembly applies this elementary deduction after adding
the characteristic and elliptic estimates. The adjoint uses the literal
conjugate scalar, which is again one half. Sources: `energy-complete-residual`,
`measured-adjoint`.
-/

@[expose] public noncomputable section
open MeasureTheory
namespace JanetCartan.RegularSector.NormalizedSolver
open Pseudodifferential ResponseTransfer.Complement
variable {n q : ℕ}
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure (Euclidean n))

/-- Real homogeneity of the existing Fourier Sobolev subspace at the exact
external factor one half (`real-sector-normalization`). -/
private theorem vectorFourierSobolev_half (s : ℝ) (u : H) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev s ((1/2 : ℂ) • u) ∧
      vectorFourierSobolevNorm s ((1/2 : ℂ) • u) =
        (1/2 : ℝ) * vectorFourierSobolevNorm s u := by
  have he : (1/2 : ℂ) • u = (1/2 : ℝ) • u := by
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
  rw [he]
  let a : vectorFourierSobolevLevel s := ⟨u, hu⟩
  refine ⟨((1/2 : ℝ) • a).property, ?_⟩
  change vectorFourierSobolevNorm s ((1/2 : ℝ) • a).val =
    (1/2 : ℝ) * vectorFourierSobolevNorm s a.val
  rw [← norm_vectorWeightedFourier, ← norm_vectorWeightedFourier, map_smul, norm_smul]
  norm_num

/-- Halving the actual complex operator halves its fixed-shift cost in
both orientations. This is applied to the full characteristic-plus-elliptic
sum before physical pairing (`energy-complete-residual`, `measured-adjoint`). -/
theorem direct_sobolev_half
    (T : H →L[ℂ] H) (s t A high : ℝ)
    (hT : ∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
      MemVectorFourierSobolev s u → MemVectorFourierSobolev t (V u) ∧
      vectorFourierSobolevNorm t (V u) ≤ A*(vectorFourierSobolevNorm s u+high*‖u‖))
    (V : H →L[ℂ] H) (hV : V = (1/2 : ℂ) • T ∨ V = ((1/2 : ℂ) • T).adjoint)
    (u : H) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev t (V u) ∧ vectorFourierSobolevNorm t (V u) ≤
      (A/2)*(vectorFourierSobolevNorm s u+high*‖u‖) := by
  have hb (W : H →L[ℂ] H) (hW : W = T ∨ W = T.adjoint) :
      MemVectorFourierSobolev t ((1/2 : ℂ) • W u) ∧
      vectorFourierSobolevNorm t ((1/2 : ℂ) • W u) ≤
        (A/2)*(vectorFourierSobolevNorm s u+high*‖u‖) := by
    obtain ⟨hm, hn⟩ := hT W hW u hu
    obtain ⟨hm', hn'⟩ := vectorFourierSobolev_half t (W u) hm
    refine ⟨hm', ?_⟩
    rw [hn']
    calc
      _ ≤ (1/2 : ℝ) * (A*(vectorFourierSobolevNorm s u+high*‖u‖)) :=
        mul_le_mul_of_nonneg_left hn (by norm_num)
      _ = _ := by ring
  rcases hV with rfl | rfl
  · exact hb T (Or.inl rfl)
  · simpa only [map_smulₛₗ, map_div₀, map_one, map_ofNat, smul_apply] using
      hb T.adjoint (Or.inr rfl)

end JanetCartan.RegularSector.NormalizedSolver
