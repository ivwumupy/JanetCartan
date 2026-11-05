module

public import JanetCartan.Analysis.Microlocal.EllipticComplement.SymbolBudgets
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.IntegerBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.EvolutionIntegral.NegativeBounds.VectorDuality
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.OperatorBounds

/-!
# Fixed-shift estimates of the actual complementary operators

Both orientations act on the same Fourier spaces as the selected finite solver.
The original fields occur additively at order `n+2*(d+2)+2`. Duality uses the
literal Hilbert adjoint. Source: `app:ch_regular_base:eq:sector-theorem-solution`,
`app:ch_regular_base:eq:sector-theorem-residual`, `measured-adjoint`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius
namespace JanetCartan.RegularSector.EllipticComplement
open FiniteMasks.ActualFamily Characteristic.EvolutionIntegral Characteristic.PdoRealization
open FiniteAssembly FourierIntegral Pseudodifferential
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ}
local notation "E" => Euclidean (d+1)
local notation "Mat" => MetricTensor (d+1)
local notation "CMat" => Matrix (Fin (d+1)) (Fin (d+1)) ℂ
local notation "Coeff" => Fin (d+1) → Mat
local notation "H" => SpacetimeL2 d (d+1)
variable {Ω : Set (Euclidean (d + 1))} {x : Euclidean (d + 1)} {RQ M : ℝ}
variable {A₀ : Fin (d + 1) → MetricTensor (d + 1)} {K : Set (Euclidean (d + 1))}
variable (f : ActualMaskFamily Ω x RQ A₀ K M) (hK : IsCompact K)

/-- The actual inverse and its full residual gain one derivative with the
original additive profile, both forwards and for the literal adjoint, at
nonnegative and negative integer orders. All constants and the loss precede
the enlarged threshold and fields (`sector-theorem-solution`, `measured-adjoint`). -/
theorem exists_elliptic_gain_constants (hΩ : IsOpen Ω) (hRQΩ : closedBall x RQ ⊆ Ω) :
    ∃ cost : ℕ → ℝ, (∀ n, 0 ≤ cost n) ∧ ∀ L ≥ f.radialThreshold,
      ∀ (Q : E → Coeff) (B : E → Mat), ContDiffOn ℝ ∞ Q Ω → ContDiffOn ℝ ∞ B Ω →
      MapsTo Q Ω (closedBall A₀ f.coefficientRadius) →
      cNorm (closedBall x RQ) (2*(d+2)+2) Q ≤ M →
      cNorm (closedBall x RQ) (2*(d+2)+2) B ≤ M →
      ∀ T ∈ ({ellipticSolver f hK L Q, ellipticResidual f hK L Q B} : Set (H →L[ℂ] H)),
        ∀ n : ℕ,
        let high := 1 + cNorm (closedBall x RQ) (n+(2*(d+2)+2)) Q +
          cNorm (closedBall x RQ) (n+(2*(d+2)+2)) B
        ∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) →
          (∀ u, MemVectorFourierSobolev (n : ℝ) u →
            MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
            vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
              cost n * (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖)) ∧
          ∀ u, MemVectorFourierSobolev (-(n : ℝ)) (V u) ∧
            vectorFourierSobolevNorm (-(n : ℝ)) (V u) ≤
              ((d+1 : ℝ)*(d+1)*cost n)*(1+high)*vectorFourierSobolevNorm (-((n : ℝ)+1)) u := by
  obtain ⟨R, _, N, _, C, _, hbud⟩ := exists_ellipticSymbols_pdo_budgets f hK hΩ hRQΩ
  choose F hF hfor using fun n ↦ exists_canonicalGraph_integer_gain_tame_constant_all_data
    (r := d+1) (Nat.succ_pos d) R n N
  choose J hJ hadj using fun n ↦ exists_canonicalGraph_adjoint_integer_gain_tame_constant_all_data
    (r := d+1) (Nat.succ_pos d) R n N
  let dim : ℝ := ((d+1 : ℕ) : ℝ)
  have hd : 0 ≤ dim * dim := by dsimp [dim]; positivity
  let G n := dim * dim * (F n + J n)
  let D n := max 1 (C (2*(d+2)+(n+1)))
  let cost n := G n * D n
  have hG n : 0 ≤ G n := mul_nonneg hd (add_nonneg (hF n) (hJ n))
  have hD n : 1 ≤ D n := le_max_left _ _
  have hcost n : 0 ≤ cost n := mul_nonneg (hG n) (zero_le_one.trans (hD n))
  refine ⟨cost, hcost, ?_⟩
  intro L hL Q B hQ hB hmap hQlow hBlow T hT n high
  have hhigh : 1 ≤ high := by
    dsimp only [high]
    linarith [cNorm_nonneg (closedBall x RQ) (n+(2*(d+2)+2)) Q,
      cNorm_nonneg (closedBall x RQ) (n+(2*(d+2)+2)) B]
  have hpos (s : E → E → CMat)
      (hs : s ∈ ({ellipticInverseSymbol f hK L Q, ellipticResidualSymbol f hK L Q B} :
        Set (E → E → CMat))) :
      let S := maskedPhysicalPDO (fun y ↦ (f.outputMask y : ℂ)) (fun z ↦ (f.inputMask z : ℂ)) s
      ∀ V : H →L[ℂ] H, (V = S ∨ V = S.adjoint) → ∀ u, MemVectorFourierSobolev (n : ℝ) u →
        MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧ vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
          cost n * (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖) := by
    intro S V hV u hu
    let A := fun y z ζ ↦ ((f.outputMask y : ℂ) * (f.inputMask z : ℂ)) • s y ζ
    obtain ⟨hb, hlow, hjet⟩ := hbud L hL Q B hQ hB hmap hQlow hBlow s hs
    have htop ξ is (hi : is.length ≤ 2*((d+1)+1)+(n+1)) z :
        (1+‖ξ‖)*‖AmplitudeBound.matrixAmplitudeCoordinateDerivList is
          (physicalPDOCycleSymbol A ξ) z‖ ≤ D n * high := by
      have he := hjet (2*(d+2)+(n+1)) ξ is hi z
      rw [show 2*(d+2)+(n+1)+1 = n+(2*(d+2)+2) by omega] at he
      exact he.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (zero_le_one.trans hhigh))
    have hDH := one_le_mul_of_one_le_of_one_le (hD n) hhigh
    let a := vectorFourierSobolevNorm (n : ℝ) u
    have ha : 0 ≤ a := norm_nonneg _
    have hnorm : 0 ≤ a + (D n * high)*‖u‖ :=
      add_nonneg ha (mul_nonneg (zero_le_one.trans hDH) (norm_nonneg _))
    have hboth : MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧
        vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤ G n * (a + (D n * high)*‖u‖) := by
      rcases hV with rfl | rfl
      · have h := hfor n A hb.smooth hb.support _ hlow htop u hu
        rw [max_eq_right hDH] at h
        exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_right (hJ n)) hd) hnorm)⟩
      · have h := hadj n A hb.smooth hb.support _ hlow htop u hu
        rw [max_eq_right hDH] at h
        exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (hF n)) hd) hnorm)⟩
    refine ⟨hboth.1, hboth.2.trans ?_⟩
    calc
      _ ≤ G n * (D n * a + (D n * high) * ‖u‖) :=
        mul_le_mul_of_nonneg_left (add_le_add_left
          (le_mul_of_one_le_left ha (hD n)) _) (hG n)
      _ = _ := by dsimp only [cost, a]; ring
  have hscaled (V : H →L[ℂ] H) (hV : V = T ∨ V = T.adjoint) (u : H)
      (hu : MemVectorFourierSobolev (n : ℝ) u) :
      MemVectorFourierSobolev ((n : ℝ)+1) (V u) ∧ vectorFourierSobolevNorm ((n : ℝ)+1) (V u) ≤
        cost n * (vectorFourierSobolevNorm (n : ℝ) u + high * ‖u‖) := by
    rcases hT with h | h
    · rw [h] at hV
      exact direct_sobolev_unit_smul _ (1 / Complex.I) (by simp) _ _ _ _
        (hpos _ (Or.inl rfl)) V hV u hu
    · have he : T = ellipticResidual f hK L Q B := h
      rw [he] at hV
      exact direct_sobolev_unit_smul _ (1 / Complex.I) (by simp) _ _ _ _
        (hpos _ (Or.inr rfl)) V hV u hu
  intro V hV
  refine ⟨hscaled V hV, fun u ↦ ?_⟩
  have hdual := negativeVectorFourierSobolev_tame_bound_of_adjoint (Nat.cast_nonneg n)
    (t := (n : ℝ)+1) (by positivity) (hcost n) (zero_le_one.trans hhigh) V
  have hVa : V.adjoint = T ∨ V.adjoint = T.adjoint := by
    rcases hV with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (ContinuousLinearMap.adjoint_adjoint _)
  simpa only [Nat.cast_add, Nat.cast_one] using hdual (hscaled V.adjoint hVa) u

end JanetCartan.RegularSector.EllipticComplement
