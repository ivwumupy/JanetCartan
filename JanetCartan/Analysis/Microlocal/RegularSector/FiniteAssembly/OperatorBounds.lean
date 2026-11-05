module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.CommonMasks
public import JanetCartan.Geometry.IsometricEmbedding.Response.Transfer.Complement.VectorEnvelope.Scale
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.PdoRealization.NegativeBounds

/-!
# Combining the actual direct factors

Only the elementary operations occurring in `energy-complete-residual` are
used here: the common output multiplication, addition, and the physical scalar
`1/i`. The concrete construction in `FiniteAssembly.Construction` instantiates
these deductions with the retained retarded and PDO estimates.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory FourierTransform
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteAssembly
open Pseudodifferential FourierIntegral LowBounds ResponseTransfer.Complement
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
variable {n q : ℕ}
local notation "E" => Euclidean n
local notation "H" => Lp (EuclideanSpace ℂ (Fin q)) 2 (volume : Measure E)

private theorem sobolev_add (s : ℝ) (u v : H)
    (hu : MemVectorFourierSobolev s u) (hv : MemVectorFourierSobolev s v) :
    MemVectorFourierSobolev s (u+v) ∧ vectorFourierSobolevNorm s (u+v) ≤
      vectorFourierSobolevNorm s u + vectorFourierSobolevNorm s v := by
  let a : vectorFourierSobolevLevel s := ⟨u, hu⟩
  let b : vectorFourierSobolevLevel s := ⟨v, hv⟩
  refine ⟨(a+b).property, ?_⟩
  change vectorFourierSobolevNorm s (a+b).val ≤
    vectorFourierSobolevNorm s a.val + vectorFourierSobolevNorm s b.val
  rw [← norm_vectorWeightedFourier, ← norm_vectorWeightedFourier,
    ← norm_vectorWeightedFourier, map_add]
  exact norm_add_le _ _

private theorem sobolev_unit_smul (s : ℝ) (z : ℂ) (hz : ‖z‖ = 1)
    (u : H) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev s (z • u) ∧
      vectorFourierSobolevNorm s (z • u) = vectorFourierSobolevNorm s u := by
  have hscalar (v : Lp ℂ 2 (volume : Measure E)) :
      weightedL2Fourier s (z • v) =ᵐ[volume] z • weightedL2Fourier s v := by
    have he : 𝓕 (z • v) = z • 𝓕 v := map_smul (fourierCLM ℂ _) z v
    filter_upwards [Lp.coeFn_smul z (𝓕 v)] with ξ hξ
    simp only [weightedL2Fourier, he, hξ, Pi.smul_apply]
    exact smul_comm _ _ _
  have hnorm (v : Lp ℂ 2 (volume : Measure E)) :
      fourierSobolevNorm s (z • v) = fourierSobolevNorm s v := by
    simp only [fourierSobolevNorm, eLpNorm_congr_ae (hscalar v), eLpNorm_const_smul,
      ENNReal.toReal_mul, enorm, ENNReal.coe_toReal, coe_nnnorm, hz, one_mul]
  constructor
  · intro j
    change MemLp (weightedL2Fourier s (finiteL2CoordinateIsometry volume (z • u) j)) 2 volume
    simpa only [map_smul, PiLp.smul_apply] using
      ((hu j).const_smul z).ae_eq (hscalar _).symm
  · unfold vectorFourierSobolevNorm matrixFourierSobolevNorm
    simp only [map_smul, PiLp.smul_apply, hnorm]

/-- Addition retains the same high quantity and literal adjoints. Consumed
by the two-term solver and all three residual terms (`energy-complete-residual`). -/
theorem direct_sobolev_add
    (S T : H →L[ℂ] H) (s t A B high : ℝ)
    (hS : ∀ V : H →L[ℂ] H, (V = S ∨ V = S.adjoint) → ∀ u,
      MemVectorFourierSobolev s u → MemVectorFourierSobolev t (V u) ∧
      vectorFourierSobolevNorm t (V u) ≤ A*(vectorFourierSobolevNorm s u+high*‖u‖))
    (hT : ∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
      MemVectorFourierSobolev s u → MemVectorFourierSobolev t (V u) ∧
      vectorFourierSobolevNorm t (V u) ≤ B*(vectorFourierSobolevNorm s u+high*‖u‖))
    (V : H →L[ℂ] H) (hV : V = S+T ∨ V = (S+T).adjoint)
    (u : H) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev t (V u) ∧ vectorFourierSobolevNorm t (V u) ≤
      (A+B)*(vectorFourierSobolevNorm s u+high*‖u‖) := by
  have h (S' T' : H →L[ℂ] H) (hs : S' = S ∨ S' = S.adjoint)
      (ht : T' = T ∨ T' = T.adjoint) :=
    sobolev_add t (S' u) (T' u) (hS S' hs u hu).1 (hT T' ht u hu).1
  rcases hV with rfl | rfl
  · exact ⟨(h S T (Or.inl rfl) (Or.inl rfl)).1,
      (h S T (Or.inl rfl) (Or.inl rfl)).2.trans
        ((add_le_add (hS S (Or.inl rfl) u hu).2 (hT T (Or.inl rfl) u hu).2).trans_eq
          (add_mul _ _ _).symm)⟩
  · simp only [map_add, add_apply]
    exact ⟨(h S.adjoint T.adjoint (Or.inr rfl) (Or.inr rfl)).1,
      (h S.adjoint T.adjoint (Or.inr rfl) (Or.inr rfl)).2.trans
        ((add_le_add (hS S.adjoint (Or.inr rfl) u hu).2
          (hT T.adjoint (Or.inr rfl) u hu).2).trans_eq (add_mul _ _ _).symm)⟩

/-- The physical factor `1/i` has unit norm; its literal adjoint uses the
conjugate scalar (`energy-complete-residual`, `measured-adjoint`). -/
theorem direct_sobolev_unit_smul
    (T : H →L[ℂ] H) (z : ℂ) (hz : ‖z‖ = 1) (s t A high : ℝ)
    (hT : ∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
      MemVectorFourierSobolev s u → MemVectorFourierSobolev t (V u) ∧
      vectorFourierSobolevNorm t (V u) ≤ A*(vectorFourierSobolevNorm s u+high*‖u‖))
    (V : H →L[ℂ] H) (hV : V = z • T ∨ V = (z • T).adjoint)
    (u : H) (hu : MemVectorFourierSobolev s u) :
    MemVectorFourierSobolev t (V u) ∧ vectorFourierSobolevNorm t (V u) ≤
      A*(vectorFourierSobolevNorm s u+high*‖u‖) := by
  rcases hV with rfl | rfl
  · obtain ⟨hm, hn⟩ := hT T (Or.inl rfl) u hu
    obtain ⟨hm', hn'⟩ := sobolev_unit_smul t z hz (T u) hm
    exact ⟨hm', hn'.le.trans hn⟩
  · simp only [map_smulₛₗ, smul_apply]
    obtain ⟨hm, hn⟩ := hT T.adjoint (Or.inr rfl) u hu
    obtain ⟨hm', hn'⟩ := sobolev_unit_smul t (star z) (by simpa using hz) (T.adjoint u) hm
    exact ⟨hm', hn'.le.trans hn⟩

/-- The fixed common OUTPUT alone preserves both orientations of an actual
PDO estimate. No extra input multiplier is inserted. Its adjoint puts the
same mask on the input (`measured-adjoint`). -/
theorem exists_outputMask_sobolev_constants
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) :
    ∃ D : ℕ → ℝ, (∀ m, 1 ≤ D m) ∧
    ∀ (T : H →L[ℂ] H) (s t : ℕ) (A high : ℝ), 0 ≤ A → 0 ≤ high →
      (∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
        MemVectorFourierSobolev (s : ℝ) u → MemVectorFourierSobolev (t : ℝ) (V u) ∧
        vectorFourierSobolevNorm (t : ℝ) (V u) ≤
          A*(vectorFourierSobolevNorm (s : ℝ) u+high*‖u‖)) →
      let S := (sourceCutMultiplier output ho.continuous hob).comp T
      ∀ V : H →L[ℂ] H, (V = S ∨ V = S.adjoint) → ∀ u,
        MemVectorFourierSobolev (s : ℝ) u → MemVectorFourierSobolev (t : ℝ) (V u) ∧
        vectorFourierSobolevNorm (t : ℝ) (V u) ≤
          (D t*A*D s)*(vectorFourierSobolevNorm (s : ℝ) u+high*‖u‖) := by
  choose C hC hc using fun m ↦
    exists_sourceCutMultiplier_fourierSobolev_bound (r := q) output ho hoc hob m
  let D m := 1+C m
  have hD m : 1 ≤ D m := by dsimp [D]; linarith [hC m]
  let Mo : H →L[ℂ] H := sourceCutMultiplier output ho.continuous hob
  have hm (m : ℕ) u (hu : MemVectorFourierSobolev (m : ℝ) u) :
      MemVectorFourierSobolev (m : ℝ) (Mo u) ∧
      vectorFourierSobolevNorm (m : ℝ) (Mo u) ≤ D m*vectorFourierSobolevNorm (m : ℝ) u :=
    ⟨(hc m u hu).1, (hc m u hu).2.trans (mul_le_mul_of_nonneg_right
      (by dsimp [D]; linarith) (norm_nonneg _))⟩
  have hnorm u : ‖Mo u‖ ≤ ‖u‖ :=
    (Mo.le_opNorm u).trans ((mul_le_mul_of_nonneg_right
      (norm_sourceCutMultiplier_le _ _ _) (norm_nonneg u)).trans_eq (one_mul _))
  refine ⟨D, hD, ?_⟩
  intro T s t A high hA hhigh hT S V hV u hu
  have he : 0 ≤ vectorFourierSobolevNorm (s : ℝ) u+high*‖u‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg hhigh (norm_nonneg u))
  rcases hV with rfl | rfl
  · obtain ⟨ht, hnt⟩ := hT T (Or.inl rfl) u hu
    obtain ⟨ho', hno⟩ := hm t (T u) ht
    refine ⟨ho', hno.trans ((mul_le_mul_of_nonneg_left hnt (zero_le_one.trans (hD t))).trans ?_)⟩
    have hh := le_mul_of_one_le_right
      (mul_nonneg (mul_nonneg (zero_le_one.trans (hD t)) hA) he) (hD s)
    nlinarith
  · have hadj : S.adjoint = T.adjoint.comp Mo := by
      simp only [S, ContinuousLinearMap.adjoint_comp, sourceCutMultiplier_adjoint]; rfl
    rw [hadj]
    obtain ⟨hi, hni⟩ := hm s u hu
    obtain ⟨ht, hnt⟩ := hT T.adjoint (Or.inr rfl) (Mo u) hi
    refine ⟨ht, hnt.trans ?_⟩
    have hh : high*‖Mo u‖ ≤ D s*(high*‖u‖) :=
      (mul_le_mul_of_nonneg_left (hnorm u) hhigh).trans
        (le_mul_of_one_le_left (mul_nonneg hhigh (norm_nonneg u)) (hD s))
    calc
      _ ≤ A*(D s*vectorFourierSobolevNorm (s : ℝ) u+D s*(high*‖u‖)) :=
        mul_le_mul_of_nonneg_left (add_le_add hni hh) hA
      _ ≤ D t*(A*(D s*(vectorFourierSobolevNorm (s : ℝ) u+high*‖u‖))) := by
        rw [← mul_add]
        exact le_mul_of_one_le_left
          (mul_nonneg hA (mul_nonneg (zero_le_one.trans (hD s)) he)) (hD t)
      _ = _ := by ring

/-- Express the proved PDO gain with the direct solver/residual output index.
This only lowers the output order, including the actual zero-order endpoint;
it adds no coefficient derivative (`sector-theorem-residual`). -/
theorem direct_gain_output_order
    (T : H →L[ℂ] H) (s : ℕ) (o : Fin 2) (A high : ℝ)
    (hT : ∀ V : H →L[ℂ] H, (V = T ∨ V = T.adjoint) → ∀ u,
      MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u →
      MemVectorFourierSobolev (((s-o.val : ℕ) : ℝ)+1) (V u) ∧
      vectorFourierSobolevNorm (((s-o.val : ℕ) : ℝ)+1) (V u) ≤
        A*(vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u+high*‖u‖))
    (V : H →L[ℂ] H) (hV : V = T ∨ V = T.adjoint) (u : H)
    (hu : MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u) :
    MemVectorFourierSobolev (s : ℝ) (V u) ∧ vectorFourierSobolevNorm (s : ℝ) (V u) ≤
      A*(vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u+high*‖u‖) := by
  have horder : (s : ℝ) ≤ ((s-o.val : ℕ) : ℝ)+1 := by
    exact_mod_cast (show s ≤ (s-o.val)+1 by have := o.isLt; omega)
  obtain ⟨hm, hn⟩ := hT V hV u hu
  exact ⟨fun j ↦ (hm j).mono horder, (vectorFourierSobolevNorm_mono hm horder).trans hn⟩

end JanetCartan.RegularSector.FiniteAssembly
