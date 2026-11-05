module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.CutoffFourier
public import JanetCartan.Analysis.Microlocal.RegularSector.Characteristic.RetardedLocalization.Restriction
public import JanetCartan.Analysis.Sobolev.Local.Fourier.Integer

/-!
# Restriction estimates with the original low-data term

Transfer a positive Fourier estimate through a fixed source plateau. The
Fourier premise is the conclusion of `exists_finite_direct_operator_bounds`;
the absorption premise must be proved for the same finite direct operator
from its literal masks. This deduction alone does not instantiate either
premise or assert the sector theorem. The quantitative conclusion keeps
`restrictionNorm u + high * ‖u‖`, including input order zero.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open MeasureTheory Set
open scoped ContDiff
namespace JanetCartan.RegularSector.FiniteAssembly
open LocalSobolev Pseudodifferential FourierIntegral.LowBounds
open Characteristic.RetardedLocalization
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin q)
local notation "H" => Lp F 2 (volume : Measure E)

/-- A fixed source plateau transfers a Fourier tame estimate without putting
the high coefficient on the higher input norm. Consumers: both actual direct
operators in `sector-theorem-solution` and `sector-theorem-residual`. The two
operator premises are respectively produced by the finite constructor and
the literal source-mask absorption proof; neither is a restriction bound. -/
theorem exists_local_sourceCut_restriction_tame_constant
    (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hb : ∀ y, ‖χ y‖ ≤ 1) (a b : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (T : H →L[ℂ] H) (A high : ℝ),
      0 ≤ A → 0 ≤ high →
      T.comp (sourceCutMultiplier χ hχ.continuous hb) = T →
      (∀ u : H, MemVectorFourierSobolev (a : ℝ) u →
        MemVectorFourierSobolev (b : ℝ) (T u) ∧
          vectorFourierSobolevNorm (b : ℝ) (T u) ≤
            A * (vectorFourierSobolevNorm (a : ℝ) u + high*‖u‖)) →
      ∀ (U V : Set E) (hU : MeasurableSet U), tsupport χ ⊆ U →
      ∀ u : LocalL2 U F, MemRestrictionSobolev U a u →
        MemRestrictionSobolev V b (localRetardedOperator hU V T u) ∧
          restrictionSobolevNorm V b (localRetardedOperator hU V T u) ≤
            (D*A) * (restrictionSobolevNorm U a u + high*‖u‖) := by
  obtain ⟨Cin, hCin, hin⟩ := exists_sourceCut_zeroExtension_fourier_bound
    (q := q) χ hχ hc hb a
  obtain ⟨Cout, hCout, hout⟩ := vector_restrictionSobolev_nat_bounds (d+1) q b
  refine ⟨(1+Cout)*Cin, one_le_mul_of_one_le_of_one_le (by linarith) hCin, ?_⟩
  intro T A high hA hhigh hsource hT U V hU hs u hu
  let z := sourceCutMultiplier χ hχ.continuous hb (SmallSupport.zeroExtend hU u)
  obtain ⟨hz, hnz⟩ := hin U hU hs u hu
  have hlz : ‖z‖ ≤ ‖u‖ := norm_sourceCutMultiplier_zeroExtend_le hU χ hχ.continuous hb u
  have he : T z = T (SmallSupport.zeroExtend hU u) :=
    DFunLike.congr_fun hsource (SmallSupport.zeroExtend hU u)
  obtain ⟨hm, hn⟩ := hT z hz
  obtain ⟨hv, hnv⟩ := hout (T z) hm V (localRetardedOperator hU V T u)
    (by rw [he]; exact (restrictL2_coeFn V _).symm)
  refine ⟨hv, hnv.trans ((mul_le_mul_of_nonneg_left hn hCout.le).trans ?_)⟩
  have hlow : high*‖z‖ ≤ Cin*(high*‖u‖) :=
    (mul_le_mul_of_nonneg_left hlz hhigh).trans
      (le_mul_of_one_le_left (mul_nonneg hhigh (norm_nonneg u)) hCin)
  have hnU : 0 ≤ restrictionSobolevNorm U a u + high*‖u‖ :=
    add_nonneg restrictionSobolevNorm_nonneg (mul_nonneg hhigh (norm_nonneg u))
  calc
    Cout*(A*(vectorFourierSobolevNorm (a : ℝ) z+high*‖z‖))
        ≤ Cout*(A*(Cin*restrictionSobolevNorm U a u+Cin*(high*‖u‖))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hnz hlow) hA) hCout.le
    _ = (Cout*Cin*A)*(restrictionSobolevNorm U a u+high*‖u‖) := by ring
    _ ≤ (((1+Cout)*Cin)*A)*(restrictionSobolevNorm U a u+high*‖u‖) := by
      apply mul_le_mul_of_nonneg_right _ hnU
      nlinarith [mul_nonneg (zero_le_one.trans hCin) hA]

/-- Both orientations use fixed source plateaux in their respective original
domains. The input order is exactly `max(s-o,0)`, with the same `high o s`
as the constructor. The literal local adjoint exchanges the domains. This is
the positive-scale deduction for `sector-theorem-residual` and
`measured-adjoint`; actual absorption remains an explicit assembly obligation. -/
theorem exists_local_sourceCut_paired_restriction_constants
    (χin χout : E → ℝ) (hi : ContDiff ℝ ∞ χin) (ho : ContDiff ℝ ∞ χout)
    (hic : HasCompactSupport χin) (hoc : HasCompactSupport χout)
    (hib : ∀ y, ‖χin y‖ ≤ 1) (hob : ∀ y, ‖χout y‖ ≤ 1) :
    ∃ D : Fin 2 → ℕ → ℝ, (∀ o s, 1 ≤ D o s) ∧
      ∀ (T : Fin 2 → H →L[ℂ] H) (cost high : Fin 2 → ℕ → ℝ),
      (∀ o s, 0 ≤ cost o s) → (∀ o s, 0 ≤ high o s) →
      (∀ o, (T o).comp (sourceCutMultiplier χin hi.continuous hib) = T o) →
      (∀ o, (T o).adjoint.comp (sourceCutMultiplier χout ho.continuous hob) = (T o).adjoint) →
      (∀ o s, ∀ V : H →L[ℂ] H, (V = T o ∨ V = (T o).adjoint) → ∀ u,
        MemVectorFourierSobolev ((s-o.val : ℕ) : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (V u) ∧
          vectorFourierSobolevNorm (s : ℝ) (V u) ≤ cost o s *
            (vectorFourierSobolevNorm ((s-o.val : ℕ) : ℝ) u + high o s*‖u‖)) →
      ∀ (U V : Set E) (hU : MeasurableSet U) (_hV : MeasurableSet V),
      tsupport χin ⊆ U → tsupport χout ⊆ V → ∀ o s,
      (∀ u : LocalL2 U F, MemRestrictionSobolev U (s-o.val) u →
        MemRestrictionSobolev V s (localRetardedOperator hU V (T o) u) ∧
          restrictionSobolevNorm V s (localRetardedOperator hU V (T o) u) ≤
            (D o s*cost o s)*(restrictionSobolevNorm U (s-o.val) u+high o s*‖u‖)) ∧
      (∀ v : LocalL2 V F, MemRestrictionSobolev V (s-o.val) v →
        MemRestrictionSobolev U s ((localRetardedOperator hU V (T o)).adjoint v) ∧
          restrictionSobolevNorm U s ((localRetardedOperator hU V (T o)).adjoint v) ≤
            (D o s*cost o s)*(restrictionSobolevNorm V (s-o.val) v+high o s*‖v‖)) := by
  choose Di hDi hfi using fun (o : Fin 2) s ↦
    exists_local_sourceCut_restriction_tame_constant (q := q) χin hi hic hib (s-o.val) s
  choose Do hDo hfo using fun (o : Fin 2) s ↦
    exists_local_sourceCut_restriction_tame_constant (q := q) χout ho hoc hob (s-o.val) s
  refine ⟨fun o s ↦ max (Di o s) (Do o s), fun o s ↦ (hDi o s).trans (le_max_left _ _), ?_⟩
  intro T cost high hcost hhigh hsource htarget hT U V hU hV hsi hso o s
  have henlarge {c D r l : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r)
      (hD : D ≤ max (Di o s) (Do o s)) (hl : l ≤ (D*c)*r) :
      l ≤ (max (Di o s) (Do o s)*c)*r :=
    hl.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD hc) hr)
  constructor
  · intro u hu
    obtain ⟨hm, hn⟩ := hfi o s (T o) (cost o s) (high o s) (hcost o s) (hhigh o s)
      (hsource o) (hT o s _ (Or.inl rfl)) U V hU hsi u hu
    exact ⟨hm, henlarge (hcost o s) (add_nonneg restrictionSobolevNorm_nonneg
      (mul_nonneg (hhigh o s) (norm_nonneg u))) (le_max_left _ _) hn⟩
  · intro v hv
    rw [localRetardedOperator_adjoint hU hV]
    obtain ⟨hm, hn⟩ := hfo o s (T o).adjoint (cost o s) (high o s) (hcost o s) (hhigh o s)
      (htarget o) (hT o s _ (Or.inr rfl)) V U hV hso v hv
    exact ⟨hm, henlarge (hcost o s) (add_nonneg restrictionSobolevNorm_nonneg
      (mul_nonneg (hhigh o s) (norm_nonneg v))) (le_max_right _ _) hn⟩

end JanetCartan.RegularSector.FiniteAssembly
