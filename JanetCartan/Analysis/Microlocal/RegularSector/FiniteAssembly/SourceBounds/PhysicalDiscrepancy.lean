module

public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.SourceBounds
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.ProtectedConstruction.SourceEquation
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Physical
public import JanetCartan.Analysis.Microlocal.RegularSector.FiniteAssembly.RestrictionBounds.Measured.Pairing

/-!
# Measured bounds for the actual paired angular discrepancy

The physical source in the retained PDE is paired before subtracting one
identity. Apply the existing finite source estimates to that exact operator,
with the original common output and the final threshold. The discrepancy has
order zero; the three analytic residual terms keep their separate gain-one
estimates. Consumers: the complete physical equation in `FixedDomainInverse`
and the terminal source of `app:ch_regular:eq:chain-tail`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Metric MeasureTheory
open scoped ContDiff Matrix.Norms.Frobenius JanetCartan.RegularSector.Realization
namespace JanetCartan.RegularSector.FiniteAssembly
open Characteristic Characteristic.EvolutionIntegral Characteristic.RetardedLocalization
open FiniteMasks FiniteMasks.ActualFamily FourierIntegral LowBounds Pseudodifferential
open LocalSobolev Realization ArbitraryAccuracy ArbitraryAccuracy.ResidualLocalization
open ArbitraryAccuracy.ResidualLocalization.IdentityDefect
open JanetCartan.CharacteristicTransport.CompleteResidual
variable {d : ℕ} {Ω : Set (Euclidean (d+1))} {x : Euclidean (d+1)} {RQ M : ℝ}
variable {A₀ : Fin (d+1) → MetricTensor (d+1)} {K : Set (Euclidean (d+1))}
local notation "E" => Euclidean (d+1)
local notation "F" => EuclideanSpace ℂ (Fin (d+1))
local notation "RF" => EuclideanSpace ℝ (Fin (d+1))
local notation "H" => SpacetimeL2 d (d+1)

/-- The literal finite source with its common output has order zero in both
orientations. Its bound comes from the actual angular PDO producer, before
any coefficients or history vary (`resolved-angular-tail`). -/
theorem exists_selectedFiniteSource_commonOutput_sobolev_bounds
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
    let A := (sourceCutMultiplier output ho.continuous hob).comp (selectedFiniteSourcePDO f L)
    ∀ s : ℕ, ∀ V : H →L[ℂ] H, (V = A ∨ V = A.adjoint) → ∀ u,
      MemVectorFourierSobolev (s : ℝ) u →
      MemVectorFourierSobolev (s : ℝ) (V u) ∧
      vectorFourierSobolevNorm (s : ℝ) (V u) ≤ C s*vectorFourierSobolevNorm (s : ℝ) u := by
  obtain ⟨C, hC, hbound⟩ := exists_selectedFiniteSourcePDO_identity_defect_bounds
    f L hL output ho hoc hob
  refine ⟨fun s ↦ C s+1, fun s ↦ add_nonneg (hC s) zero_le_one, ?_⟩
  intro A s V hV u hu
  have hd : V-1 = A-1 ∨ V-1 = (A-1).adjoint := by
    rcases hV with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by simp)
  obtain ⟨hm, hn⟩ := hbound s (V-1) hd u hu
  obtain ⟨hm', hn'⟩ := TerminalBounds.add_bound hm hu
  have he : (V-1) u+u = V u := by simp
  rw [he] at hm' hn'
  exact ⟨hm', hn'.trans ((add_le_add hn le_rfl).trans_eq (by ring))⟩

/-- Real compression of the original paired source subtracts the identity
exactly once (`sector-theorem-identity`, `prop:complete-residual`). -/
theorem selectedFiniteRealSource_sub_identity_eq
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ)
    (output : E → ℝ) (ho : Continuous output) (hob : ∀ y, ‖output y‖ ≤ 1) :
    selectedFiniteRealSource f L output ho hob - 1 =
      realCompression (physicalPairedSectorSum {()} (fun _ : Unit ↦
        (sourceCutMultiplier output ho hob).comp (selectedFiniteSourcePDO f L)) - 1) := by
  ext1 u
  simp [selectedFiniteRealSource, realCompression, realPart_inclusion]

/-- Weak-extension inclusion and real part give the actual order-zero
compression bound, used below for the paired discrepancy (`measured-adjoint`). -/
private theorem realCompression_order_zero_restriction_bound
    {U V : Set E} (hU : MeasurableSet U) (T : H →L[ℂ] H)
    (s : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ u : LocalL2 U F, MemRestrictionSobolev U s u →
      MemRestrictionSobolev V s (localRetardedOperator hU V T u) ∧
      restrictionSobolevNorm V s (localRetardedOperator hU V T u) ≤
        C*restrictionSobolevNorm U s u)
    (u : LocalL2 U RF) (hu : MemRestrictionSobolev U s u) :
    MemRestrictionSobolev V s (localRealCompression hU V T u) ∧
    restrictionSobolevNorm V s (localRealCompression hU V T u) ≤
      (4*C)*restrictionSobolevNorm U s u := by
  obtain ⟨hi, hni⟩ := compLp_restrictionSobolev_bound
    (euclideanComplexInclusion (ι := Fin (d+1))) hu
  obtain ⟨ht, hnt⟩ := hT _ hi
  obtain ⟨hr, hnr⟩ := compLp_restrictionSobolev_bound
    (euclideanRealPart (ι := Fin (d+1))) ht
  refine ⟨hr, ?_⟩
  have hi' : restrictionSobolevNorm U s
      (l2ComplexInclusion (volume.restrict U) u) ≤ 2*restrictionSobolevNorm U s u :=
    hni.trans (mul_le_mul_of_nonneg_right
      (by linarith [euclideanComplexInclusion_norm_le (ι := Fin (d+1))])
      restrictionSobolevNorm_nonneg)
  have hr' : restrictionSobolevNorm V s (localRealCompression hU V T u) ≤
      2*restrictionSobolevNorm V s
        (localRetardedOperator hU V T (l2ComplexInclusion (volume.restrict U) u)) :=
    hnr.trans (mul_le_mul_of_nonneg_right
      (by linarith [euclideanRealPart_norm_le (ι := Fin (d+1))])
      restrictionSobolevNorm_nonneg)
  exact hr'.trans ((mul_le_mul_of_nonneg_left
    (hnt.trans (mul_le_mul_of_nonneg_left hi' hC)) (by norm_num)).trans_eq (by ring))

/-- Actual measured restriction bounds for the full physical angular source
minus ONE identity. Both literal adjoints and real compression use the same
cutoffs and zero extensions. The constants precede the source/measurement
domains, every varying coefficient and history. No terminal estimate or
symbol budget is assumed (`measured-adjoint`, `resolved-angular-tail`). -/
theorem exists_selectedFinitePhysicalSource_measured_discrepancy_bounds
    (f : ActualMaskFamily Ω x RQ A₀ K M) (L : ℝ) (hL : f.radialThreshold ≤ L)
    (output : E → ℝ) (ho : ContDiff ℝ ∞ output) (hoc : HasCompactSupport output)
    (hob : ∀ y, ‖output y‖ ≤ 1)
    (μ ν : E → ℝ) (hμ : ContDiff ℝ ∞ μ) (hν : ContDiff ℝ ∞ ν)
    (hμc : HasCompactSupport μ) (hνc : HasCompactSupport ν)
    (hμb : ∀ y, ‖μ y‖ ≤ 1) (hνb : ∀ y, ‖ν y‖ ≤ 1) :
    ∃ C : ℕ → ℝ, (∀ s, 0 ≤ C s) ∧
    let A := (sourceCutMultiplier output ho.continuous hob).comp (selectedFiniteSourcePDO f L)
    let D := physicalPairedSectorSum {()} (fun _ : Unit ↦ A) - 1
    let T := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb D
    ∀ (U V : Set E) (hU : MeasurableSet U) (_hV : MeasurableSet V),
      tsupport ν ⊆ U → tsupport μ ⊆ V →
    let J := localRetardedOperator hU V T
    let R := localRealCompression hU V T
    ∀ s,
      (∀ u : LocalL2 U F, MemRestrictionSobolev U s u →
        MemRestrictionSobolev V s (J u) ∧
        restrictionSobolevNorm V s (J u) ≤ C s*restrictionSobolevNorm U s u) ∧
      (∀ v : LocalL2 V F, MemRestrictionSobolev V s v →
        MemRestrictionSobolev U s (J.adjoint v) ∧
        restrictionSobolevNorm U s (J.adjoint v) ≤ C s*restrictionSobolevNorm V s v) ∧
      (∀ u : LocalL2 U RF, MemRestrictionSobolev U s u →
        MemRestrictionSobolev V s (R u) ∧
        restrictionSobolevNorm V s (R u) ≤ (4*C s)*restrictionSobolevNorm U s u) ∧
      (∀ v : LocalL2 V RF, MemRestrictionSobolev V s v →
        MemRestrictionSobolev U s (R.adjoint v) ∧
        restrictionSobolevNorm U s (R.adjoint v) ≤ (4*C s)*restrictionSobolevNorm V s v) := by
  classical
  obtain ⟨Ca, hCa, hA⟩ := exists_selectedFiniteSource_commonOutput_sobolev_bounds
    f L hL output ho hoc hob
  choose Cf hCf hf using fun s ↦ exists_measuredOperator_restriction_tame_constant
    (q := d+1) μ ν hμ hν hμc hνc hμb hνb s s
  choose Cr hCr hr using fun s ↦ exists_measuredOperator_restriction_tame_constant
    (q := d+1) ν μ hν hμ hνc hμc hνb hμb s s
  let C s := max (Cf s) (Cr s)
  have hC s : 0 ≤ C s := zero_le_one.trans ((hCf s).trans (le_max_left _ _))
  refine ⟨fun s ↦ 5*(C s*Ca s)+C s,
    fun s ↦ add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (hC s) (hCa s))) (hC s), ?_⟩
  intro A D T U V hU hV hνU hμV J R s
  have hmeasure (B : H →L[ℂ] H) {cost : ℝ} (hc : 0 ≤ cost)
      (hb : ∀ W : H →L[ℂ] H, (W = B ∨ W = B.adjoint) → ∀ u,
        MemVectorFourierSobolev (s : ℝ) u →
        MemVectorFourierSobolev (s : ℝ) (W u) ∧
        vectorFourierSobolevNorm (s : ℝ) (W u) ≤ cost*vectorFourierSobolevNorm (s : ℝ) u) :
      let S := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb B
      (∀ u : LocalL2 U F, MemRestrictionSobolev U s u →
        MemRestrictionSobolev V s (localRetardedOperator hU V S u) ∧
        restrictionSobolevNorm V s (localRetardedOperator hU V S u) ≤
          (C s*cost)*restrictionSobolevNorm U s u) ∧
      (∀ v : LocalL2 V F, MemRestrictionSobolev V s v →
        MemRestrictionSobolev U s ((localRetardedOperator hU V S).adjoint v) ∧
        restrictionSobolevNorm U s ((localRetardedOperator hU V S).adjoint v) ≤
          (C s*cost)*restrictionSobolevNorm V s v) := by
    intro S
    constructor
    · intro u hu
      obtain ⟨hm, hn⟩ := hf s B cost 0 hc le_rfl
        (by simpa only [zero_mul, add_zero] using hb B (Or.inl rfl)) U V hU hνU u hu
      refine ⟨hm, ?_⟩
      simp only [zero_mul, add_zero] at hn
      exact hn.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hc) restrictionSobolevNorm_nonneg)
    · intro v hv
      rw [local_measuredOperator_adjoint hU hV]
      obtain ⟨hm, hn⟩ := hr s B.adjoint cost 0 hc le_rfl
        (by simpa only [zero_mul, add_zero] using hb B.adjoint (Or.inr rfl)) V U hV hμV v hv
      refine ⟨hm, ?_⟩
      simp only [zero_mul, add_zero] at hn
      exact hn.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hc) restrictionSobolevNorm_nonneg)
  have hsource := hmeasure A (hCa s) (hA s)
  have hid := hmeasure (1 : H →L[ℂ] H) (cost := 1) zero_le_one (by
    intro W hW u hu
    rcases hW with rfl | rfl <;> simpa using And.intro hu (le_refl (vectorFourierSobolevNorm (s : ℝ) u)))
  let S := measuredOperator μ ν hμ.continuous hν.continuous hμb hνb A
  let I := localRetardedOperator hU V
    (measuredOperator μ ν hμ.continuous hν.continuous hμb hνb (1 : H →L[ℂ] H))
  let P := localRetardedOperator hU V (physicalPairedSectorSum {()} (fun _ : Unit ↦ S))
  have hp := local_physicalPair_restriction_tame_bounds hU hV S s s
    (C s*Ca s) 0 (mul_nonneg (hC s) (hCa s)) le_rfl
    (by simpa only [zero_mul, add_zero] using hsource.1)
    (by simpa only [zero_mul, add_zero] using hsource.2)
  have hT : T = physicalPairedSectorSum {()} (fun _ : Unit ↦ S) -
      measuredOperator μ ν hμ.continuous hν.continuous hμb hνb (1 : H →L[ℂ] H) := by
    rw [physicalPair_measuredOperator]
    ext1 u
    simp [T, D, measuredOperator]
  have hJ : J = P-I := by
    rw [show J = localRetardedOperator hU V T from rfl, hT]
    ext1 u
    simp [localRetardedOperator, P, I]
  have hbound (V₁ V₂ : Set E)
      (Q₁ Q₂ : LocalL2 V₁ F →L[ℝ] LocalL2 V₂ F)
      (hq₁ : ∀ u, MemRestrictionSobolev V₁ s u → MemRestrictionSobolev V₂ s (Q₁ u) ∧
        restrictionSobolevNorm V₂ s (Q₁ u) ≤ (5*(C s*Ca s))*restrictionSobolevNorm V₁ s u)
      (hq₂ : ∀ u, MemRestrictionSobolev V₁ s u → MemRestrictionSobolev V₂ s (Q₂ u) ∧
        restrictionSobolevNorm V₂ s (Q₂ u) ≤ C s*restrictionSobolevNorm V₁ s u)
      (u : LocalL2 V₁ F) (hu : MemRestrictionSobolev V₁ s u) :
      MemRestrictionSobolev V₂ s ((Q₁-Q₂) u) ∧
        restrictionSobolevNorm V₂ s ((Q₁-Q₂) u) ≤
          (5*(C s*Ca s)+C s)*restrictionSobolevNorm V₁ s u := by
    obtain ⟨hm₁, hn₁⟩ := hq₁ u hu
    obtain ⟨hm₂, hn₂⟩ := hq₂ u hu
    have hm := hm₁.add (hm₂.smul (-1))
    have hn := restrictionSobolevNorm_add_le hm₁ (hm₂.smul (-1))
    rw [restrictionSobolevNorm_smul hm₂] at hn
    simp only [abs_neg, abs_one, one_mul, neg_smul, one_smul] at hm hn
    change MemRestrictionSobolev V₂ s (Q₁ u-Q₂ u) ∧
      restrictionSobolevNorm V₂ s (Q₁ u-Q₂ u) ≤
        (5*(C s*Ca s)+C s)*restrictionSobolevNorm V₁ s u
    simpa only [sub_eq_add_neg] using
      And.intro hm (hn.trans ((add_le_add hn₁ hn₂).trans_eq (by ring)))
  have hjf : ∀ u : LocalL2 U F, MemRestrictionSobolev U s u →
      MemRestrictionSobolev V s (J u) ∧ restrictionSobolevNorm V s (J u) ≤
        (5*(C s*Ca s)+C s)*restrictionSobolevNorm U s u := by
    rw [hJ]
    exact hbound U V P I (by simpa only [zero_mul, add_zero] using hp.1)
      (by simpa only [mul_one] using hid.1)
  have hja : ∀ v : LocalL2 V F, MemRestrictionSobolev V s v →
      MemRestrictionSobolev U s (J.adjoint v) ∧ restrictionSobolevNorm U s (J.adjoint v) ≤
        (5*(C s*Ca s)+C s)*restrictionSobolevNorm V s v := by
    rw [hJ, map_sub]
    exact hbound V U P.adjoint I.adjoint (by simpa only [zero_mul, add_zero] using hp.2)
      (by simpa only [mul_one] using hid.2)
  have hc : 0 ≤ 5*(C s*Ca s)+C s :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (hC s) (hCa s))) (hC s)
  refine ⟨hjf, hja, realCompression_order_zero_restriction_bound hU T s hc hjf, ?_⟩
  intro v hv
  rw [show R = localRealCompression hU V T from rfl, localRealCompression_adjoint hU hV]
  exact realCompression_order_zero_restriction_bound hV T.adjoint s hc
    (by simpa only [J, localRetardedOperator_adjoint hU hV] using hja) v hv

end JanetCartan.RegularSector.FiniteAssembly
