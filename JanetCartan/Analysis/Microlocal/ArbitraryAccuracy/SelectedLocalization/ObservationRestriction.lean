module

public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.SelectedLocalization.WholeSpaceRestriction
public import JanetCartan.Analysis.Microlocal.ArbitraryAccuracy.ResidualLocalization.PolynomialCosts.FiberMaps

/-!
# Restricting the whole-space word observation

The analytic chain lives on the whole-space restriction measure. Its actual
Sobolev extensions also extend the same field restricted to the original
observation domain. This transfers the bound without a positive-order assertion
about zero extension across a boundary (`app:ch_regular:lem:finite-chain`).
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
namespace JanetCartan.ArbitraryAccuracy.SelectedLocalization
open LocalSobolev RegularSector.Characteristic.RetardedLocalization
open RegularSector.Characteristic.EvolutionIntegral ResidualLocalization RegularSector.Realization
variable {d q : ℕ}
local notation "E" => Euclidean (d+1)
local notation "V" => EuclideanSpace ℂ (Fin q)
local notation "H" => SpacetimeL2 d q

/-- The genuine extension of a whole-space observation supplies its SAME
restriction to every measured domain, with norm at most the original norm.
Consumer: the local normalized mixed-word observation
(`app:not:fourier`, `app:ch_regular:eq:resolved-angular-tail`). -/
theorem restrictL2_sobolev_bound_of_univ (W : Set E) {s : ℕ} (v : H)
    (hv : MemRestrictionSobolev univ s (restrictL2 univ v)) :
    MemRestrictionSobolev W s (restrictL2 W v) ∧
      restrictionSobolevNorm W s (restrictL2 W v) ≤
        restrictionSobolevNorm univ s (restrictL2 univ v) := by
  have hext (e : SobolevExtension univ s (restrictL2 univ v)) :
      e.toFun =ᵐ[volume.restrict W] restrictL2 W v := by
    have he : e.toFun =ᵐ[volume] v := by
      simpa only [Measure.restrict_univ] using e.restrict_eq.trans (restrictL2_coeFn univ v)
    have heW : e.toFun =ᵐ[volume.restrict W] v := ae_restrict_of_ae he
    exact heW.trans (restrictL2_coeFn W v).symm
  let cut (e : SobolevExtension univ s (restrictL2 univ v)) : SobolevExtension W s (restrictL2 W v) :=
    { e with restrict_eq := hext e }
  refine ⟨⟨cut hv.some⟩, ?_⟩
  unfold restrictionSobolevNorm
  refine le_csInf ⟨hv.some.jetNorm, hv.some, rfl⟩ ?_
  rintro _ ⟨e, rfl⟩
  exact restrictionSobolevNorm_le (cut e)

/-- Restrict the complex whole-word observation with no change to its rate
or budget. All constants still precede the family index
(`app:ch_regular:eq:chain-tail`). -/
theorem restrictL2_rapidDecayAt_of_univ {ι : Type*} (ρ A : ι → ℝ) (v : ι → H)
    (s : ℕ) (W : Set E) (hW : MeasurableSet W)
    (hv : RapidDecayAt (restrictionSobolevScale univ V MeasurableSet.univ) s ρ A
      (fun i ↦ restrictL2 univ (v i))) :
    RapidDecayAt (restrictionSobolevScale W V hW) s ρ A (fun i ↦ restrictL2 W (v i)) := by
  intro accuracy
  obtain ⟨C, hC, hbound⟩ := hv accuracy
  refine ⟨C, hC, ?_⟩
  intro i
  obtain ⟨hm, hn⟩ := restrictL2_sobolev_bound_of_univ W (v i) (hbound i).1
  refine ⟨hm, ?_⟩
  dsimp only
  rw [restrictionSobolevScale_gradeNorm hW hm]
  have hb := (hbound i).2
  dsimp only at hb
  rw [restrictionSobolevScale_gradeNorm MeasurableSet.univ (hbound i).1] at hb
  exact hn.trans hb

/-- Project to real part only after restricting the complete complex
observation. The fixed fiber map has no frequency loss
(`app:ch_regular:eq:resolved-angular-tail`, `real-sector-normalization`). -/
theorem realPart_restrictL2_rapidDecayAt_of_univ {ι : Type*}
    (ρ A : ι → ℝ) (v : ι → H) (s : ℕ) (W : Set E) (hW : MeasurableSet W)
    (hv : RapidDecayAt (restrictionSobolevScale univ V MeasurableSet.univ) s ρ A
      (fun i ↦ restrictL2 univ (v i))) :
    RapidDecayAt (restrictionSobolevScale W (EuclideanSpace ℝ (Fin q)) hW) s ρ A
      (fun i ↦ l2RealPart (volume.restrict W) (restrictL2 W (v i))) := by
  have hr := restrictL2_rapidDecayAt_of_univ ρ A v s W hW hv
  intro accuracy
  obtain ⟨C, hC, hbound⟩ := hr accuracy
  refine ⟨(‖euclideanRealPart (ι := Fin q)‖+1)*C, by positivity, ?_⟩
  intro i
  obtain ⟨hm, hn⟩ := compLp_restrictionSobolev_bound (euclideanRealPart (ι := Fin q)) (hbound i).1
  refine ⟨hm, ?_⟩
  change (restrictionSobolevScale W (EuclideanSpace ℝ (Fin q)) hW).gradeNorm s
    ((euclideanRealPart (ι := Fin q)).compLp _) ≤ _
  rw [restrictionSobolevScale_gradeNorm hW hm]
  apply hn.trans
  rw [← restrictionSobolevScale_gradeNorm hW (hbound i).1]
  exact (mul_le_mul_of_nonneg_left (hbound i).2 (by positivity)).trans_eq (by ring)

end JanetCartan.ArbitraryAccuracy.SelectedLocalization
