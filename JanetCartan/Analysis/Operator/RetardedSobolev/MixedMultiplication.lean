module

public import JanetCartan.Analysis.Operator.RetardedSobolev.MixedEnergy
public import JanetCartan.Analysis.Operator.RetardedSobolev.TransverseLeibniz

/-!
# Smooth cutoff multiplication for mixed classical energies

The cutoff step of `app:ch_osc:prop:osc-retarded-tube`. The estimates use the
actual ordered transverse derivatives and time derivatives, and include L²
membership of every output derivative. Constants are chosen before the input.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ContDiff BigOperators

namespace JanetCartan.RetardedSobolev

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

private theorem transverseJet_append (vs ws : List Y) (f : ℝ × Y → ℂ) :
    transverseJet (vs ++ ws) f = transverseJet vs (transverseJet ws f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp only [List.cons_append, transverseJet, ih]

private theorem transverseJet_add (vs : List Y) {f g : ℝ × Y → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    transverseJet vs (fun x ↦ f x + g x) =
      fun x ↦ transverseJet vs f x + transverseJet vs g x := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [transverseJet, ih]
    funext x
    exact congrArg (fun L ↦ L v) (fderiv_add
      (((contDiff_transverseJet hf vs).comp (contDiff_prodMk_right x.1)).differentiable
        (by simp) x.2)
      (((contDiff_transverseJet hg vs).comp (contDiff_prodMk_right x.1)).differentiable
        (by simp) x.2))

private theorem timeJet_add (j : ℕ) {f g : ℝ × Y → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    timeJet j (fun x ↦ f x + g x) = fun x ↦ timeJet j f x + timeJet j g x := by
  funext x
  exact iteratedDeriv_fun_add
    (((hf.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp) :
      ContDiff ℝ j (fun t ↦ f (t, x.2))).contDiffAt)
    (((hg.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp) :
      ContDiff ℝ j (fun t ↦ g (t, x.2))).contDiffAt)

variable [MeasurableSpace Y]

private theorem timeSobolev_add_bound (ν : Measure Y) (a b : ℝ) (n : ℕ)
    {f g : ℝ × Y → ℂ} (hfc : ContDiff ℝ ∞ f) (hgc : ContDiff ℝ ∞ g)
    (hf : TimeJetsMemLp ν a b n f) (hg : TimeJetsMemLp ν a b n g) :
    TimeJetsMemLp ν a b n (fun x ↦ f x + g x) ∧
      timeSobolevEnergy ν a b n (fun x ↦ f x + g x) ≤
        2 * timeSobolevEnergy ν a b n f + 2 * timeSobolevEnergy ν a b n g := by
  constructor
  · intro j hj
    simp only [timeJet_add j hfc hgc]
    exact (hf j hj).add (hg j hj)
  · unfold timeSobolevEnergy
    simp only [timeJet_add _ hfc hgc]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have hjn : j ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj
    exact integral_sq_add_le _ _ (hf j hjn) (hg j hjn)

variable [BorelSpace Y]

private theorem exists_timeSobolev_cutoff_bound (ν : Measure Y) (a b : ℝ) (n : ℕ)
    {χ : ℝ × Y → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ × Y → ℂ, ContDiff ℝ ∞ f →
      TimeJetsMemLp ν a b n f →
      TimeJetsMemLp ν a b n (fun x ↦ (χ x : ℂ) * f x) ∧
        timeSobolevEnergy ν a b n (fun x ↦ (χ x : ℂ) * f x) ≤
          C * timeSobolevEnergy ν a b n f := by
  have hc : ContDiff ℝ ∞ (fun x ↦ (χ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  obtain ⟨C, hC, hb⟩ := exists_timeJet_bound hc (hs.comp_left Complex.ofReal_zero) n
  refine ⟨timeMultiplierConstant n C, timeMultiplierConstant_nonneg _ _, ?_⟩
  intro f hfc hf
  exact timeSobolev_mul_bound ν a b n _ f
    (fun _ ↦ (hc.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp))
    (fun _ ↦ (hfc.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp))
    (fun j _ ↦ ((contDiff_timeJet hc j).continuous.comp continuous_swap).aestronglyMeasurable)
    hC (fun j hj ↦ Filter.Eventually.of_forall (fun p ↦ hb j hj (p.2, p.1))) hf

variable {ι : Type*}

/-- A wordwise Leibniz bound for `app:ch_osc:prop:osc-retarded-tube`.
The auxiliary input bound ranges over words of no greater length, so differentiating
an input consumes one of the available transverse orders. -/
theorem exists_transverseJet_cutoff_bound (directions : ι → Y) (ν : Measure Y)
    (a b : ℝ) (n : ℕ) (word : List ι)
    {χ : ℝ × Y → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ × Y → ℂ), ContDiff ℝ ∞ f → ∀ E : ℝ,
      (∀ l : List ι, l.length ≤ word.length →
        TimeJetsMemLp ν a b n (transverseJet (l.map directions) f) ∧
        timeSobolevEnergy ν a b n (transverseJet (l.map directions) f) ≤ E) →
      TimeJetsMemLp ν a b n
        (transverseJet (word.map directions) (fun x ↦ (χ x : ℂ) * f x)) ∧
      timeSobolevEnergy ν a b n
        (transverseJet (word.map directions) (fun x ↦ (χ x : ℂ) * f x)) ≤ C * E := by
  induction word using List.reverseRecOn generalizing χ with
  | nil =>
    obtain ⟨C, hC, hb⟩ := exists_timeSobolev_cutoff_bound ν a b n hχ hs
    refine ⟨C, hC, ?_⟩
    intro f hfc E hf
    have h := hf [] (by simp)
    have hb' := hb f hfc h.1
    exact ⟨hb'.1, hb'.2.trans (mul_le_mul_of_nonneg_left h.2 hC)⟩
  | append_singleton word i ih =>
    have hdχ : ContDiff ℝ ∞ (transverseDeriv (directions i) χ) :=
      contDiff_transverseJet hχ [directions i]
    have hds : HasCompactSupport (transverseDeriv (directions i) χ) :=
      hasCompactSupport_transverseJet hχ hs [directions i]
    obtain ⟨C, hC, hb⟩ := ih hχ hs
    obtain ⟨D, hD, hd⟩ := ih hdχ hds
    refine ⟨2 * C + 2 * D, by positivity, ?_⟩
    intro f hfc E hf
    have hdf : ContDiff ℝ ∞ (transverseDeriv (directions i) f) :=
      contDiff_transverseJet hfc [directions i]
    have hshift : ∀ l : List ι, l.length ≤ word.length →
        TimeJetsMemLp ν a b n
          (transverseJet (l.map directions) (transverseDeriv (directions i) f)) ∧
        timeSobolevEnergy ν a b n
          (transverseJet (l.map directions) (transverseDeriv (directions i) f)) ≤ E := by
      intro l hl
      have h := hf (l ++ [i]) (by simpa using hl)
      simpa only [List.map_append, List.map_cons, List.map_nil, transverseJet_append,
        transverseJet] using h
    have hshort : ∀ l : List ι, l.length ≤ word.length →
        TimeJetsMemLp ν a b n (transverseJet (l.map directions) f) ∧
        timeSobolevEnergy ν a b n (transverseJet (l.map directions) f) ≤ E := by
      intro l hl
      exact hf l (by simp only [List.length_append, List.length_singleton]; omega)
    have hb' := hb _ hdf E hshift
    have hd' := hd f hfc E hshort
    have hc₁ : ContDiff ℝ ∞ (fun x ↦ (χ x : ℂ) * transverseDeriv (directions i) f x) :=
      (Complex.ofRealCLM.contDiff.comp hχ).mul hdf
    have hc₂ : ContDiff ℝ ∞ (fun x ↦ ((transverseDeriv (directions i) χ x : ℝ) : ℂ) * f x) :=
      (Complex.ofRealCLM.contDiff.comp hdχ).mul hfc
    simp only [List.map_append, List.map_cons, List.map_nil, transverseJet_append,
      transverseJet, transverseDeriv_real_mul (directions i) hχ hfc,
      transverseJet_add _ hc₁ hc₂]
    have hadd := timeSobolev_add_bound ν a b n
      (contDiff_transverseJet hc₁ (word.map directions))
      (contDiff_transverseJet hc₂ (word.map directions)) hb'.1 hd'.1
    refine ⟨hadd.1, hadd.2.trans ?_⟩
    nlinarith [hb'.2, hd'.2]

variable [Fintype ι]

omit [BorelSpace Y] in
/-- Each transverse-word time energy is a summand of the mixed energy in
`app:ch_osc:prop:osc-retarded-tube`. -/
theorem timeSobolevEnergy_transverseJet_le_mixed (directions : ι → Y) (ν : Measure Y)
    (a b : ℝ) (m k : ℕ) (hk : k ≤ m) (word : Fin k → ι) (f : ℝ × Y → ℂ) :
    timeSobolevEnergy ν a b (m - k) (transverseJet (List.ofFn (directions ∘ word)) f) ≤
      mixedSobolevEnergy directions ν a b m f := by
  have hn (j : ℕ) (w : Fin j → ι) : 0 ≤
      timeSobolevEnergy ν a b (m - j) (transverseJet (List.ofFn (directions ∘ w)) f) :=
    Finset.sum_nonneg fun _ _ ↦ integral_nonneg fun _ ↦ sq_nonneg _
  calc
    _ ≤ ∑ w : Fin k → ι,
        timeSobolevEnergy ν a b (m - k) (transverseJet (List.ofFn (directions ∘ w)) f) :=
      Finset.single_le_sum (fun w _ ↦ hn k w) (Finset.mem_univ word)
    _ ≤ mixedSobolevEnergy directions ν a b m f :=
      Finset.single_le_sum (f := fun j ↦ ∑ w : Fin j → ι,
        timeSobolevEnergy ν a b (m - j) (transverseJet (List.ofFn (directions ∘ w)) f))
        (fun j _ ↦ Finset.sum_nonneg fun w _ ↦ hn j w)
        (show k ∈ Finset.range (m + 1) from Finset.mem_range.mpr (by omega))

/-- Multiplication by a smooth compactly supported real cutoff is bounded for
all the mixed classical energies of `app:ch_osc:prop:osc-retarded-tube`.
The constant is chosen before the input, and the conclusion proves L² membership
of every mixed derivative through total order `m`. -/
theorem mixedSobolev_mul_bound (directions : ι → Y) (ν : Measure Y)
    (a b : ℝ) (m : ℕ) (χ : ℝ × Y → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hs : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ × Y → ℂ, ContDiff ℝ ∞ f →
      MixedJetsMemLp directions ν a b m f →
      MixedJetsMemLp directions ν a b m (fun x ↦ (χ x : ℂ) * f x) ∧
      mixedSobolevEnergy directions ν a b m (fun x ↦ (χ x : ℂ) * f x) ≤
        C * mixedSobolevEnergy directions ν a b m f := by
  classical
  have hw (k : ℕ) (word : Fin k → ι) :=
    exists_transverseJet_cutoff_bound directions ν a b (m - k) (List.ofFn word) hχ hs
  choose C hC hb using hw
  refine ⟨∑ k ∈ Finset.range (m + 1), ∑ word : Fin k → ι, C k word,
    Finset.sum_nonneg (fun k _ ↦ Finset.sum_nonneg (fun word _ ↦ hC k word)), ?_⟩
  intro f hfc hf
  have hword (k : ℕ) (hk : k ≤ m) (word : Fin k → ι) :
      TimeJetsMemLp ν a b (m - k)
        (transverseJet (List.ofFn (directions ∘ word)) (fun x ↦ (χ x : ℂ) * f x)) ∧
      timeSobolevEnergy ν a b (m - k)
        (transverseJet (List.ofFn (directions ∘ word)) (fun x ↦ (χ x : ℂ) * f x)) ≤
        C k word * mixedSobolevEnergy directions ν a b m f := by
    have hinput (l : List ι) (hl : l.length ≤ (List.ofFn word).length) :
        TimeJetsMemLp ν a b (m - k) (transverseJet (l.map directions) f) ∧
        timeSobolevEnergy ν a b (m - k) (transverseJet (l.map directions) f) ≤
          mixedSobolevEnergy directions ν a b m f := by
      have hlk : l.length ≤ k := by simpa only [List.length_ofFn] using hl
      have hlm : l.length ≤ m := hlk.trans hk
      have heq : List.ofFn (directions ∘ l.get) = l.map directions := by
        rw [← List.map_ofFn, List.ofFn_get]
      have hi := hf l.length hlm l.get
      rw [heq] at hi
      refine ⟨fun j hj ↦ hi j (by omega), ?_⟩
      have he := timeSobolevEnergy_transverseJet_le_mixed directions ν a b m l.length hlm l.get f
      rw [heq] at he
      exact (timeSobolevEnergy_mono ν a b (by omega) _).trans he
    simpa only [List.map_ofFn] using hb k word f hfc
      (mixedSobolevEnergy directions ν a b m f) hinput
  refine ⟨fun k hk word ↦ (hword k hk word).1, ?_⟩
  unfold mixedSobolevEnergy
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro k hk
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro word _
  exact (hword k (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk) word).2

end JanetCartan.RetardedSobolev
