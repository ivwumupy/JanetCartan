module

public import JanetCartan.Iteration.RevisedGlobal
public import JanetCartan.Geometry.IsometricEmbedding.Iteration.CoefficientScale.ScaleGap

/-!
# A fixed ambient index for every original history and source frequency

The native letter threshold is selected before the family of admitted histories.
This data-only index does not depend on that threshold. Once a threshold is
known, a retraction onto its admitted subset permits the unchanged native family
theorem to be applied on this SAME ambient type. At every admitted query the
retraction is literally the identity; the default is used only at invalid
indices. An empty admitted subset requires no physical construction.

Consumer: the uniform actual original-data applications of residual53 and
solver50, before `actual_finite_residual_word_reserved_bounds_of_one_step`
(`new:sec:order-of-choices`, `app:ch_response:eq:fixed-factor-transfer`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000
namespace JanetCartan.PhysicalPrimary.OriginalHistoryFamily

/-- Only raw data, with no success or threshold predicate. The payload can carry
an arbitrary prescribed scalar or other source datum without changing the index
when the prehistory threshold is selected. -/
structure RawIndex (d : ℕ) (Payload : Type) where
  R₀ : ℝ
  length : ℕ
  u : Fin length → SchwartzMap (Euclidean (d+1)) (Euclidean (embeddingDimension (d+1)))
  ell : Fin length → ℕ
  lam : ℝ
  K : ℝ
  amplitude : ℝ
  datum : Payload

/-- These are precisely the existing history and scale-window admissions; the
history scale, auxiliary source scale and oscillation frequency stay distinct. -/
def Admitted {d : ℕ} {Payload : Type} (Bband : ℝ) (kMin : ℕ) (ν S : ℝ)
    (i : RawIndex d Payload) : Prop :=
  S ≤ i.R₀ ∧ RevisedGlobal.IsAdmissibleHistory Bband i.R₀ kMin i.u i.ell ∧
    1 ≤ i.lam ∧ currentCoefficientScale i.R₀ i.length ≤ i.K ∧
    i.K ≤ i.lam ^ (1-ν) ∧ 0 ≤ i.amplitude

/-- A valid default fills only INVALID raw indices. `SourceAdmission` is the
primitive source-data admission, such as the original scalar input bounds;
it is not a response estimate. No queried admitted history, frequency, source
scale, amplitude or payload is changed. -/
def admittedRetraction {d : ℕ} {Payload : Type} (Bband : ℝ) (kMin : ℕ) (ν S : ℝ)
    (SourceAdmission : RawIndex d Payload → Prop)
    (hne : Nonempty {i : RawIndex d Payload // Admitted Bband kMin ν S i ∧ SourceAdmission i}) :
    RawIndex d Payload → {i : RawIndex d Payload // Admitted Bband kMin ν S i ∧ SourceAdmission i} := by
  classical
  exact fun i ↦ if hi : Admitted Bband kMin ν S i ∧ SourceAdmission i then ⟨i,hi⟩ else Classical.choice hne

@[simp] theorem admittedRetraction_of_admitted {d : ℕ} {Payload : Type}
    (Bband : ℝ) (kMin : ℕ) (ν S : ℝ) (SourceAdmission : RawIndex d Payload → Prop)
    (hne : Nonempty {i : RawIndex d Payload // Admitted Bband kMin ν S i ∧ SourceAdmission i})
    (i : RawIndex d Payload) (hi : Admitted Bband kMin ν S i ∧ SourceAdmission i) :
    admittedRetraction Bband kMin ν S SourceAdmission hne i = ⟨i,hi⟩ := by
  simp only [admittedRetraction, dite_eq_left hi]

/-- The native family estimates therefore quantify uniformly over ALL admitted
original data, not merely the one history used to fill the invalid indices. -/
theorem admittedRetraction_surjective {d : ℕ} {Payload : Type}
    (Bband : ℝ) (kMin : ℕ) (ν S : ℝ) (SourceAdmission : RawIndex d Payload → Prop)
    (hne : Nonempty {i : RawIndex d Payload // Admitted Bband kMin ν S i ∧ SourceAdmission i}) :
    Function.Surjective (admittedRetraction Bband kMin ν S SourceAdmission hne) := by
  intro i
  exact ⟨i.val, admittedRetraction_of_admitted Bband kMin ν S SourceAdmission hne i.val i.property⟩

/-- The same uniform constant works for every admitted original tuple. This
transport performs no analytic estimate and introduces no reserve change. -/
theorem uniform_constant_of_admittedRetraction {d : ℕ} {Payload : Type}
    (Bband : ℝ) (kMin : ℕ) (ν S : ℝ) (SourceAdmission : RawIndex d Payload → Prop)
    (hne : Nonempty {i : RawIndex d Payload // Admitted Bband kMin ν S i ∧ SourceAdmission i})
    (P : RawIndex d Payload → ℝ → Prop)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      P (admittedRetraction Bband kMin ν S SourceAdmission hne i).val C) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, Admitted Bband kMin ν S i ∧ SourceAdmission i → P i C := by
  obtain ⟨C,hC,hbound⟩ := h
  refine ⟨C,hC,?_⟩
  intro i hi
  simpa only [admittedRetraction_of_admitted Bband kMin ν S SourceAdmission hne i hi] using hbound i

end JanetCartan.PhysicalPrimary.OriginalHistoryFamily
