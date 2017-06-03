import unity.scheduling.basic
import unity.scheduling.finite2
import unity.scheduling.infinite

import unity.temporal

import util.data.stream

namespace scheduling


open stream temporal has_mem

variables  {lbl : Type}
variables [sched lbl] [nonempty lbl]

lemma sched.sched_str
  (r : list lbl → set lbl)
: ∃ τ : stream lbl, fair (req_of r τ) τ :=
begin
  cases _inst_1 with _fin _inf,
  { apply finite.sched' ; apply_instance },
  { apply infinite.sched' ; apply_instance },
end

lemma sched.sched_str'
  (r : list lbl → set lbl)
: ∃ τ : stream lbl,
  ∀ (l : lbl),
      ([]<>•mem l) (req_of r τ) →
      ([]<>•(λ x : lbl × set lbl, l = x.fst ∧ (l ∈ x.snd ∨ x.snd = ∅))) (zip' τ $ req_of r τ)  :=
begin
  apply exists_imp_exists _ (sched.sched_str r),
  intros τ h l h',
  assert Heq : (λ (x : lbl × set lbl), l = x.fst ∧ (l ∈ x.snd ∨ x.snd = ∅))
            = (λ (x : lbl × set lbl), (x.fst ∈ x.snd ∨ x.snd = ∅) ∧ l = x.fst),
  { apply funext, intro x, cases x with x₀ x₁,
    unfold prod.fst prod.snd,
    rw [-iff_eq_eq],
    assert Hrw : l = x₀ → (l ∈ x₁ ∨ x₁ = ∅ ↔ x₀ ∈ x₁ ∨ x₁ = ∅),
    { intro h, rw h },
    simp [and_congr_right Hrw], },
  rw Heq,
  apply coincidence,
  { apply eventually_weaken,
    intro i, unfold drop zip', simp,
    apply h.valid i, },
  { change (([]<>•(eq l ∘ prod.fst)) (zip' τ $ req_of r τ)),
    rw [inf_often_trace_init_trading,fst_comp_zip'],
    apply h.fair _ h' },
end


noncomputable def fair_sched_of (req : list lbl → set lbl)
: stream lbl :=
classical.some (sched.sched_str req)

variables lbl

noncomputable def fair_sched : stream lbl :=
fair_sched_of (λ _ _, true)

variables {lbl}

noncomputable def fair_sched_of' (req : stream (set lbl))
: stream lbl := fair_sched_of (req ∘ list.length)

lemma fair_sched_of_spec (r : list lbl → set lbl)
: fair (req_of r (fair_sched_of r)) (fair_sched_of r) :=
by apply classical.some_spec (sched.sched_str r)

lemma fair_sched_of_spec' (r : stream (set lbl))
: fair r (fair_sched_of' r) :=
begin
  note H :=  fair_sched_of_spec (r ∘ list.length),
  rw req_of_comp_length r (fair_sched_of (r ∘ list.length)) at H,
  apply H,
end

lemma fair_sched_of_is_fair
  (r : list lbl → set lbl)
  (l : lbl)
: ([]<>•mem l) (req_of r (fair_sched_of r)) → ([]<>•eq l) (fair_sched_of r) :=
(fair_sched_of_spec r).fair l

lemma fair_sched_of_is_fair'
  (r : stream (set lbl))
  (l : lbl)
: ([]<>•mem l) r → ([]<>•eq l) (fair_sched_of' r) :=
begin
  unfold fair_sched_of',
  intro H,
  rw -req_of_comp_length r (fair_sched_of $ r ∘ list.length) at H,
  apply fair_sched_of_is_fair (r ∘ list.length) l H,
end

lemma fair_sched_is_fair (l : lbl)
: ([]<>•eq l) (fair_sched lbl) :=
begin
  apply (fair_sched_of_spec _).fair l,
  intro i,
  apply eventually_weaken,
  simp [init_drop],
end

lemma sched.sched' (lbl : Type) [nonempty lbl] [sched lbl]
: ∃ τ : stream lbl, ∀ (l : lbl), ([]<>•(eq l)) τ  := ⟨_,fair_sched_is_fair⟩

lemma sched.sched'' (lbl : Type) [nonempty lbl] [sched lbl]
  (req : stream (set lbl))
: ∃ τ : stream lbl,
  ∀ (l : lbl),
    ([]<>•mem l) req →
    ([]<>•(λ x : lbl × set lbl, l = x.fst ∧ (l ∈ x.snd ∨ x.snd = ∅))) (zip' τ req)  :=
begin
  apply exists_imp_exists _ (sched.sched_str' $ req ∘ list.length),
  intro τ,
  apply forall_imp_forall _,
  intros l,
  apply imp_mono _ _
  ; apply eq.substr _,
  { apply req_of_comp_length req τ },
  { apply congr_arg,
    rw req_of_comp_length req τ },
end

instance {lbl} [i : nonempty lbl] : nonempty (stream lbl) :=
begin
  cases i with l,
  apply nonempty.intro,
  intro i, apply l,
end

lemma fair_sched_of_mem  {lbl : Type} [nonempty lbl] [sched lbl] (r : list lbl → set lbl)
  (i : ℕ)
  (Hnemp : req_of r (fair_sched_of r) i ≠ ∅)
: fair_sched_of r i ∈ req_of r (fair_sched_of r) i :=
begin
  revert Hnemp, rw -or_iff_not_imp,
  apply (fair_sched_of_spec r).valid i,
end

lemma fair_sched_of_mem'  {lbl : Type} [nonempty lbl] [sched lbl] (r : stream (set lbl))
  (i : ℕ)
  (Hnemp : r i ≠ ∅)
: fair_sched_of' r i ∈ r i :=
begin
  rw -req_of_comp_length r (fair_sched_of $ r ∘ list.length) at Hnemp,
  note H := fair_sched_of_mem (r ∘ list.length) i Hnemp,
  rw req_of_comp_length r (fair_sched_of $ r ∘ list.length) at H,
  apply H,
end

end scheduling
