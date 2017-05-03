
import data.stream
import unity.temporal
import util.data.bijection
import util.data.perm
import util.data.nat
import util.data.stream
import util.data.minimum
import util.data.fin

namespace scheduling

open temporal
open classical nat

variable {lbl : Type}

structure fair {lbl : Type} (req : stream (set lbl)) (τ : stream lbl) : Prop :=
  (valid : ∀ i, req i = ∅ ∨ τ i ∈ req i)
  (fair : ∀ l, ([]<>•mem l) req → ([]<>•eq l) τ)

class inductive sched (lbl : Type)
  | fin : finite lbl → sched
  | inf : infinite lbl → sched

noncomputable def fin.first [pos_finite lbl] (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: fin $ succ $ pos_finite.pred_count lbl :=
minimum { x | l.f x ∈ req }

noncomputable def fin.select [pos_finite lbl] (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
: bijection (fin $ succ $ pos_finite.pred_count lbl) lbl :=
l ∘ rev (perm.rotate_right (fin.first req l))

lemma fin.selected [pos_finite lbl] (req : set lbl)
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
  (h : req ≠ ∅)
: (fin.select req l).f fin.max ∈ req :=
begin
  unfold fin.select,
  rw [comp_f,rev_f],
  unfold function.comp,
  rw perm.rotate_right_g_max,
  unfold fin.first,
  apply minimum_mem {x : fin (succ (pos_finite.pred_count lbl)) | l.f x ∈ req},
  note h' := exists_mem_of_ne_empty _ h,
  cases h' with x h',
  apply (@set.ne_empty_of_mem _ _ $ l.g x),
  rw [mem_set_of,bijection.g_inv],
  apply h',
end

lemma fin.progress [pos_finite lbl]
  {x : lbl}
  {req : set lbl}
  (l : bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
  (h : x ∈ req)
: (fin.select req l).f fin.max = x ∨ ((fin.select req l).g x).succ = l.g x :=
begin
  unfold fin.select,
  rw [comp_f,rev_f,comp_g,rev_g],
  unfold function.comp,
  assert H : fin.first req l < l.g x ∨ fin.first req l = l.g x,
  { apply lt_or_eq_of_le,
    unfold fin.first,
    apply minimum_le,
    rw [mem_set_of,bijection.g_inv],
    apply h },
  cases H with H H,
  { right,
    rw [perm.rotate_right_f_lt_shifted _ _ H,fin.succ_pred],
    rw [fin.lt_def,fin.zero_def],
    rw [fin.lt_def] at H,
    apply lt_of_le_of_lt (zero_le _) H, },
  { left,
    rw [perm.rotate_right_g_max,H],
    apply bijection.g_inv }
end

def state_t [pos_finite lbl] := (set lbl × bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)

noncomputable def fin.state' [pos_finite lbl] (req : stream (set lbl))
: stream (bijection (fin $ succ $ pos_finite.pred_count lbl) lbl)
  | 0 := fin.select (req 0) (rev (finite.to_nat _))
  | (succ n) := fin.select (req $ succ n) (fin.state' n)

noncomputable def fin.state [pos_finite lbl] (req : stream (set lbl))
: stream state_t :=
  λ i, (req i, fin.state' req i)

def fin.last {n α} (l : bijection (fin $ succ n) α) : α :=
l.f fin.max

lemma fin.state_fst {lbl : Type} [s : pos_finite lbl]
  (req : stream (set lbl))
: req = prod.fst ∘ fin.state req :=
by refl

lemma fin.sched {lbl : Type} [s : finite lbl] [nonempty lbl]
  (req : stream (set lbl))
: ∃ τ : stream lbl, fair req τ :=
sorry

lemma inf.sched {lbl : Type} [s : infinite lbl] [nonempty lbl]
  (req : stream (set lbl))
: ∃ τ : stream lbl, fair req τ :=
sorry

lemma sched.sched {lbl : Type} [s : sched lbl] [nonempty lbl]
  (req : stream (set lbl))
: ∃ τ : stream lbl, fair req τ :=
begin
  cases s with _fin _inf,
  { apply fin.sched ; apply_instance },
  { apply inf.sched ; apply_instance },
end

instance {lbl} [i : nonempty lbl] : nonempty (stream lbl) :=
begin
  cases i with l,
  apply nonempty.intro,
  intro i, apply l,
end

noncomputable def fair_sched_of [nonempty lbl] [sched lbl] (req : stream (set lbl)) : stream lbl :=
epsilon (fair req)

lemma fair_sched_of_spec {lbl : Type} [nonempty lbl] [sched lbl] (req : stream (set lbl))
: fair req (fair_sched_of req) :=
begin
  unfold fair_sched_of,
  apply epsilon_spec,
  apply sched.sched req
end

lemma fair_sched_of_mem  {lbl : Type} [nonempty lbl] [sched lbl] (req : stream (set lbl))
  (i : ℕ)
  (Hnemp : req i ≠ ∅)
: fair_sched_of req i ∈ req i :=
begin
  cases (fair_sched_of_spec req).valid i with H' H',
  { cases Hnemp H' },
  { apply H' }
end

open stream

lemma fair_sched_of_is_fair  {lbl : Type} [nonempty lbl] [sched lbl] (req : stream (set lbl)) (l : lbl)
: ([]<>•mem l) req → ([]<>•eq l) (fair_sched_of req) :=
(fair_sched_of_spec req).fair l

noncomputable def fair_sched (lbl : Type) [nonempty lbl] [sched lbl] : stream lbl :=
fair_sched_of (λ _ _, true)

lemma fair_sched_is_fair  {lbl : Type} [nonempty lbl] [sched lbl] (l : lbl)
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
: ∃ τ : stream lbl, ∀ (l : lbl),
  ([]<>•mem l) req →
  ([]<>•(λ x : lbl × set lbl, l = x.fst ∧ (l ∈ x.snd ∨ x.snd = ∅))) (zip' τ req)  :=
begin
  existsi fair_sched_of req,
  intros l h,
  note sched := fair_sched_of_is_fair req l h,
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
    rw or_iff_not_imp,
    intro h,
    apply fair_sched_of_mem _ _ h, },
  { change (([]<>•(eq l ∘ prod.fst)) (zip' (fair_sched_of req) req)),
    rw [inf_often_trace_init_trading,fst_comp_zip'],
    apply sched },
end

instance fin_sched {lbl : Type} [pos_finite lbl] : sched lbl :=
sched.fin (by apply_instance)

instance inf_sched {lbl : Type} [infinite lbl] : sched lbl :=
sched.inf (by apply_instance)

instance sched_option_inf {lbl : Type} : ∀ [sched lbl], sched (option lbl)
  | (sched.inf inf) := sched.inf (by apply_instance)
  | (sched.fin fin) := sched.fin (by apply_instance)

end scheduling
