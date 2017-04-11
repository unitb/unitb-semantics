
import unity.logic
import unity.temporal

import util.logic

universe variable u
namespace schedules

section schedules

open predicate

parameter α : Type

def pred := α → Prop

structure event : Type :=
  (coarse_sch : pred)
  (fine_sch : pred)
  (step : ∀ s, coarse_sch s → fine_sch s → α)

structure prog (lbl : Type) : Type :=
  (first : α)
  (event' : lbl → event)

variables {lbl : Type}

def prog.event (s : prog lbl) : option lbl → event
  | none := { coarse_sch := True, fine_sch := True, step := λ s _ _, s }
  | (some e) := s^.event' e

def prog.init (s : prog lbl) (p : pred) : Prop
:= p (s^.first)

def prog.guard  (s : prog lbl) (e : option lbl) : α → Prop :=
(s^.event α e)^.coarse_sch && (s^.event α e)^.fine_sch

def prog.take_step (s : prog lbl) : ∀ (e : option lbl) (σ : α), s^.guard _ e σ → α
  | none σ _ := σ
  | (some e) σ p := (s^.event _ e)^.step σ p.left p.right

noncomputable def dite' {β : Type u} (p : Prop) (t : p → β) (f : ¬ p → β) : β :=
match classical.decidable_inhabited p with
  | (inhabited.mk (is_true h))  := t h
  | (inhabited.mk (is_false h)) := f h
end

open temporal

structure prog.ex (s : prog lbl) (τ : stream α) : Prop :=
    (init : τ 0 = s^.first)
    (safety : ∀ i, ∃ e, dite' (prog.guard s e (τ i)) (λ H, s^.take_step _ e (τ i) H) (λ H, τ i) = τ (i+1))
    (liveness : ∀ e, (<>[] •(s^.event _ e)^.coarse_sch) τ →
                     ([]<> •(s^.event _ e)^.fine_sch) τ →
                     ([]<> (λ τ, ∃ h, τ 1 = (s^.take_step α e (τ 0) h))) τ)

structure prog.falsify (s : prog lbl) (act : option lbl) (p : pred' α) : Prop :=
  (enable : ∀ σ, p σ → (s^.event _ act)^.coarse_sch σ)
  (schedule : ∀ τ, prog.ex s τ → ((<>[]•p) ⟶ ([]<>• (s^.event α act)^.fine_sch)) τ)
  (negate : ∀ σ (H : s^.guard α act σ), p σ → ¬ p (s^.take_step α act σ H))

def prog.transient (s : prog lbl) (p : pred' α) : Prop :=
∃ (act : option lbl), prog.falsify s act p

section theorems

variable (s : prog lbl)

open prog
open event

theorem prog.transient_false : transient s False :=
begin
  unfold prog.transient,
  existsi none,
  apply falsify.mk,
  { intros σ h, cases h },
  { intros τ i h₀ h₁,
    simp at h₀,
    cases h₀, },
  { intros σ h₀ h₁, cases h₁ }
end

def prog.transient_str : ∀ (s : prog lbl) {p q : α → Prop}, (∀ (i : α), p i → q i) → prog.transient s q → prog.transient s p :=
begin
  intros s p q h,
  unfold transient,
  apply exists_imp_exists,
  intros e h',
  apply falsify.mk,
  { apply forall_imp_forall _ h'.enable,
    intro x,
    apply imp_imp_imp_left,
    apply h },
  { apply forall_imp_forall _ h'.schedule,
    intro τ,
    apply forall_imp_forall _,
    intro j,
    apply p_imp_p_imp_p_imp_left _,
    apply ex_map,
    apply hence_map,
    apply init_map,
    apply h },
  { apply forall_imp_forall _ h'.negate,
    intro σ,
    apply forall_imp_forall _,
    intro H,
    apply imp_mono _ _,
    { apply h },
    { intros hnq hp,
      apply hnq (h _ hp) } }
end

end theorems

def is_step (s : prog lbl) (σ σ' : α) : Prop :=
∃ ev guard, σ' = s^.take_step _ ev σ guard

instance prog_is_system : unity.system (prog lbl) :=
{ σ := α
, transient := @prog.transient lbl
, step := is_step
, init   := prog.init
, transient_false := prog.transient_false
, transient_str := prog.transient_str }

section soundness

open prog

variables {s : prog lbl} {p : pred' α}
variables (T₀ : prog.transient s p)
include T₀
variables (τ : stream α)

lemma transient.semantics (h : ex s τ)
: ∀ (i : ℕ), p (τ i) → (∃ (j : ℕ), ¬p (τ (i + j))) :=
begin
  intros i hp,
  cases (temporal.em' (•p) τ) with h_p ev_np,
  { unfold prog.transient at T₀,
    cases T₀ with ev T₀,
    assert Hc : (<>[]•(event s ev).coarse_sch) τ,
    { apply ex_map _ _ h_p,
      apply hence_map _ ,
      apply init_map _ ,
      apply T₀.enable },
    assert Hf : ([]<>•(event s ev).fine_sch) τ,
    { apply T₀.schedule _ h h_p, },
    cases h_p with k h_p,
    note sch := h.liveness ev Hc Hf (i+k),
    cases sch with j sch,
    cases sch with guard sch,
    revert guard sch,
    pose X := (stream.drop j (stream.drop (i+k) τ)),
    assert hX : X = (stream.drop j (stream.drop (i+k) τ)), refl,
    revert hX,
    generalize (stream.drop j (stream.drop (i+k) τ)) Y,
    revert X, simp,
    intros Y hY guard act,
    rw stream.drop_drop at hY,
    existsi (k+j+1),
    note neg := T₀.negate _ guard,
    rw [-act,-hY] at neg,
    unfold stream.drop at neg,
    simp at neg,
    apply neg,
    note h_p' := h_p (i+j),
    unfold stream.drop temporal.init at h_p',
    simp at h_p',
    apply h_p' },
  { note ev_np' := ev_np i,
    cases ev_np' with j ev_np',
    unfold stream.drop p_not temporal.init at ev_np',
    simp at ev_np',
    existsi j,
    apply ev_np' },
end

end soundness

-- instance {α} [sched lbl] : system_sem (prog lbl) :=
instance : unity.system_sem (prog lbl) :=
  { (_ : unity.system (prog lbl)) with
    ex := prog.ex
  , inhabited := sorry
  , transient_sem := @transient.semantics _ }

end schedules

end schedules
