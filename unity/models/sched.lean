
import unity.logic

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

def cpred (β : Type) := stream β → Prop

def action {β} (a : β → β → Prop) : cpred β
  | τ := a (τ 0) (τ 1)

def eventually {β} (p : cpred β) : cpred β
  | τ := ∃ i, p (τ.drop i)
def henceforth {β} (p : cpred β) : cpred β
  | τ := ∀ i, p (τ.drop i)
def init  {β} (p : pred' β) : cpred β
  | τ := p (τ 0)

prefix `<>`:5 := eventually
prefix `[]`:5 := henceforth
prefix `•`:5 := init
notation `[[` act `]]`:5 := action act

section coincidence

parameter {τ : stream α}
parameters {p q : cpred α}

theorem coincidence
  (hp : (<>[] p) τ)
  (hq : ([]<> q) τ)
: ([]<> (p && q)) τ :=
begin
  -- unfold
  intro i,
  cases hp with j hp,
  note hq' := hq (i+j),
  cases hq' with k hq',
  note hp' := hp (i+k),
  unfold eventually p_and,
  existsi (j+k),
  simp [stream.drop_drop],
  simp [stream.drop_drop] at hq',
  simp [stream.drop_drop] at hp',
  split ; assumption
end

end coincidence

noncomputable def when {p q : cpred α} {τ}
   (hp : (<>[] p) τ)
   (hq : ([]<> q) τ)
   (h : ∀ τ (h : (p && q) τ), Prop)
: Prop := ∀ i : ℕ,
show Prop,
begin
  note h' := coincidence _ hp hq,
  note h'' := h' i,
  unfold eventually at h'',
  cases (classical.indefinite_description _ h'') with j h'',
  apply h _ h''
end

structure prog.ex (s : prog lbl) (τ : stream α) : Prop :=
    (init : τ 0 = s^.first)
    (safety : ∀ i, ∃ e, dite' (prog.guard s e (τ i)) (λ H, s^.take_step _ e (τ i) H) (λ H, τ i) = τ (i+1))
    (liveness : ∀ e, ∀ hc : (<>[] •(s^.event _ e)^.coarse_sch) τ,
                     ∀ hf : ([]<> •(s^.event _ e)^.fine_sch) τ,
                       when hc hf (λ τ h, τ 1 = (s^.take_step α e (τ 0) h)))

structure prog.falsify (s : prog lbl) (act : option lbl) (p : pred' α) : Prop :=
  (enable : ∀ σ, p σ → (s^.event _ act)^.coarse_sch σ)
  (schedule : ∀ τ i, prog.ex s τ → p (τ i) → ∃ j, (s^.event _ act)^.fine_sch (τ $ i+j))
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
    existsi 0,
    unfold prog.event event.fine_sch,
    trivial },
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
    apply imp_imp_imp_right' _,
    intro h₁,
    apply imp_imp_imp_left,
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

-- instance {α} [sched lbl] : system_sem (prog lbl) :=
instance : unity.system_sem (prog lbl) :=
sorry

end schedules

end schedules
