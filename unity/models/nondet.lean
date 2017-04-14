
import unity.logic
import unity.temporal

import util.logic

universe variable u
namespace nondet

section nondet

open predicate

parameter {α : Type}

def pred := α → Prop

structure event : Type :=
  (coarse_sch : pred)
  (fine_sch : pred)
  (step : ∀ s, coarse_sch s → fine_sch s → α → Prop)
  (fis : ∀ s CS FS, ∃ s', step s CS FS s')

structure prog (lbl : Type) : Type :=
  (first : α → Prop)
  (first_fis : ∃ s, first s)
  (event' : lbl → event)

variables {lbl : Type}

def skip : event :=
{ coarse_sch := True
, fine_sch := True
, step := λ s _ _ s', s = s'
, fis := take s _ _, ⟨s,rfl⟩ }

def prog.event (s : prog lbl) : option lbl → event
  | none := skip
  | (some e) := s^.event' e

def prog.init (s : prog lbl) (p : pred) : Prop
:= s^.first ⟹ p

def prog.guard  (s : prog lbl) (e : option lbl) : α → Prop :=
(s^.event e)^.coarse_sch && (s^.event e)^.fine_sch

def prog.take_step (s : prog lbl) : ∀ (e : option lbl) (σ : α), s^.guard e σ → α → Prop
  | none σ _ := λ σ', σ = σ'
  | (some e) σ p := (s^.event e)^.step σ p.left p.right

open temporal

def prog.coarse_sch_of (s : prog lbl) (act : option lbl) : α → Prop :=
(s.event act).coarse_sch

def prog.fine_sch_of (s : prog lbl) (act : option lbl) : α → Prop :=
(s.event act).fine_sch

def prog.step_of (s : prog lbl) (act : option lbl) : α → α → Prop :=
λ σ σ', ∃ guard, s.take_step act σ guard σ'

def is_step (s : prog lbl) (σ σ' : α) : Prop :=
∃ ev, s.step_of ev σ σ'

structure prog.ex (s : prog lbl) (τ : stream α) : Prop :=
    (init : s^.first (τ 0))
    (safety : ∀ i, ⟦ is_step s ⟧ (τ.drop i))
    (liveness : ∀ e, (<>[]• s^.coarse_sch_of e) τ →
                     ([]<>• s^.fine_sch_of e) τ →
                     ([]<> ⟦ s.step_of e ⟧) τ)

structure prog.falsify (s : prog lbl) (act : option lbl) (p : pred' α) : Prop :=
  (enable : p ⟹ s^.coarse_sch_of act)
  (schedule : prog.ex s ⟹ (<>[]•p ⟶ []<>• s^.fine_sch_of act) )
  (negate' : ⦃ •p ⟶ ⟦ s^.step_of act ⟧ ⟶ ⟦ λ _, ~p ⟧ ⦄)

open temporal

lemma prog.falsify.negate
   {s : prog lbl} {act : option lbl} {p : pred' α}
:  prog.falsify s act p
→  •p && ⟦ s^.step_of act ⟧ ⟹ <>~•p :=
begin
  intros h₀ τ h₁,
  note h₂ := h₀.negate' _ h₁^.left h₁^.right,
  unfold eventually p_not init,
  existsi 1,
  apply h₂,
end

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
  { intros σ h₀ h₁, cases h₀ with h₂ }
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
  { apply forall_imp_forall _ h'.negate',
    intro τ,
    apply imp_mono _ _,
    { apply h },
    apply imp_imp_imp_right _,
    apply next_imp_next _ _,
    apply entail_contrapos,
    apply h }
end

end theorems

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
: ([]<>~•p) τ :=
begin
  cases (temporal.em' (•p) τ) with h_p ev_np,
  { unfold prog.transient at T₀,
    cases T₀ with ev T₀,
    assert Hc : (<>[]•s.coarse_sch_of ev) τ,
    { apply ex_map _ _ h_p,
      apply hence_map _ ,
      apply init_map _ ,
      apply T₀.enable },
    assert Hf : ([]<>•s.fine_sch_of ev) τ,
    { apply T₀.schedule _ h h_p, },
    note act := coincidence h_p (h.liveness ev Hc Hf),
    rw [-eventually_eventually],
    apply hence_map _ _ act,
    apply ex_map _ ,
    apply T₀.negate },
  { apply ev_np },
end

end soundness

-- instance {α} [sched lbl] : system_sem (prog lbl) :=
instance : unity.system_sem (prog lbl) :=
  { (_ : unity.system (prog lbl)) with
    ex := prog.ex
  , safety := @prog.ex.safety _ _
  , inhabited := sorry
  , transient_sem := @transient.semantics _ }

open unity

theorem transient_rule {s : prog lbl} {p : pred' α} (ev : option lbl)
   (EN : p ⟹ s.coarse_sch_of ev)
   (FLW : leads_to s (p && s.coarse_sch_of ev) (s.fine_sch_of ev))
   (NEG : ∀ σ σ', p σ → s.step_of ev σ σ' → ¬p σ')
: s.transient p :=
begin
  unfold prog.transient,
  existsi ev,
  apply falsify.mk,
    -- enablement
  { apply EN },
    -- follow
  { intros τ sem H,
    apply inf_often_of_leads_to (system_sem.leads_to_sem FLW _ sem),
    note H' := inf_often_of_stable _ H,
    apply hence_map _ _ H',
    apply ex_map _ ,
    apply init_map _ ,
    intros σ Hp,
    apply and.intro Hp,
    apply EN _ Hp },
    -- negation
  { intros σ Hp Hact,
    apply NEG _ _ Hp Hact }
end

end nondet

end nondet
