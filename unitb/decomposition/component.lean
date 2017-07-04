
import unitb.models.nondet

namespace d

open nondet unitb function

section

parameter α : Type

@[reducible]
private def pred := α → Prop

parameter {α}

structure program : Type 2 :=
  (asm : α → α → Prop)
  (mch : nondet.program α)

def compatible {t : Type} (m : t → program) : Prop :=
∀ i j, i ≠ j → ∀ s s', is_step (m i).mch s s' → (m i).asm s s'

def compose {t : Type} (m : t → program) {s₀ : α}
  (h₀ : ∀ i, (m i).mch.first s₀)
  (h : compatible m)
: program :=
{ mch :=
    { lbl := Σ i, (m i).mch.lbl
    , lbl_is_sched := sorry
    , first := λ s, ∀ i, (m i).mch.first s
    , first_fis := ⟨_,h₀⟩
    , event' := λ i, (m i.1).mch.event' i.2 }
, asm := sorry }

def step (p : program) (s s' : α) : Prop :=
nondet.is_step p.mch s s' ∨ p.asm s s'

instance : system program :=
{ σ := α
, init := nondet.program.init ∘ program.mch
, step := step
, transient := nondet.program.transient ∘ program.mch
, transient_false := λ s, @system.transient_false _ _ s.mch
, transient_antimono := λ s, @system.transient_antimono _ _ s.mch }

structure program.ex (s : program) (τ : stream α) : Prop :=
    (init : s.mch.first (τ 0))
    (safety : unitb.saf_ex s τ)
    (liveness : ∀ e, fair' s.mch e τ)

lemma ex_of_ex_mch (s : program) (τ : stream α)
  (h : s.mch.ex τ)
: s.ex τ :=
begin
  apply d.program.ex.mk,
  { apply h.init },
  { unfold saf_ex,
    apply temporal.henceforth_entails_henceforth _ _ h.safety,
    apply temporal.action_entails_action,
    intros s s',
    unfold unitb.step has_safety.step is_step step,
    apply or.intro_left },
  { apply h.liveness },
end

instance : system_sem program :=
{ (_ : system program) with
  ex := λ p, program.ex p
, init_sem  := λ s p τ Hτ H₀, by { apply H₀, apply Hτ.init }
, inhabited := λ s, exists_imp_exists (ex_of_ex_mch s) (system_sem.inhabited s.mch)
, safety    := λ s p, d.program.ex.safety
, transient_sem := λ s p q τ Hτ T, by apply transient.semantics' _ Hτ.liveness T }

end

end d
