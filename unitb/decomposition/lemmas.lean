
import unitb.decomposition.component

universe variables u

namespace decomposition
section

open predicate unitb function

parameter {α  : Type}
parameter {t : Type}
parameter s : t → program α
parameter {s₀ : α}
parameter {asm : α → α → Prop}
parameter {h₀ : ∀ i, (s i).mch.first s₀}
parameter {h : compatible s}
def s' := compose s asm h₀ h

variables {i : t}
variables {p q : pred' α}

lemma local_reasoning.transient
  (T : transient' (s i) p q)
: transient' s' p q :=
begin
  unfold transient' system.transient nondet.program.transient comp,
  unfold transient' system.transient nondet.program.transient comp at T,
  cases T with e Te,
  cases e,
  case some e
  { existsi some (⟨i,e⟩ : Σ i, (s i).mch.lbl),
    unfold s' compose program.mch nondet.program.lbl,
    apply nondet.program.falsify.mk,
    { apply Te.enable },
    { apply Te.schedule },
    { apply Te.negate' } },
  case none
  { existsi none,
    apply nondet.program.falsify.mk,
    { apply Te.enable },
    { apply Te.schedule },
    { apply Te.negate' } },
end

lemma local_reasoning.unless
  (S : unless (s i) p q)
: unless s' p q :=
begin
  unfold unless,
  intros σ σ' STEP,
  apply S,
  unfold unitb.step has_safety.step step,
  unfold unitb.step has_safety.step step s' compose at STEP,
  unfold program.mch program.asm nondet.is_step nondet.program.lbl at STEP,
  unfold nondet.program.step_of nondet.program.event at STEP,
  admit
end

theorem leads_to.subst {p q}
  (H : p ↦ q in s i)
: p ↦ q in s' :=
unitb.leads_to.subst id _ _
(@local_reasoning.transient i) (@local_reasoning.unless i) H

theorem often_imp_often.subst {p q}
  (H : p >~> q in s i)
: p >~> q in s' :=
unitb.often_imp_often.subst id _ _
(@local_reasoning.transient i) (@local_reasoning.unless i) H

end
end decomposition
