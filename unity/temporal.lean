
import data.stream
import unity.predicate

import util.logic

namespace temporal

open predicate

universe variables u u'

variables {β : Type u}

def cpred (β : Type u) := stream β → Prop

def action {β} (a : β → β → Prop) : cpred β
  | τ := a (τ 0) (τ 1)

def eventually {β} (p : cpred β) : cpred β
  | τ := ∃ i, p (τ.drop i)
def henceforth {β} (p : cpred β) : cpred β
  | τ := Π i, p (τ.drop i)
def init  {β} (p : β → Prop) : cpred β
  | τ := p (τ 0)

def ew {β} (p : β → Prop) : Prop :=
∀ x, p x

prefix `<>`:85 := eventually
prefix `[]`:85 := henceforth
prefix `•`:5 := init
notation `[[` act `]]`:95 := action act
-- notation `⦃` act `⦄`:95 := ew act

lemma not_henceforth {β} (p : cpred β) : (~[]p) = (<>~p) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  apply not_forall_iff_exists_not,
end

lemma not_eventually {β} (p : cpred β) : (~<>p) = ([]~p) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  apply not_exists_iff_forall_not,
end

theorem em {β} (p : cpred β) : ew (<>[]p || []<>(~ p)) :=
begin
  intro τ,
  assert h : (<>[]p || ~<>[]p) τ,
  { apply classical.em (<>[]p $ τ) },
  simp [not_eventually,not_henceforth] at h,
  apply h
end

theorem em' {β} (p : cpred β) (τ) : (<>[]p) τ ∨ ([]<>(~ p)) τ :=
by apply em

lemma ex_map {p q : cpred β} (f : p ⟹ q) : (<>p) ⟹ (<>q) :=
begin
  intro τ,
  apply exists_imp_exists,
  intro i,
  apply f,
end

lemma hence_map {p q : cpred β} (f : p ⟹ q) : ([]p) ⟹ ([]q) :=
begin
  intro τ,
  apply forall_imp_forall,
  intro i,
  apply f,
end

lemma init_map {p q : pred' β} (f : p ⟹ q) : (•p) ⟹ (•q) :=
begin
  intro τ,
  apply f,
end

lemma stable_imp_inf {p : cpred β} : (<>[]p) ⟹ ([]<>p) :=
begin
  intros τ h i,
  cases h with j h,
  unfold eventually,
  existsi j,
  note h' := h i,
  simp [stream.drop_drop],
  simp [stream.drop_drop] at h',
  apply h',
end

@[simp]
lemma hence_false : [](False : cpred β) = False :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { cases h 0 },
  { cases h }
end

@[simp]
lemma event_false : <>(False : cpred β) = False :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { cases h with _ h, cases h },
  { cases h }
end

@[simp]
lemma init_false : (•False) = (False : cpred β) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { cases h },
  { cases h }
end

@[simp]
lemma hence_true : [](True : cpred β) = True :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { trivial },
  { intro, trivial }
end

@[simp]
lemma event_true : <>(True : cpred β) = True :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h,
  { trivial },
  { apply exists.intro 0, trivial }
end

@[simp]
lemma init_true : (•True) = (True : cpred β) :=
begin
  apply funext,
  intro x,
  rw -iff_eq_eq,
  split ; intro h ; trivial,
end

end temporal
