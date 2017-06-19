
import unity.models.nondet
import unity.predicate

import util.data.option

universe variables u v

open nat predicate

section

parameters (σ : Type) (lbl : Type)

@[reducible]
def pred := σ → Prop

inductive code : pred → pred → Type
  | skip {} : ∀ p, code p p
  | action : ∀ p q, lbl → code p q
  | seq : ∀ {p q r}, code p q → code q r → code p r
  | if_then_else : ∀ p {pa pb q}, pred → code pa q → code pb q → code p q
  | while : ∀ {p inv} q, pred → code p inv → code inv q

parameters {σ lbl}

inductive current : ∀ {p q}, code p q → Type
  | action : ∀ p q l, current (code.action p q l)
  | seq_left : ∀ p q r (c₀ : code p q) (c₁ : code q r), current c₀ → current (code.seq c₀ c₁)
  | seq_right : ∀ p q r (c₀ : code p q) (c₁ : code q r), current c₁ → current (code.seq c₀ c₁)
  | if_then_else_cond  : ∀ p t pa pb q (c₀ : code pa q) (c₁ : code pb q),
         current (code.if_then_else p t c₀ c₁)
  | if_then_else_left  : ∀ p t pa pb q (c₀ : code pa q) (c₁ : code pb q),
         current c₀ → current (code.if_then_else p t c₀ c₁)
  | if_then_else_right : ∀ p t pa pb q (c₀ : code pa q) (c₁ : code pb q),
         current c₁ → current (code.if_then_else p t c₀ c₁)
  | while_cond : ∀ p inv w (c : code p inv) q,
         current (code.while q w c)
  | while_body : ∀ p inv w (c : code p inv) q,
         current c → current (code.while q w c)

def is_control : Π {p q} {c : code p q}, current c →  Prop
  | ._ ._ ._ (current.action _ _ _) := false
  | ._ ._ ._ (current.seq_left  p q r _ _ pc) := is_control pc
  | ._ ._ ._ (current.seq_right p q r _ _ pc) := is_control pc
  | ._ ._ ._ (current.if_then_else_cond  p t _ _ _ _ _)    := true
  | ._ ._ ._ (current.if_then_else_left  p t _ _ _ _ _ pc) := is_control pc
  | ._ ._ ._ (current.if_then_else_right p t _ _ _ _ _ pc) := is_control pc
  | ._ ._ ._ (current.while_cond _ _ _ _ _)    := true
  | ._ ._ ._ (current.while_body _ _ _ _ _ pc) := is_control pc

def control {p q} (c : code p q) := subtype (@is_control _ _ c)

def condition' : Π {p q} {c : code p q} (pc : current c), is_control pc → σ → Prop
  | ._ ._ ._ (current.action _ _ _) h := by cases h
  | ._ ._ ._ (current.seq_left  p q r c₀ c₁ pc) h := condition' pc h
  | ._ ._ ._ (current.seq_right p q r c₀ c₁ pc) h := condition' pc h
  | ._ ._ ._ (current.if_then_else_cond  pa pb p q c c₀ c₁) h := c
  | ._ ._ ._ (current.if_then_else_left  pa pb p q c c₀ c₁ pc) h := condition' pc h
  | ._ ._ ._ (current.if_then_else_right pa pb p q c c₀ c₁ pc) h := condition' pc h
  | ._ ._ ._ (current.while_cond _ _ c _ _) h    := c
  | ._ ._ ._ (current.while_body _ _ _ _ _ pc) h := condition' pc h

def condition {p q} {c : code p q} : control c → σ → Prop
  | ⟨pc,H⟩ := condition' pc H

def selects' : Π {p q} {c : code p q}, current c → lbl → Prop
  | ._ ._ ._ (current.action _ _ e') e := e = e'
  | ._ ._ ._ (current.seq_left _ _ _ s c p) e := selects' p e
  | ._ ._ ._ (current.seq_right _ _ _ _ _ p) e := selects' p e
  | ._ ._ ._ (current.if_then_else_cond _ _ _ _ _ _ _) e    := false
  | ._ ._ ._ (current.if_then_else_left _ _ _ _ _ _ _ p) e  := selects' p e
  | ._ ._ ._ (current.if_then_else_right _ _ _ _ _ _ _ p) e := selects' p e
  | ._ ._ ._ (current.while_cond _ _ _ _ _) e   := false
  | ._ ._ ._ (current.while_body _ _ _ _ _ p) e := selects' p e

def selects {p q} {c : code p q} : option (current c) → lbl → Prop
  | (some c) := selects' c
  | none := False

def assert_of' : Π {p q} {c : code p q}, current c → σ → Prop
  | .(p) ._ ._ (current.action p _ _) := p
  | ._ ._ ._ (current.seq_left  _ _ _ _ _ pc) := assert_of' pc
  | ._ ._ ._ (current.seq_right _ _ _ _ _ pc) := assert_of' pc
  | .(p) ._ ._ (current.if_then_else_cond  p _ _ _ _ _ _)  := p
  | ._ ._ ._ (current.if_then_else_left  _ _ _ _ _ _ _ pc) := assert_of' pc
  | ._ ._ ._ (current.if_then_else_right _ _ _ _ _ _ _ pc) := assert_of' pc
  | .(p) ._ ._ (current.while_cond _ p _ _ _)  := p
  | ._ ._ ._ (current.while_body _ _ _ _ _ pc) := assert_of' pc

def assert_of {p q} {c : code p q} : option (current c) → σ → Prop
  | none := q
  | (some pc) := assert_of' pc

def next_assert' : Π {p q} {c : code p q}, current c → σ → Prop
  | ._ .(q) ._ (current.action _ q _) s := q s
  | ._ ._ ._ (current.seq_left  _ _ _ _ _ pc) s := next_assert' pc s
  | ._ ._ ._ (current.seq_right _ _ _ _ _ pc) s := next_assert' pc s
  | ._ .(q) ._ (current.if_then_else_cond  _ _ _ _ q _ _) s  := q s
  | ._ ._ ._ (current.if_then_else_left  _ _ _ _ _ _ _ pc) s := next_assert' pc s
  | ._ ._ ._ (current.if_then_else_right _ _ _ _ _ _ _ pc) s := next_assert' pc s
  | ._ .(q) ._ (current.while_cond _ _ _ _ q) s    := q s
  | ._ ._ ._ (current.while_body _ _ _ _ _ pc) s := next_assert' pc s

def next_assert {p q} {c : code p q} : option (current c) → σ → Prop
  | none := q
  | (some pc) := next_assert' pc

def first : Π {p q} (c : code p q), option (current c)
  | ._ ._ (code.skip p) := none
  | ._ ._ (code.action p _ l) := some $ current.action _ _ _
  | .(p) .(r) (@code.seq ._ ._ p q r c₀ c₁) :=
        current.seq_left _ _ _ _ _ <$> first _
    <|> current.seq_right _ _ _ _ _ <$> first _
  | ._ ._ (@code.if_then_else ._ ._ p _ _ _ c b₀ b₁) :=
    some $ current.if_then_else_cond _ _ _ _ _ _ _
  | ._ ._ (@code.while ._ ._ _ _ _ c b) :=
    some $ current.while_cond _ _ _ _ _

lemma assert_of_first {p q} {c : code p q}
: assert_of (first c) = p :=
begin
  induction c
  ; try { refl },
  { unfold first,
    destruct first a,
    { intro h,
      simp [h],
      destruct first a_1,
      { intro h',
        simp [h'], unfold assert_of,
        simp [h'] at ih_2, unfold assert_of at ih_2,
        simp [h] at ih_1, unfold assert_of at ih_1,
        subst r, subst q_1 },
      { intros x h', simp [h'],
        unfold assert_of assert_of',
        rw h at ih_1, rw h' at ih_2,
        unfold assert_of at ih_1 ih_2,
        subst p_1, rw ih_2, } },
    { intros x h,
      simp [h],
      unfold assert_of assert_of',
      rw h at ih_1, unfold assert_of at ih_1,
      rw ih_1 }, }
end

local attribute [instance] classical.prop_decidable

noncomputable def next' (s : σ) : ∀ {p q} {c : code p q}, current c → option (current c)
  | ._ ._ ._ (current.action p q l) := none
  | ._ ._ ._ (current.seq_left _ _ _ c₀ c₁ cur₀) :=
        current.seq_left _ _ _ _ c₁ <$> next' cur₀
    <|> current.seq_right _ _ _ c₀ _ <$> first c₁
  | ._ ._ ._ (current.seq_right _ _ _ c₀ c₁ cur₁) :=
        current.seq_right _ _ _ _ c₁ <$> next' cur₁
  | ._ ._ ._ (current.if_then_else_cond _ _ _ p c b₀ b₁) :=
      if c s
         then current.if_then_else_left  _ _ _ _ _ _ _ <$> first b₀
         else current.if_then_else_right _ _ _ _ _ _ _ <$> first b₁
  | ._ ._ ._ (current.if_then_else_left _ _ _ _ _ b₀ b₁ cur₀) :=
      current.if_then_else_left _ _ _ _ _ b₀ b₁ <$> next' cur₀
  | ._ ._ ._ (current.if_then_else_right _ _ _ _ _ b₀ b₁ cur₁) :=
      current.if_then_else_right _ _ _ _ _ b₀ b₁ <$> next' cur₁
  | ._ ._ ._ (current.while_cond _ _ c b q) :=
      current.while_body _ _ c b q <$> first b
  | ._ ._ ._ (current.while_body _ _ c b q cur) :=
      current.while_body _ _ c b q <$> next' cur

noncomputable def next (s : σ) {p q : pred} {c : code p q}
: option (current c) → option (current c)
  | (some pc) := next' s pc
  | none := none

lemma assert_of_next {p q : pred} {c : code p q} (pc : option (current c)) (s : σ)
: assert_of (next s pc) s ↔ next_assert pc s :=
sorry

-- def control_nodes : Π {p q : pred}, code p q → ℕ
--   | ._ ._ (code.skip _) := 0
--   | ._ ._ (code.action _ _ _) := 1
--   | ._ ._ (@code.seq ._ ._ p q r c₀ c₁) := control_nodes c₀ + control_nodes c₁
--   | ._ ._ (@code.if_then_else ._ ._ c pa pb q _ c₀ c₁) :=
--      1 + control_nodes c₀ + control_nodes c₁
--   | ._ ._ (@code.while ._ ._ p inv q c b) :=
--      1 + control_nodes b

-- def bij.finite.f : Π {p q} {c : code p q}, current c → fin (control_nodes c)
--   | ._ ._ ._ (current.action _ _ _) := ⟨0,zero_lt_one⟩
--   | ._ ._ ._ (current.seq_left p q r c₀ c₁ pc) := _
--   | ._ ._ ._ (current.seq_right p q r c₀ c₁ pc) := _

instance control_finite {p q : pred} {c : code p q} : finite (control c) :=
sorry
-- ⟨ control_nodes c, _ ⟩

instance control_sched {p q : pred} {c : code p q} : scheduling.sched (control c) :=
scheduling.sched.fin (by apply_instance)

def cpred : Type := stream σ → Prop

parameters {σ lbl}

def pre (p : pred) (q : cpred) : cpred
 | τ := p (τ 0) ∧ q τ

def act (a : σ → σ → Prop) (p : cpred) : cpred
 | τ := a (τ 0) (τ 1) ∧ p τ.tail

def skip : cpred → cpred :=
act eq

def skipn : ℕ → cpred → cpred
  | 0 p := p
  | (succ n) p := skipn n (skip p)

def stutter (p : cpred) : cpred
 | τ := ∃ i, skipn i p τ

def test (f g : cpred → cpred) (p : cpred) : cpred
 | τ := f p τ ∨ g p τ

end

namespace code.semantics

section
open code

parameters (σ : Type)
-- def rel := σ → σ → Prop

-- def ex : code σ rel → cpred σ → cpred σ
--  | (action p a) := stutter ∘ pre p ∘ act a
--  | (seq p₀ p₁) := ex p₀ ∘ ex p₁
--  | (if_then_else p c a₀ a₁) := pre p ∘ test (pre c ∘ ex a₀) (pre (-c) ∘ ex a₁)
--  | (while p c a inv) := _

parameters (p : nondet.program σ)
parameters {term : pred σ}
parameters (c : code σ p.lbl p.first term)

structure local_correctness : Prop :=
  (enabled : ∀ (pc : option $ current c) l, selects pc l → assert_of pc ⟹ p.guard l)
  (correct : ∀ (pc : option $ current c) l, selects pc l →
       ∀ s s', assert_of pc s → p.step_of l s s' → next_assert pc s')

-- instance : scheduling.sched (control c ⊕ p.lbl) := _

structure state :=
  (pc : option (current c))
  (intl : σ)
  (assertion : assert_of pc intl)

parameter Hcorr : local_correctness

include Hcorr

section event

parameter (e : p.lbl)
parameter (s : state)
parameter (h₀ : selects (s.pc) e)
parameter (h₁ : true)

include h₁

theorem evt_guard
: p.guard e s.intl :=
Hcorr.enabled s.pc e h₀ s.intl s.assertion

theorem evt_coarse_sch
: p.coarse_sch_of e s.intl :=
evt_guard.left

theorem evt_fine_sch
: p.fine_sch_of e s.intl :=
evt_guard.right

noncomputable def machine.step (s' : state) : Prop :=
  (p.event e).step s.intl evt_coarse_sch evt_fine_sch s'.intl
∧ s'.pc = next s.intl s.pc

include evt_coarse_sch evt_fine_sch

def machine.step_fis
: ∃ (s' : state), machine.step s' :=
begin
  note CS := evt_coarse_sch _ p c Hcorr e s h₀ h₁,
  note FS := evt_fine_sch _ _ c Hcorr e s h₀ h₁,
  cases (p.event e).fis s.intl CS FS with s' H,
  assert Hss' : assert_of (next s.intl s.pc) s',
  { cases s.pc, admit, admit },
  note ss' := state.mk (next s.intl s.pc) s' Hss',
  existsi ss',
  admit
end

end event

section test

parameter (s : state)

noncomputable def machine.test (s' : state) : Prop :=
  s.intl = s'.intl
∧ s'.pc = next s.intl s.pc

def machine.test_fis
: ∃ (s' : state), machine.test s' :=
sorry

end test

noncomputable def machine.event : control c ⊕ p.lbl → nondet.event state
| (sum.inr e) :=
  { coarse_sch := λ s, selects s.pc e
  , fine_sch   := True
  , step := machine.step e
  , fis  := machine.step_fis e }
| (sum.inl pc) :=
  { coarse_sch := λ s, s.pc = pc.val
  , fine_sch   := True
  , step := λ s _ _ s', machine.test s s'
  , fis  := λ s _ _, machine.test_fis s }

def machine_of : nondet.program state :=
 { lbl := control c ⊕ p.lbl
 , lbl_is_sched := by apply_instance
 , first := λ ⟨s₀,s₁,_⟩, s₀ = first c ∧ p.first s₁
 , first_fis :=
   begin cases p.first_fis with s Hs,
         assert Hss : assert_of (first c) s, admit,
         pose ss := state.mk (first c) s Hss,
         existsi ss,
         unfold machine_of._match_1,
         exact ⟨rfl,Hs⟩
   end
 , event' := machine.event }

end
end code.semantics
