
import unitb.models.nondet
import unitb.predicate

import util.data.option
import util.data.sum

universe variables u v

open nat predicate

section

parameters (σ : Type) (lbl : Type)

@[reducible]
def pred := σ → Prop

parameters {σ}

inductive code : pred → pred → Type
  | skip {} : ∀ p, code p p
  | action : ∀ p q, set lbl → lbl → code p q
  | seq : ∀ {p q r}, code p q → code q r → code p r
  | if_then_else : ∀ p {pa pb q}, set lbl → pred → code pa q → code pb q → code p q
  | while : ∀ {p inv} q, set lbl → pred → code p inv → code inv q

parameters {σ lbl}

@[pattern,reducible]
def if_then_else : ∀ p {pa pb q}, set lbl → pred → code pa q → code pb q → code p q :=
code.if_then_else

@[pattern,reducible]
def while : ∀ {p inv} q, set lbl → pred → code p inv → code inv q :=
@code.while

inductive current : ∀ {p q}, code p q → Type
  | action : ∀ p q s l, current (code.action p q s l)
  | seq_left : ∀ p q r (c₀ : code p q) (c₁ : code q r), current c₀ → current (code.seq c₀ c₁)
  | seq_right : ∀ p q r (c₀ : code p q) (c₁ : code q r), current c₁ → current (code.seq c₀ c₁)
  | ite_cond  : ∀ p t pa pb q s (c₀ : code pa q) (c₁ : code pb q),
         current (code.if_then_else p s t c₀ c₁)
  | ite_left  : ∀ p t pa pb q s (c₀ : code pa q) (c₁ : code pb q),
         current c₀ → current (code.if_then_else p s t c₀ c₁)
  | ite_right : ∀ p t pa pb q s (c₀ : code pa q) (c₁ : code pb q),
         current c₁ → current (code.if_then_else p s t c₀ c₁)
  | while_cond : ∀ p inv q s w (c : code p inv),
         current (code.while q s w c)
  | while_body : ∀ p inv q s w (c : code p inv),
         current c → current (code.while q s w c)

@[reducible]
def seq_left {p q r} {c₀ : code p q} (c₁ : code q r)
  (cur : current c₀)
: current (code.seq c₀ c₁) :=
current.seq_left _ _ _ c₀ _ cur

@[reducible]
def seq_right {p q r} (c₀ : code p q) {c₁ : code q r}
  (cur : current c₁)
: current (code.seq c₀ c₁) :=
current.seq_right _ _ _ c₀ _ cur

@[reducible]
def ite_cond (p t) {pa pb q} (s : set lbl) (c₀ : code pa q) (c₁ : code pb q)
: current (if_then_else p s t c₀ c₁) :=
current.ite_cond p t _ _ _ s c₀ c₁

@[reducible]
def ite_left (p t) {pa pb q} (s : set lbl) {c₀ : code pa q} (c₁ : code pb q) (cur₀ : current c₀)
: current (if_then_else p s t c₀ c₁) :=
current.ite_left p t _ _ _ s c₀ c₁ cur₀

@[reducible]
def ite_right (p t : pred) {pa pb q : pred} (s : set lbl)
  (c₀ : code pa q) {c₁ : code pb q}
  (cur₁ : current c₁)
: current (if_then_else p s t c₀ c₁) :=
current.ite_right p t _ _ _ s c₀ c₁ cur₁

@[reducible]
def while_cond {p inv} (q s w) (c : code p inv)
: current (code.while q s w c) :=
current.while_cond p inv q s w c

@[reducible]
def while_body {p inv} (q s w) {c : code p inv}
  (cur : current c)
: current (code.while q s w c) :=
current.while_body p inv q s w c cur

def selects' : Π {p q} {c : code p q}, current c → lbl → Prop
  | ._ ._ ._ (current.action _ _ _ e') e := e = e'
  | ._ ._ ._ (current.seq_left _ _ _ s c p) e := selects' p e
  | ._ ._ ._ (current.seq_right _ _ _ _ _ p) e := selects' p e
  | ._ ._ ._ (current.ite_cond _ _ _ _ _ _ _ _) e    := false
  | ._ ._ ._ (current.ite_left _ _ _ _ _ _ _ _ p) e  := selects' p e
  | ._ ._ ._ (current.ite_right _ _ _ _ _ _ _ _ p) e := selects' p e
  | ._ ._ ._ (current.while_cond _ _ _ _ _ _) e   := false
  | .(inv) .(q) ._ (current.while_body p inv q _ _ _ pc) e := selects' pc e

def selects {p q} {c : code p q} : option (current c) → lbl → Prop
  | (some c) := selects' c
  | none := False

def is_control' : Π {p q} {c : code p q}, current c → bool
  | ._ ._ ._ (current.action _ _ _ l) := ff
  | ._ ._ ._ (current.seq_left  p q r _ _ pc)       := is_control' pc
  | ._ ._ ._ (current.seq_right p q r _ _ pc)       := is_control' pc
  | .(p) .(q) ._ (current.ite_cond  p t pa pb q _ _ _) := tt
  | ._ ._ ._ (current.ite_left  p t _ _ _ _ _ _ pc)    := is_control' pc
  | ._ ._ ._ (current.ite_right p t _ _ _ _ _ _ pc)    := is_control' pc
  | .(inv) .(q) ._ (current.while_cond p inv q _ t _) := tt
  | ._ ._ ._ (current.while_body _ _ _ _ _ _ pc)      := is_control' pc

def is_control {p q} {c : code p q} : option (current c) → bool
  | (some pc) := is_control' pc
  | none := ff

-- def control {p q} (c : code p q) := subtype (@is_control _ _ c)

-- instance is_control_decidable
-- : ∀ {p q} {c : code p q} (cur : current c), decidable (is_control cur)
--   | ._ ._ ._ (current.action _ _ _) := decidable.false
--   | ._ ._ ._ (current.seq_left p q r c₀ c₁ cur) := is_control_decidable cur
--   | ._ ._ ._ (current.seq_right p q r c₀ c₁ cur) := is_control_decidable cur
--   | ._ ._ ._ (current.ite_cond  p t pa pb q c₀ c₁) := decidable.true
--   | ._ ._ ._ (current.ite_left  p t pa pb q c₀ c₁ cur) := is_control_decidable cur
--   | ._ ._ ._ (current.ite_right p t pa pb q c₀ c₁ cur) := is_control_decidable cur
--   | ._ ._ ._ (current.while_cond p t inv q c) := decidable.true
--   | ._ ._ ._ (current.while_body p t inv q c cur) := is_control_decidable cur

def condition' : Π {p q} {c : code p q} (pc : current c), is_control' pc → σ → Prop
  | ._ ._ ._ (current.action _ _ _ _) h := by cases h
  | ._ ._ ._ (current.seq_left  p q r c₀ c₁ pc) h := condition' pc h
  | ._ ._ ._ (current.seq_right p q r c₀ c₁ pc) h := condition' pc h
  | .(p) .(q) ._ (current.ite_cond  p c pa pb q _ c₀ c₁) h := c
  | .(p) .(q) ._ (current.ite_left  p c pa pb q _ c₀ c₁ pc) h := condition' pc h
  | .(p) .(q) ._ (current.ite_right p c pa pb q _ c₀ c₁ pc) h := condition' pc h
  | .(inv) .(q) ._ (current.while_cond p inv q _ c _) h    := c
  | .(inv) .(q) ._ (current.while_body p inv q _ _ _ pc) h := condition' pc h

def condition {p q} {c : code p q} : ∀ pc : option $ current c, is_control pc → σ → Prop
  | (some pc) := condition' pc
  | none := assume h, by cases h

def action_of : Π {p q} {c : code p q} (cur : current c),
{ p // ∃ P, condition (some cur) P = p }  ⊕ subtype (selects (some cur))
  | ._ ._ ._ (current.action _ _ _ l) := sum.inr ⟨l,rfl⟩
  | ._ ._ ._ (current.seq_left  p q r _ _ pc) := action_of pc
  | ._ ._ ._ (current.seq_right p q r _ _ pc) := action_of pc
  | .(p) .(q) ._ (current.ite_cond  p t pa pb q _ _ _) := sum.inl ⟨t,rfl,rfl⟩
  | ._ ._ ._ (current.ite_left  p t _ _ _ _ _ _ pc) := action_of pc
  | ._ ._ ._ (current.ite_right p t _ _ _ _ _ _ pc) := action_of pc
  | .(inv) .(q) ._ (current.while_cond p inv q _ t _)    := sum.inl ⟨t,rfl,rfl⟩
  | ._ ._ ._ (current.while_body _ _ _ _ _ _ pc) := action_of pc

def assert_of' : Π {p q} {c : code p q}, current c → σ → Prop
  | .(p) ._ ._ (current.action p _ _ _) := p
  | ._ ._ ._ (current.seq_left  _ _ _ _ _ pc) := assert_of' pc
  | ._ ._ ._ (current.seq_right _ _ _ _ _ pc) := assert_of' pc
  | .(p) ._ ._ (current.ite_cond  p _ _ _ _ _ _ _)  := p
  | ._ ._ ._ (current.ite_left  _ _ _ _ _ _ _ _ pc) := assert_of' pc
  | ._ ._ ._ (current.ite_right _ _ _ _ _ _ _ _ pc) := assert_of' pc
  | .(inv) .(q) ._ (current.while_cond p inv q _ _ _)  := inv
  | ._ ._ ._ (current.while_body _ _ _ _ _ _ pc) := assert_of' pc

def assert_of {p q} {c : code p q} : option (current c) → σ → Prop
  | none := q
  | (some pc) := assert_of' pc

local attribute [instance] classical.prop_decidable

noncomputable def next_assert' : Π {p q} {c : code p q}, current c → σ → σ → Prop
  | ._ .(q) ._ (current.action _ q _ _) := λ _, q
  | ._ ._ ._ (current.seq_left  _ _ _ _ _ pc) := next_assert' pc
  | ._ ._ ._ (current.seq_right _ _ _ _ _ pc) := next_assert' pc
  | .(p) .(q) ._ (current.ite_cond  p t pa pb q _ _ _)  := λ s, if t s then pa else pb
  | ._ ._ ._ (current.ite_left  _ _ _ _ _ _ _ _ pc) := next_assert' pc
  | ._ ._ ._ (current.ite_right _ _ _ _ _ _ _ _ pc) := next_assert' pc
  | .(inv) .(q) ._ (current.while_cond p inv q _ t _)  := λ s, if t s then p else q
  | ._ ._ ._ (current.while_body _ _ _ _ _ _ pc) := next_assert' pc

noncomputable def next_assert {p q} {c : code p q} : option (current c) → σ → σ → Prop
  | none := λ _, q
  | (some pc) := next_assert' pc

def first : Π {p q} (c : code p q), option (current c)
  | ._ ._ (code.skip p) := none
  | ._ ._ (code.action p _ _ l) := some $ current.action _ _ _ _
  | .(p) .(r) (@code.seq ._ ._ p q r c₀ c₁) :=
        seq_left c₁ <$> first _
    <|> seq_right _ <$> first _
  | ._ ._ (@if_then_else ._ ._ p _ _ _ _ c b₀ b₁) :=
    some $ ite_cond _ _ _ _ _
  | ._ ._ (@code.while ._ ._ _ _ _ _ c b) :=
    some $ while_cond _ _ _ _

noncomputable def next' (s : σ) : ∀ {p q} {c : code p q}, current c → option (current c)
  | ._ ._ ._ (current.action p q _ l) := none
  | ._ ._ ._ (current.seq_left _ _ _ c₀ c₁ cur₀) :=
        seq_left c₁ <$> next' cur₀
    <|> seq_right c₀ <$> first c₁
  | ._ ._ ._ (current.seq_right _ _ _ c₀ c₁ cur₁) :=
        seq_right _ <$> next' cur₁
  | .(p) .(q) ._ (current.ite_cond p c pa pb q _ b₀ b₁) :=
      if c s
         then ite_left _ _ _ _ <$> first b₀
         else ite_right _ _ _ _ <$> first b₁
  | ._ ._ ._ (current.ite_left _ _ _ _ _ _ b₀ b₁ cur₀) :=
      ite_left _ _ _ b₁ <$> next' cur₀
  | ._ ._ ._ (current.ite_right _ _ _ _ _ _ b₀ b₁ cur₁) :=
      ite_right _ _ _ _ <$> next' cur₁
  | .(inv) .(q) ._ (current.while_cond p inv q ds c b) :=
      if c s
      then while_body q ds c <$> first b <|> some (while_cond _ ds _ b)
      else none
  | ._ ._ ._ (current.while_body _ _ q _ c b cur) :=
          while_body q _ c <$> next' cur
      <|> some (while_cond _ _ _ b)

noncomputable def next (s : σ) {p q : pred} {c : code p q}
: option (current c) → option (current c)
  | (some pc) := next' s pc
  | none := none

inductive subtree {p q : pred} (c : code p q) : ∀ {p' q' : pred}, code p' q' → Type
  | rfl {} : subtree c
  | seq_left  : ∀ (p' q' r) (c₀ : code p' q') (c₁ : code q' r),
    subtree c₀ →
    subtree (code.seq c₀ c₁)
  | seq_right : ∀ (p' q' r) (c₀ : code p' q') (c₁ : code q' r),
    subtree c₁ →
    subtree (code.seq c₀ c₁)
  | ite_left  : ∀ (ds t p' pa pb q') (c₀ : code pa q') (c₁ : code pb q'),
    subtree c₀ →
    subtree (code.if_then_else p' ds t c₀ c₁)
  | ite_right : ∀ (ds t p' pa pb q') (c₀ : code pa q') (c₁ : code pb q'),
    subtree c₁ →
    subtree (code.if_then_else p' ds t c₀ c₁)
  | while : ∀ (ds t p' q' inv) (c' : code q' inv),
    subtree c' →
    subtree (code.while p' ds t c')

set_option eqn_compiler.lemmas false
def within' {p q : pred} {c : code p q}
: ∀ {p' q'} {c' : code p' q'} (P : subtree c c') (pc : current c'), bool
  | ._ ._ ._ subtree.rfl pc := tt
  | ._ ._ ._ (subtree.seq_left p' q' r' c₀ c₁ P)
             (current.seq_left ._ ._ ._ ._ ._ pc) := within' P pc
  | ._ ._ ._ (subtree.seq_left p' q' r' c₀ c₁ P)
             (current.seq_right ._ ._ ._ ._ ._ pc) := ff
  | ._ ._ ._ (subtree.seq_right p' q' r' c₀ c₁ P)
             (current.seq_left ._ ._ ._ ._ ._ pc) := ff
  | ._ ._ ._ (subtree.seq_right p' q' r' c₀ c₁ P)
             (current.seq_right ._ ._ ._ ._ ._ pc) := within' P pc
  | ._ ._ ._ (subtree.ite_left ds t p' pa pb q' c₀ c₁ P)
             (current.ite_left ._ ._ ._ ._ ._ ._ ._ ._ pc) := within' P pc
  | ._ ._ ._ (subtree.ite_left ds t p' pa pb q' c₀ c₁ P)
             (current.ite_right ._ ._ ._ ._ ._ ._ ._ ._ pc) := ff
  | ._ ._ ._ (subtree.ite_left ds t p' pa pb q' c₀ c₁ P)
             (current.ite_cond ._ ._ ._ ._ ._ ._ ._ ._) := ff
  | ._ ._ ._ (subtree.ite_right ds t p' pa pb q' c₀ c₁ P)
             (current.ite_left ._ ._ ._ ._ ._ ._ ._ ._ pc) := ff
  | ._ ._ ._ (subtree.ite_right ds t p' pa pb q' c₀ c₁ P)
             (current.ite_right ._ ._ ._ ._ ._ ._ ._ ._ pc) := within' P pc
  | ._ ._ ._ (subtree.ite_right ds t p' pa pb q' c₀ c₁ P)
             (current.ite_cond ._ ._ ._ ._ ._ ._ ._ ._) := ff
  | ._ ._ ._ (subtree.while ds t p' q' inv c' P)
             (current.while_body ._ ._ ._ ._ ._ ._ pc) := within' P pc
  | ._ ._ ._ (subtree.while ds t p' q' inv c' P)
             (current.while_cond .(q') .(inv) .(p') .(ds) .(t) .(c')) := ff

def exit' {p q : pred} {c : code p q}
: ∀ {p' q'} {c' : code p' q'} (P : subtree c c'), option (current c')
  | ._ ._ ._ subtree.rfl := none
  | ._ ._ ._ (subtree.seq_left p' q' r' c₀ c₁ P)  :=
        (seq_left c₁ <$> exit' P)
    <|> (seq_right c₀ <$> first c₁)
  | ._ ._ ._ (subtree.seq_right p' q' r' c₀ c₁ P) :=
        seq_right c₀ <$> exit' P
  | ._ ._ ._ (subtree.ite_left  ds t p' pa pb q' c₀ c₁ P) :=
        ite_left p' t ds c₁ <$> exit' P
  | ._ ._ ._ (subtree.ite_right ds t p' pa pb q' c₀ c₁ P) :=
        ite_right p' t ds c₀ <$> exit' P
  | ._ ._ ._ (subtree.while ds t p' q' inv c' P)       :=
        (    while_body _ ds _ <$> exit' P
         <|> some (current.while_cond _ _ _ _ _ _))
set_option eqn_compiler.lemmas true

@[simp]
lemma exit'_rfl
: ∀ {p' q'} {c' : code p' q'}, exit' (subtree.rfl : subtree c' c') = none :=
by { intros, cases c' ; refl }

@[simp]
lemma exit'_seq_left {p' q' p q r : pred}
  {c : code p' q'} {c₀ : code p q} {c₁ : code q r}
  {P : subtree c c₀ }
: exit' (subtree.seq_left p q r c₀ c₁ P) =
  (     (seq_left c₁ <$> exit' P)
    <|> (seq_right c₀ <$> first c₁) ) :=
by refl

@[simp]
lemma exit'_seq_right {p' q' p q r : pred}
  {c : code p' q'} {c₀ : code p q} {c₁ : code q r}
  {P : subtree c c₁ }
: exit' (subtree.seq_right p q r c₀ c₁ P) =
  (seq_right c₀ <$> exit' P) :=
by refl

@[simp]
lemma exit'_ite_left {p' q' p pa pb q : pred}
  {ds} {t : pred}
  {c : code p' q'} {c₀ : code pa q} {c₁ : code pb q}
  {P : subtree c c₀ }
: exit' (subtree.ite_left ds t p pa pb q c₀ c₁ P) =
  ite_left p t ds c₁ <$> exit' P :=
by refl

@[simp]
lemma exit'_ite_right {p' q' p pa pb q : pred}
  {ds} {t : pred}
  {c : code p' q'} {c₀ : code pa q} {c₁ : code pb q}
  {P : subtree c c₁ }
: exit' (subtree.ite_right ds t p pa pb q c₀ c₁ P) =
  ite_right p t ds c₀ <$> exit' P :=
by refl

@[simp]
lemma exit'_while {p' q' p inv q : pred}
  {ds} {t : pred}
  {c : code p' q'} {c' : code p inv}
  {P : subtree c c' }
: exit' (subtree.while ds q t p inv c' P) =
  (    while_body t ds q <$> exit' P
   <|> some (current.while_cond _ _ _ _ _ _)) :=
by refl

lemma within'_seq_left {p' q' p q r : pred}
  {c : code p' q'} {c₀ : code p q} {c₁ : code q r}
  {P : subtree c c₀ }
  {pc : current (code.seq c₀ c₁)}
:   within' (subtree.seq_left p q r c₀ c₁ P) pc
  ↔ (∃ pc₀, within' P pc₀ ∧ pc = current.seq_left p q r c₀ c₁ pc₀) :=
begin
  cases pc with pc,
  { split ; intro h,
    { existsi a,
      split, apply h, refl },
    { cases h with pc₀ h, cases h with h₀ h₁,
      rw h₁, apply h₀ }, },
  { split ; intro h,
    { cases h },
    { cases h with pc₀ h, cases h with h₀ h₁,
      cases h₁, } }
end

lemma within'_seq_right {p' q' p q r : pred}
  {c : code p' q'} {c₀ : code p q} {c₁ : code q r}
  {P : subtree c c₁ }
  {pc : current (code.seq c₀ c₁)}
:   within' (subtree.seq_right p q r c₀ c₁ P) pc
  ↔ (∃ pc₁, within' P pc₁ ∧ pc = current.seq_right p q r c₀ c₁ pc₁) :=
begin
  cases pc with pc,
  { split ; intro h,
    { cases h },
    { cases h with pc₀ h, cases h with h₀ h₁,
      cases h₁, } },
  { split ; intro h,
    { existsi a,
      split, apply h, refl },
    { cases h with pc₀ h, cases h with h₀ h₁,
      rw h₁, apply h₀ }, },
end

@[simp]
lemma within'_ite_left {p' q' p pa pb q : pred}
  {ds} {t : pred}
  {c : code p' q'} {c₀ : code pa q} {c₁ : code pb q}
  {P : subtree c c₀ }
  {pc : current _}
:   within' (subtree.ite_left ds t p pa pb q c₀ c₁ P) pc
  ↔ ∃ pc₀, within' P pc₀ ∧ pc = current.ite_left _ _ _ _ _ _ c₀ c₁ pc₀ :=
begin
  cases pc with pc,
  { split ; intro h,
    { cases h },
    { cases h with pc₀ h, cases h with h₀ h₁,
      cases h₁, } },
  { split ; intro h,
    { existsi a,
      split, apply h, refl },
    { cases h with pc₀ h, cases h with h₀ h₁,
      rw h₁, apply h₀ }, },
  { split ; intro h,
    { cases h },
    { cases h with pc₀ h, cases h with h₀ h₁,
      cases h₁, } }
end

@[simp]
lemma within'_ite_right {p' q' p pa pb q : pred}
  {ds} {t : pred}
  {c : code p' q'} {c₀ : code pa q} {c₁ : code pb q}
  {P : subtree c c₁ }
  {pc : current _}
:   within' (subtree.ite_right ds t p pa pb q c₀ c₁ P) pc
  ↔ ∃ pc₁, within' P pc₁ ∧ pc = current.ite_right _ _ _ _ _ _ c₀ c₁ pc₁ :=
begin
  cases pc with pc,
  { split ; intro h,
    { cases h },
    { cases h with pc₀ h, cases h with h₀ h₁,
      cases h₁, } },
  { split ; intro h,
    { cases h },
    { cases h with pc₀ h, cases h with h₀ h₁,
      cases h₁, } },
  { split ; intro h,
    { existsi a,
      split, apply h, refl },
    { cases h with pc₀ h, cases h with h₀ h₁,
      rw h₁, apply h₀ }, },
end

@[simp]
lemma within'_while {p' q' p inv q : pred}
  {ds} {t : pred}
  {c : code p' q'} {c' : code p inv}
  {P : subtree c c' }
  {pc : current _}
:   within' (subtree.while ds q t p inv c' P) pc
  ↔ ∃ pc', within' P pc' ∧ pc = current.while_body _ _ _ _ _ c' pc' :=
begin
  split ; intro h,
  { cases pc,
    { cases h },
    { existsi a, split,
      { apply h },
      { refl } } },
  { cases h with pc' h, cases h with h₀ h₁,
    subst pc, apply h₀ }
end

def counter {p q ds l}
: ∀ {p' q'} {c' : code p' q'}, subtree (code.action p q ds l) c' → current c'
  | ._ ._ ._ subtree.rfl := current.action _ _ _ _
  | ._ ._ ._ (subtree.seq_left p q r c₀ c₁ P) :=
    current.seq_left _ _ _ _ _ (counter P)
  | ._ ._ ._ (subtree.seq_right p q r c₀ c₁ P) :=
    current.seq_right _ _ _ _ _ (counter P)
  | ._ ._ ._ (subtree.ite_left ds p t pa pb q c₀ c₁ P) :=
    current.ite_left _ _ _ _ _ _ _ _ (counter P)
  | ._ ._ ._ (subtree.ite_right ds p t pa pb q c₀ c₁ P) :=
    current.ite_right _ _ _ _ _ _ _ _ (counter P)
  | ._ ._ ._ (subtree.while p t inv q c₀ c₁ P) :=
    current.while_body _ _ _ _ _ _ (counter P)

def within {p q : pred} {c : code p q} {p' q'} {c' : code p' q'} (P : subtree c c')
: option (current c') → Prop
  | (some pc) := within' P pc ∨ exit' P = some pc
  | none := exit' P = none

def exits {p q : pred} {c : code p q} {p' q'} {c' : code p' q'} (P : subtree c c')
  (pc : option (current c')) : Prop :=
exit' P = pc


lemma within_rfl {p q : pred} {c : code p q}
  (pc : option (current c))
: within subtree.rfl pc :=
begin
  cases pc with pc,
  { dunfold within,
    cases c ; refl },
  { dunfold within,
    left, cases c ; apply rfl }
end

end
