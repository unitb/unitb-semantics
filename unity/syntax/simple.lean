
import unity.logic

import unity.models.simple

variables var : Type

def {u} from_empty {α : Type u} (x : empty) : α :=
match x with
end

namespace ast.simple

inductive oper : Type
  | plus  : oper
  | minus : oper
  | times : oper

inductive expr : Type
  | var : var → expr
  | lit {} : ℕ → expr
  | oper : oper → expr → expr → expr

def expr.fmap {α β : Type} (f : α → β) : expr α → expr β
  | (expr.var v) := expr.var (f v)
  | (expr.lit x) := expr.lit x
  | (expr.oper o e₀ e₁) := expr.oper o (expr.fmap e₀) (expr.fmap e₁)

instance : functor expr :=
{ map := @expr.fmap
, id_map :=
  begin
    intros,
    induction x,
    { refl }, { refl },
    { unfold expr.fmap,
      rw [ih_1,ih_2] },
  end
, map_comp :=
  begin
    intros,
    induction x,
    { refl }, { refl },
    { unfold expr.fmap,
      rw [ih_1,ih_2] },
  end }

inductive rel : Type
  | le : rel
  | eq : rel
  | gt : rel

inductive connective : Type
  | and : connective
  | or  : connective
  | imp : connective
  | eqv : connective

inductive prop : Type
  | true {} : prop
  | false {} : prop
  | odd : expr var → prop
  | bin : rel → expr var → expr var → prop
  | not : prop → prop
  | cnt : connective → prop → prop → prop

def prop.fmap {α β : Type} (f : α → β) : prop α → prop β
  | prop.true  := prop.true
  | prop.false := prop.false
  | (prop.odd e) := prop.odd (f <$> e)
  | (prop.bin r e₀ e₁) := prop.bin r (f <$> e₀) (f <$> e₁)
  | (prop.not e) := prop.not $ prop.fmap e
  | (prop.cnt c p₀ p₁) := prop.cnt c (prop.fmap p₀) (prop.fmap p₁)

instance functor_prop : functor prop :=
{ map := @prop.fmap
, id_map :=
  begin
    intros,
    induction x
    ; try { refl }
    ; unfold prop.fmap
    ; repeat { rw [functor.id_map] }
    ; rw ih_1
    ; rw ih_2
  end
, map_comp :=
  begin
    intros,
    induction x
    ; try { refl }
    ; unfold prop.fmap,
    { rw [functor.map_comp] },
    { repeat { rw [functor.map_comp g h] }, },
    { rw ih_1, },
    { rw [ih_1,ih_2] },
  end }

structure prog :=
  (inv_lbl : Type)
  (inv : inv_lbl → prop var)
  (tr_lbl : Type)
  (tr : tr_lbl → prop var)
  (first : var → expr empty)
  (step : var → expr var)

structure sequent :=
  (lbl : Type)
  (var : Type)
  (asm : lbl → prop var)
  (goal : prop var)

inductive primed
  | primed : var → primed
  | unprimed : var → primed

variable {var}

@[inline]
def post {f : Type → Type} [functor f] : f var → f (primed var) :=
functor.map primed.primed

@[inline]
def pre {f : Type → Type} [functor f] : f var → f (primed var) :=
functor.map primed.unprimed

def establish_inv (p : prog var) (l : p.inv_lbl) : sequent :=
  { lbl := var
  , var := var
  , asm := λ v, prop.bin rel.eq (expr.var v) (from_empty <$> p.first v)
  , goal := p.inv l }

def maintain_inv_asm (p : prog var) : p.inv_lbl ⊕ var → prop (primed var)
  | (sum.inr x) := prop.bin rel.eq (post $ expr.var x) (pre $ p.step x)
  | (sum.inl x) := pre $ p.inv x

def maintain_inv (p : prog var) (l : p.inv_lbl) : sequent :=
  { lbl := p.inv_lbl ⊕ var
  , var := primed var
  , asm := maintain_inv_asm p
  , goal := post (p.inv l) }

def transient_asm (p : prog var) (e : prop var) : option (p.inv_lbl ⊕ var) → prop (primed var)
  | (some x) := maintain_inv_asm p x
  | none := pre e

def is_transient (p : prog var) (l : p.tr_lbl) : sequent :=
  { lbl := option (p.inv_lbl ⊕ var)
  , var := primed var
  , asm := transient_asm p (p.tr l)
  , goal := post (prop.not $ p.tr l) }

namespace semantics

variable (var)

def state_t : Type := var → ℕ

variable {var}

def empty_s : state_t empty :=
from_empty

def apply : oper → ℕ → ℕ → ℕ
  | oper.plus i j := i + j
  | oper.minus i j := i - j
  | oper.times i j := i * j

def eval (s : state_t var) : expr var → ℕ
  | (expr.var v) := s v
  | (expr.lit n) := n
  | (expr.oper op e₀ e₁) := apply op (eval e₀) (eval e₁)

open nat

def odd : ℕ → Prop
  | 0 := true
  | 1 := false
  | (succ (succ n)) := odd n

def rel.meaning : rel → ℕ → ℕ → Prop
  | rel.le e₀ e₁ := e₀ ≤ e₁
  | rel.eq e₀ e₁ := e₀ = e₁
  | rel.gt e₀ e₁ := e₀ > e₁

def connective.meaning : connective → Prop → Prop → Prop
  | connective.and p₀ p₁ := p₀ ∧ p₁
  | connective.or p₀ p₁  := p₀ ∨ p₁
  | connective.imp p₀ p₁ := p₀ → p₁
  | connective.eqv p₀ p₁ := p₀ ↔ p₁

def valid {var : Type} (s : state_t var) : prop var → Prop
  | prop.true := true
  | prop.false := false
  | (prop.odd e) := odd (eval s e)
  | (prop.bin op e₀ e₁) := rel.meaning op (eval s e₀) (eval s e₁)
  | (prop.not e) := ¬ valid e
  | (prop.cnt c p₀ p₁) := connective.meaning c (valid p₀) (valid p₁)

def holds (s : sequent) : Prop :=
∀ σ : state_t s.var, (∀ l, valid σ (s.asm l)) → valid σ s.goal

def meaning_first (p : ast.simple.prog var) : state_t var :=
λ v, eval empty_s (p.first v)

def meaning_next (p : ast.simple.prog var) (s : state_t var) : state_t var :=
λ v, eval s (p.step v)

def meaning (p : ast.simple.prog var) : simple.prog (state_t var) :=
  { first := meaning_first p
  , step  := meaning_next p }

def state_t' (p : ast.simple.prog var) := { s : state_t var // ∀ l, valid s (p.inv l) }

lemma eval_from_empty (e : expr empty) (s : state_t var)
: eval s (from_empty <$> e) = eval empty_s e :=
begin
  induction e,
  { cases a },
  { refl },
  { unfold functor.map expr.fmap eval,
    unfold functor.map at ih_1 ih_2,
    rw [ih_1,ih_2] },
end

def pair {α : Type} (s₀ s₁ : state_t α) : state_t (primed α)
 | (primed.unprimed x) := s₀ x
 | (primed.primed x) := s₁ x

lemma eval_trade {var' : Type} (s : state_t var') (p : expr var) (f : var → var')
: eval (s ∘ f) p = eval s (f <$> p) :=
begin
  induction p
  ; try { refl }
  ; unfold post fmap functor.map expr.fmap eval,
  rw [ih_1,ih_2], refl
end

lemma pair_primed (s s' : state_t var)
: pair s s' ∘ primed.primed = s' :=
by { apply funext, intro x, refl }

lemma pair_unprimed (s s' : state_t var)
: pair s s' ∘ primed.unprimed = s :=
by { apply funext, intro x, refl }

lemma eval_pair_post (s s' : state_t var) (p : expr var)
: eval (pair s s') (post p) = eval s' p :=
by { unfold post, rw [-eval_trade,pair_primed] }

lemma eval_pair_pre (s s' : state_t var) (p : expr var)
: eval (pair s s') (pre p) = eval s p :=
by { unfold pre, rw [-eval_trade,pair_unprimed] }

lemma valid_trade {var' : Type} (s : state_t var') (p : prop var) (f : var → var')
: valid (s ∘ f) p = valid s (f <$> p) :=
begin
  induction p
  ; try { refl }
  ; unfold post fmap functor.map prop.fmap valid
  ; repeat { rw [eval_trade _ _ f] },
  { refl },
  { refl },
  { rw ih_1, refl },
  { rw [ih_1,ih_2], refl },
end

lemma valid_pair_post (s s' : state_t var) (p : prop var)
: valid (pair s s') (post p) = valid s' p :=
by { unfold post, rw [-valid_trade,pair_primed] }

lemma valid_pair_pre (s s' : state_t var) (p : prop var)
: valid (pair s s') (pre p) = valid s p :=
by { unfold pre, rw [-valid_trade,pair_unprimed] }

section meaning

variable (p : ast.simple.prog var)
variables h₀ : ∀ l, holds (establish_inv p l)
variables h₁ : ∀ l, holds (maintain_inv p l)

section meaning_first_valid

include h₀

lemma meaning_first_valid (l : p.inv_lbl)
: valid (meaning_first p) (p.inv l) :=
begin
  unfold meaning_first,
  unfold establish_inv at h₀,
  apply h₀,
  unfold sequent.lbl sequent.asm,
  intro l',
  unfold valid eval,
  rw eval_from_empty,
  unfold rel.meaning,
  refl,
end

end meaning_first_valid

section meaning_next_valid

include h₁

lemma meaning_next_valid (s : state_t var) (inv : ∀ l, valid s (p.inv l))
: ∀ (l : p.inv_lbl), valid (meaning_next p s) (p.inv l) :=
begin
  intro l,
  unfold holds maintain_inv
     sequent.goal sequent.asm sequent.lbl sequent.var at h₁,
  rw -valid_pair_post s,
  apply h₁ l,
  clear l, intro l,
  cases l with l l
  ; unfold maintain_inv_asm,
  { rw valid_pair_pre,
    apply inv, },
  { unfold valid,
    rw [eval_pair_post,eval_pair_pre],
    unfold rel.meaning,
    refl, }
end

end meaning_next_valid

def meaning' : simple.prog (state_t' p) :=
  { first := ⟨meaning_first p,meaning_first_valid p h₀⟩
  , step := λ s, ⟨meaning_next p s.val, meaning_next_valid p h₁ s.val s.property⟩  }

def valid' (e : prop var) (s : state_t' p) : Prop := valid s.val e

lemma transient_is_sound (l : p.tr_lbl)
  (h : holds (is_transient p l))
: unity.transient (meaning' p h₀ h₁) (valid' p (p.tr l)) :=
begin
  unfold valid',
  intros σ h',
  unfold valid' meaning' simple.prog.step subtype.val,
  unfold valid' meaning' simple.prog.step subtype.val at h',
  unfold is_transient holds sequent.var sequent.lbl sequent.asm sequent.goal at h,
  rw -valid_pair_post σ.val,
  unfold post functor.map prop.fmap valid at h,
  apply h,
  intro l, cases l with l
  ; unfold transient_asm,
  { rw valid_pair_pre, apply h' },
  cases l with l v ; unfold maintain_inv_asm,
  { rw valid_pair_pre, apply σ.property },
  { unfold valid rel.meaning,
    rw [eval_pair_post,eval_pair_pre],
    unfold eval, refl, }
end

end meaning

end semantics

end ast.simple
