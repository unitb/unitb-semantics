
import unitb.logic

import unitb.models.simple

import util.data.functor

universe variables u₀ u₁ u₂
variables {α : Type u₀} {β β' : Type u₁} {γ : Type u₂}
variables var : Type

def {u} from_empty {α : Type u} (x : empty) : α :=
match x with
end

-- Todo:
-- * Well-definedness
-- * variables of different types

namespace ast.simple

inductive oper : Type
  | plus  : oper
  | minus : oper
  | times : oper

inductive expr : Type
  | var : var → expr
  | lit {} : ℕ → expr
  | oper : oper → expr → expr → expr

namespace expr

def map {α β : Type} (f : α → β) : expr α → expr β
  | (expr.var v) := expr.var (f v)
  | (expr.lit x) := expr.lit x
  | (expr.oper o e₀ e₁) := expr.oper o (map e₀) (map e₁)

lemma id_map {α} (x : expr α) : map id x = x :=
begin
  induction x
  ; dunfold map,
  { refl }, { refl },
  { rw [ih_1,ih_2] },
end

lemma map_comp {α β γ : Type} (g : α → β) (h : β → γ) (x : expr α)
: expr.map (h ∘ g) x = expr.map h (expr.map g x) :=
begin
  revert β γ g h,
  induction x ; intros β γ g h
  ; dunfold map,
  { refl }, { refl },
  { rw [ih_1,ih_2] },
end

end expr

instance : functor expr :=
{ map := @expr.map
, id_map := @expr.id_map
, map_comp := @expr.map_comp }

namespace expr

def bind {α β : Type} : expr α → (α → expr β) → expr β
  | (expr.var x) f := f x
  | (expr.lit v) _ := expr.lit v
  | (expr.oper o e₀ e₁) f := expr.oper o (bind e₀ f) (bind e₁ f)

local infixl ` >>= ` := bind

lemma pure_bind {α β : Type} (x : α) (f : α → expr β)
: expr.var x >>= f = f x :=
by refl

lemma bind_pure_comp_eq_map {α β : Type} (f : α → β) (x : expr α)
: x >>= expr.var ∘ f = f <$> x :=
begin
  induction x with v v op e₀ e₁ ih1 ih2 ; try { refl },
  { unfold bind,
    rw [ih1,ih2], refl }
end

lemma bind_assoc {α β γ : Type} (x : expr α) (f : α → expr β) (g : β → expr γ)
: x >>= f >>= g = x >>= λ (x : α), f x >>= g :=
begin
  induction x with v v op e₀ e₁ ih1 ih2 ; try { refl },
  { unfold bind,
    rw [ih1,ih2], },
end

end expr

instance : monad expr :=
{ map := @expr.map
, id_map := @expr.id_map
, pure := @expr.var
, bind := @expr.bind
, pure_bind := @expr.pure_bind
, bind_pure_comp_eq_map := @expr.bind_pure_comp_eq_map
, bind_assoc := @expr.bind_assoc }

inductive rel : Type
  | le : rel
  | eq : rel
  | gt : rel

inductive connective : Type
  | and : connective
  | or  : connective
  | imp : connective
  | eqv : connective

inductive prop : Type → Type 2
  | true  : ∀ {v}, prop v
  | false : ∀ {v}, prop v
  | odd : ∀ {v}, expr v → prop v
  | bin : ∀ {v}, rel → expr v → expr v → prop v
  | not : ∀ {v}, prop v → prop v
  | cnt : ∀ {v}, connective → prop v → prop v → prop v
  | all : ∀ {v}, prop (option v) → prop v

def prop.fmap : ∀ {α : Type} {β : Type}, (α → β) → prop α → prop β
  | α β f prop.true  := prop.true
  | α β f prop.false := prop.false
  | α β f (prop.odd e) := prop.odd (f <$> e)
  | α β f (prop.bin r e₀ e₁) := prop.bin r (f <$> e₀) (f <$> e₁)
  | α β f (prop.not e) := prop.not $ prop.fmap f e
  | α β f (prop.cnt c p₀ p₁) := prop.cnt c (prop.fmap f p₀) (prop.fmap f p₁)
  | α β f (prop.all e) := prop.all (prop.fmap (has_map.map f) e)

instance functor_prop : functor prop :=
{ map := @prop.fmap
, id_map :=
  begin
    intros,
    induction x
    ; try { refl }
    ; unfold prop.fmap
    ; repeat { rw [functor.id_map] },
    { rw ih_1 },
    { rw [ih_1,ih_2] },
    { rw [functor.id_map',ih_1] }
  end
, map_comp :=
  begin
    intros, revert β γ,
    induction x ; intros β γ g h
    ; try { refl }
    ; unfold prop.fmap,
    { rw [functor.map_comp] },
    { repeat { rw [functor.map_comp g h] }, },
    { rw ih_1, },
    { rw [ih_1,ih_2] },
    { rw [functor.map_comp',ih_1] },
  end }

variables {var}

def prop.and : prop var → prop var → prop var :=
prop.cnt connective.and

def prop.implies : prop var → prop var → prop var :=
prop.cnt connective.imp

variable (var)

structure sequent : Type 2 :=
  (lbl : Type)
  (var : Type)
  (asm : lbl → prop var)
  (goal : prop var)

def add (x : α) (s : β → α) : option β → α
  | none := x
  | (some v) := s v

lemma add_comp (x : α)  (s : β → α) (f : β' → β)
: add x (s ∘ f) = add x s ∘ has_map.map f :=
begin
  apply funext, intro a, cases a ; refl,
end

def union (x : α → γ) (y : β → γ) : α ⊕ β → γ
 | (sum.inl i) := x i
 | (sum.inr i) := y i

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

def valid : ∀ {var : Type} (s : state_t var), prop var → Prop
  | _ s prop.true := true
  | _ s prop.false := false
  | _ s (prop.odd e) := odd (eval s e)
  | _ s (prop.bin op e₀ e₁) := rel.meaning op (eval s e₀) (eval s e₁)
  | var s (prop.not e) := ¬ valid s e
  | _ s (prop.cnt c p₀ p₁) := connective.meaning c (valid s p₀) (valid s p₁)
  | _ s (prop.all e) := ∀ x, valid (add x s) e

def holds (s : sequent) : Prop :=
∀ σ : state_t s.var, (∀ l, valid σ (s.asm l)) → valid σ s.goal

end semantics

end ast.simple
