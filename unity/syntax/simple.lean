
import unity.logic

import unity.models.simple

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
  ; unfold map,
  { refl }, { refl },
  { rw [ih_1,ih_2] },
end

lemma map_comp {α β γ : Type} (g : α → β) (h : β → γ) (x : expr α)
: expr.map (h ∘ g) x = expr.map h (expr.map g x) :=
begin
  revert β γ g h,
  induction x ; intros β γ g h
  ; unfold map,
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
  | α β f (prop.all e) := prop.all (prop.fmap (fmap f) e)

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

variables (var)

inductive proof (n : ℕ)
  | ref : fin n → prop var → prop var → proof
  | basis {} : prop var → prop var → proof
  | trans : prop var → proof → proof → prop var → proof
  | mono : prop var → proof → prop var → proof

open nat

def bump {var : Type} {n : ℕ} : proof var n → proof var (succ n)
  | (proof.ref ⟨i,P⟩ p q) := (proof.ref ⟨succ i,succ_lt_succ P⟩ p q)
  | (proof.basis p q) := (proof.basis p q)
  | (proof.trans p P₀ P₁ q) := (proof.trans p (bump P₀) (bump P₁) q)
  | (proof.mono p P₀ q) := (proof.mono p (bump P₀) q)


inductive proof_list : ℕ → Type 2
  | nil {} : proof_list 0
  | cons : ∀ {n}, proof var n → proof_list n → proof_list (succ n)

variable {var}

def {u} proof_list.to_list' {α : Type u}
: ∀ {n : ℕ}, proof_list var n → (∀ {n}, proof var n → proof_list var n → α) → list α
  | .(0) proof_list.nil f := list.nil
  | .(succ _) (@proof_list.cons .(var) n p ps) f := f p ps :: proof_list.to_list' ps @f

def {u} proof_list.to_list {α : Type u} {n : ℕ}
  (ls : proof_list var n)
  (f : ∀ {n}, proof var n → α)
: list α :=
proof_list.to_list' ls (λ n p _, f p)

def proof_list.nth : ∀ {n : ℕ}, proof_list var n → fin n → proof var n
  | 0 proof_list.nil ⟨i,P⟩ := absurd P (not_lt_zero i)
  | (succ .(_)) (@proof_list.cons .(var) n p ps) ⟨0,P⟩ := bump p
  | (succ .(_)) (@proof_list.cons .(var) n p ps) ⟨(succ i),P⟩ :=
    bump $ proof_list.nth ps ⟨i,lt_of_succ_lt_succ P⟩

variable (var)

structure prog : Type 2 :=
  (inv_lbl : Type)
  (inv : inv_lbl → prop var)
  (tr_lbl : Type)
  (tr : tr_lbl → prop var)
  (first : var → expr empty)
  (step : var → expr var)
  (liveness : Σ n, proof_list var n)

structure property :=
  (p : prop var)
  (q : prop var)

variable {var}

def proof.prop_of {n} : proof var n → property var
 | (proof.ref r p q) := ⟨p,q⟩
 | (proof.basis p q) := ⟨p,q⟩
 | (proof.trans p P₀ P₁ q) := ⟨p,q⟩
 | (proof.mono p P₀ q) := ⟨p,q⟩

def prog.properties (p : prog var) : list (property var) :=
p.liveness.snd.to_list (@proof.prop_of var)

variable (var)

structure sequent : Type 2 :=
  (lbl : Type)
  (var : Type)
  (asm : lbl → prop var)
  (goal : prop var)

inductive {u} primed (var : Type u) : Type u
  | primed : var → primed
  | unprimed : var → primed

variable {var}

@[inline]
def {u u'} post {f : Type u → Type u'} {var : Type u} [functor f] : f var → f (primed var) :=
functor.map primed.primed

@[inline]
def {u u'} pre {f : Type u → Type u'} {var : Type u} [functor f] : f var → f (primed var) :=
functor.map primed.unprimed

def establish_inv (p : prog var) (l : p.inv_lbl) : sequent :=
  { lbl := var
  , var := var
  , asm := λ v, prop.bin rel.eq (expr.var v) (from_empty <$> (p.first v)) /- from_empty <$> p.first v -/
  , goal := p.inv l }

def add (x : α) (s : β → α) : option β → α
  | none := x
  | (some v) := s v

lemma add_comp (x : α)  (s : β → α) (f : β' → β)
: add x (s ∘ f) = add x s ∘ fmap f :=
begin
  apply funext, intro a, cases a ; refl,
end

def union (x : α → γ) (y : β → γ) : α ⊕ β → γ
 | (sum.inl i) := x i
 | (sum.inr i) := y i

def action_asm (p : prog var) (v : var) : prop (primed var) :=
prop.bin rel.eq (post (expr.var v)) (pre $ p.step v)

def inv_act_asm (p : prog var) : p.inv_lbl ⊕ var → prop (primed var) :=
union (pre ∘ p.inv) (action_asm p)

def maintain_inv (p : prog var) (l : p.inv_lbl) : sequent :=
  { lbl := p.inv_lbl ⊕ var
  , var := primed var
  , asm := inv_act_asm p
  , goal := post (p.inv l) }


def entails (pp : prog var) (p q : prop var) : sequent :=
  { lbl := pp.inv_lbl
  , var := _
  , asm := pp.inv
  , goal := prop.implies p q }

def matches (pp : prog var) (prp : property var) (p q : prop var) : list sequent :=
[entails pp p prp.p, entails pp prp.q q]

def check_unless (pp : prog var) (p q : prop var) : sequent :=
  { lbl := option (pp.inv_lbl ⊕ var)
  , var := primed var
  , asm := add (pre $ p) (inv_act_asm pp)
  , goal := post q }

def check_transient (pp : prog var) (p : prop var) : sequent :=
  { lbl := option (pp.inv_lbl ⊕ var)
  , var := primed var
  , asm := add (pre $ p) (inv_act_asm pp)
  , goal := post (prop.not p) }

def check_proof (pp : prog var) {n} : proof var n → proof_list var n → list sequent
  | (proof.ref r p q) ps := matches pp (ps.nth r).prop_of p q
  | (proof.basis p q) ps := [check_unless pp p q, check_transient pp $ prop.and p (prop.not q)]
  | (proof.trans p P₀ P₁ q) ps := [ entails pp p P₀.prop_of.p
                                  , entails pp P₀.prop_of.q P₁.prop_of.p
                                  , entails pp P₁.prop_of.q q ]
                               ++ check_proof P₀ ps ++ check_proof P₁ ps
  | (proof.mono p P₀ q) ps := matches pp P₀.prop_of p q
                           ++ check_proof P₀ ps

def check_proof' (pp : prog var) : proof var 0 → list sequent
  | (proof.ref r p q) := r.elim0
  | (proof.basis p q) := [check_unless pp p q, check_transient pp $ prop.and p (prop.not q)]
  | (proof.trans p P₀ P₁ q) := [ entails pp p P₀.prop_of.p
                               , entails pp P₀.prop_of.q P₁.prop_of.p
                               , entails pp P₁.prop_of.q q ]
                            ++ check_proof' P₀ ++ check_proof' P₁
  | (proof.mono p P₀ q) := matches pp P₀.prop_of p q
                        ++ check_proof' P₀

def is_transient (p : prog var) (l : p.tr_lbl) : sequent :=
check_transient p $ p.tr l

def check_liveness (p : prog var) : list sequent :=
list.join $ p.liveness.snd.to_list' (@check_proof var p)

def flat_proof {n : ℕ} (t : fin n → proof var 0) : proof var n → proof var 0
  | (proof.ref r p q) := proof.mono p (t r) q
  | (proof.basis p q) := proof.basis p q
  | (proof.trans p P₀ P₁ q) := proof.trans p (flat_proof P₀) (flat_proof P₁) q
  | (proof.mono p P₀ q) := proof.mono p (flat_proof P₀) q

def flat_proof_list : ∀ {n}, proof_list var n → fin n → proof var 0
 | .(_) proof_list.nil i := fin.elim0 i
 | (succ .(n)) (@proof_list.cons .(_) n p ps) i :=
     let t := flat_proof_list ps in
     match i with
      | ⟨0,_⟩ :=  flat_proof t p
      | ⟨succ i,P⟩ := t ⟨i,lt_of_succ_lt_succ P⟩
     end

def flat_proof_list' {n} (ps : proof_list var n) : list (proof var 0) :=
array.to_list { data := flat_proof_list ps }

lemma flat_proof_list_cons {n : ℕ}
  (p : proof var n)
  (ps : proof_list var n)
:   flat_proof_list' (proof_list.cons p ps)
  = flat_proof (flat_proof_list ps) p :: flat_proof_list' ps :=
begin
  unfold flat_proof_list' array.to_list array.rev_iterate,
  admit
end

def check_liveness_flat (p : prog var) : list sequent :=
list.join $ list.map (@check_proof' var p) (flat_proof_list' p.liveness.snd)

lemma mem_check_liveness_iff_mem_check_liveness_flat
  (s : sequent)
  (p : prog var)
: s ∈ check_liveness p ↔ s ∈ check_liveness_flat p :=
begin
  unfold check_liveness check_liveness_flat,
  generalize (p.liveness) k,
  intro k, cases k with n ps,
  unfold sigma.snd,
  induction ps with k p ps IH,
  { refl, },
  { unfold proof_list.to_list' flat_proof_list' array.to_list
           array.rev_iterate array.rev_iterate_aux,
    admit, }
end

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
  { unfold functor.map expr.map eval,
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
  ; unfold post fmap functor.map expr.map eval,
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
  revert var',
  induction p ; intros var' s f
  ; try { refl }
  ; unfold post fmap functor.map prop.fmap valid
  ; repeat { rw [eval_trade _ _ f] },
  { refl },
  { refl },
  { rw ih_1, refl },
  { rw [ih_1,ih_2], refl },
  { rw [-iff_eq_eq],
    apply forall_congr, intro x,
    rw [add_comp,ih_1], refl, }
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
  ; unfold inv_act_asm ast.simple.union,
  { rw valid_pair_pre,
    apply inv, },
  { unfold valid action_asm,
    rw [eval_pair_post,eval_pair_pre],
    unfold rel.meaning,
    refl, }
end

end meaning_next_valid

def meaning' : simple.prog (state_t' p) :=
  { first := ⟨meaning_first p,meaning_first_valid p h₀⟩
  , step := λ s, ⟨meaning_next p s.val, meaning_next_valid p h₁ s.val s.property⟩  }

def valid' (e : prop var) (s : state_t' p) : Prop := valid s.val e

lemma transient_is_sound (q : prop var)
  (h : holds (check_transient p q))
: unity.transient (meaning' p h₀ h₁) (valid' p q) :=
begin
  unfold valid',
  intros σ h',
  unfold valid' meaning' simple.prog.step subtype.val,
  unfold valid' meaning' simple.prog.step subtype.val at h',
  unfold check_transient holds sequent.var sequent.lbl sequent.asm sequent.goal at h,
  rw -valid_pair_post σ.val,
  unfold post functor.map prop.fmap valid at h,
  apply h,
  intro l, cases l with l
  ; unfold ast.simple.add,
  { rw valid_pair_pre, apply h' },
  cases l with l v ; unfold inv_act_asm ast.simple.union action_asm,
  { rw valid_pair_pre, apply σ.property },
  { unfold valid rel.meaning,
    rw [eval_pair_post,eval_pair_pre],
    unfold eval, refl, }
end

lemma transient_is_sound' (l : p.tr_lbl)
  (h : holds (is_transient p l))
: unity.transient (meaning' p h₀ h₁) (valid' p (p.tr l)) :=
transient_is_sound _ h₀ h₁ _ h

variables h₂ : ∀ s, s ∈ check_liveness p → holds s
variables pp : property var
variables h₃ : pp ∈ p.properties

include h₂ h₃

lemma proof_is_sound
: valid' p pp.p ↦ valid' p pp.q in meaning' p h₀ h₁ :=
sorry
end meaning

end semantics

end ast.simple
