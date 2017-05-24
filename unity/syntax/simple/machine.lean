
import unity.logic

import unity.models.simple
import unity.syntax.simple.expr

import util.data.functor

universe variables u₀ u₁ u₂
variables {α : Type u₀} {β β' : Type u₁} {γ : Type u₂}
variables var : Type

namespace ast.simple

variables (var)

inductive proof (n : ℕ)
  | ref : fin n → prop var → prop var → proof
  | basis {} : prop var → prop var → proof
  | trans : prop var → proof → proof → prop var → proof
  | mono : prop var → proof → prop var → proof
--  | cancellation : prop var → proof → proof → prop var → proof
--  | psp : prop var → proof → prop var → proof

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

inductive {u} primed (var : Type u) : Type u
  | primed : var → primed
  | unprimed : var → primed

variable {var}

@[inline]
def {u u'} post {f : Type u → Type u'} {var : Type u} [functor f] : f var → f (primed var) :=
has_map.map primed.primed

@[inline]
def {u u'} pre {f : Type u → Type u'} {var : Type u} [functor f] : f var → f (primed var) :=
has_map.map primed.unprimed

def establish_inv (p : prog var) (l : p.inv_lbl) : sequent :=
  { lbl := var
  , var := var
  , asm := λ v, prop.bin rel.eq (expr.var v) (from_empty <$> (p.first v)) /- from_empty <$> p.first v -/
  , goal := p.inv l }

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
  { unfold has_map.map expr.map eval,
    unfold has_map.map at ih_1 ih_2,
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
  ; unfold post has_map.map expr.map eval,
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
  ; unfold post has_map.map prop.fmap valid
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
  unfold post has_map.map prop.fmap valid at h,
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
-- begin
-- --  destruct p,
-- --  intros inv_lbl inv tr_lbl tr first step liveness Hp,
-- --  pose liveness := p.liveness.snd,
-- --  assert Hliveness : p.liveness.snd = liveness, refl,
-- --  destruct p.liveness,
-- --  intros n liveness Hliveness,
-- --  assert Hliveness : p.liveness.snd = liveness,
-- --  unfold prog.properties prog.liveness proof_list.to_list sigma.snd at h₃,
-- --  rw [Hliveness] at h₃,
--   induction (p.liveness.snd) with k l ls,
--   { unfold proof_list.to_list' at h₃,
--     cases h₃, },
--   cases h₃ with HH HH,
--   { simp at HH,
--     unfold check_liveness at h₂,
--     induction l with r PP QQ,
--     {  },
--     {  },
--     {  }, },
--   {  },
-- end

end meaning

end semantics

end ast.simple
