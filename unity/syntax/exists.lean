
import data.set

import unity.syntax.simple.expr

import util.data.traversable

universe variables u u₀ u₁ u₂
variables v : Type

open ast.simple

structure existential :=
  (lv : Type)
  (clauses : set (prop (lv ⊕ v)))

namespace ast.simple

def sum.map {α : Type u₀} {β β' : Type u₁} (f : β → β') : α ⊕ β → α ⊕ β'
  | (sum.inr x) := sum.inr (f x)
  | (sum.inl x) := sum.inl x

lemma sum.id_map {α : Type u₀} {β : Type u₁}
: ∀ (x : α ⊕ β), sum.map id x = x
 | (sum.inl _) := rfl
 | (sum.inr _) := rfl

lemma sum.map_comp {t : Type u₀} {α β γ : Type u₁} (g : α → β) (h : β → γ)
: ∀ (x : t ⊕ α),
  sum.map (h ∘ g) x = sum.map h (sum.map g x)
 | (sum.inl _) := rfl
 | (sum.inr _) := rfl

instance sum_functor {α : Type u₀} : functor (sum α) :=
 { map := @sum.map α
 , id_map := @sum.id_map α
 , map_comp := @sum.map_comp α }

end ast.simple

def existential.map {α β : Type} (f : α → β) : existential α → existential β
  | ⟨n,cs⟩ := ⟨n,has_map.map (has_map.map f) <$> cs⟩

lemma existential.id_map {α : Type} (x : existential α)
: existential.map id x = x :=
begin
  cases x with n cs,
  unfold existential.map,
  simp [functor.id_map',functor.id_map],
end

lemma existential.map_comp {α β γ : Type} (g : α → β) (h : β → γ) (x : existential α)
: existential.map (h ∘ g) x = existential.map h (existential.map g x) :=
begin
  cases x with n cs,
  unfold existential.map,
  rw [functor.map_comp' g h
     ,functor.map_comp' (has_map.map g) (has_map.map h)
     ,functor.map_comp (has_map.map $ has_map.map g) (has_map.map $ has_map.map h)],
end

instance : functor existential :=
  { map := @existential.map
  , id_map := @existential.id_map
  , map_comp := @existential.map_comp }

def list.has {α : Type u} (xs : list α) (x : α) := list.mem x xs

protected lemma list.map_has_aux {α : Type u} (xs ys : list α) (x : α)
: xs ++ [x] ++ ys = xs ++ x :: ys :=
sorry

def list.map_has' {α : Type u}
: ∀ (ys : list α) (xs : list α), list (subtype (list.has $ ys ++ xs))
  | _ [ ] := [ ]
  | ys (list.cons x xs) :=
     have H : list (subtype (list.has $ ys ++ [x] ++ xs)) = list (subtype (list.has $ ys ++ x :: xs)),
       by rw [list.map_has_aux],
     have H' : list.has (ys ++ x :: xs) x,
       by { apply list.mem_append_right, apply list.mem_cons_self },
     list.cons ⟨x,H'⟩ (cast H $ list.map_has' (ys ++ [x]) xs)
-- begin
--   apply list.cons,
--   { existsi x,
--     apply list.mem_append_right,
--     apply list.mem_cons_self },
--   { rw [-list.nil_append xs,-list.cons_append,-list.append_assoc],
--     apply list.map_has' (ys ++ [x]) xs, },
-- end

def list.map_has {α : Type u} [_inst_1 : functor list]
: ∀ (xs : list α), list (subtype (list.has xs)) :=
begin intro xs, rw [-list.nil_append xs], apply list.map_has' end

def list.map_has_nil {α : Type u} (xs : list α)
: (@list.nil α).map_has = [ ] :=
rfl

-- def list.map_has_cons {α : Type u} (x : α) (xs : list α)
-- : (list.cons x xs).map_has = list.cons _ _ :=
-- sorry

lemma list.has_def {α : Type u} [_inst_2 : functor list] (t : list α)
: subtype.val <$> list.map_has t = t :=
begin
  induction t with t ts,
  { refl },
  { unfold list.map_has list.map_has', admit },
end

instance : foldable list :=
  { foldr := λ α β f, flip $ list.foldr f }
  -- , has := @list.has
  -- , map := @list.map_has
  -- , has_def := _ }

namespace ast.simple

def expr.foldr {α : Type} {r : Type u} (f : α → r → r) : expr α → r → r
  | (expr.lit n) := id
  | (expr.oper _ e₀ e₁) := expr.foldr e₀ ∘ expr.foldr e₁
  | (expr.var v) := f v

instance expr_foldable : foldable expr :=
{ foldr := @expr.foldr }

def prop.foldr : ∀ {α : Type} {r : Type u}, (α → r → r) → prop α → r → r
  | _ _ f prop.true := id
  | _ _ f prop.false := id
  | _ _ f (prop.odd e) := foldr' f e
  | _ _ f (prop.bin _ e₀ e₁) := foldr' f e₀ ∘ foldr' f e₁
  | _ _ f (prop.not p) := prop.foldr f p
  | _ _ f (prop.cnt _ e₀ e₁) := prop.foldr f e₀ ∘ prop.foldr f e₁
  | α r f (prop.all p) := prop.foldr (@option.rec α (λ _, r → r) id f) p

instance : foldable prop :=
{ foldr := @prop.foldr }

end ast.simple

def sum.foldr {β : Type u₁} {α : Type u₀} {r : Type u} (f : α → r → r) : β ⊕ α → r → r
  | (sum.inr y) x := f y x
  | (sum.inl _) x := x

instance sum_foldable {α : Type u₀} : foldable (sum α) :=
  { foldr := @sum.foldr α }

-- def existential.foldr  {r : Type u} {α : Type} (f : α → r → r) : existential α → r → r
--   | ⟨_,cs⟩ x := list.foldr (foldr' $ foldr' f) x cs

-- instance : foldable existential :=
--   { foldr := @existential.foldr }

def sum.swap {α : Type u₀} {β : Type u₁} : α ⊕ β → β ⊕ α
  | (sum.inr x) := sum.inl x
  | (sum.inl x) := sum.inr x

namespace existential

variables {α' β' : Type}
variables {α : Type u₀}
variables {β : Type u₁}

def locals (x : prop (α' ⊕ β')) : set α' :=
foldr' (foldr' insert ∘ sum.swap : α' ⊕ β' → set α' → set α') x ∅

def rel (x y : prop (α' ⊕ β')) : Prop :=
locals x ∩ locals y ≠ ∅

infix ≈ := rel

-- def set.map {α : Type u₀} {β : Type u₁} (f : α → β) (s : set α) : set β :=
-- { y | ∃ x, x ∈ s ∧ y = f x }

-- def set.id_map {α : Type u₀} (x : set α)
-- : set.map id x = x :=
-- begin
--   unfold set.map, apply funext, intro i,
--   unfold set_of, simp,
--   rw [exists_one_point_right i], simp, refl,
--   intros j h, cases h, subst i,
-- end

-- def set.map_comp {α β γ : Type u₀}
--    (f : α → β)
--    (g : β → γ)
--    (x : set α)
-- : set.map (g ∘ f) x = set.map g (set.map f x) :=
-- begin
--   unfold set.map, apply funext, intro i,
--   unfold set_of, simp,
--   rw -iff_eq_eq,
--   split,
--   { apply exists_imp_exists' f,
--     intros a h, cases h with h₀ h₁,
--     split,
--     { apply h₁ },
--     { unfold mem has_mem.mem set.mem, existsi a,
--       split, refl, apply h₀ } },
--   { intro h,
--     cases h with z h, cases h with h₀ h₁,
--     cases h₁ with j h₁,
--     cases h₁ with h₁ h₂,
--     subst z,
--     exact ⟨j,h₂,h₀⟩ },
-- end

-- instance set_functor : functor set :=
-- { map := @set.map
-- , id_map := @set.id_map
-- , map_comp := @set.map_comp }

lemma mem_fmap {α' : Type u₀} {x : α} {s : set α} (f : α → α')
  (h : x ∈ s)
: f x ∈ f <$> s :=
begin
  unfold has_map.map set.image set_of,
  apply Exists.intro x,
  exact ⟨h,rfl⟩
end

lemma mem_of_mem_fmap {α' : Type u₀} {x : α'} {s : set α} {f : α → α'}
  (h : x ∈ f <$> s)
: ∃ i, i ∈ s ∧ f i = x := h

def close (s : set α) (r : α → α → Prop) (x y : α) : Prop :=
x ∈ s ∧ y ∈ s ∧ (r x y ∨ r y x)

lemma rtc_close_sym' (s : set α) (r : α → α → Prop) (i j : α)
: rtc (close s r) i j → rtc (close s r) j i :=
begin
  intro h,
  cases h with h h,
  { subst j },
  { unfold rtc, right,
    induction h with i j h /- -/ i j k h₀ h₁,
    { apply tc.base,
      unfold close,
      rw [or_comm,-and_assoc,and_comm (j ∈ s),and_assoc],
      apply h },
    { apply tc.trans _ _ _ ih_2 ih_1 }, },
end

lemma rtc_close_sym (s : set α) (r : α → α → Prop) (i j : α)
: rtc (close s r) i j ↔ rtc (close s r) j i :=
by { split ; apply rtc_close_sym' }

def part_of (s : set α) (r : α → α → Prop) (x : α) : set α :=
{ y ∈ s | rtc (close s r) x y }

def quot (s : set α) (r : α → α → Prop) : set (set α) :=
part_of s r <$> s

lemma mem_singleton (x y : α)
: x ∈ ({y} : set α) ↔ x = y :=
begin
  unfold singleton has_insert.insert,
  change _ ∨ _ ↔ _,
  simp [iff_eq_eq,set.mem_empty_eq x],
end

lemma mem_union (x : α) (s₀ s₁ : set α)
: x ∈ s₀ ∪ s₁ ↔ x ∈ s₀ ∨ x ∈ s₁ :=
by refl

lemma mem_sep (x : α) (s : set α) (p : α → Prop)
: x ∈ has_sep.sep p s ↔ x ∈ s ∧ p x :=
by refl

lemma mem_part_of {s : set α} (r : α → α → Prop) {i : α}
  (h : i ∈ s)
: i ∈ part_of s r i :=
begin
  unfold part_of,
  rw [mem_sep],
  split,
  { apply h },
  { refl }
end

lemma part_of_subset_part_of
  {s : set α} {r : α → α → Prop}
  {i j : α} {x : set α}
  (h : x ∈ quot s r)
  (Hi : i ∈ x)
  (Hj : j ∈ x)
: part_of s r i ⊆ part_of s r j :=
begin
  intro z,
  unfold part_of,
  unfold existential.quot at h,
  note h₂ := mem_of_mem_fmap h,
  cases h₂ with k h₂, cases h₂ with h₂ h₃,
  clear h,
  rw -h₃ at Hi Hj,
  unfold part_of at Hi Hj,
  simp [mem_union,mem_singleton,mem_sep],
  simp [mem_union,mem_singleton,mem_sep] at Hi Hj,
  intro h'
  ; cases h' with h₀ h₁
  ; cases Hi with Hi Hi'
  ; cases Hj with Hj Hj',
  split,
  { rw rtc_close_sym at Hj,
    apply rtc_trans k Hj,
    apply rtc_trans i Hi,
    apply h₀ },
  { apply h₁ },
end

lemma part_of_eq_part_of
  {s : set α} {r : α → α → Prop}
  {i j : α} {x : set α}
  (h : x ∈ quot s r)
  (Hi : i ∈ x)
  (Hj : j ∈ x)
: part_of s r i = part_of s r j :=
begin
  apply set.eq_of_subset_of_subset,
  { apply part_of_subset_part_of h Hi Hj, },
  { apply part_of_subset_part_of h Hj Hi, }
end

lemma part_of_subset_quot
  {s : set α} (r : α → α → Prop) {x : α}
  (h : x ∈ s)
: part_of s r x ⊆ s :=
begin
  intros i h',
  unfold part_of at h',
  cases h' with h' h'',
  apply h',
end

lemma quot_partition
  (s : set α) (r : α → α → Prop)
  (x : α)
: x ∈ s ↔ (∃! y, y ∈ quot s r ∧ x ∈ y) :=
begin
  split
  ; intro h,
  apply exists_unique.intro (part_of s r x),
  split,
  { unfold existential.quot,
    apply mem_fmap _ h, },
  { unfold part_of,
    rw mem_sep,
    split, apply h,
    refl },
  { intros A h',
    cases h' with h₀ h₁,
    unfold existential.quot at h₀,
    note h₂ := mem_of_mem_fmap h₀,
    cases h₂ with i h₂,
    cases h₂ with h₂ h₃,
    rw [-h₃,part_of_eq_part_of h₀ h₁],
    rw -h₃, apply mem_part_of _ h₂ },
  { cases h with A h,
    cases h with h₀ h₂, cases h₀ with h₀ h₁,
    note h₂ := mem_of_mem_fmap h₀,
    cases h₂ with i h₃, cases h₃ with h₃ h₄,
    subst A,
    apply part_of_subset_quot _ h₃ h₁, },
end

namespace semantics

variables {v}

def meaning : existential v → ast.simple.semantics.state_t v → Prop
  | ⟨n,cs⟩ s := ∃ s', ∀ p, p ∈ cs → ast.simple.semantics.valid (ast.simple.union s' s) p

variables lv : Type
variables cs : set (prop (lv ⊕ v))
variables s : ast.simple.semantics.state_t v

lemma partition_maintains_meaning
: meaning ({ lv := lv, clauses := cs}) s ↔
(∀ c, c ∈ quot cs rel ∧ meaning ({ lv := _, clauses := c}) s) :=
sorry

end semantics

end existential
