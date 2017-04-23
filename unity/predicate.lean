
import util.logic

namespace predicate

universe variables u u' u₀ u₁

variables {α β : Type u}

@[reducible]
def pred' α := α → Prop

def lifted₀ : Prop → pred' α := λ p _, p
def lifted₁ (op : Prop → Prop) : pred' α → pred' α :=
λ p i, op (p i)
def lifted₂ (op : Prop → Prop → Prop) (p q : pred' α) : pred' α :=
λ i, op (p i) (q i)

def ew (p : pred' α) : Prop :=
∀ i, p i

def False : pred' α := lifted₀ false
def True : pred' α := lifted₀ true

def p_or (p₀ p₁ : pred' α) : pred' α
:= lifted₂ or p₀ p₁

@[simp]
lemma p_or_to_fun (p₀ p₁ : pred' α) (x : α)
: p_or p₀ p₁ x ↔ p₀ x ∨ p₁ x := by refl

def p_and (p₀ p₁ : pred' α) : pred' α
:= lifted₂ and p₀ p₁

@[simp]
lemma p_and_to_fun (p₀ p₁ : pred' α) (x : α)
: p_and p₀ p₁ x ↔ p₀ x ∧ p₁ x := by refl

def p_impl (p₀ p₁ : pred' α) : pred' α
:= lifted₂ implies p₀ p₁

@[simp]
lemma p_impl_to_fun (p₀ p₁ : pred' α) (x : α)
: p_impl p₀ p₁ x ↔ (p₀ x → p₁ x) := by refl


def p_entails (p₀ p₁ : pred' α) : Prop
:= ew (p_impl p₀ p₁)

lemma p_entails_of_fun (p₀ p₁ : pred' α) (x : β)
: p_entails p₀ p₁ ↔ ∀ x, p₀ x → p₁ x := by refl


def p_not (p : pred' α) : pred' α
:= lifted₁ not p

@[simp]
lemma False_eq_false (τ : β) : False τ = false := rfl
@[simp]
lemma True_eq_true (τ : β) : True τ = true := rfl

def p_exists {t : Type u} {β : Type u'} (P : t → pred' β) : pred' β :=
λ x, ∃ y, P y x

def p_forall {t : Type u} {β : Type u'} (P : t → pred' β) : pred' β :=
λ x, ∀ y, P y x

notation `∃∃` binders `, ` r:(scoped P, p_exists P) := r
notation `∀∀` binders `, ` r:(scoped P, p_forall P) := r

infixl ` || ` := p_or
infixl ` && ` := p_and
infixr ` ⟶ `:60 := p_impl
infix ` ⟹ `:60 := p_entails
notation `⦃ `:max act ` ⦄`:0 := ew act

instance : has_neg (pred' α) := has_neg.mk p_not

@[simp]
lemma p_not_to_fun (p₀ : pred' α) (x : α)
: (- p₀) x ↔ ¬ p₀ x := by refl

lemma p_not_eq_not (p : pred' β) (τ) : ¬ p τ ↔ (-p) τ :=
by refl

@[simp]
lemma p_not_True : (- True) = (False : pred' α) :=
begin
  apply funext, intro x,
  rw [-p_not_eq_not],
  simp,
end

@[simp]
lemma True_p_and (p : pred' α)
: True && p = p :=
begin
  apply funext, intro x,
  simp,
end

@[simp]
lemma p_or_False (p : pred' α)
: p || False = p :=
begin
  apply funext, intro x,
  simp,
end

lemma p_or_p_imp_p_or' {p p' q q' : pred' α}
  (hp : p ⟹ p')
  (hq : q ⟹ q')
: (p || q)  ⟹  (p' || q')  :=
by { intro, apply or.imp (hp _) (hq _) }

lemma p_or_p_imp_p_or {p p' q q' : pred' α} {τ}
  (hp : (p ⟶ p') τ)
  (hq : (q ⟶ q') τ)
: ( p || q ) τ → ( p' || q' ) τ :=
by apply or.imp hp hq

lemma p_or_p_imp_p_or_right' {p q q' : pred' α}
  (hq : q ⟹ q')
: ( p || q ) ⟹ ( p || q' ) :=
by { intro, apply or.imp id (hq _) }

lemma p_or_p_imp_p_or_right {p q q' : pred' α} {τ}
  (hq : (q ⟶ q') τ)
: ( p || q ) τ → ( p || q' ) τ :=
by apply or.imp id hq

lemma p_imp_p_imp_p_imp {p p' q q' : pred' α} {τ}
  (hp : (p' ⟶ p) τ)
  (hq : (q ⟶ q') τ)
: ( p ⟶ q ) τ → ( p' ⟶ q' ) τ :=
take hpq, hq ∘ hpq ∘ hp

lemma p_imp_p_imp_p_imp_left {p p' q : pred' α} {τ}
  (hp : (p' ⟶ p) τ)
: ( p ⟶ q ) τ → ( p' ⟶ q ) τ :=
p_imp_p_imp_p_imp hp id

lemma p_imp_p_imp_p_imp_right {p q q' : pred' α} {τ}
  (hq : (q ⟶ q') τ)
: ( p ⟶ q ) τ → ( p ⟶ q' ) τ :=
p_imp_p_imp_p_imp id hq

lemma p_not_p_not_iff_self (p : pred' β) :
- - p = p :=
begin
  apply funext, intro x,
  simp [not_not_iff_self],
end

lemma p_not_p_and (p q : pred' β) :
- (p && q) = -p || -q :=
begin
  apply funext, intro x,
  simp [not_and_iff_not_or_not],
end

-- lemma p_not_p_forall {t} (p : t → pred' β) :
-- (- ∀∀ x, p x) = (∃∃ x, -p x) :=
-- sorry

lemma p_not_p_exists {t} (p : t → pred' β) :
(- ∃∃ x, p x) = (∀∀ x, -p x) :=
sorry

lemma p_or_comm (p q : pred' β) : p || q = q || p :=
begin apply funext, intro x, simp end

lemma p_and_comm (p q : pred' β) : p && q = q && p :=
begin apply funext, intro x, simp end

lemma p_and_p_imp (p q r : pred' β) : p && q ⟶ r = p ⟶ (q ⟶ r) :=
begin
  apply funext, intro x, simp,
  rw -iff_eq_eq,
  split
  ; intros h h' ; intros
  ; apply h
  ; try { split }
  ; try { cases h' }
  ; assumption
end

lemma True_p_imp (p : pred' β)
: True ⟶ p = p :=
begin
  apply funext, intro, rw [-iff_eq_eq],
  split
  ; intro h
  ; try { intro }
  ; apply h,
  trivial
end

lemma ew_eq_true {p : pred' β} : ⦃ p ⦄ → p = True :=
begin
  intros h,
  apply funext, intro x,
  simp [eq_true],
  apply h
end

@[simp]
lemma p_exists_to_fun {t : Type u'} (P : t → pred' β) (i : β)
: (∃∃ x, P x) i ↔ (∃ x, P x i) :=
by refl

lemma p_and_over_p_exists_right {t} (p : t → pred' β) (q : pred' β)
: (∃∃ x, p x) && q = (∃∃ x, p x && q) :=
begin
  apply funext, intro i,
  rw -iff_eq_eq,
  simp,
  split
  ; intro h
  ; cases h with x y
  ; cases y with y h
  ; exact ⟨y,x,h⟩,
end

lemma shunting (p q r : pred' β)
: p ⟶ q || r = (p && - q) ⟶ r :=
begin
  apply funext, intro i,
  simp, rw -iff_eq_eq,
  split ; intros h₀ h₁,
  { cases h₁ with h₁ h₂,
    cases h₀ h₁ with h₃ h₃,
    { cases h₂ h₃ },
    { apply h₃ } },
  { cases classical.em (q i) with h₂ h₂,
    { left, apply h₂ },
    { right, apply h₀, exact ⟨h₁,h₂⟩ } }
end

lemma p_not_p_imp (p q : pred' β)
: (-p) ⟶ q = p || q :=
begin
  rw [-True_p_and (-p),-shunting,True_p_imp],
end

lemma p_or_entails_p_or_right (p q x : pred' β)
: p ⟹ q → x || p ⟹ x || q :=
begin
  intros h i, simp,
  apply or.imp_left (h _),
end


lemma p_exists_entails_p_exists {t : Type u'} (p q : t → pred' β)
: (∀ x, p x ⟹ q x) → (∃∃ x, p x) ⟹ (∃∃ x, q x) :=
begin
  intros h i,
  simp,
  apply exists_imp_exists,
  intro,
  apply h
end

lemma p_exists_entails_p_exists' {t : Type u₀} {t' : Type u₁}
  (p : t → pred' β)
  (q : t' → pred' β)
  (f : t → t')
  (h : (∀ x, p x ⟹ q (f x)))
: (∃∃ x, p x) ⟹ (∃∃ x, q x) :=
begin
  intros h' h'',
  simp,
  apply exists_imp_exists',
  intro,
  apply h a,
  apply h''
end

lemma p_exists_entails_eq_p_forall_entails
  (p : α → pred' β) (q : pred' β)
: ((∃∃ x, p x) ⟹ q) = (∀ x, p x ⟹ q) :=
sorry

end predicate
