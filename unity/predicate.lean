

namespace predicate

universe variables u u'

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
lemma p_not_to_fun (p₀ : pred' α) (x : α)
: p_not p₀ x ↔ ¬ p₀ x := by refl


@[simp]
lemma False_eq_false (τ : β) : False τ = false := rfl
@[simp]
lemma True_eq_true (τ : β) : True τ = true := rfl

def p_exists {t : Type u} {β : Type u'} (P : t → pred' β) : pred' β :=
λ x, ∃ y, P y x

notation `∃∃` binders `, ` r:(scoped P, p_exists P) := r

infixl ` || ` := p_or
infixl ` && ` := p_and
infixr ` ⟶ `:60 := p_impl
infix ` ⟹ `:60 := p_entails
notation `⦃ `:max act ` ⦄` := ew act

notation `~`:75 x := p_not x

@[simp]
lemma p_not_True : (~ True) = (False : pred' α) :=
begin
  apply funext, intro x,
  simp,
end

@[simp]
lemma True_p_and (p : pred' α)
: True && p = p :=
begin
  apply funext, intro x,
  simp,
end

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

lemma p_not_eq_not (p : pred' β) (τ) : ¬ p τ ↔ (~p) τ :=
by refl

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

lemma shunting (p q r : pred' β)
: p ⟶ q || r = (p && ~ q) ⟶ r :=
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

lemma p_or_entails_p_or_right (p q x : pred' β)
: p ⟹ q → x || p ⟹ x || q :=
begin
  intros h i, simp,
  apply or.imp_left (h _),
end

@[simp]
lemma p_exists_to_fun {t : Type u'} (P : t → pred' β) (i : β)
: (∃∃ x, P x) i ↔ (∃ x, P x i) :=
by refl

lemma p_exists_entails_p_exists {t : Type u'} (p q : t → pred' β)
: (∀ x, p x ⟹ q x) → (∃∃ x, p x) ⟹ (∃∃ x, q x) :=
begin
  intros h i,
  simp,
  apply exists_imp_exists,
  intro,
  apply h
end

end predicate
