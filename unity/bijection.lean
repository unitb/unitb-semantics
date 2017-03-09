
section

universe variables u₀ u₁ u₂
variables {α α' : Type (u₀)}
variables {β β' γ : Type (u₁)}

protected lemma nat.mul_div_cancel (x y : ℕ) : x * y / x = y := sorry

protected lemma nat.mul_mod_cancel (x y : ℕ) : x * y % x = 0 := sorry

protected lemma nat.mul_add_modulo_cancel (x y k : ℕ) (h : k < x)
: (x * y + k) % x = k := sorry

protected lemma nat.mul_add_div_cancel (x y k : ℕ) (h : k < x)
: (x * y + k) / x = y := sorry

record bijection (α  : Type (u₀)) (β : Type (u₁)) : Type (max (u₀) (u₁)) :=
  mk' ::
  (f : α → β)
  (g : β → α)
  (inverse : ∀ x y, f x = y ↔ x = g y)
--  (right_cancel : ∀ x, g (f x) = x)

def bijection.mk (f : α → β) (g : β → α)
    (f_inv : ∀ x, g (f x) = x)
    (g_inv : ∀ x, f (g x) = x) : bijection α β :=
  { f := f, g := g, inverse :=
    begin
      intros x y,
      split ; intro h,
      { subst y, rw f_inv },
      { subst x, rw g_inv },
    end }

lemma bijection.f_inv (b : bijection α β) (x : α) : b^.g (b^.f x) = x := sorry

lemma bijection.g_inv (b : bijection α β) (x : β) : b^.f (b^.g x) = x := sorry

class finite (α : Type (u₀)) : Type (u₀) :=
  (count : ℕ)
  (to_nat : bijection α (fin count))

class infinite (α : Type u₀) : Type u₀ :=
  (to_nat : bijection α ℕ)

def bij.id : bijection α α :=
    bijection.mk id id (λ _, by simp) (λ _, by simp)

def bij.comp (x : bijection β γ) (y : bijection α β) : bijection α γ :=
   { f := x^.f ∘ y^.f
   , g := y^.g ∘ x^.g
   , inverse :=
       begin
         intros a b,
         unfold function.comp,
         rw [x^.inverse,y^.inverse]
       end }

check @function.swap

def sum.swap : α ⊕ β → β ⊕ α
  | (sum.inl x) := sum.inr x
  | (sum.inr x) := sum.inl x

def bij.swap : bijection (α ⊕ β) (β ⊕ α) :=
   bijection.mk sum.swap sum.swap
   (by intro x ; cases x with x x ; unfold sum.swap ; refl)
   (by intro x ; cases x with x x ; unfold sum.swap ; refl)

def bij.rev (x : bijection α β) : bijection β α :=
  { f := x^.g
  , g := x^.f
  , inverse :=
    begin
      intros i j,
      split ; intro h ; symmetry,
      { rw [x^.inverse,h] },
      { rw [-x^.inverse,-h], }
    end }

infixr ∘ := bij.comp

section pre

parameter (n : ℕ)

def bij.pre.f : fin n ⊕ ℕ → ℕ
  | (sum.inl ⟨x,Px⟩) := x
  | (sum.inr x) := x + n
def bij.pre.g (i : ℕ) : fin n ⊕ ℕ :=
  if P : i < n
     then sum.inl ⟨i, P⟩
     else sum.inr (i - n)

def bij.pre : bijection (fin n ⊕ ℕ) ℕ :=
  bijection.mk bij.pre.f bij.pre.g
  begin
    intro x
    ; cases x with x x,
    { cases x with x Px,
      unfold bij.pre.f bij.pre.g,
      rw [dif_pos Px] },
    { assert h : ¬ x + n < n,
      { apply not_lt_of_ge, apply nat.le_add_left },
      unfold bij.pre.f bij.pre.g,
      rw [dif_neg h,nat.add_sub_cancel] }
  end
  begin
    intro x,
    cases decidable.em (x < n) with h h,
    { unfold bij.pre.g,
      rw [dif_pos h],
      unfold bij.pre.f, refl },
    { unfold bij.pre.g,
      rw [dif_neg h],
      unfold bij.pre.f,
      rw [nat.sub_add_cancel],
      apply le_of_not_gt h }
  end

end pre

section append

parameters (m n : ℕ)

def bij.append.f : fin m ⊕ fin n → fin (n+m)
  | (sum.inl ⟨x,Px⟩) := ⟨x,lt_of_lt_of_le Px (nat.le_add_left _ _)⟩
  | (sum.inr ⟨x,Px⟩) := ⟨x + m,add_lt_add_right Px _⟩

def bij.append.g : fin (n+m) → fin m ⊕ fin n
  | ⟨x,Px⟩ :=
  if P : x < m
     then sum.inl ⟨x, P⟩
     else sum.inr ⟨x - m,
        begin
          apply @lt_of_add_lt_add_right _ _ _ m,
          rw nat.sub_add_cancel,
          apply Px, apply le_of_not_gt P
        end⟩

def bij.append : bijection (fin m ⊕ fin n) (fin (n+m)) :=
  bijection.mk bij.append.f bij.append.g
  begin
    intro x
    ; cases x with x x,
    { cases x with x Px,
      unfold bij.append.f bij.append.g,
      rw [dif_pos Px] },
    { cases x with x Px,
      assert h : ¬ x + m < m,
      { apply not_lt_of_ge, apply nat.le_add_left },
      unfold bij.append.f bij.append.g,
      rw [dif_neg h], apply congr_arg,
      apply fin.eq_of_veq, unfold fin.val,
      apply nat.add_sub_cancel }
  end
  begin
    intro x,
    cases x with x Px,
    cases decidable.em (x < m) with h h,
    { unfold bij.append.g,
      rw [dif_pos h],
      unfold bij.append.f, refl },
    { unfold bij.append.g,
      rw [dif_neg h],
      unfold bij.append.f,
      apply fin.eq_of_veq, unfold fin.val,
      rw [nat.sub_add_cancel],
      apply le_of_not_gt h }
  end

end append

section

open list
open nat

def less : ℕ → list ℕ
  | 0 := []
  | (succ n) := n :: less n

lemma enum_less {n k : ℕ} (h : n < k) : n ∈ less k :=
begin
  induction k with k,
  { cases nat.not_lt_zero _ h },
  { unfold less, note h' := @lt_or_eq_of_le ℕ _ _ _ h,
    cases h' with h' h',
    { apply or.inr, apply ih_1,
      apply lt_of_succ_lt_succ h' },
    { apply or.inl, injection h' with h, apply h } }
end

end

def bij.even_odd.f x := if x % 2 = 1 then sum.inr (x / 2) else sum.inl (x / 2)
def bij.even_odd.g : ℕ ⊕ ℕ → ℕ
  | (sum.inr x) := 2 * x + 1
  | (sum.inl x) := 2 * x

def bij.even_odd : bijection (ℕ ⊕ ℕ) ℕ :=
    bijection.mk bij.even_odd.g
                 bij.even_odd.f
      begin
        intro x,
        cases x with x x,
        { assert h : ¬ 2 * x % 2 = 1,
          { rw nat.mul_mod_cancel, contradiction },
          unfold bij.even_odd.g bij.even_odd.f,
          rw [if_neg h,nat.mul_div_cancel 2] },
        { unfold bij.even_odd.g bij.even_odd.f,
          note h' := nat.le_refl 2,
          rw [if_pos,nat.mul_add_div_cancel _ _ _ h'],
          rw [nat.mul_add_modulo_cancel _ _ _ h'] }
      end
      begin
        intros x,
        cases decidable.em (x % 2 = 1) with h h
        ; unfold bij.even_odd.f,
        { rw [if_pos h],
          unfold bij.even_odd.f bij.even_odd.g,
          note h₂ := nat.mod_add_div x 2,
          rw add_comm, rw h at h₂, apply h₂ },
        { rw [if_neg h],
          assert h' : x % 2 = 0,
          { note h₂ := @nat.mod_lt x 2 (nat.le_succ _),
            note h₃ := enum_less h₂,
            unfold less mem has_mem.mem list.mem at h₃,
            cases h₃ with h₃ h₃,
            { cases h h₃ },
            cases h₃ with h₃ h₃,
            { apply h₃ },
            { cases h₃ } },
          { unfold bij.even_odd.g,
            note h₂ := nat.mod_add_div x 2,
            rw h' at h₂, simp at h₂, apply h₂ } },
      end

open nat

def bij.prod.succ : ℕ × ℕ → ℕ × ℕ
  | (n,0) := (0,succ n)
  | (n,succ m) := (succ n,m)

check @prod.lex_wf
check @inv_image.wf

def diag : ℕ × ℕ → ℕ × ℕ → Prop
:= inv_image (prod.lex lt lt) (λ x, (x^.fst+x^.snd, x^.fst))
--  | (x₀,x₁) (y₀,y₁) := prod.lex lt lt (x₀+y₀,x₀) (x₁+y₁,x₁)

def diag_wf : well_founded diag
:= @inv_image.wf (ℕ × ℕ) _ _
        (λ x, (x^.fst+x^.snd, x^.fst))
        (prod.lex_wf nat.lt_wf nat.lt_wf)

def bij.prod.f : ℕ → ℕ × ℕ
  | 0 := (0,0)
  | (nat.succ n) := bij.prod.succ (bij.prod.f n)
def bij.prod.g (t : ℕ × ℕ) : ℕ :=
  well_founded.recursion diag_wf t $
   take ⟨x₀,x₁⟩,
   match (x₀,x₁) with
    | (0,0) := take _, 0
    | (0,succ n) :=
       take g : Π (y : ℕ × ℕ), diag y (0,succ n) → ℕ,
       have h : diag (n, 0) (0, succ n),
         begin
           unfold diag inv_image prod.fst prod.snd,
           apply prod.lex.left, simp, apply lt_succ_self
         end,
       succ (g (n,0) h)
    | (succ n,m) :=
       take g : Π (y : ℕ × ℕ), diag y (succ n,m) → ℕ,
       have h : diag (n, succ m) (succ n, m),
         begin
           unfold diag inv_image prod.fst prod.snd,
           simp [add_succ,succ_add],
           apply prod.lex.right, apply lt_succ_self
         end,
       succ (g (n,succ m) h)
   end

def bij.prod : bijection (ℕ × ℕ) ℕ :=
    bijection.mk bij.prod.g
                 bij.prod.f
begin
end
begin
end


instance : finite unit :=
  { count := 1
  , to_nat :=
      { f := λ _, fin.mk 0 $ nat.le_refl _
      , g := λ _, ()
      , inverse :=
        begin
          intros x y,
          cases y with y Py,
          cases x,
          note h' := nat.le_of_succ_le_succ Py,
          note h := nat.le_antisymm h' (nat.zero_le _),
          subst y,
          { split ; intro h₂ ; refl },
        end } }

instance (n : ℕ) : finite (fin n) :=
  { count := n
  , to_nat := bij.id }

instance : infinite ℕ :=
  { to_nat := bij.id }

end

section bijection_add

universe variables u₀ u₁
parameters {α α' : Type (u₀)}
parameters {β β' γ : Type (u₁)}
parameters (b₀ : bijection α β) (b₁ : bijection α' β')

def bijection.add.f : α ⊕ α' → β ⊕ β'
  | (sum.inr x) := sum.inr (b₁^.f x)
  | (sum.inl x) := sum.inl (b₀^.f x)

def bijection.add.g : β ⊕ β' → α ⊕ α'
  | (sum.inr x) := sum.inr (b₁^.g x)
  | (sum.inl x) := sum.inl (b₀^.g x)

def bijection.add
: bijection (α ⊕ α') (β ⊕ β') :=
bijection.mk bijection.add.f bijection.add.g
begin
  intro x,
  cases x with x x
  ; unfold bijection.add.f bijection.add.g
  ; rw bijection.f_inv
end
begin
  intro x,
  cases x with x x
  ; unfold bijection.add.f bijection.add.g
  ; rw bijection.g_inv
end

-- def bijection.sum.f : α ⊕ β → ℕ := _
-- def bijection.sum.g : ℕ → α ⊕ β := _

end bijection_add

section bijection_mul

universe variables u₀ u₁
parameters {α α' : Type (u₀)}
parameters {β β' γ : Type (u₁)}
parameters (b₀ : bijection α β) (b₁ : bijection α' β')

def bijection.mul.f : α × α' → β × β'
  | (x,y) := (b₀^.f x,b₁^.f y)

def bijection.mul.g : β × β' → α × α'
  | (x,y) := (b₀^.g x,b₁^.g y)

def bijection.mul
: bijection (α × α') (β × β') :=
bijection.mk bijection.mul.f bijection.mul.g
begin
  intro x ; cases x with x y,
  unfold bijection.mul.f bijection.mul.g,
  simp [bijection.f_inv]
end
begin
  intro x ; cases x with x y,
  unfold bijection.mul.f bijection.mul.g,
  simp [bijection.g_inv]
end

end bijection_mul

section

universe variables u₀ u₁ u₂
variables {α α' : Type (u₀)}
variables {β β' γ : Type (u₀)}

local infixr ∘ := bij.comp
local infix + := bijection.add

instance inf_inf_inf_sum [infinite α] [infinite β] : infinite (α ⊕ β) :=
  { to_nat := bij.even_odd ∘ (infinite.to_nat α + infinite.to_nat β) }

instance inf_fin_inf_sum [infinite α] [finite β] : infinite (α ⊕ β) :=
  { to_nat := bij.pre _ ∘ bij.swap ∘ (infinite.to_nat α + finite.to_nat β) }

instance fin_inf_inf_sum [finite α] [infinite β] : infinite (α ⊕ β) :=
  { to_nat := bij.pre _ ∘ (finite.to_nat α + infinite.to_nat β) }

instance [finite α] [finite β] : finite (α ⊕ β) :=
  { count := _
  , to_nat := bij.append _ _ ∘ (finite.to_nat α + finite.to_nat β)
  }

instance inf_inf_inf_prod [infinite α] [infinite β] : infinite (α × β) :=
  { to_nat := bij.even_odd ∘ (infinite.to_nat α + infinite.to_nat β) }

instance inf_fin_inf_prod [infinite α] [finite β] : infinite (α × β) :=
  { to_nat := bij.pre _ ∘ bij.swap ∘ (infinite.to_nat α + finite.to_nat β) }

instance fin_inf_inf_prod [finite α] [infinite β] : infinite (α × β) :=
  { to_nat := bij.pre _ ∘ (finite.to_nat α + infinite.to_nat β) }

instance [finite α] [finite β] : finite (α × β) :=
  { count := _
  , to_nat := bij.append _ _ ∘ (finite.to_nat α + finite.to_nat β)
  }

end
