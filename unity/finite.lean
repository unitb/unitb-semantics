
open nat
open list

def below (n : ℕ) := { x // x < n }

theorem lt_of_not_le {m n : ℕ} (h : ¬ m ≤ n) : n < m :=
begin
  cases lt_or_ge n m with h' h',
  { apply h' },
  { cases h h' }
end

theorem mod_of_lt {m n : ℕ} (h : n > m) : m % n = m :=
begin
  rw [nat.mod_def,dif_neg],
  intro h',
  cases h' with h₀ h₁,
  apply not_le_of_gt h h₁,
end

theorem mod_lt (m n : ℕ) (h : n > 0) : m % n < n :=
begin
  apply @well_founded.induction _ _ nat.lt_wf _ m ,
  intros m IH,
  rw [nat.mod_def],
  cases decidable.em (n ≤ m) with h' h',
  { rw dif_pos (and.intro h h'), apply IH, apply sub_lt,
    { apply lt_of_lt_of_le h h' },
    { apply h } },
  { rw dif_neg, cases lt_or_ge m n with h h,
    apply h, cases h' h,
    intro h'', apply h',
    cases h'' with h₀ h₁, apply h₁ }
end

theorem mod_mod (m n : ℕ) : (m % n) % n = m % n :=
begin
  cases decidable.em (n > 0) with h h,
  { apply mod_of_lt, apply mod_lt _ _ h },
  { note h' := not_pos_of_eq_zero h,
    subst n, rw [mod_def,dif_neg],
    intro h', apply h,
    cases h' with h₀ h₁, apply h₀ }
end

theorem mod_plus (n p : ℕ) (h : p > 0) : ∃k q, q < p ∧ n = k * p + q :=
begin
  existsi (n / p), existsi (n % p),
  split,
  { apply mod_lt _ _ h, },
  { rw [div_add_mod] }
end

theorem mul_plus_mod (k p q : ℕ) (h : q < p) : (k * p + q) % p = q :=
begin
  induction k with k,
  { rw [mod_def,dif_neg], simp,
    simp, intro h', apply not_lt_of_ge h'^.left h },
  { rw [mod_def,dif_pos,succ_mul],
    simp [nat.add_sub_cancel_left],
    simp at ih_1,
    apply ih_1,
    { split,
      { apply lt_of_le_of_lt (zero_le _), apply h },
      { simp [succ_mul], apply nat.le_add_right  } } }
end

theorem mod_zero : ∀ n : ℕ, n % 0 = n  :=
    begin
      intro n,
      rw [mod_def,dif_neg],
      intro h,
      cases h with h h',
      apply lt_irrefl _ h,
    end

theorem succ_mod' {n p : ℕ} (h : succ (n % p) < p) : succ n % p = succ (n % p) :=
begin
   assert h₁ : p > 0,
   { apply lt_of_le_of_lt (zero_le _), apply h },
   note h₀ := mod_plus n p h₁,
   cases h₀ with k h₀, cases h₀ with q h₀,
   cases h₀ with h₀ h₁,
   subst n,
   rw mul_plus_mod _ _ _ h₀ at h,
   rw [-add_succ,mul_plus_mod _ _ _ h₀,mul_plus_mod _ _ _ h],
end

theorem succ_mod (n p : ℕ) : succ n % p = succ (n % p) % p :=
begin
  symmetry,
  cases decidable.em (0 < p ∧ p ≤ succ (n % p)) with h h,
  { assert h' : succ (n % p) = p,
    { apply le_antisymm _ h^.right,
      { apply mod_lt _ _ h^.left } },
    cases mod_plus n p h^.left with k h₀,
    cases h₀ with q h₀,
    cases h₀ with h₀ h₁,
    rw [mod_def,dif_pos h,h',nat.sub_self,zero_mod],
    subst n, rw [mul_plus_mod _ _ _ h₀] at h',
    assert h₁ : k * p + succ q = (k+1) * p + 0,
    { rw h', simp [add_mul] },
    rw [-add_succ, h₁, mul_plus_mod _ _ _ h^.left], },
  { cases classical.not_and_of_not_or_not h with h₀ h₀,
    { note h'' := not_pos_of_eq_zero h₀,
      subst p, simp [mod_zero] },
    { note h₁ := lt_of_not_le h₀,
      rw [succ_mod' h₁,succ_mod',mod_mod],
      { rw mod_mod, apply h₁ }  } }
end

theorem mod_add' {m n p : ℕ} : (m + n) % p = (m + n % p) % p :=
begin
  induction m with m,
  { symmetry, simp, apply mod_mod },
  { rw [succ_add,succ_mod,ih_1,succ_add,-succ_mod] }
end

theorem mod_add {m n p : ℕ} : (m + n) % p = (m % p + n % p) % p :=
begin
  rw [mod_add',nat.add_comm,mod_add',nat.add_comm]
end

theorem nat.mod_self' {m : ℕ} : m % m = 0 :=
begin
  rw [mod_def],
  cases decidable.em (0 < m) with h h,
  { note h' := and.intro h (nat.le_refl m),
    rw [dif_pos h',nat.sub_self,zero_mod] },
  { assert h' : ¬ (0 < m ∧ m ≤ m),
    { intro h', apply h,
      cases h' with h₀ h₁,
      apply h₀ },
    rw [dif_neg h'],
    apply not_pos_of_eq_zero h },
end

def fin_interleave (n : ℕ) (i : ℕ) : below (succ n)
:= ⟨i % succ n,mod_lt _ _ (succ_le_succ $ zero_le _)⟩

theorem inf_repeat_fin_inter {n : ℕ} : ∀ x i, ∃ j, fin_interleave n (i+j) = x :=
begin
  intro x,
  cases x with x H,
  intro i,
  existsi x + succ n - (i % succ n),
  -- refine ⟨x + succ n - (i % succ n),_⟩, -- i + x + succ n - (i % succ n)
  tactic.swap,
  unfold fin_interleave,
  assert h : i % succ n ≤ succ n,
  { apply nat.le_of_lt (mod_lt _ _ _),
    apply succ_le_succ, apply zero_le },
  apply subtype.eq, unfold subtype.elt_of ,
  rw [nat.add_sub_assoc h,add_comm x,-add_assoc,mod_add,@mod_add i],
  rw [-@mod_add' (i % succ n),-nat.add_sub_assoc h],
  rw [nat.add_sub_cancel_left, nat.mod_self',nat.zero_add,mod_mod,mod_of_lt],
  apply H,
end
