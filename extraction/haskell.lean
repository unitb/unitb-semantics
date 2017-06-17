
universe variables u₀ u₁ u₂ u₃

namespace prod

variables {α : Type u₀} {α' : Type u₁}
variables {β : Type u₂} {β' : Type u₃}

lemma fst_map {f : α → α'} {g : β → β'} (x : α × β)
: (map f g x).1 = f x.1 :=
by { cases x, refl }

lemma snd_map {f : α → α'} {g : β → β'} (x : α × β)
: (map f g x).2 = g x.2 :=
by { cases x, refl }

end prod

structure rws (r : Type u₀) (w : Type u₁) (s : Type u₂) (α : Type u₃) :=
  (run_rws : r → s → α × list w × s)

namespace rws

variables {r : Type u₀} {w : Type u₁} {s : Type u₂} {α β γ : Type u₃}

def rws.pure (x : α) : rws r w s α :=
⟨ λ r s, (x,[],s) ⟩

def rws.bind : rws r w s α → (α → rws r w s β) → rws r w s β
  | ⟨ f ⟩ g := ⟨ λ r s, let (x,w,s') := f r s
                        in prod.map id (prod.map (append w) id) ((g x).run_rws r s') ⟩

instance : has_bind (rws r w s) :=
{ bind := @rws.bind r w s }

section laws

variables {i : α}
variables {x y : rws r w s α}
variables {f : α → rws r w s β}
variables {f' : α → β}
variables {g : β → rws r w s γ}

lemma rws.ext
  (h₀ : ∀ r s, (x.run_rws r s).1 = (y.run_rws r s).1)
  (h₁ : ∀ r s, (x.run_rws r s).2.1 = (y.run_rws r s).2.1)
  (h₂ : ∀ r s, (x.run_rws r s).2.2 = (y.run_rws r s).2.2)
: x = y :=
begin
  cases x, cases y,
  apply congr_arg,
  apply funext, intro rr,
  apply funext, intro ss,
  unfold rws.run_rws at h₀ h₁ h₂,
  note hh₀ := h₀ rr ss, clear h₀,
  note hh₁ := h₁ rr ss, clear h₁,
  note hh₂ := h₂ rr ss, clear h₂,
  cases run_rws rr ss,
  cases run_rws_1 rr ss,
  cases snd, cases snd_1,
  unfold prod.fst prod.snd at hh₀ hh₁ hh₂,
  rw [hh₀,hh₁,hh₂],
end

lemma rws.run_rws_bind_1 (i : r) (j : s)
: ((x >>= f).run_rws i j).1 = ((f (x.run_rws i j).1).run_rws i (x.run_rws i j).2.2).1 :=
begin
  cases x,
  unfold has_bind.bind rws.bind rws.run_rws,
  simp, cases (run_rws i j),
  cases snd,
  unfold rws.bind._match_1,
  unfold prod.fst,
  rw prod.fst_map, refl,
end

lemma rws.run_rws_bind_2 (i : r) (j : s)
:   ((x >>= f).run_rws i j).2.1
  = (x.run_rws i j).2.1 ++ ((f (x.run_rws i j).1).run_rws i (x.run_rws i j).2.2).2.1 :=
begin
  cases x,
  unfold has_bind.bind rws.bind rws.run_rws,
  simp, cases (run_rws i j),
  cases snd,
  unfold rws.bind._match_1,
  unfold prod.fst,
  rw [prod.snd_map,prod.fst_map],
end

lemma rws.run_rws_bind_3 (i : r) (j : s)
: ((x >>= f).run_rws i j).2.2 = ((f (x.run_rws i j).1).run_rws i (x.run_rws i j).2.2).2.2 :=
begin
  cases x,
  unfold has_bind.bind rws.bind rws.run_rws,
  simp, cases (run_rws i j),
  cases snd,
  unfold rws.bind._match_1,
  unfold prod.fst,
  rw [prod.snd_map,prod.snd_map],
  refl,
end

lemma rws.bind_assoc
: x >>= f >>= g = x >>= (λ i, f i >>= g) :=
begin
  apply rws.ext
  ; intros ss rr
  ; simp [rws.run_rws_bind_1,rws.run_rws_bind_2,rws.run_rws_bind_3],
end

lemma rws.pure_bind
: rws.pure i >>= f = f i :=
begin
  apply rws.ext
  ; intros ss rr
  ; unfold rws.pure
  ; simp [rws.run_rws_bind_1,rws.run_rws_bind_2,rws.run_rws_bind_3],
end

lemma rws.id_map
: x >>= (rws.pure ∘ id) = x :=
begin
  cases x,
  unfold has_bind.bind rws.bind,
  apply congr_arg,
  apply funext, intro i,
  apply funext, intro j,
  cases run_rws i j, cases snd,
  unfold rws.bind._match_1 prod.map function.comp id,
  unfold rws.pure rws.run_rws prod.map,
  simp
end

end laws

instance : monad (rws r w s) :=
{ pure := @rws.pure r w s
, bind := @rws.bind r w s
, bind_assoc := @rws.bind_assoc r w s
, pure_bind  := @rws.pure_bind r w s
, id_map := @rws.id_map r w s }

variables {r w s α}

def ask : rws r w s r :=
⟨ λ r s, (r,[],s) ⟩

def asks {α : Type u₀} (f : r → α) : rws r w s α :=
f <$> ask

def get : rws r w s s :=
⟨ λ _ s, (s, [], s) ⟩

def gets {α : Type u₂} (f : s → α) : rws r w s α :=
f <$> get

end rws

def error_t (e : Type u₀) (m : Type (max u₀ u₂) → Type u₁) (α : Type u₂) : Type u₁ :=
m (e ⊕ α)

namespace error_t

variables {e : Type u₀}
variables {m : Type (max u₀ u₂) → Type u₁}
variables [monad m]
variables {α β : Type u₂}

def pure (x : α) : error_t e m α :=
(return (sum.inr x) : m (e ⊕ α))

def bind (x : m (e ⊕ α)) (f : α → m (e ⊕ β)) : m (e ⊕ β) :=
x >>= λ i, @sum.rec e α (λ j, m (e ⊕ β)) (λ j, return $ sum.inl j) (λ j, f j) i
     -- match i with
     --  | (sum.inl x) := return (sum.inl x)
     --  | (sum.inr x) := f x
     -- end) : m (e ⊕ α))

instance : has_bind (error_t e m) :=
{ bind := @bind e m _ }

section laws

variables {i : α}
variables {x y : rws r w s α}
variables {f : α → rws r w s β}
variables {f' : α → β}
variables {g : β → rws r w s γ}


instance [monad m] : monad (error_t e m) :=
sorry

def fail [monad m] (x : e) : error_t e m α :=
(return (sum.inl x) : m (e ⊕ α))

end error_t

namespace extractor

open rws

variables (decl : Type u₀)

@[reducible]
def M := error_t string (rws (list string) (list decl) (name → option decl))

variables {decl}

def with_msg {α : Type u₂} (msg : string) (opt : option α) : string ⊕ α :=
option.rec (sum.inl msg) sum.inr opt

def lookup_local (v : ℕ) : M decl string :=
asks (λ xs, with_msg ("undefined local: " ++ to_string v) (xs.nth v))

def lookup_def (v : name) : M decl decl :=
gets (λ f, with_msg ("undefined local: " ++ to_string v) (f v))

end extractor

namespace haskell

inductive expr : Type
  | var : string → expr
  | app : expr → expr → expr

def expr.to_string : expr → string
  | (expr.var v) := v
  | (expr.app e₀ e₁) := "(" ++ expr.to_string e₀ ++ " " ++ expr.to_string e₁ ++ ")"

instance : has_to_string expr :=
{ to_string := expr.to_string }

end haskell

open extractor error_t

meta def extract : expr → M string haskell.expr
 | (expr.var v) := haskell.expr.var <$> lookup_local v
 | e := fail (to_string e)

def rev {α : Type} : list α → list α
  | [] := []
  | (x :: xs) := rev xs ++ [x]

#eval extract `(rev [1,2,3] : list ℕ)
