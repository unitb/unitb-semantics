
import unitb.category.basic

universes u u₀ u₁ v

variable {k : Sort u₀}

variable {k}

variable {σ : Type u₀}

open predicate unitb

structure invariant (inv : pred' σ) (cat : pred' σ → pred' σ → Sort v) (p q : pred' σ) :=
  (run : cat (inv && p) (inv && q))

structure except
     (excp : pred' σ)
     (cat : pred' σ → pred' σ → Sort v)
     (p q : pred' σ) : Type v :=
  (run : cat p (q || excp))

variables {cat : pred' σ → pred' σ → Sort u}

def except_lift (e : pred' σ)
  [lifted_pred cat]
  {α β : pred' σ}
  (x : cat α β)
: except e cat α β :=
⟨ begin
    apply lifted_pred.mono_right _ _ _ x,
    apply p_or_intro_left,
  end ⟩

instance except_finite_disjunctive (e : pred' σ)
  [finite_disjunctive cat]
: finite_disjunctive (except e cat) :=
 { ident := by { intro, apply except.mk, apply lifted_pred.imp, apply p_or_intro_left }
 , comp  :=
   begin
     introv h₀ h₁,
     apply except.mk,
     apply cancellation,
     apply h₁.run,
     apply h₀.run,
   end
 , assoc :=
   begin
     intros, cases x, cases y, cases z,
     unfold has_comp.comp,
     apply congr_arg,
     apply cancellation_assoc cat,
   end
 , left_ident  :=
   begin
     introv, cases x with x,
     have h : cat α (β || e) :=
        cancellation cat β x (lifted_pred.weaken _ _),
     { unfold has_comp.comp except.run,
       apply congr_arg,
       unfold cancellation,
       simp [disj_imp_imp,imp_self_eq_ident] },
     apply p_or_intro_left
   end
 , right_ident :=
   begin
     introv, cases x with x,
     have h : cat α (β || e) :=
        cancellation cat β x (lifted_pred.weaken _ _),
     { unfold has_comp.comp except.run,
       apply congr_arg,
       unfold cancellation,
       simp [select_left_disj], },
       apply p_or_intro_left
   end
 , imp := assume p q,
   except.mk ∘ lifted_pred.imp cat p (q || e) ∘ entails_p_or_of_entails_left
 , disj :=
   begin
     introv h₀ h₁,
     apply except.mk,
     apply disj,
     apply h₀.run,
     apply h₁.run
   end
 , disj_imp_imp := by { introv,
                        apply congr_arg,
                        simp [function.comp,disj_imp_imp], }
 , select_left_disj := by { introv, cases Pp,
                            simp [cancellation,function.comp],
                            rw [disj.select_left_disj',select_left_disj] }
 , comp_over_disj_right := by { introv, simp [cancellation,comp_over_disj_right], }
 , imp_comp_imp_eq_imp_trans :=
   begin
     introv,
     simp [function.comp,has_comp.comp,except.run,cancellation],
     apply congr_arg,
     rw [disj_imp_imp,imp_comp_imp_eq_imp_trans],
   end
 , imp_self_eq_ident := by { introv, refl }
 , disj_flip :=
   begin
     introv, cases P₀ with P₀, cases P₁ with P₁,
     unfold has_comp.comp except.run cancellation function.comp,
     apply congr_arg,
     rw [disj.select_left_disj',disj_flip],
   end }

instance except_disjunctive (e : pred' σ)
  [disjunctive cat]
: disjunctive (except e cat) :=
 { (_ : finite_disjunctive (except e cat)) with
  disj' := by { introv h, apply except.mk, apply disj', intro, apply (h x).run, } }

instance inv_cat (inv : pred' σ)
  [category cat]
: category (invariant inv cat) :=
 { ident := assume p, ⟨ ident cat ⟩
 , comp := assume p q r m₀ m₁, ⟨ m₀.run <<< m₁.run ⟩
 , left_ident  := by { intros, cases x, simp [has_comp.comp] }
 , right_ident := by { intros, cases x, simp [has_comp.comp] }
 , assoc := by { intros, cases x, simp [has_comp.comp] }
 }

instance inv_lifted (inv : pred' σ)
  [lifted_pred cat]
: lifted_pred (invariant inv cat) :=
 { (_ : category (invariant inv cat)) with
   imp := assume p q Hpq, ⟨ lifted_pred.imp _ _ _ (p_and_entails_p_and_right _ Hpq) ⟩
 , imp_comp_imp_eq_imp_trans := by { introv, simp [has_comp.comp,imp_comp_imp_eq_imp_trans] }
 , imp_self_eq_ident := by { introv, simp [ident,imp_self_eq_ident] }
 }

lemma hcongr_arg
: ∀ {p q : Prop} {Hp : p} {Hq : q}, p = q → Hp == Hq
  | p ._ Hp Hq rfl := heq.rfl

lemma mpr_eq_comp_imp [lifted_pred cat] {p p' q : pred' σ}
  (P : cat p q)
  (H : p' = p)
: eq.mpr (by subst p) P = (P <<< lifted_pred.imp cat p' p (by subst p)) :=
by { subst p, simp [imp_self_eq_ident,eq.mpr], }


instance inv_fin_disj (inv : pred' σ) {cat : pred' σ → pred' σ → Sort u}
  [finite_disjunctive cat]
: finite_disjunctive (invariant inv cat) :=
 { inv_lifted inv with
   disj :=
   begin
     introv h₀ h₁,
     apply invariant.mk,
     rw p_and_over_or_left,
     apply disj _ h₀.run h₁.run,
   end
 , disj_imp_imp :=
   begin
     introv, simp [lifted_pred.imp,disj_imp_imp,eq.mpr],
     apply congr_arg,
     apply eq_rec_of_heq_left,
     tactic.congr,
     simp [p_and_over_or_left],
     apply hcongr_arg,
     simp [p_and_over_or_left],
   end
 , select_left_disj :=
   begin
     introv,
     cases Pp with Pp,
     unfold has_comp.comp invariant.run,
     apply congr_arg,
     rw [mpr_eq_comp_imp, ← category.assoc, imp_comp_imp_eq_imp_trans, select_left_disj],
     { simp [p_and_over_or_left] },
   end
 , comp_over_disj_right :=
   begin
     introv,
     unfold has_comp.comp invariant.run,
     rw [mpr_eq_comp_imp, category.assoc,comp_over_disj_right, mpr_eq_comp_imp],
     all_goals { simp [p_and_over_or_left] },
   end
 , disj_flip :=
   begin
     introv,
     unfold has_comp.comp invariant.run,
     apply congr_arg,
     rw [disj_flip,mpr_eq_comp_imp, ← category.assoc, imp_comp_imp_eq_imp_trans],
     rw [@mpr_eq_comp_imp _ cat, ← category.assoc, imp_comp_imp_eq_imp_trans],
     all_goals { simp [p_and_over_or_left] },
   end
 }

instance inv_disj (inv : pred' σ) {cat : pred' σ → pred' σ → Sort u}
  [disjunctive cat]
: disjunctive (invariant inv cat) :=
 { inv_fin_disj inv with
   disj' :=
   begin
     introv H,
     apply invariant.mk,
     simp [p_and_over_p_exists_left],
     apply disj', intro,
     apply invariant.run (H x),
   end }
