
import unitb.category.basic

universes u u₀ u₁ v

variable {k : Sort u₀}

variable {k}

variable {σ : Type u₀}

open predicate unitb

structure invariant (inv : pred' σ) (cat : pred' σ → pred' σ → Sort v) (p q : pred' σ) :=
  (run_invariant : cat (inv && p) (inv && q))

structure except
     (excp : pred' σ)
     (cat : pred' σ → pred' σ → Sort v)
     (p q : pred' σ) : Type v :=
  (run_excp : cat p (q || excp))

def except_lift (e : pred' σ)
  {cat : pred' σ → pred' σ → Sort u} [lifted_pred cat]
  {α β : pred' σ}
  (x : cat α β)
: except e cat α β :=
⟨ begin
    apply lifted_pred.mono_right _ _ _ x,
    apply p_or_intro_left,
  end ⟩

instance except_disjunctive (e : pred' σ) {cat : pred' σ → pred' σ → Sort u}
  [finite_disjunctive cat]
: finite_disjunctive (except e cat) :=
 { ident := by { intro, apply except.mk, apply lifted_pred.imp, apply p_or_intro_left }
 , comp  :=
   begin
     introv h₀ h₁,
     apply except.mk,
     apply cancellation,
     apply h₁.run_excp,
     apply h₀.run_excp,
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
     { unfold has_comp.comp except.run_excp,
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
     { unfold has_comp.comp except.run_excp,
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
     apply h₀.run_excp,
     apply h₁.run_excp
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
     simp [function.comp,has_comp.comp,except.run_excp,cancellation],
     apply congr_arg,
     rw [disj_imp_imp,imp_comp_imp_eq_imp_trans],
   end
 , imp_self_eq_ident := by { introv, refl } }
