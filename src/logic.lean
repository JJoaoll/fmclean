section propositional

variable (P Q R : Prop)

------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  (P → ¬¬P)  := by
  intro p
  intro np
  apply np 
  exact p

end propositional

theorem doubleneg_elim :
  ¬¬P → P  := by
  intro nnp
  by_cases p : P 
  exact p 
  contradiction 
  --apply nnp
 -- exact p

theorem doubleneg_law :
  ¬¬P ↔ P  := by
  apply Iff.intro 
  exact doubleneg_elim 
  exact doubleneg_intro P 

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
  intro h
  apply Or.elim h
  intro p 
  apply Or.inr 
  exact p 
  intro q 
  apply Or.inl 
  exact q


theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro h
  apply And.intro 
  exact And.right h
  exact And.left h

------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  := by
  intro h
  intro p 
  apply Or.elim h 
  intro np 
  apply False.elim
  exact np p
  intro q 
  exact q  

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  := by
  intro h
  intro np 
  apply Or.elim h
  intro p 
  apply False.elim 
  exact np p 
  intro q 
  exact q 
------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  := by
intro h 
intro nq 
intro p 
apply False.elim 
apply nq 
apply h
exact p 

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  := by
intro h
intro p 
by_cases q : Q 
exact q 
apply False.elim 
exact h q p

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  := by
  apply Iff.intro 
  exact impl_as_contrapositive 
  exact impl_as_contrapositive_converse

------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  := by
  intro h
  have h': (P∨¬P) := by 
    apply Or.inr; 
    intro p; 
    have h'': (P∨¬P) := by 
      apply Or.inl;
      exact p;
    exact h h''
  exact h h'

------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  := by
  intro h
  intro np  
  have h': (P -> Q) := by    
    intro p
    apply False.elim
    exact np p    
  have p := h h'
  exact np p

------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  := by
  intro h 
  intro j 
  apply Or.elim h
  apply And.left j 
  apply And.right j 
  
theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  := by
  intro h
  intro j 
  apply Or.elim j
  intro np
  apply np
  exact And.left h  
  intro nq
  apply nq
  exact And.right h


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  := by
  intro h 
  apply And.intro 
  intro j
  have h': (P ∨ Q) := by 
    apply Or.inl;
    exact j
  exact h h' 
  intro q
  have h': (P ∨ Q) := by 
    apply Or.inr;
    exact q
  exact h h' 

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  := by
  intro h 
  intro j 
  apply Or.elim j 
  intro p 
  apply And.left h 
  exact p 
  intro q 
  apply And.right h 
  exact q 

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  := by
  intro h 
  by_cases p : P 
  apply Or.inl 
  intro q 
  have h' : P ∧ Q := by
    apply And.intro; 
    exact p;
    exact q 
  exact h h' 
  apply Or.inr 
  exact p 

  /-apply Or.inl 
  intro q
  have h' : ¬Q ∨ ¬P := by 
    apply Or.inr;
    intro p;
    have h'' : P ∧ Q := by 
      apply And.intro; 
      exact p; 
      exact q;
    exact h h''  
  apply h'.elim 
  intro nq 
  exact nq q 
  intro np
  by_cases p : P 
  exact np p  -/

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  := by
  intro h 
  intro mh 
  apply h.elim
  intro nq 
  exact nq mh.right 
  intro np 
  exact np mh.left 


theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  := by
  apply Iff.intro 
  intro h 
  by_cases p : P 
  apply Or.inl 
  intro q
  have peq: P ∧ Q := by 
    apply And.intro;
    exact p;
    exact q;
  exact h peq 
  apply Or.inr
  intro p'
  exact p p' 
  exact demorgan_conj_converse  


theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  := by
  apply Iff.intro 
  apply demorgan_disj 
  apply demorgan_disj_converse
------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  := by
  intro h
  have j := h.right
  have p := h.left
  apply j.elim 
  intro q 
  apply Or.inl 
  apply And.intro 
  exact p 
  exact q 
  intro r 
  apply Or.inr 
  apply And.intro
  exact p 
  exact r 

  
  apply Or.inr

  

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  := by


theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  sorry,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  sorry,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  sorry,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  sorry,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  sorry,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  sorry,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  sorry,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  sorry,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  sorry,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  sorry,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  sorry,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate