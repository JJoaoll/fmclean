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

--end propositional

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
  exact doubleneg_elim  P 
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
  exact impl_as_contrapositive P Q 
  exact impl_as_contrapositive_converse P Q   

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
  exact demorgan_conj_converse P Q 


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
 

  

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  := by
  intro h 
  apply Or.elim h 
  intro h'   
  apply And.intro 
  exact h'.left 
  apply Or.inl 
  exact h'.right 
  intro h' 
  apply And.intro 
  exact h'.left 
  apply Or.inr 
  exact h'.right 

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  := by 
  intro h 
  apply Or.elim h 
  intro p 
  apply And.intro
  apply Or.inl
  exact p 
  apply Or.inl
  exact p 
  intro h' 
  apply Or.elim h 
  intro p 
  apply And.intro 
  apply Or.inl
  exact p 
  apply Or.inr
  exact h'.right 
  intro qer 
  apply And.intro 
  apply Or.inr 
  exact qer.left 
  apply Or.inr 
  exact qer.right

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  := by
  intro h 
  apply Or.elim h.left 
  intro p 
  apply Or.inl 
  exact p 
  intro q 
  apply Or.elim h.right 
  intro p 
  apply Or.inl 
  exact p 
  intro r 
  apply Or.inr 
  apply And.intro 
  exact q 
  exact r 

------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  := by
  intro h 
  intro p 
  intro q 
  have peq : (P ∧ Q) := by 
    apply And.intro; 
    exact p; 
    exact q
  exact h peq    

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  := by
  intro h 
  intro peq 
  have qtr:= h peq.left 
  have r:= qtr peq.right 
  exact r  



------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  := by
  intro p   
  exact p 
------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  := by
  intro p 
  apply Or.inl 
  exact p

theorem weaken_disj_left :
  Q → (P∨Q)  := by
  intro q 
  apply Or.inr 
  exact q 

theorem weaken_conj_right :
  (P∧Q) → P  := by
  intro peq 
  exact peq.left   

theorem weaken_conj_left :
  (P∧Q) → Q  := by
  intro peq 
  exact peq.right 

theorem conj_idempot :
  (P∧P) ↔ P := by
  apply Iff.intro
  intro pep 
  exact pep.left 
  intro p 
  apply And.intro 
  exact p 
  exact p   

theorem disj_idempot :
  (P∨P) ↔ P  := by
  apply Iff.intro
  intro pop 
  apply Or.elim pop 
  intro p 
  exact p 
  intro p 
  exact p 
  intro p 
  apply Or.inr 
  exact p 

end propositional


----------------------------------------------------------------


section predicate

variable (U : Type)
variable (P Q : U -> Prop)


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  := by
  intro h 
  intro a 
  intro Pa
  apply h 
  apply Exists.intro a Pa

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  := by
  intro h 
  intro Epx 
  apply Exists.elim Epx 
  intro a 
  intro Pa 
  have nPa := h a 
  exact nPa Pa 

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  := by
  intro h 
  apply Classical.byContradiction -- RAA
  -- by_cases lem : (∃ x, ¬P x)
  intro ne 
  apply h 
  intro a 
  by_cases Pa : P a
  exact Pa 
  have Px : ∃ (x : U), ¬P x := by
    apply Exists.intro a 
    exact Pa
  apply False.elim  
  apply ne 
  exact Px 

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  := by
  intro e 
  intro pt 
  apply Exists.elim e 
  intro a 
  intro Pa 
  exact Pa (pt a)

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  := by
  apply Iff.intro 
  exact demorgan_forall U P 
  exact demorgan_forall_converse U P 


theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  := by 
  apply Iff.intro 
  exact demorgan_exists U P 
  exact demorgan_exists_converse U P 
------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  := by 
  intro h 
  intro h2
  apply Exists.elim h 
  intro a 
  intro Pa 
  have j := h2 a 
  apply j 
  exact Pa 

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  := by
  intro h 
  intro he 
  apply Exists.elim he 
  intro a 
  intro nPa 
  have j:= h a 
  apply nPa 
  exact j
theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  := by 
  intro h 
  intro ha 
  by_cases Pha : P ha
  exact Pha 
  apply False.elim
  apply h 
  apply Exists.intro ha 
  exact Pha 
  
theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  := by 
  intro h 
  apply Classical.byContradiction
  intro h2 
  have h3: (∀x, ¬P x) := by
    intro a
    intro px
    have Epx : (∃x, P x) := by
      exact Exists.intro a px
    exact h2 Epx
  exact h h3


theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  := by 
  apply Iff.intro 
  exact forall_as_neg_exists U P 
  exact forall_as_neg_exists_converse U P  


theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  := by 
  apply Iff.intro 
  exact exists_as_neg_forall U P 
  exact exists_as_neg_forall_converse U P   

------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  := by
intro h
apply Exists.elim h
intro a 
intro has
apply And.intro 
apply Exists.intro a has.left 
apply Exists.intro a has.right 
--  intro samir 
--  apply Exists.elim samir 
--  intro tonhao 
--  intro tonhaos 
--  apply And.intro 
--  apply Exists.intro tonhao tonhaos.left 

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  := by
  intro h 
  apply Exists.elim h
  intro a 
  intro has 
  apply Or.elim has
  intro Pa 
  apply Or.inl 
  exact Exists.intro a Pa
  intro Qa 
  apply Or.inr 
  exact Exists.intro a Qa

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  := by
  intro h 
  apply Or.elim h 
  intro hpa
  apply Exists.elim hpa
  intro a
  intro Pa
  apply Exists.intro a
  apply Or.inl 
  exact Pa 
  intro hqa
  apply Exists.elim hqa
  intro a
  intro Qa
  apply Exists.intro a
  apply Or.inr 
  exact Qa

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  := by
  intro h 
  apply And.intro 
  intro a 
  have j:= h a 
  exact j.left   
  intro a 
  have j:= h a 
  exact j.right

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  := by
  intro h 
  intro a   
  apply And.intro
  have Pa:= h.left a 
  exact Pa 
  have Qa:= h.right a 
  exact Qa


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  := by
  intro h 
  apply Or.elim h 
  intro Pa 
  intro a 
  apply Or.inl 
  exact Pa a 
  intro Qa 
  intro a 
  apply Or.inr 
  exact Qa a   


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