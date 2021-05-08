theory Sequent_Solver
  imports Main "Propositional_Proof_Systems.SC"
begin

ML_file \<open>./solver.ML\<close>

method_setup solve_sequent = \<open>
Scan.succeed (fn ctxt => (SIMPLE_METHOD (solver_tac ctxt)))
\<close>

lemma "(Atom P),\<bottom>, \<Gamma>\<Rightarrow>\<Delta>"
by solve_sequent

lemma "Atom Q,Atom ''s'',{#}\<Rightarrow>Atom R,\<bottom>,Atom ''s'',\<Delta>"
by solve_sequent

lemma "Atom P,F,Not F,\<Gamma>\<Rightarrow>\<Delta>"
by solve_sequent

lemma "\<Gamma>\<Rightarrow>Atom P,Not F,F,\<Delta>"
by solve_sequent

lemma "Not P,P,\<Gamma>\<Rightarrow>F,Not F,\<Delta>"
by solve_sequent

lemma "\<Gamma>\<Rightarrow>Not \<bottom>,\<Delta>"
by solve_sequent

lemma "And \<bottom> P, \<Gamma>\<Rightarrow>\<Delta>"
by solve_sequent

lemma "Not P,Atom Q,And P \<bottom>,\<Gamma>\<Rightarrow>\<Delta>"
by solve_sequent

lemma "P,Q,\<Gamma>\<Rightarrow>And Q P,\<Delta>"
by solve_sequent

lemma "And (Or P Q) G,\<Gamma>\<Rightarrow>Or (And Q P) G,\<Delta>"
by solve_sequent

(* Complexe example form lecture *)
lemma "{#}\<Rightarrow>Imp(And(Or(Atom P)(Atom R))(Or(Atom Q)(Not(Atom R))))(Or(Atom P)(Atom Q)),{#}"
by solve_sequent

(* Invalid example from lecture *)
(* lemma "Or (Atom P) (Atom Q),{#}\<Rightarrow>And (Atom P) (Atom Q),{#}"
apply solve_sequent
sorry *)

lemma tertium_non_datur: "{#}\<Rightarrow>F,Not F,\<Delta>"
by solve_sequent

lemma consequentia_mirabilis: "Imp (Not F) F,{#}\<Rightarrow>{#F#}"
by solve_sequent

lemma "{#}\<Rightarrow>Not (Not(Imp (Imp (Not F) F) F)),{#}"
by solve_sequent
end