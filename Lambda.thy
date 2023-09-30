theory Lambda
  imports Main "Nominal2.Nominal2" "HOL-Eisbach.Eisbach"
begin

atom_decl ident

nominal_datatype lam
  = Var ident
  | App lam lam (infix "\<degree>" 200)
  | Abs x::ident m::lam binds x in m ("\<lambda>[_]. _" 300)

lemma shows "(\<lambda>[x]. Var x) = \<lambda>[y]. Var y"
  by auto

ML \<open>
fun graph_aux_tac ctxt =
  SUBGOAL (fn (subgoal, i) =>
    (case subgoal of
      Const (@{const_name Trueprop}, _) $ (Const (@{const_name eqvt}, _) $ Free (f, _)) =>
        full_simp_tac (
          ctxt addsimps [@{thm eqvt_def}, Proof_Context.get_thm ctxt (f ^ "_def")]) i
    | _ => no_tac))
\<close>

method_setup eqvt_graph_aux =
  \<open>Scan.succeed (fn ctxt : Proof.context => SIMPLE_METHOD' (graph_aux_tac ctxt))\<close>
  "show equivariance of auxilliary graph construction for nominal functions"

method without_alpha_lst methods m =
  (match termI in H [simproc del: alpha_lst]: _ \<Rightarrow> \<open>m\<close>)

method Abs_lst =
  (match premises in
    "atom ?x \<sharp> c" and P [thin]: "[[atom _]]lst. _ = [[atom _]]lst. _" for c :: "'a::fs" \<Rightarrow>
      \<open>rule Abs_lst1_fcb2' [where c = c, OF P]\<close>
  \<bar> P [thin]: "[[atom _]]lst. _ = [[atom _]]lst. _" \<Rightarrow> \<open>rule Abs_lst1_fcb2' [where c = "()", OF P]\<close>)

method pat_comp_aux =
  (match premises in
    "x = (_ :: lam) \<Longrightarrow> _" for x \<Rightarrow> \<open>rule lam.strong_exhaust [where y = x and c = x]\<close>
  \<bar> "x = (Var _, _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule lam.strong_exhaust [where y = "fst x" and c = x]\<close>
  \<bar> "x = (_, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule lam.strong_exhaust [where y = "snd x" and c = x]\<close>
  \<bar> "x = (_, _, Var _) \<Longrightarrow> _" for x :: "_ :: fs" \<Rightarrow>
    \<open>rule lam.strong_exhaust [where y = "snd (snd x)" and c = x]\<close>)

method pat_comp = (pat_comp_aux; force simp: fresh_star_def fresh_Pair_elim)

method freshness uses fresh =
  (match conclusion in
    "_ \<sharp> _" \<Rightarrow> \<open>simp add: fresh_Unit fresh_Pair fresh\<close>
  \<bar> "_ \<sharp>* _" \<Rightarrow> \<open>simp add: fresh_star_def fresh_Unit fresh_Pair fresh\<close>)

method solve_eqvt_at =
  (simp add: eqvt_at_def; simp add: perm_supp_eq fresh_star_Pair)+

method nf uses fresh = without_alpha_lst \<open>
  eqvt_graph_aux, rule TrueI, pat_comp, auto, Abs_lst,
  auto simp: Abs_fresh_iff pure_fresh perm_supp_eq,
  (freshness fresh: fresh)+,
  solve_eqvt_at?\<close>

nominal_function subst :: "lam \<Rightarrow> ident \<Rightarrow> lam \<Rightarrow> lam" ("_[_::=_]" [300, 0, 0] 300) where
  lift_Var: "(Var i)[y::=s] = (if i = y then s else Var i)"
| lift_App: "(m \<degree> n)[y::=s] = m[y::=s] \<degree> n[y::=s]"
| lift_Abs: "atom x\<sharp>(y,s) \<Longrightarrow> (\<lambda>[x]. m)[y::=s] = \<lambda>[x]. (m[y::=s])"
  by (nf)

nominal_termination (eqvt) by lexicographic_order

inductive beta :: "lam \<Rightarrow> lam \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<beta>" 50) where
  appL: "m \<rightarrow>\<^sub>\<beta> m' \<Longrightarrow> m \<degree> n \<rightarrow>\<^sub>\<beta> m' \<degree> n"
| appR: "n \<rightarrow>\<^sub>\<beta> n' \<Longrightarrow> m \<degree> n \<rightarrow>\<^sub>\<beta> m \<degree> n'"
| abs: "m \<rightarrow>\<^sub>\<beta> m' \<Longrightarrow> (\<lambda>[x]. m) \<rightarrow>\<^sub>\<beta> \<lambda>[x]. m'"
| beta: "atom x\<sharp>n \<Longrightarrow> (\<lambda>[x]. m) \<degree> n \<rightarrow>\<^sub>\<beta> m[x::=n]"

equivariance beta

lemma fresh_subst:
  "atom x\<sharp>n \<Longrightarrow> x = y \<or> atom x\<sharp>m \<Longrightarrow> atom x\<sharp>(m[y::=n])"
  apply (nominal_induct m avoiding: x y n rule: lam.strong_induct)
    apply auto
  done

lemma fresh_subst':
  "atom x\<sharp>n \<Longrightarrow> atom x\<sharp>m \<Longrightarrow> atom x\<sharp>m[y::=n]"
  apply (nominal_induct m avoiding: x y n rule: lam.strong_induct)
    apply auto
  done

nominal_inductive beta avoids abs:x | beta:x
     apply (auto simp add: fresh_star_def fresh_subst)
  done

abbreviation beta_star :: "lam \<Rightarrow> lam \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50) where
  "x \<rightarrow>\<^sub>\<beta>\<^sup>* y \<equiv> beta\<^sup>*\<^sup>* x y"

inductive par_beta (infix "\<Rightarrow>\<^sub>\<beta>" 50) where
  app: "\<lbrakk> m \<Rightarrow>\<^sub>\<beta> m'; n \<Rightarrow>\<^sub>\<beta> n' \<rbrakk> \<Longrightarrow> m \<degree> n \<Rightarrow>\<^sub>\<beta> m' \<degree> n'"
| abs: "m \<Rightarrow>\<^sub>\<beta> m' \<Longrightarrow> (\<lambda>[x]. m) \<Rightarrow>\<^sub>\<beta> \<lambda>[x]. m'"
| beta: "\<lbrakk> m \<Rightarrow>\<^sub>\<beta> m'; n \<Rightarrow>\<^sub>\<beta> n' \<rbrakk> \<Longrightarrow> (\<lambda>[x]. m) \<degree> n \<Rightarrow>\<^sub>\<beta> m'[x::=n']"

equivariance par_beta

nominal_inductive par_beta .

abbreviation par_beta_star :: "lam \<Rightarrow> lam \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>\<beta>\<^sup>*" 50) where
  "x \<Rightarrow>\<^sub>\<beta>\<^sup>* y \<equiv> par_beta\<^sup>*\<^sup>* x y"

lemma par_beta_fresh:
  assumes "m \<Rightarrow>\<^sub>\<beta> m'" and "atom x\<sharp>m"
  shows "atom x\<sharp>m'"
  using assms
  apply (nominal_induct rule: par_beta.strong_induct)
     apply (auto simp: fresh_at_base fresh_subst fresh_subst')
  done

thm par_beta.induct

lemma abs_eq:
  assumes "(\<lambda>[x]. m) \<Rightarrow>\<^sub>\<beta> n"
  obtains t where "n = (\<lambda>[x]. t)" "m \<Rightarrow>\<^sub>\<beta> t"
  using assms
proof (nominal_induct "(\<lambda>[x]. m)" n avoiding: m rule: par_beta.strong_induct)
  case (abs m' m'' x')
  then show ?case
    apply (auto simp: Abs1_eq_iff par_beta.eqvt fresh_permute_left)
    by (metis par_beta.eqvt permute_flip_cancel2 par_beta_fresh)
qed

lemma
  assumes "m \<degree> n \<Rightarrow>\<^sub>\<beta> s"
  shows "(s = m' \<degree> n' \<and> m \<Rightarrow>\<^sub>\<beta> m' \<and> n \<Rightarrow>\<^sub>\<beta> n') \<or> (m = (\<lambda>[x]. t) \<and> s = t[x::=n'] \<and> t \<Rightarrow>\<^sub>\<beta> t' \<and> n \<Rightarrow>\<^sub>\<beta> n')"a
  using assms
  apply (nominal_induct "m \<degree> n" s rule: par_beta.strong_induct)

theorem confluent:
  assumes "m \<Rightarrow>\<^sub>\<beta> m\<^sub>1" and "m \<Rightarrow>\<^sub>\<beta> m\<^sub>2"
  shows "\<exists>u. m\<^sub>1 \<Rightarrow>\<^sub>\<beta> u \<and> m\<^sub>2 \<Rightarrow>\<^sub>\<beta> u"
  using assms
proof (nominal_induct m m\<^sub>1 avoiding: m\<^sub>2 rule: par_beta.strong_induct)
  case (app m m' n n')
  then show ?case by metis
next
  case (abs m m' x)
  hence ?case by (metis abs_eq par_beta.abs)
next
  case (beta m m' n n' x)
  then show ?case sorry
qed

end
