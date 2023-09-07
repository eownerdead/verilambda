theory Lambda
  imports Main
begin

smt_status help

datatype lam
  = LVar string
  | LApp lam lam (infix "°⇩λ" 200)
  | LAbs string lam ("λ⇩λ_. _" 300)

datatype db
  = Var nat
  | App db db (infix "°" 200)
  | Abs db ("λ_" 300)

primrec lift :: "db ⇒ nat ⇒ db" where
  lift_Var: "lift (Var i) k = (if i < k then Var i else Var (i+1))"
| lift_App: "lift (m ° n) k = lift m k ° lift n k"
| lift_Abs: "lift (λm) k = λlift m (k+1)"

primrec lam_to_db' :: "lam ⇒ (string ⇒ nat) ⇒ db" where
  "lam_to_db' (LVar x) σ = Var (σ x)"
| "lam_to_db' (m °⇩λ n) σ = (lam_to_db' m σ) ° (lam_to_db' n σ)"
| "lam_to_db' (λ⇩λx. m) σ = λlift (lam_to_db' m (σ(x:=0))) 0"

definition lam_to_db :: "lam ⇒ db" where
  "lam_to_db x = lam_to_db' x (λ_. 0)"

value "lam_to_db ((λ⇩λ''y''. (λ⇩λ''x''. (LVar ''y''))) °⇩λ (λ⇩λ''x''. LVar ''x''))"

primrec subst :: "db ⇒ nat ⇒ db ⇒ db" ("_[_::=_]" [300, 0, 0] 300) where
  subst_Var: "(Var i)[k::=e] = (if k < i then Var (i-1) else
                               if k = i then e else Var i)"
| subst_App: "(m ° n)[k::=e] = m[k::=e] ° n[k::=e]"
| subst_Abs: "(λ m)[k::=e] = λ(m[k+1::=lift e 1])"

inductive beta :: "db ⇒ db ⇒ bool" (infix "→⇩β" 50) where
  beta_appL: "m →⇩β m' ⟹ m ° n →⇩β m' ° n"
| beta_appR: "n →⇩β n' ⟹ m ° n →⇩β m ° n'"
| beta_abs: "m →⇩β m' ⟹ (λm) →⇩β λm'"
| beta_beta: "(λm) ° n →⇩β m[1::=n]"

abbreviation beta_reds :: "db ⇒ db ⇒ bool" (infix "→⇩β⇧*" 50) where
  "m →⇩β⇧* m' == beta⇧*⇧* m m'"

theorem
  shows "∃m'. lam_to_db m →⇩β⇧* m' ∧ lam_to_db ((λ⇩λx. LVar x) °⇩λ m) →⇩β⇧* m'"
proof (induct m)
  case (LVar x)
  have "lam_to_db (LVar y) = Var 0" by (simp add: lam_to_db_def)
  have "lam_to_db ((λ⇩λx. LVar x) °⇩λ LVar y) = (λVar 1) ° Var 0" by (simp add: lam_to_db_def)
  then show ?case
    apply (auto simp add: lam_to_db_def beta_beta)
next
  case (LApp m1 m2)
  then show ?case sorry
next
  case (LAbs x1a m)
  then show ?case sorry
qed

code_pred (modes: i ⇒ o ⇒ bool as reduce') beta .

definition "reduce t = Predicate.the (reduce' t)"

end
