theory Lambda
  imports Main
begin

datatype db
  = Var nat
  | App db db (infix "°" 200)
  | Abs db ("λ_" 300)

primrec lift :: "db ⇒ nat ⇒ db" where
  lift_Var: "lift (Var i) k = (if i < k then Var i else Var (i+1))"
| lift_App: "lift (m ° n) k = lift m k ° lift n k"
| lift_Abs: "lift (λm) k = λlift m (k+1)"

primrec subst :: "db ⇒ nat ⇒ db ⇒ db" ("_[_::=_]" [300, 0, 0] 300) where
  lift_Var: "(Var i)[k::=e] = (if k < i then Var (i-1) else
                               if k = i then e else Var i)"
| lift_App: "(m ° n)[k::=e] = m[k::=e] ° n[k::=e]"
| lift_Abs: "(λ m)[k::=e] = λ(m[k+1::=lift e 0])"

inductive beta :: "db ⇒ db ⇒ bool" (infix "→⇩β" 50) where
  appL: "m →⇩β m' ⟹ m ° n →⇩β m' ° n"
| appR: "n →⇩β n' ⟹ m ° n →⇩β m ° n'"
| abs: "m →⇩β m' ⟹ (λm) →⇩β λm'"
| beta: "(λm) ° n →⇩β m[0::=n]"

abbreviation beta_reds :: "db ⇒ db ⇒ bool" (infix "→⇩β⇧*" 50) where
  "x →⇩β⇧* y ≡ beta⇧*⇧* x y"

(*inductive beta_star :: "db ⇒ db ⇒ bool" (infix "→⇩β⇧*" 50) where
  refl: "x →⇩β⇧* x"
| step: "x →⇩β y ⟹ y →⇩β⇧* z ⟹ x →⇩β⇧* z"*)

(*lemma star_beta_abs:
  assumes "m →⇩β⇧* m'"
    shows "(λm) →⇩β⇧* λm'"
  using assms
proof (induct rule: rtranclp_induct)
qed (auto intro: abs)*)

lemma abs_eq:
  assumes "(λm) →⇩β⇧* n" and "m →⇩β⇧* m'"
    shows "n = λm'"
  using assms
  nitpick
proof (induct m rule: db.induct)
  case (Var x)
  then show ?case sorry
next
  case (App x1a x2)
  assume "(λm) →⇩β (x1a ° x2)"
  hence "(λm) →⇩β (x1a ° x2) ⟹ False"
  apply induct
  apply auto
  thus "False"
next
  case (Abs x)
  then show ?case sorry
qed (auto simp add: beta.beta beta.abs beta.appL beta.appR)  
  
  
proof (induct n)
  case abs
  from assms show ?case by auto


theorem diamond:
  assumes "x →⇩β y" "x →⇩β z"
    shows "∃u. y →⇩β⇧* u ∧ z →⇩β⇧* u"
  using assms
proof (induct x y arbitrary: z)
  from assms show ?case by auto


theorem diamond:
  assumes "x →⇩β y" "x →⇩β z"
    shows "∃u. y →⇩β⇧* u ∧ z →⇩β⇧* u"
  using assms
proof (induct x y arbitrary: z)
  case (appL m m' n)
  then show ?case by 
next
  case (appR n n' m)
  then show ?case sorry
next
  case (abs m m')
  assume 1:"m →⇩β m'"
     and 2: "⋀z'. m →⇩β z' ⟹ ∃u. m' →⇩β⇧* u ∧ z' →⇩β⇧* u"
     and 3: "(λm) →⇩β z"
  from 3 and 1 have 4: "z = λm'" by (simp add: abs_eq)
  from 1 have "(λm) →⇩β λm'" by (rule beta.abs)
  have "∃u. (λm') →⇩β⇧* u" by auto
  hence "∃u. (λm') →⇩β⇧* u ∧ (λm') →⇩β⇧* u" by auto
  from 4 and this show ?case by auto
next
  case (beta m n)
  then show ?case sorry
qed

     

code_pred (modes: i ⇒ o ⇒ bool as reduce') beta .

definition "reduce t = Predicate.the (reduce' t)"

value "reduce ((λVar 0) ° Var 0) ° Var 0"

end
