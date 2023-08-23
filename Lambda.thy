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

code_pred (modes: i ⇒ o ⇒ bool as reduce') beta .

definition "reduce t = Predicate.the (reduce' t)"

end
