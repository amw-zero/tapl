theory STLC

imports Main

begin 

datatype lctype =
  Func lctype lctype
  | Other
 
datatype lcterm =
  Var nat
  | Abstract lctype lcterm
  | Applic lcterm lcterm

type_synonym lccontext = "lcterm list"

fun shift :: "int \<Rightarrow> int \<Rightarrow> lcterm \<Rightarrow> lcterm" where
"shift c d (Var k) = (if k < (nat c) then Var k else Var (k + nat d))" |  
"shift c d (Abstract typ trm) = Abstract typ (shift (c + 1) d trm)" |
"shift c d (Applic t1 t2) = Applic (shift c d t1) (shift c d t2)"

fun subst :: "lcterm \<Rightarrow> nat \<Rightarrow> lcterm \<Rightarrow> lcterm" where
"subst s j (Var k) = (if k  = j then s else (Var k))" |
"subst s j (Abstract typ t) = (Abstract typ (subst (shift 0 1 s) (j + 1) t))" |
"subst s j (Applic t1 t2) = (Applic (subst s j t1) (subst s j t2))"

value "subst (Abstract Other (Var 0)) 0 (Var 1)"

definition "is_value t = (case t of
  Abstract _ _ \<Rightarrow> True
| _ \<Rightarrow> False)"

definition "eval_applic v t = shift 0 (-1) (subst (shift 0 1 v) 0 t)"

inductive eval :: "lcterm \<Rightarrow> lcterm \<Rightarrow> bool" where
app1: "\<lbrakk> eval t1 t1' \<rbrakk> \<Longrightarrow> eval (Applic t1 t2) (Applic t1' t2)" |
app2: "\<lbrakk> eval t2 t2'; is_value v \<rbrakk> \<Longrightarrow> eval (Applic v t2) (Applic v t2')" |
appAbs: "\<lbrakk> is_value v \<rbrakk> \<Longrightarrow> eval (Applic (Abstract typ t) v) (eval_applic v t)"

type_synonym typ_context = "lctype list"

definition add_type :: "lctype \<Rightarrow> typ_context \<Rightarrow> typ_context" where
"add_type t ctx = t # ctx"

definition var_type :: "(nat,  lctype) prod \<Rightarrow> typ_context \<Rightarrow> bool" where
"var_type var ctx = (fst var < length ctx \<and> nth ctx (fst var) = snd var)" 

inductive has_type :: "typ_context \<Rightarrow> lcterm \<Rightarrow> lctype \<Rightarrow> bool" where
tvar: "\<lbrakk> var_type (x, T) ctx \<rbrakk> \<Longrightarrow> has_type ctx (Var x) T" |
tabs: "\<lbrakk> 
  add_type T1 ctx = ctx'; 
  has_type ctx' t T2 
\<rbrakk> \<Longrightarrow> has_type ctx (Abstract T1 t) (Func T1 T2)" |
"\<lbrakk>
  has_type ctx t1 (Func T1 T2);
  has_type ctx t2 T1
\<rbrakk> \<Longrightarrow> has_type ctx (Applic t1 t2) T2"

lemma inversion:
  "has_type ctx (Var v) R \<Longrightarrow> var_type (v, R) ctx"
  by (auto elim: has_type.cases)

end