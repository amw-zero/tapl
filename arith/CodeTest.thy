theory CodeTest

imports Main

begin

datatype color = Red | Green

definition "is_red c = (case c of Red \<Rightarrow> True | _ \<Rightarrow> False)"

export_code is_red Red in OCaml

end