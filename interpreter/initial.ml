open Syntax
open Eval
open Define

let alpha = -1

let option = "-1#option"

let option_body =
  let param = ["'a"] in
  let body =
    [Constructor ("None", TyNone "None");
     Constructor ("Some", TyStringVar "'a")] in
  (param, body)

let ref_rec = "-2#ref"

let ref_rec_body =
  let param = ["'a"] in
  let body =
    [Field ("contents", TyStringVar "'a", Mutable)] in
  (param, body)

let ref_fun = "ref"

let ref_fun_body =
  Record (ConsR (("contents", (Var "x", [])), EmpR))

let ref_fun_type =
  TyScheme ([alpha], TyFun (TyVar alpha, TyRecord (ref_rec, [TyVar alpha])))

let assign = "_assign"

let assign_body =
  FunExp (("y", []), (AssignExp ((Var "x", []), "contents", (Var "y", [])), []))

let assign_type =
  TyScheme ([alpha], TyFun (TyRecord (ref_rec, [TyVar alpha]), TyFun (TyVar alpha, TyUnit)))

let deref = "_deref"

let deref_body =
  MatchExp ((Var "x", []), [((RecordPattern (ConsR (("contents", (Var "_a", [])), EmpR)), []), (Var "_a", []))])

let deref_type =
  TyScheme ([alpha], TyFun (TyRecord (ref_rec, [TyVar alpha]), TyVar alpha))

let env =
  Environment.extend ref_fun (ProcV ("x", ref_fun_body, ref Environment.empty))
    (Environment.extend assign (ProcV ("x", assign_body, ref Environment.empty))
       (Environment.extend deref (ProcV ("x", deref_body, ref Environment.empty)) Environment.empty))

let tyenv =
  Environment.extend ref_fun ref_fun_type
    (Environment.extend assign assign_type
       (Environment.extend deref deref_type Environment.empty))

let defenv =
  Environment.extend option option_body
    (Environment.extend ref_rec ref_rec_body (Environment.empty))

let rev_defenv =
  Rev_environment.extend "None" (TyNone "None", option)
    (Rev_environment.extend "Some" (TyStringVar "'a", option)
       (Rev_environment.extend "contents" (TyStringVar "'a", ref_rec) (Rev_environment.empty)))

let store = Store.empty
