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
  (param, [Safe], body)

let ref_rec = "-2#ref"

let ref_rec_body =
  let param = ["'a"] in
  let body =
    [Field ("contents", TyStringVar "'a", Mutable)] in
  (param, [Out], body)

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

let env_l =
  [(ref_fun, ProcV ("x", ref_fun_body, ref Environment.empty));
   (assign, ProcV ("x", assign_body, ref Environment.empty));
   (deref, ProcV ("x", deref_body, ref Environment.empty))]

let tyenv_l =
  [(ref_fun, ref_fun_type);
   (assign, assign_type);
   (deref, deref_type)]

let defenv_l =
  [(option, option_body);
   (ref_rec, ref_rec_body)]

let rev_defenv_l =
  [("None", (TyNone "None", option));
   ("Some", (TyStringVar "'a", option));
   ("contents", (TyStringVar "'a", ref_rec))]


let rec make_env l env =
  match l with
    [] -> env
  | (id, value) :: rest ->
     Environment.extend id value (make_env rest env)

let rec make_rev_defenv l rev_env =
  match l with
    [] -> rev_env
  | (name, ty) :: rest ->
     Rev_environment.extend name ty (make_rev_defenv rest rev_env)


let env = make_env env_l Environment.empty

let tyenv = make_env tyenv_l Environment.empty

let defenv = make_env defenv_l Environment.empty

let rev_defenv = make_rev_defenv rev_defenv_l Rev_environment.empty

let store = Store.empty
