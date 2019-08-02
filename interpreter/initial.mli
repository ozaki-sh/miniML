val env : Eval.dnval Environment.t
val tyenv : Syntax.tysc Environment.t
val defenv : (string list * Syntax.property list * Syntax.tydecl list) Environment.t
val rev_defenv : Rev_environment.t
val store : Eval.dnval Store.t
