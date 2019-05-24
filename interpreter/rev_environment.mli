type t

exception Not_bound

val empty : t
val extend : Syntax.tydecl -> Syntax.id -> t -> t
val lookup : Syntax.tydecl -> t -> Syntax.id
