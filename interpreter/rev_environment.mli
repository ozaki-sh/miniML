type t

exception Not_bound

val empty : t
val extend : Syntax.name -> (Syntax.ty option * Syntax.id) -> t -> t
val lookup : Syntax.name -> t -> (Syntax.ty option * Syntax.id) list
