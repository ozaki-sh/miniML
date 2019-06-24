type 'a t

exception Not_bound

val empty : 'a t
val extend : Syntax.id -> 'a -> 'a t -> 'a t
val lookup : Syntax.id -> 'a t -> 'a
val map : ('a -> 'b) -> 'a t -> 'b t
val fold_right : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b
(*val member : Syntax.id -> 'a t -> bool*)
val partition : ('a -> bool) -> 'a t -> 'a t * 'a t
val dlookup : Syntax.id -> 'a t -> 'a
val ilookup : Syntax.id -> 'a t -> Syntax.id
