type 'a t

val empty : 'a t
val extend : int -> 'a -> 'a t -> 'a t
val lookup : int -> 'a t -> 'a
val update : int -> 'a -> 'a t -> 'a t
