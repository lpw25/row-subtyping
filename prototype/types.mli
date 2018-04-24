
module Constructor : sig

  type t

  val of_string : string -> t

  val to_string : t -> string

  module CSet : sig

    type constructor = t

    type t

    val empty : t

    val singleton : constructor -> t

    val union : t -> t -> t

    val inter : t -> t -> t

    val diff : t -> t -> t

    val is_empty : t -> bool

  end

end

module Var : sig

  type t

  val fresh : unit -> t

  module Set : Set.S with type elt = t

end

module Ident : sig

  type t

  val fresh : string -> t

  module Set : Set.S with type elt = t

end

module rec Type : sig

  type t

  val var : Var.t -> Kind.t -> t

  val constructor : Constructor.t -> t -> t

  val or_ : t -> t -> t

  val proj : t -> Constructor.CSet.t -> t

  val row : t -> t

  val variant : t -> t

  val arrow : t -> t -> t

  val top : Constructor.CSet.t -> t

  val bot : Constructor.CSet.t -> t

  val meet : t -> t -> t

  val join : t -> t -> t

  val free_variables : t -> Var.Set.t

  val subst : Subst.t -> t -> t

  val generalize : Env.t -> Type.t -> Scheme.t

  val unify : t -> t -> Subst.t Result.t

end

and Kind : sig

  type t

  val free_variables : t -> Var.Set.t

  val subst : Subst.t -> t -> t

  val type_ : t

  val row : Constructor.CSet.t -> t

  val range : Type.t -> Type.t -> t

end

and Subst : sig

  type t

end

and Error : sig

  type t

end

and Result : sig

  type 'a t = ('a, Error.t) result

  val return : 'a -> 'a t

  val bind : 'a t -> ('a -> 'b t) -> 'b t

  val (>>=) : 'a t -> ('a -> 'b t) -> 'b t

end

and Scheme : sig

  type t

  val of_type : Type.t -> t

  val instantiate : t -> Type.t

end

and Env : sig

  type t

  val add : Ident.t -> Scheme.t -> t -> t

  val lookup : t -> Ident.t -> Scheme.t

  val free_variables : t -> Var.Set.t

  val subst : Subst.t -> t -> t

end

module Printing : sig

  val print : Type.t -> unit

end
