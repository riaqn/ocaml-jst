open Solver_intf

(* [Lattices] specialized to [type 'a obj = unit] *)
module type Lattice = sig
  type t

  val min : t
  val max : t

  val le : t -> t -> bool
  val join : t -> t -> t
  val meet : t -> t -> t
  val print : Format.formatter -> t -> unit
end

module type Lattice_indexed_bound = sig
  module Index : sig
    type t
  end

  type t

  val min : t
  val max : Index.t -> t
  val le : t -> t -> bool
  val join : t -> t -> t
  val meet : t -> t -> t
  val print : Format.formatter -> t -> unit
end

module type Common = sig
  module Const : Lattice

  type error
  type 'd t
  type l = (allowed * disallowed) t
  type r = (disallowed * allowed) t
  type lr = (allowed * allowed) t

  val min : lr
  val max : lr
  val disallow_right : ('l * 'r) t -> ('l * disallowed) t
  val disallow_left : ('l * 'r) t -> (disallowed * 'r) t
  val allow_right : ('l * allowed) t -> ('l * 'r) t
  val allow_left : (allowed * 'r) t -> ('l * 'r) t
  val newvar : ?hint:string -> unit -> ('l * 'r) t
  val submode : (allowed * 'r) t -> ('l * allowed) t -> (unit, error) result
  val equate : lr -> lr -> (unit, error) result
  val submode_exn : (allowed * 'r) t -> ('l * allowed) t -> unit
  val equate_exn : lr -> lr -> unit
  val join : (allowed * 'r) t list -> left_only t
  val meet : ('l * allowed) t list -> right_only t
  val newvar_above : ?hint:string -> (allowed * 'r) t -> ('l * 'r_) t * bool
  val newvar_below : ?hint:string -> ('l * allowed) t -> ('l_ * 'r) t * bool

  val print :
    ?verbose:bool -> ?axis:string -> Format.formatter -> ('l * 'r) t -> unit

  val print_simple : Format.formatter -> ('l * 'r) t -> unit
  val constrain_lower : (allowed * 'r) t -> Const.t
  val constrain_upper : ('l * allowed) t -> Const.t
  val check_const : ('l * 'r) t -> Const.t option
  val of_const : Const.t -> ('l * 'r) t
  val legacy : lr
end

module type Common_indexed_bound = sig
  module Index : sig
    type t
  end
  module Const : Lattice_indexed_bound with module Index := Index

  type error
  type 'd t
  type l = (allowed * disallowed) t
  type r = (disallowed * allowed) t
  type lr = (allowed * allowed) t

  val min : lr
  val max : Index.t -> ('l * 'r) t
  val disallow_right : ('l * 'r) t -> ('l * disallowed) t
  val disallow_left : ('l * 'r) t -> (disallowed * 'r) t
  val allow_right : ('l * allowed) t -> ('l * 'r) t
  val allow_left : (allowed * 'r) t -> ('l * 'r) t
  val newvar : Index.t -> ?hint:string -> unit -> ('l * 'r) t
  val submode : (allowed * 'r) t -> ('l * allowed) t -> (unit, error) result
  val equate : lr -> lr -> (unit, error) result
  val submode_exn : (allowed * 'r) t -> ('l * allowed) t -> unit
  val equate_exn : lr -> lr -> unit
  val join : (allowed * 'r) t list -> left_only t
  val meet : ('l * allowed) t list -> right_only t
  val newvar_above : Index.t -> ?hint:string -> (allowed * 'r) t -> ('l * 'r_) t * bool
  val newvar_below : Index.t -> ?hint:string -> ('l * allowed) t -> ('l_ * 'r) t * bool

  val print :
    ?verbose:bool -> ?axis:string -> Format.formatter -> ('l * 'r) t -> unit

  val print_simple : Format.formatter -> ('l * 'r) t -> unit
  val constrain_lower : Index.t -> (allowed * 'r) t -> Const.t
  val constrain_upper : Index.t -> ('l * allowed) t -> Const.t
  val check_const : Index.t -> ('l * 'r) t -> Const.t option
  val of_const : Const.t -> ('l * 'r) t
end


module type Value = sig

  module Regionality : Common_indexed_bound
  module Uniqueness : Common
  module Linearity : Common

end

module type S = sig
  type nonrec allowed = allowed
  type nonrec disallowed = disallowed

  type ('a, 'b) monadic_comonadic = {monadic : 'a; comonadic : 'b}

  module Locality : sig
    module Const : sig
      type t = Global | Local
      include Lattice with type t := t
    end
    type error = unit

    include Common with module Const := Const and type error := error

    val global : lr
    val local : lr
    val constrain_legacy : (allowed * 'r) t -> Const.t
  end

  module Regionality : sig
    module Index : sig
      type t
      val innermost : t
      val outermost : t

      (* [val exit_exn : t -> t ]
         is not provided on purpose; you should record the old index before
         [enter] if you plan to exit later. *)

      val enter : t -> t

      val print : Format.formatter -> t -> unit
    end

    module Const : sig
        type t
        include Lattice_indexed_bound with type t := t and module Index = Index
        val global : t

        val local : Index.t -> t

        val escape : Index.t -> t
        (** returns the mode needed to escape certain region *)
    end
    type error = unit
    include Common_indexed_bound with module Index := Index and module Const := Const and type error := error

    val legacy : lr
    val global : lr
    val local : Index.t -> lr
    val constrain_legacy : Index.t -> (allowed * 'r) t -> Const.t
  end

  module Linearity : sig
    module Const : sig
      type t = Many | Once
      include Lattice with type t := t
    end
    type error = unit
    include Common with module Const := Const and type error := error

    val many : lr
    val once : lr
    val constrain_legacy : (allowed * 'r) t -> Const.t
  end

  module Uniqueness : sig

    module Const : sig
      type t = Unique | Shared
      include Lattice with type t := t
    end
    type error = unit
    include Common with module Const := Const and type error := error

    val shared : lr
    val unique : lr
    val constrain_legacy : ('l * allowed) t -> Const.t
  end

  module Value : sig
    module Monadic : sig
      include Common with type error = [`Uniqueness]
      val check_const : ('l * 'r) t -> Uniqueness.Const.t option
    end
    module Comonadic : sig
      include Common_indexed_bound
      with type error = [`Regionality | `Linearity ]
      with module Index := Regionality.Index

      val check_const : Regionality.Index.t -> ('l * 'r) t -> (Regionality.Const.t option) * (Linearity.Const.t option)
      val linearity : ('l * 'r) t -> ('l * 'r) Linearity.t
    end

    module Const : sig
      include Lattice_indexed_bound with type t =
        Regionality.Const.t * Linearity.Const.t * Uniqueness.Const.t
        and module Index := Regionality.Index
      val legacy : t
    end

    type error = [ `Regionality | `Uniqueness | `Linearity ]

    type 'd t = ('d Monadic.t, 'd Comonadic.t) monadic_comonadic

    include Common_indexed_bound with
    module Index := Regionality.Index and
    module Const := Const and type error := error and type 'd t := 'd t

    val legacy : lr

    (* some overriding *)
    val print : ?verbose:bool -> Format.formatter -> ('l * 'r) t -> unit

    val check_const :
      Regionality.Index.t ->
      ('l * 'r) t ->
      (Regionality.Const.t option) *
      (Linearity.Const.t option) *
      (Uniqueness.Const.t option)

    val regionality : ('l * 'r) t -> ('l * 'r) Regionality.t
    val uniqueness : ('l * 'r) t -> ('l * 'r) Uniqueness.t
    val linearity : ('l * 'r) t -> ('l * 'r) Linearity.t
    val max_with_uniqueness : Regionality.Index.t -> ('l * 'r) Uniqueness.t -> (disallowed * 'r) t
    val min_with_uniqueness : ('l * 'r) Uniqueness.t -> ('l * disallowed) t
    val min_with_regionality :  ('l * 'r) Regionality.t -> ('l * disallowed) t
    val max_with_regionality :  ('l * 'r) Regionality.t -> (disallowed * 'r) t
    val min_with_linearity :  ('l * 'r) Linearity.t -> ('l * disallowed) t
    val max_with_linearity : Regionality.Index.t -> ('l * 'r) Linearity.t -> (disallowed * 'r) t
    val set_regionality_min : ('l * 'r) t -> ('l * disallowed) t
    val set_regionality_max : Regionality.Index.t -> ('l * 'r) t -> (disallowed * 'r) t
    val set_linearity_min : ('l * 'r) t -> ('l * disallowed) t
    val set_linearity_max :  ('l * 'r) t -> (disallowed * 'r) t
    val set_uniqueness_min : ('l * 'r) t -> ('l * disallowed) t
    val set_uniqueness_max : ('l * 'r) t -> (disallowed * 'r) t
    val constrain_legacy : Regionality.Index.t -> lr -> Const.t
  end


  module Alloc : sig
      module Monadic : sig
        include Common with type error = [`Uniqueness]
        val check_const : ('l * 'r) t -> Uniqueness.Const.t option
      end
      module Comonadic : sig
        include Common with type error = [`Locality | `Linearity ]
        val check_const : ('l * 'r) t -> (Locality.Const.t option) * (Linearity.Const.t option)
      end

      module Const : sig
        include Lattice with type t =
        Locality.Const.t * Linearity.Const.t * Uniqueness.Const.t
        val legacy : t
        val close_over : t -> t
        val partial_apply : t -> t
      end

      type error = [ `Locality | `Uniqueness | `Linearity ]

      type 'd t = ('d Monadic.t, 'd Comonadic.t) monadic_comonadic

      include Common with module Const := Const and type error := error and type 'd t := 'd t

      (* some overriding *)
      val print : ?verbose:bool -> Format.formatter -> ('l * 'r) t -> unit

      val check_const :
        ('l * 'r) t ->
        (Locality.Const.t option) *
        (Linearity.Const.t option) *
        (Uniqueness.Const.t option)

      val locality : ('l * 'r) t -> ('l * 'r) Locality.t
      val uniqueness : ('l * 'r) t -> ('l * 'r) Uniqueness.t
      val linearity : ('l * 'r) t -> ('l * 'r) Linearity.t
      val max_with_uniqueness : ('l * 'r) Uniqueness.t -> (disallowed * 'r) t
      val min_with_uniqueness : ('l * 'r) Uniqueness.t -> ('l * disallowed) t
      val min_with_locality : ('l * 'r) Locality.t -> ('l * disallowed) t
      val max_with_locality : ('l * 'r) Locality.t -> (disallowed * 'r) t
      val min_with_linearity : ('l * 'r) Linearity.t -> ('l * disallowed) t
      val max_with_linearity : ('l * 'r) Linearity.t -> (disallowed * 'r) t
      val set_locality_min : ('l * 'r) t -> ('l * disallowed) t
      val set_locality_max : ('l * 'r) t -> (disallowed * 'r) t
      val set_linearity_min : ('l * 'r) t -> ('l * disallowed) t
      val set_linearity_max : ('l * 'r) t -> (disallowed * 'r) t
      val set_uniqueness_min : ('l * 'r) t -> ('l * disallowed) t
      val set_uniqueness_max : ('l * 'r) t -> (disallowed * 'r) t
      val constrain_legacy : lr -> Const.t

      val close_over : (allowed * 'r) Comonadic.t -> ('l * allowed) Monadic.t -> l
      val partial_apply : (allowed * 'r) t -> l

  end

  val unique_to_linear : ('l * 'r) Uniqueness.t -> ('r * 'l) Linearity.t
  (** maps uniqueness to linearity  *)

  val linear_to_unique : ('l * 'r) Linearity.t -> ('r * 'l) Uniqueness.t
  (** maps linearity to uniqueness *)

  (* val instantiate_local : region:Regionality.Const.Region.t -> ('l * 'r) Locality.t -> ('l * disallowed) Regionality.t
  (** maps L to [region+1], G to 0 *)

  val generalize_local : region:Regionality.Const.Region.t -> ('l * 'r) Regionality.t -> ('l * 'r) Locality.t
  * maps maps <=[region] to G, >[region] to L *)

  val regional_to_local : Regionality.Index.t -> ('l * 'r) Regionality.t -> ('l * 'r) Locality.t

  val locality_as_regionality : Regionality.Index.t -> ('l * 'r) Locality.t -> ('l * 'r) Regionality.t

  val regional_to_global : Regionality.Index.t -> ('l * 'r) Regionality.t -> ('l * 'r) Locality.t


  val alloc_as_value : Regionality.Index.t -> ('l * 'r) Alloc.t -> ('l * 'r) Value.t
  (** similar to [locality_as_regionality], behaves as identity on other axes *)

  (* val alloc_to_value_l2r : ('l * 'r) Alloc.t -> ('l * disallowed) Value.t *)

  (* not used; only for completeness*)
  (* val alloc_to_value_g2r : Regionality.Const.t -> ('l * 'r) Alloc.t -> (disallowed * 'r) Value.t *)

  (* val value_to_alloc : region:Regionality.Const.Region.t ->
    ('l * 'r) Value.t -> ('l * 'r) Alloc.t *)
  (* similar to [generalize_local], behaves as identity in other axes *)

  (* val alloc_to_value : outer_region:Regionality.Const.Region.t ->
    ('l * 'r) Alloc.t -> ('l * disallowed) Value.t *)
  (* similar to [instantiate_local], behaves as identity in other axes *)


  val alloc_to_value_l2r : Regionality.Index.t -> ('l * 'r) Alloc.t -> ('l * disallowed) Value.t
  (** similar to [locality_to_regionality], behaves as identity in other axes *)

  val value_to_alloc_r2l : ('l * 'r) Value.t -> ('l * 'r) Alloc.t
  (** similar to [regional_to_local], identity on other axes *)

  val value_to_alloc_r2g : Regionality.Index.t -> ('l * 'r) Value.t -> ('l * 'r) Alloc.t
  (** similar to [regional_to_global], identity on other axes *)

  module Const : sig
    val unique_to_linear : Uniqueness.Const.t -> Linearity.Const.t
  end

end
