type allowed = private Allowed
type disallowed = private Disallowed
type left_only = allowed * disallowed
type right_only = disallowed * allowed
type both = allowed * allowed
type ('a, 'b) eq = Refl : ('a, 'a) eq
type 'a positive = 'b * 'c constraint 'a = 'b * 'c
type 'a negative = 'c * 'b constraint 'a = 'b * 'c


(** A collection of lattices, indexed by [obj] *)
module type Lattices = sig
  type 'a obj
  (** identifies lattices, where 'a is the type of elements in that
      lattice *)

  val min : 'a obj -> 'a
  val max : 'a obj -> 'a
  val le : 'a obj -> 'a -> 'a -> bool
  val join : 'a obj -> 'a -> 'a -> 'a
  val meet : 'a obj -> 'a -> 'a -> 'a
  val print : 'a obj -> Format.formatter -> 'a -> unit

  val eq_obj : 'a obj -> 'b obj -> ('a, 'b) eq option
end

(* Extend [Lattices] with monotone functions (including identity) to form a
  category. Among those monotone functions some will have left and right
  adjoints. *)
module type Lattices_mono = sig
  include Lattices

  (* Due to the implementation of the solver, a mode doesn't know
  the object it lives in, whether at compile-time or runtime. There is info at
  compile-time to distinguish between e.g. uniqueness and linearity, but not
  between regionalities of different indices. Therefore, we can treat modes as
  mostly "untyped".

  In particular, a regionality mode doesn't tell us
  which regionality (out of the indexed family) it lives in. This can be used at
  our advantage (implicit casting between levels), but also tricky to deal with.

  - [submode m0 m1] also takes an [obj] indicating the object the two modes live
    in, or particularly in the case of regionality, which level are we in. In
    fact, it must, due to the implementation of the solver.
  - Should [apply f m] also take as arguments the [src] and [dst] of [f]? Note
    that some [f] runs differently for different [src]/[dst], so one might want
    to provide both to [apply]. However, the solver's internal works such that
    the morphism is not immediately applied on a var, and the [dst] has to be
    silently ignored. That means two things: First, [apply] should not take [dst]
    because that would be bad interface. Second, [f] itself should contain
    enough info about [dst] to decide how it will behave on const. [src] is
    faithfully stored and it's fine for the user to pass in.

  - Therefore, at the very least, [src] and [f] should suffice for [C.apply]
    . That means [f] should contain enough info about [dst] for itself to
    decide runtime behaviour.

  - Now for [compose f g], we have [src], [mid], [dst]. Obviously [dst] should
    not be provided, because it would not be included in the result morphism.
    [src] should not be provided either, because it would be provided when the
    resulted morphism is used for [apply]. Therefore, only [mid] should be
    provided.

  - For [left_adjoint f], first of all we need [f] and its [src] to pin down its
  runtime behaviour. As a result we get [g] and its [src] (which would be [dst]
  for [f] )
    *)

  (** 'd = 'l * 'r
     l = allowed means the morphism have right adjoint
     r = allowed means the morphism have left adjoint *)
  type ('a, 'b, 'd) morph

  val id : ('a, 'a, 'd) morph

  val compose :
    'b obj -> ('b, 'c, 'd) morph -> ('a, 'b, 'd) morph -> ('a, 'c, 'd) morph

  (* left_only means allowed * disallowed, which is weaker than what we want,
     which is \exists r. allowed * disallowed. But ocaml doesn't like existentials,
     and this weakened version is good enough for us *)
  val left_adjoint : 'a obj -> ('a, 'b, 'l * allowed) morph -> 'b obj * ('b, 'a, left_only) morph
  val right_adjoint : 'a obj -> ('a, 'b, allowed * 'r) morph -> 'b obj * ('b, 'a, right_only) morph

  (* forget whether a function can be on the right. *)
  val disallow_right :
    ('a, 'b, 'l * 'r) morph -> ('a, 'b, 'l * disallowed) morph

  val disallow_left : ('a, 'b, 'l * 'r) morph -> ('a, 'b, disallowed * 'r) morph
  val allow_right : ('a, 'b, 'l * allowed) morph -> ('a, 'b, 'l * 'r) morph
  val allow_left : ('a, 'b, allowed * 'r) morph -> ('a, 'b, 'l * 'r) morph
  val apply : 'a obj -> ('a, 'b, 'd) morph -> 'a -> 'b

  val print_morph :
    'a obj -> Format.formatter -> ('a, 'b, 'd) morph -> unit
end

module type S = sig
  type changes
  val undo_changes : changes -> unit
  val append_changes : (changes ref -> unit) ref
  module Solver_mono (C : Lattices_mono) : sig
    type ('a, 'd) mode
    type 'a var

    val min : 'a C.obj -> ('a, 'l * 'r) mode
    val max : 'a C.obj -> ('a, 'l * 'r) mode
    val of_const : 'a -> ('a, 'l * 'r) mode

    val apply :
      'a C.obj ->
      ('a, 'b, 'd0 * 'd1) C.morph ->
      ('a, 'd0 * 'd1) mode ->
      ('b, 'd0 * 'd1) mode

    val submode :
      'a C.obj ->
      ('a, allowed * 'r) mode ->
      ('a, 'l * allowed) mode ->
      (unit, unit) result
    (** the [obj] is only used to obtain [le] *)

    (* val submode_try :
      'a C.obj ->
      ('a, allowed * 'r) mode ->
      ('a, 'l * allowed) mode ->
      (change Log.log, unit) result *)

    val equate :
      'a C.obj -> ('a, both) mode -> ('a, both) mode -> (unit, unit) result

    val submode_exn :
      'a C.obj -> ('a, allowed * 'r) mode -> ('a, 'l * allowed) mode -> unit

    val equate_exn : 'a C.obj -> ('a, both) mode -> ('a, both) mode -> unit
    val newvar : ?hint:string -> 'a C.obj -> ('a, 'l * 'r) mode
    val constrain_lower : 'a C.obj -> ('a, allowed * 'r) mode -> 'a
    val constrain_upper : 'a C.obj -> ('a, 'e * allowed) mode -> 'a

    val newvar_above :
      ?hint:string ->
      'a C.obj ->
      ('a, allowed * 'r_) mode ->
      ('a, 'l * 'r) mode * bool

    val newvar_below :
      ?hint:string ->
      'a C.obj ->
      ('a, 'l_ * allowed) mode ->
      ('a, 'l * 'r) mode * bool


    val join : 'a C.obj -> ('a, allowed * 'r) mode list -> ('a, left_only) mode
    (** [obj] is used to obtain [min] [max] [join]  *)

    val meet : 'a C.obj -> ('a, 'l * allowed) mode list -> ('a, right_only) mode
    (** [obj] is used to obtain [min] [max] [meet] *)

    val check_const : 'a C.obj -> ('a, 'd0 * 'd1) mode -> 'a option

    val print :
      ?verbose:bool ->
      ?axis:string ->
      'a C.obj ->
      Format.formatter ->
      ('a, 'l * 'r) mode ->
      unit
  end

  module Solver_polarized (C : Lattices_mono) : sig
    module S : module type of Solver_mono (C)

    type 'a neg = Neg of 'a [@@unboxed]
    type 'a pos = Pos of 'a [@@unboxed]

    (* This category contains two kinds of objects:
      Those from the base category, those from the base category but dualized *)
    type 'a obj =
      | Positive : 'a C.obj -> 'a pos obj
      | Negative : 'a C.obj -> 'a neg obj

    (* 'a and 'b are source and destination
      'd and 'e are source and desitnation adjoint status *)
    type ('a, 'd, 'b, 'e) morph =
      | Pos_Pos :
          ('a, 'b, 'd) C.morph
          -> ('a pos, 'd positive, 'b pos, 'd positive) morph
      | Pos_Neg :
          ('a, 'b, 'd) C.morph
          -> ('a pos, 'd positive, 'b neg, 'd negative) morph
      | Neg_Pos :
          ('a, 'b, 'd) C.morph
          -> ('a neg, 'd negative, 'b pos, 'd positive) morph
      | Neg_Neg :
          ('a, 'b, 'd) C.morph
          -> ('a neg, 'd negative, 'b neg, 'd negative) morph

    (* id and compose not used; just for fun *)
    val id : 'a obj -> ('a, 'l * 'r, 'a, 'l * 'r) morph

    val compose :
      'b obj ->
      ('b, 'bl * 'br, 'c, 'cl * 'cr) morph ->
      ('a, 'al * 'ar, 'b, 'bl * 'br) morph ->
      ('a, 'al * 'ar, 'c, 'cl * 'cr) morph

    type ('a, 'd) mode =
      | Positive : ('a, 'd) S.mode -> ('a pos, 'd positive) mode
      | Negative : ('a, 'd) S.mode -> ('a neg, 'd negative) mode

    val disallow_right : ('a, 'l * 'r) mode -> ('a, 'l * disallowed) mode
    val disallow_left : ('a, 'l * 'r) mode -> ('a, disallowed * 'r) mode
    val allow_right : ('a, 'l * allowed) mode -> ('a, 'l * 'r) mode
    val allow_left : ('a, allowed * 'r) mode -> ('a, 'l * 'r) mode

    val apply :
      'a obj ->
      ('a, 'd0 * 'd1, 'b, 'e0 * 'e1) morph ->
      ('a, 'd0 * 'd1) mode ->
      ('b, 'e0 * 'e1) mode


    val of_const : 'a obj -> 'a -> ('a, 'l * 'r) mode
    (** Only looks the positive/negative of [obj]; the content is ignored *)

    val min : 'a obj -> ('a, 'l * 'r) mode
    val max : 'a obj -> ('a, 'l * 'r) mode
    val constrain_lower : 'a obj -> ('a, allowed * 'r) mode -> 'a
    val constrain_upper : 'a obj -> ('a, 'l * allowed) mode -> 'a
    val newvar : ?hint:string -> 'a obj -> ('a, 'l * 'r) mode

    val submode :
      'a obj ->
      ('a, allowed * 'r) mode ->
      ('a, 'l * allowed) mode ->
      (unit, unit) result

    (* val submode_try :
      'a obj ->
      ('a, allowed * 'r) mode ->
      ('a, 'l * allowed) mode ->
      (change Log.log, unit) result *)

    val equate :
      'a obj -> ('a, both) mode -> ('a, both) mode -> (unit, unit) result

    val submode_exn :
      'a obj -> ('a, allowed * 'r) mode -> ('a, 'l * allowed) mode -> unit

    val equate_exn : 'a obj -> ('a, both) mode -> ('a, both) mode -> unit

    val newvar_above :
      ?hint:string ->
      'a obj ->
      ('a, allowed * 'r_) mode ->
      ('a, 'l * 'r) mode * bool

    val newvar_below :
      ?hint:string ->
      'a obj ->
      ('a, 'l_ * allowed) mode ->
      ('a, 'l * 'r) mode * bool

    val join : 'a obj -> ('a, allowed * 'r) mode list -> ('a, left_only) mode
    val meet : 'a obj -> ('a, 'l * allowed) mode list -> ('a, right_only) mode
    val check_const : 'a obj -> ('a, 'l * 'r) mode -> 'a option

    val print :
      ?verbose:bool ->
      ?axis:string ->
      'a obj ->
      Format.formatter ->
      ('a, 'l * 'r) mode ->
      unit
  end
end