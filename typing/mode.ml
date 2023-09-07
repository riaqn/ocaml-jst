include Mode_intf
open Solver
open Solver_intf

type nonrec allowed = allowed
type nonrec disallowed = disallowed

module Product = struct
  type ('a0, 'a1) t = 'a0 * 'a1

  (* type aware indexing into a tuple *)
  type ('a0, 'a1, 'a) axis =
    | Axis0 : ('a0, 'a1, 'a0) axis
    | Axis1 : ('a0, 'a1, 'a1) axis

  let print_axis : type a0 a1 a. Format.formatter -> (a0, a1, a) axis -> unit =
   fun ppf -> function
    | Axis0 -> Format.fprintf ppf "0"
    | Axis1 -> Format.fprintf ppf "1"

  let proj (type a0 a1 a) : (a0, a1, a) axis -> a0 * a1 -> a = function
    | Axis0 -> fun (x, _) -> x
    | Axis1 -> fun (_, x) -> x

  let eq_axis (type a0 a1 a b) :
      (a0, a1, a) axis -> (a0, a1, b) axis -> (a, b) eq option =
   fun a b ->
    match (a, b) with
    | Axis0, Axis0 -> Some Refl
    | Axis1, Axis1 -> Some Refl
    | _ -> None

  type ('a0, 'a1, 'a, 'b0, 'b1, 'b) saxis =
    | SAxis0 : ('a0, 'a1, 'a0, 'b0, 'a1, 'b0) saxis
    | SAxis1 : ('a0, 'a1, 'a1, 'a0, 'b1, 'b1) saxis

  let _flip (type a0 a1 a b0 b1 b) :
      (a0, a1, a, b0, b1, b) saxis -> (b0, b1, b, a0, a1, a) saxis = function
    | SAxis0 -> SAxis0
    | SAxis1 -> SAxis1

  let set (type a0 a1 a b0 b1 b) :
      (a0, a1, a, b0, b1, b) saxis -> (a -> b) -> (a0, a1) t -> (b0, b1) t =
    function
    | SAxis0 -> fun f (a0, a1) -> (f a0, a1)
    | SAxis1 -> fun f (a0, a1) -> (a0, f a1)

  let diag (type a0 a1 a) : (a0, a1, a) axis -> (a0, a1, a, a0, a1, a) saxis =
    function
    | Axis0 -> SAxis0
    | Axis1 -> SAxis1

  let src (type a0 a1 a b0 b1 b) :
      (a0, a1, a, b0, b1, b) saxis -> (a0, a1, a) axis = function
    | SAxis0 -> Axis0
    | SAxis1 -> Axis1

  let _dst (type a0 a1 a b0 b1 b) :
      (a0, a1, a, b0, b1, b) saxis -> (b0, b1, b) axis = function
    | SAxis0 -> Axis0
    | SAxis1 -> Axis1

  let update (type a0 a1 a) : (a0, a1, a) axis -> a -> a0 * a1 -> a0 * a1 =
   fun ax a t -> set (diag ax) (fun _ -> a) t

  module Lattice (L0 : Lattice) (L1 : Lattice) = struct
    type nonrec t = L0.t * L1.t

    let min = (L0.min, L1.min)
    let max = (L0.max, L1.max)
    let le (a0, a1) (b0, b1) = L0.le a0 b0 && L1.le a1 b1
    let join (a0, a1) (b0, b1) = (L0.join a0 b0, L1.join a1 b1)
    let meet (a0, a1) (b0, b1) = (L0.meet a0 b0, L1.meet a1 b1)
    let print ppf (a0, a1) = Format.fprintf ppf "%a,%a" L0.print a0 L1.print a1
  end

  module Lattice_indexed (L0 : Lattice_indexed_bound) (L1 : Lattice) = struct
    module Index = L0.Index
    type t = L0.t * L1.t

    let min = (L0.min, L1.min)

    let max i = (L0.max i, L1.max)

    let le (a0, a1) (b0, b1) = L0.le a0 b0 && L1.le a1 b1

    let join
      (a0, a1) (b0, b1) = (L0.join a0 b0, L1.join a1 b1)

    let meet
      (a0, a1) (b0, b1) = (L0.meet a0 b0, L1.meet a1 b1)

    let print
     ppf (a0, a1) =
      Format.fprintf ppf "%a,%a" L0.print a0 L1.print a1
  end
end

module Lattices = struct
  module Opposite (L : Lattice) : Lattice with type t = L.t = struct
    type t = L.t

    let min = L.max
    let max = L.min
    let le a b = L.le b a
    let join = L.meet
    let meet = L.join
    let print = L.print
  end

  module Locality = struct
    type t = Global | Local

    let min = Global
    let max = Local

    let le a b =
      match (a, b) with
      | Global, _ | _, Local -> true
      | Local, Global -> false

    let join a b =
      match (a, b) with
      | Local, _ | _, Local -> Local
      | Global, Global -> Global

    let meet a b =
      match (a, b) with
      | Global, _ | _, Global -> Global
      | Local, Local -> Local

    let print ppf = function
      | Global -> Format.fprintf ppf "Global"
      | Local -> Format.fprintf ppf "Local"
  end

  module Regionality : sig
    type t = private T of Int.t

    module Index : sig
      type t = private T of Int.t
      val outermost : t
      val innermost : t
      val valid : t -> bool
      val enter : t -> t
      val print : Format.formatter -> t -> unit
    end

    val local : Index.t -> t
    val escape : Index.t -> t
    include Lattice_indexed_bound with type t := t and module Index := Index
  end = struct
    type t = T of Int.t

    module Index = struct
      type t = T of Int.t

      let outermost = T 1
      let valid (T i) = i > 0
      let innermost = T Int.max_int
      let enter (T t) = T (t + 1)

      let print ppf (T a) = Format.fprintf ppf "%i" a
    end

    let local (Index.T i) = T i
    let escape (Index.T i) =
      (* note that we have i > 0 for any [Index.T i] *)
      T (i - 1)
    let min = T 0
    let max (Index.T i) = T i

    let join  (T a) (T b) =
      T (Int.max a b)

    let meet  (T a) (T b) =
      T (Int.min a b)

    let le (T a) (T b) =
      a <= b

    let print ppf (T a) = Format.fprintf ppf "%i" a
  end

  module Uniqueness = struct
    type t = Unique | Shared

    let min = Unique
    let max = Shared

    let le a b =
      match (a, b) with
      | Unique, _ | _, Shared -> true
      | Shared, Unique -> false

    let join a b =
      match (a, b) with
      | Shared, _ | _, Shared -> Shared
      | Unique, Unique -> Unique

    let meet a b =
      match (a, b) with
      | Unique, _ | _, Unique -> Unique
      | Shared, Shared -> Shared

    let print ppf = function
      | Shared -> Format.fprintf ppf "Shared"
      | Unique -> Format.fprintf ppf "Unique"
  end

  module Uniqueness_op = Opposite (Uniqueness)

  module Linearity = struct
    type t = Many | Once

    let min = Many
    let max = Once

    let le a b =
      match (a, b) with Many, _ | _, Once -> true | Once, Many -> false

    let join a b =
      match (a, b) with Once, _ | _, Once -> Once | Many, Many -> Many

    let meet a b =
      match (a, b) with Many, _ | _, Many -> Many | Once, Once -> Once

    let print ppf = function
      | Once -> Format.fprintf ppf "Once"
      | Many -> Format.fprintf ppf "Many"
  end

  module Comonadic_with_locality = Product.Lattice (Locality) (Linearity)

  module Comonadic_with_regionality = Product.Lattice_indexed (Regionality) (Linearity)

  type 'a obj =
    | Locality : Locality.t obj
    | Regionality : Regionality.Index.t -> Regionality.t obj
    (* use the flipped version of uniqueness, so that unique_to_linear is monotone *)
    | Uniqueness_op : Uniqueness_op.t obj
    | Linearity : Linearity.t obj
    | Comonadic_with_regionality :
        Comonadic_with_regionality.Index.t -> Comonadic_with_regionality.t obj
    | Comonadic_with_locality : Comonadic_with_locality.t obj

  let _print_obj : type a. _ -> a obj -> unit =
   fun ppf -> function
    | Locality -> Format.fprintf ppf "Locality"
    | Regionality i -> Format.fprintf ppf "Regionality_%a" Regionality.Index.print i
    | Uniqueness_op -> Format.fprintf ppf "Uniqueness_op"
    | Linearity -> Format.fprintf ppf "Linearity"
    | Comonadic_with_locality -> Format.fprintf ppf "Comonadic_with_locality"
    | Comonadic_with_regionality i -> Format.fprintf ppf "Comonadic_with_regionality_%a" Regionality.Index.print i

  let proj_obj :
      type a0 a1 a. (a0, a1, a) Product.axis -> (a0, a1) Product.t obj -> a obj
      = function
    | Axis0 -> (
        function
        | Comonadic_with_locality -> Locality
        | Comonadic_with_regionality i -> Regionality i)
    | Axis1 -> (
        function
        | Comonadic_with_locality -> Linearity
        | Comonadic_with_regionality _ -> Linearity)

  let set_obj :
      type a0 a1 a b0 b1 b.
    (a0, a1, a, b0, b1, b) Product.saxis ->
    (a obj -> b obj) ->
    (a0, a1) Product.t obj ->
    (b0, b1) Product.t obj = function
    | SAxis0 -> ( fun f -> function
      | Comonadic_with_locality -> (match f Locality with
        | Locality -> Comonadic_with_locality
        | Regionality i -> Comonadic_with_regionality i
        | _ -> assert false
      )
      | Comonadic_with_regionality i -> (match f (Regionality i) with
        | Locality -> Comonadic_with_locality
        | Regionality i -> Comonadic_with_regionality i
        | _ -> assert false
      )
    )
    | SAxis1 -> ( fun f -> function
      | Comonadic_with_locality -> (match f Linearity with
        | Linearity -> Comonadic_with_locality
        | _ -> assert false
      )
      | Comonadic_with_regionality i -> (match f Linearity with
        | Linearity -> Comonadic_with_regionality i
        | _ -> assert false
      )
      )

  let min : type a. a obj -> a = function
    | Locality -> Locality.min
    | Regionality _ -> Regionality.min
    | Uniqueness_op -> Uniqueness_op.min
    | Linearity -> Linearity.min
    | Comonadic_with_locality -> Comonadic_with_locality.min
    | Comonadic_with_regionality _ -> Comonadic_with_regionality.min

  let max : type a. a obj -> a = function
    | Locality -> Locality.max
    | Regionality obj -> Regionality.max obj
    | Uniqueness_op -> Uniqueness_op.max
    | Linearity -> Linearity.max
    | Comonadic_with_locality -> Comonadic_with_locality.max
    | Comonadic_with_regionality obj -> Comonadic_with_regionality.max obj

  let le : type a. a obj -> a -> a -> bool = function
    | Locality -> Locality.le
    | Regionality _ -> Regionality.le
    | Uniqueness_op -> Uniqueness_op.le
    | Linearity -> Linearity.le
    | Comonadic_with_locality -> Comonadic_with_locality.le
    | Comonadic_with_regionality _ -> Comonadic_with_regionality.le

  let join : type a. a obj -> a -> a -> a = function
    | Locality -> Locality.join
    | Regionality _ -> Regionality.join
    | Uniqueness_op -> Uniqueness_op.join
    | Linearity -> Linearity.join
    | Comonadic_with_locality -> Comonadic_with_locality.join
    | Comonadic_with_regionality _ -> Comonadic_with_regionality.join

  let meet : type a. a obj -> a -> a -> a = function
    | Locality -> Locality.meet
    | Regionality _ -> Regionality.meet
    | Uniqueness_op -> Uniqueness_op.meet
    | Linearity -> Linearity.meet
    | Comonadic_with_locality -> Comonadic_with_locality.meet
    | Comonadic_with_regionality _ -> Comonadic_with_regionality.meet

  let print : type a. a obj -> _ -> a -> unit = function
    | Locality -> Locality.print
    | Regionality _ -> Regionality.print
    | Uniqueness_op -> Uniqueness_op.print
    | Linearity -> Linearity.print
    | Comonadic_with_locality -> Comonadic_with_locality.print
    | Comonadic_with_regionality _ -> Comonadic_with_regionality.print

  let eq_obj : type a b. a obj -> b obj -> (a, b) eq option =
   fun a b ->
    match (a, b) with
    | Locality, Locality -> Some Refl
    | Regionality n, Regionality m -> if n = m then Some Refl else None
    | Uniqueness_op, Uniqueness_op -> Some Refl
    | Linearity, Linearity -> Some Refl
    | Comonadic_with_locality, Comonadic_with_locality -> Some Refl
    | Comonadic_with_regionality n, Comonadic_with_regionality m ->
        if n = m then Some Refl else None
    | _ -> None
end

module Lattices_mono = struct
  include Lattices

  type ('a, 'b, 'd) morph =

    | Id : ('a, 'a, 'd) morph  (** identity morphism *)
    | Const_min : 'b obj -> ('a, 'b, 'd * disallowed) morph
    | Const_max : 'b obj -> ('a, 'b, disallowed * 'd) morph
        (** They are special because they have adjoint
       which is needed to make compose type check (note that compose requires
       all morphs have the same 'l and 'r ) *)
    | Proj :
        ('a0, 'a1, 'a) Product.axis
        -> (('a0, 'a1) Product.t, 'a, 'l * 'r) morph
        (** projection from product to axis *)
    | Max_with :
        ('a0, 'a1, 'a) Product.axis * ('a0, 'a1) Product.t obj
        -> ('a, ('a0, 'a1) Product.t, disallowed * 'r) morph
        (** pushes to top except specified axis *)
    | Min_with :
        ('a0, 'a1, 'a) Product.axis * ('a0, 'a1) Product.t obj
        -> ('a, ('a0, 'a1) Product.t, 'l * disallowed) morph
        (** pushes to bot except specified axis *)
    | Set :
        ('a0, 'a1, 'a, 'b0, 'b1, 'b) Product.saxis * ('a, 'b, 'd) morph
        -> (('a0, 'a1) Product.t, ('b0, 'b1) Product.t, 'd) morph
        (** set the value of one axis in a product *)
    | Unique_to_linear : (Uniqueness.t, Linearity.t, 'l * 'r) morph
        (** unique -> linear  *)
    | Linear_to_unique : (Linearity.t, Uniqueness.t, 'l * 'r) morph
        (** linear -> unique *)
    (* following is a chain of adjunction (complete and cannot extend in
       either direction) *)

    | Local_to_regional :
      Regionality.Index.t ->
      (Locality.t, Regionality.t, 'l * disallowed) morph
    (** If i >= 1, maps local to 1, global to 0.
        If i = 0, undefined. *)

    | Regional_to_local :
    (Regionality.t, Locality.t, 'l * 'r) morph
    (** maps 0 to G, <=i to L.
        assert i>=1 for this to have left adjoint;
        i given by the [src] object *)

    | Locality_as_regionality :
        Regionality.Index.t ->
    (Locality.t, Regionality.t, 'l * 'r) morph
    (** maps L to i, G to 0, SL to inf *)

    | Regional_to_global :
    (Regionality.t, Locality.t, 'l * 'r) morph
    (** maps =i to L, <i to G;
        assert i>=1 for this to have right adjoint
        (i given by the [src] object) *)

    | Global_to_regional :
          Regionality.Index.t ->
    (Locality.t, Regionality.t, disallowed * 'r) morph
    (** If i >= 1, maps L to i, G to i-1;
        If i = 0, undefined *)

    | Compose :
        'b obj * ('b, 'c, 'd) morph * ('a, 'b, 'd) morph
        -> ('a, 'c, 'd) morph  (** composing morphisms  *)

  let rec print_morph :
      type a b d. a obj -> Format.formatter -> (a, b, d) morph -> unit
      =
   fun src ppf -> function
    | Id -> Format.fprintf ppf "id"
    | Const_min _ -> Format.fprintf ppf "const_min"
    | Const_max _ -> Format.fprintf ppf "const_max"
    | Proj ax -> Format.fprintf ppf "proj_%a" Product.print_axis ax
    | Max_with (ax, _) -> Format.fprintf ppf "max_with_%a" Product.print_axis ax
    | Min_with (ax, _) -> Format.fprintf ppf "min_with_%a" Product.print_axis ax
    | Set (sax, morph) ->
      let ax = Product.src sax in
      Format.fprintf ppf "set_%a(%a)" Product.print_axis ax (print_morph (proj_obj ax src)) morph
    | Unique_to_linear -> Format.fprintf ppf "unique_to_linear"
    | Linear_to_unique -> Format.fprintf ppf "linear_to_unique"
    | Local_to_regional i -> Format.fprintf ppf "local_to_regional_%a" Regionality.Index.print i
    | Regional_to_local -> Format.fprintf ppf "regional_to_local"
    | Locality_as_regionality i -> Format.fprintf ppf "locality_as_regionality_%a" Regionality.Index.print i
    | Regional_to_global ->
      let Regionality i = src in
      Format.fprintf ppf "regional_to_global_%a" Regionality.Index.print i
    | Global_to_regional _ -> Format.fprintf ppf "global_to_regional"
    | Compose (mid, f0, f1) ->
        Format.fprintf ppf "%a ∘ %a" (print_morph mid ) f0
          (print_morph src) f1

  let id = Id

  let linear_to_unique = function
    | Linearity.Many -> Uniqueness.Shared
    | Linearity.Once -> Uniqueness.Unique

  let unique_to_linear = function
    | Uniqueness.Unique -> Linearity.Once
    | Uniqueness.Shared -> Linearity.Many

  let local_to_regional _ =
    function
    | Locality.Global -> Regionality.escape (Regionality.Index.outermost)
    | Locality.Local -> Regionality.max (Regionality.Index.outermost)

  let regional_to_local i n =
    assert (Regionality.le n (Regionality.local i));
    if Regionality.le n Regionality.min then Locality.Global
    else Locality.Local

  let locality_as_regionality i = function
    | Locality.Local -> Regionality.max i
    | Locality.Global -> Regionality.min

  let regional_to_global i n =
    (* TODO: uncomment the following line *)
    (* assert (Regionality.le n (Regionality.local i)); *)
    if Regionality.le (Regionality.max i) n
    then Locality.Local
    else Locality.Global

  let global_to_regional i =
    function
    | Locality.Local -> Regionality.max i
    | Locality.Global -> Regionality.escape i

  let rec apply : type a b d. a obj -> (a, b, d) morph -> a -> b =
   fun src f a ->
    match f with
    | Id -> a
    | Proj ax -> Product.proj ax a
    | Max_with (ax, dst) -> Product.update ax a (max dst)
    | Min_with (ax, dst) -> Product.update ax a (min dst)
    | Const_min dst -> min dst
    | Const_max dst -> max dst
    | Compose (mid, f, g) -> apply mid f (apply src g a)
    | Unique_to_linear -> unique_to_linear a
    | Linear_to_unique -> linear_to_unique a
    | Local_to_regional i -> local_to_regional i a
    | Regional_to_local ->
      let Regionality i = src in
      regional_to_local i a
    | Locality_as_regionality i ->
        locality_as_regionality i a
    | Regional_to_global ->
        let Regionality i = src in
        regional_to_global i a
    | Global_to_regional i ->
        global_to_regional i a
    | Set (ax, f) ->
        Product.set ax
          (apply
             (proj_obj (Product.src ax) src)
             f)
          a

  (* m0 wraps around m1;
     raise NotCollapse if m0 and m1 cannot collapse
     TODO: finer grained: tells if collapsed on each side.
  *)
  let rec maybe_compose :
      type a b c d.
      b obj -> (b, c, d) morph -> (a, b, d) morph -> (a, c, d) morph option =
   fun mid m0 m1 ->
    match (m0, m1) with
    | Id, m -> Some m
    | m, Id -> Some m
    | Const_min dst, _ -> Some (Const_min dst)
    | Const_max dst, _ -> Some (Const_max dst)
    | Proj ax0, Max_with (ax1, _) -> (
        match Product.eq_axis ax0 ax1 with
        | None -> Some (Const_max (proj_obj ax0 mid))
        | Some Refl -> Some Id)
    | Proj ax0, Min_with (ax1, _) -> (
        match Product.eq_axis ax0 ax1 with
        | None -> Some (Const_min (proj_obj ax0 mid))
        | Some Refl -> Some Id)
    (* | Min_with (ax0, dst), Proj (ax1, _) -> (
        match (ax0, ax1) with
        | Axis0, Axis0 -> Some (Set (Product.SAxis1, Const_min (proj_obj Axis1 dst)))
        | Axis1, Axis1 -> Some (Set (Product.SAxis0, Const_min (proj_obj Axis0 dst)))
        | _ -> None)
    | Max_with (ax0, dst), Proj (ax1, _) -> (
        match (ax0, ax1) with
        | Axis0, Axis0 -> Some (Set (Product.SAxis1, Const_max (proj_obj Axis1 dst)))
        | Axis1, Axis1 -> Some (Set (Product.SAxis0, Const_max (proj_obj Axis0 dst)))
        | _ -> None) *)
    | Proj ax, Const_min dst -> Some (Const_min (proj_obj ax dst))
    | Proj ax, Const_max dst -> Some (Const_max (proj_obj ax dst))
    | Max_with (_, dst), Const_max _ -> Some (Const_max dst)
    | Min_with (_, dst), Const_min _ -> Some (Const_min dst)
    | Unique_to_linear, Const_min Uniqueness_op -> Some (Const_min Linearity)
    | Linear_to_unique, Const_min Linearity -> Some (Const_min Uniqueness_op)
    | Unique_to_linear, Const_max Uniqueness_op -> Some (Const_max Linearity)
    | Linear_to_unique, Const_max Linearity -> Some (Const_max Uniqueness_op)
    | Unique_to_linear, Linear_to_unique -> Some Id
    | Linear_to_unique, Unique_to_linear -> Some Id
    | Set (ax0, f0), Set (ax1, f1) -> (
        match (ax0, ax1) with
        | Product.SAxis0, Product.SAxis0 ->
            Some
              (Set (Product.SAxis0, compose (proj_obj Axis0 mid) f0 f1))
        | Product.SAxis1, Product.SAxis1 ->
            Some
              (Set (Product.SAxis1, compose (proj_obj Axis1 mid) f0 f1))
        | _ -> None)
    (* the following are important: look inside compose *)
    | Compose (mid', f0, f1), g -> (
        match maybe_compose mid f1 g with
        | Some m -> Some (compose mid' f0 m)
        (* the check needed to prevent infinite loop *)
        | None -> None)
    | f, Compose (mid', g0, g1) -> (
        match maybe_compose mid f g0 with
        | Some m -> Some (compose mid' m g1)
        | None ->
            None
            (* | Regional_to_local, Local_to_regional -> Some Id
               | Regional_to_local, Global_to_regional -> Some Const_max
               | Regional_to_local, Const_min -> Some Const_min
               | Regional_to_local, Const_max -> Some Const_max *)
            (* | Regional_to_global, Local_to_regional -> Some Const_min *)

            (* | Regional_to_global _, Const_min -> Some Const_min *)
            (* | Regional_to_global _, Const_max -> Some Const_max *)
            (* | Local_to_regional, Regional_to_local -> None
               | Local_to_regional, Regional_to_global -> None
               | Local_to_regional, Const_min -> Some Const_min
               | Local_to_regional, Const_max -> None *)
            (* | Locality_as_regionality, Regional_to_local -> None *)
            (* | Locality_as_regionality, Regional_to_global -> None *)
            (* | Locality_as_regionality, Const_min -> Some Const_min *)
            (* | Locality_as_regionality, Const_max -> None *)
            (* | Global_to_regional, Regional_to_local -> None *))
    | Proj _, Set _ ->
        (* TODO: collapse this *)
        None
    | Min_with _, _ -> None
    | Max_with _, _ -> None
    | _, Proj _ -> None
    | Set _, _ -> None
    (* TODO: remove the following line *)
    | _, _ -> None

  and compose :
      type a b c d.
      b obj -> (b, c, d) morph -> (a, b, d) morph -> (a, c, d) morph =
   fun mid f g ->
    match maybe_compose mid f g with Some m -> m | None -> Compose (mid, f, g)

  let rec left_adjoint :
      type a b l.
      a obj -> (a, b, l * allowed) morph -> b obj * (b, a, allowed * disallowed) morph =
      fun src -> function
    | Id -> src, Id
    | Proj ax -> proj_obj ax src, Min_with (ax, src)
    | Max_with (ax, dst) -> dst, Proj ax
    | Compose (mid, f, g) ->
      let mid', f' = left_adjoint mid f in
      let src', g' = left_adjoint src g in
      mid', Compose (src', g', f')
    | Const_max dst -> dst, Const_min src
    | Unique_to_linear -> Linearity, Linear_to_unique
    | Linear_to_unique -> Uniqueness_op, Unique_to_linear
    | Global_to_regional i -> Regionality i, Regional_to_global
    | Regional_to_global ->
      let Regionality i = src in
      Locality, Locality_as_regionality i
    | Locality_as_regionality i -> Regionality i, Regional_to_local
    | Regional_to_local ->
      let Regionality i = src in
      assert (Regionality.Index.valid i);
      Locality, Local_to_regional i
    | Set (sax, f) ->
      let ax = Product.src sax in
      let src_ = proj_obj ax src in
      let (src_', f') = left_adjoint src_ f in
      set_obj sax (fun _ -> src_') src,
      (match sax with | SAxis0 -> Set (SAxis0, f') | SAxis1 -> Set (SAxis1, f'))

  let rec right_adjoint :
      type a b r.
      a obj ->
      (a, b, allowed * r) morph -> b obj * (b, a, disallowed * allowed) morph =
      fun src -> function
    | Id -> src, Id
    | Proj ax ->
      (* Format.eprintf "right_adjoint(Proj) %a\n" print_obj src; *)
      (proj_obj ax src, Max_with (ax, src))
    | Min_with (ax, dst) -> dst, Proj ax
    | Compose (mid, f, g) ->
      let mid', f' = right_adjoint mid f in
      let src', g' = right_adjoint src g in
      mid', Compose (src', g', f')
    | Const_min dst -> dst, Const_max src
    | Unique_to_linear -> Linearity, Linear_to_unique
    | Linear_to_unique -> Uniqueness_op, Unique_to_linear
    | Local_to_regional i -> (Regionality i, Regional_to_local)
    | Regional_to_local ->
      let Regionality i = src in (Locality, Locality_as_regionality i)
    | Locality_as_regionality i -> (Regionality i,  Regional_to_global)
    | Regional_to_global ->
      let Regionality i = src in
      assert (Regionality.Index.valid i);
      (Locality, Global_to_regional i)
    | Set (sax, f) ->
      let ax = Product.src sax in
      let src_ = proj_obj ax src in
      let (src_', f') = right_adjoint src_ f in
      set_obj sax (fun _ -> src_') src,
      (match sax with | SAxis0 -> Set (SAxis0, f') | SAxis1 -> Set (SAxis1, f'))

  let disallow_right :
      type a b l r. (a, b, l * r) morph -> (a, b, l * disallowed) morph =
    Obj.magic

  let disallow_left :
      type a b l r. (a, b, l * r) morph -> (a, b, disallowed * r) morph =
    Obj.magic

  let allow_left :
      type a b l r. (a, b, allowed * r) morph -> (a, b, l * r) morph =
    Obj.magic

  let allow_right :
      type a b l r. (a, b, l * allowed) morph -> (a, b, l * r) morph =
    Obj.magic
end

module C = Lattices_mono
module S = Solver_polarized (C)

(** Representing a single object *)
module type Obj = sig
  type const
  type const_s

  (* val obj_c : Const.t C.obj *)
  val obj_s : const_s S.obj
  val unpack : const_s -> const
  val pack : const -> const_s
end

module Common (Obj : Obj) = struct
  open Obj
  (* module Const = Const *)

  type 'd t = (const_s, 'd) S.mode
  type l = (allowed * disallowed) t
  type r = (disallowed * allowed) t
  type lr = (allowed * allowed) t
  type error = unit

  let disallow_right m = S.disallow_right m
  let disallow_left m = S.disallow_left m
  let allow_left m = S.allow_left m
  let allow_right m = S.allow_right m
  let newvar ?hint () = S.newvar ?hint obj_s
  let min = S.min obj_s
  let max = S.max obj_s
  let newvar_above ?hint m = S.newvar_above ?hint obj_s m
  let newvar_below ?hint m = S.newvar_below ?hint obj_s m
  let submode m0 m1 : (unit, error) result = S.submode obj_s m0 m1
  let join l = S.join obj_s l
  let meet l = S.meet obj_s l
  let submode_exn m0 m1 = S.submode_exn obj_s m0 m1
  let equate m0 m1 = S.equate obj_s m0 m1
  let equate_exn m0 m1 = S.equate_exn obj_s m0 m1
  let print ?verbose ?axis ppf m = S.print obj_s ?verbose ?axis ppf m
  let print_simple ppf m = print ~verbose:false ?axis:None ppf m
  let constrain_upper m = Obj.unpack (S.constrain_upper obj_s m)
  let constrain_lower m = Obj.unpack (S.constrain_lower obj_s m)

  let of_const : type l r. const -> (l * r) t =
   fun a -> S.of_const obj_s (Obj.pack a)

  let check_const m = Option.map Obj.unpack (S.check_const obj_s m)
end

(* Representing a family of indexed objects that shares the same base type,
  and only differ in their upper bounds *)
module type Obj_indexed_bound = sig
  type index
  val innermost : index

  type const
  type const_s

  val obj_s : index -> const_s S.obj
  val unpack : const_s -> const
  val pack : const -> const_s
end

module Common_indexed_bound (Obj : Obj_indexed_bound) = struct
  open Obj
  (* module Const = Const *)

  type 'd t = (const_s, 'd) S.mode
  type l = (allowed * disallowed) t
  type r = (disallowed * allowed) t
  type lr = (allowed * allowed) t
  type error = unit

  let disallow_right m = S.disallow_right m
  let disallow_left m = S.disallow_left m
  let allow_left m = S.allow_left m
  let allow_right m = S.allow_right m
  let newvar i ?hint () = S.newvar ?hint (obj_s i)
  let min = S.min (obj_s innermost)
  let max i = S.max (obj_s i)
  let newvar_above i ?hint m = S.newvar_above ?hint (obj_s i) m
  let newvar_below i ?hint m = S.newvar_below ?hint (obj_s i) m
  let submode m0 m1 : (unit, error) result = S.submode (obj_s innermost) m0 m1
  (* let submode_mvc m0 a1 : (unit, erorr) result = S.submode_mvc m0 a1 *)

  let join l = S.join (obj_s innermost) l

  let meet l = S.meet (obj_s innermost) l

  let submode_exn m0 m1 = S.submode_exn (obj_s innermost) m0 m1
  let equate m0 m1 = S.equate (obj_s innermost) m0 m1
  let equate_exn m0 m1 = S.equate_exn (obj_s innermost) m0 m1
  let print ?verbose ?axis ppf m = S.print (obj_s innermost) ?verbose ?axis ppf m
  let print_simple ppf m = print ~verbose:false ?axis:None ppf m
  let constrain_upper i m = Obj.unpack (S.constrain_upper (obj_s i) m)
  let constrain_lower i m = Obj.unpack (S.constrain_lower (obj_s i) m)

  let of_const : type l r. const -> (l * r) t =
   fun a -> S.of_const (obj_s innermost) (Obj.pack a)

  let check_const i m = Option.map Obj.unpack (S.check_const (obj_s i) m)
end

module Locality = struct
  module Const = struct
    include C.Locality

    let legacy = Global
  end

  module Obj = struct
    type const = Const.t
    type const_s = Const.t S.pos

    let obj_c = C.Locality
    let obj_s : const_s S.obj = S.Positive obj_c
    let unpack (S.Pos a) = a
    let pack a = S.Pos a
  end

  include Common (Obj)

  let global = of_const Global
  let local = of_const Local
  let legacy = of_const Const.legacy
  let constrain_legacy = constrain_lower
end

module Regionality = struct

  module Const = struct
    include C.Regionality

    let global = min
    let legacy = global
  end
  module Index = Const.Index


  module Obj = struct
    type nonrec index = Index.t
    let innermost = Index.innermost

    type const = Const.t
    type const_s = Const.t S.pos

    let obj_s i : const_s S.obj = S.Positive (C.Regionality i)
    let unpack (S.Pos a) = a
    let pack a = S.Pos a
  end

  include Common_indexed_bound (Obj)

  let local i = of_const (Const.local i)
  let global = of_const Const.global
  let legacy = of_const Const.legacy

  let constrain_legacy = constrain_lower
end

module Linearity = struct
  module Const = struct
    include C.Linearity

    let legacy = Many
  end

  module Obj = struct
    type const = Const.t
    type const_s = Const.t S.pos

    let obj_c = C.Linearity
    let obj_s : const_s S.obj = S.Positive obj_c
    let unpack (S.Pos a) = a
    let pack a = S.Pos a
  end

  include Common (Obj)

  let many = of_const Many
  let once = of_const Once
  let legacy = of_const Const.legacy
  let constrain_legacy = constrain_lower
end

module Uniqueness = struct
  module Const = struct
    include C.Uniqueness

    let legacy = Shared
  end

  module Obj = struct
    type const = Const.t

    (* the negation of Uniqueness_op gives us the proper uniqueness *)
    type const_s = Const.t S.neg

    let obj_c = C.Uniqueness_op
    let obj_s : const_s S.obj = S.Negative obj_c
    let unpack (S.Neg a) = a
    let pack a = S.Neg a
  end

  include Common (Obj)

  let shared = of_const Shared
  let unique = of_const Unique
  let legacy = of_const Const.legacy
  let constrain_legacy = constrain_upper
end

let unique_to_linear m =
  S.apply Uniqueness.Obj.obj_s
    (S.Neg_Pos C.Unique_to_linear) m

let linear_to_unique m =
  S.apply Linearity.Obj.obj_s
    (S.Pos_Neg C.Linear_to_unique) m

(* let instantiate_local i m =
     S.apply Locality.Obj.obj_s Regionality.Obj.obj_s
       (S.Pos_Pos (C.Locality_to_regionality i)) (S.disallow_right m)

   let generalize_local i m =
     S.apply Regionality.Obj.obj_s Locality.Obj.obj_s
       (S.Pos_Pos (C.Regionality_to_locality i)) m *)

let regional_to_local i m =
  S.apply (Regionality.Obj.obj_s i)
    (S.Pos_Pos C.Regional_to_local) m

let locality_as_regionality i m =
  S.apply Locality.Obj.obj_s
    (S.Pos_Pos (C.Locality_as_regionality i)) m

let regional_to_global i m =
  S.apply (Regionality.Obj.obj_s i)
    (S.Pos_Pos C.Regional_to_global) m

module Const = struct
  let unique_to_linear a = C.unique_to_linear a
end

(* We now define alloc and value, each is a product of mode of opposite
   polarities (and thus cannot be defined in Mono_lattices).
   It is a simple wraper so that submoding on the product
   immediately translates to submoding on individual lattices. Note that if you
   want to combine lattices of the same polarity, you should make a native
   product lattice with native projections and adjunctions, like what we did in
   mode.ml, which is more efficient because one submoding doesn't translates to
   two submoding underneath.

   Alloc and Value differ only in the first axis so we do a bit of abstraction.
*)

module Comonadic_with_regionality = struct
  module Const = struct
    include C.Comonadic_with_regionality
  end

  module Obj = struct
    type nonrec index = Regionality.Index.t
    let innermost = Regionality.Index.innermost

    type const = Const.t
    type const_s = Const.t S.pos

    let obj i : const C.obj = C.Comonadic_with_regionality i
    let obj_s i : const_s S.obj = S.Positive (obj i)
    let unpack (S.Pos a) = a
    let pack a = S.Pos a
  end

  include Common_indexed_bound (Obj)

  (* TODO: Attach the gap in the offending axis causing the submode error. *)
  type error = [ `Regionality | `Linearity ]

  let regionality m =
    S.apply (Obj.obj_s Regionality.Index.innermost)
      (S.Pos_Pos (C.Proj Axis0)) m

  let min_with_regionality m =
    S.apply (Regionality.Obj.obj_s Regionality.Index.innermost)
      (S.Pos_Pos (C.Min_with (Axis0, Obj.obj Regionality.Index.innermost))) (S.disallow_right m)

  let max_with_regionality m =
    S.apply (Regionality.Obj.obj_s Regionality.Index.innermost)
      (S.Pos_Pos (C.Max_with (Axis0, C.Comonadic_with_regionality Regionality.Index.innermost))) (S.disallow_left m)

  let set_regionality_max i m =
    S.apply (Obj.obj_s i)
      (S.Pos_Pos (C.Set (Product.SAxis0, C.Const_max (Regionality i))))
      (S.disallow_left m)

  let set_regionality_min m =
    (* Cheating: regionality.min is not affected by index *)
    S.apply (Obj.obj_s Regionality.Index.innermost)
      (S.Pos_Pos (C.Set (Product.SAxis0, C.Const_min (Regionality Regionality.Index.innermost))))
      (S.disallow_right m)

  let linearity m =
    S.apply (Obj.obj_s Regionality.Index.innermost)
      (S.Pos_Pos (C.Proj Axis1)) m

  let min_with_linearity m =
    (* Cheating: regionality.min is not affected by index *)
    S.apply Linearity.Obj.obj_s
      (S.Pos_Pos (C.Min_with (Axis1, Obj.obj Regionality.Index.innermost))) (S.disallow_right m)

  let max_with_linearity i m =
    S.apply Linearity.Obj.obj_s
      (S.Pos_Pos (C.Max_with (Axis1, Obj.obj i))) (S.disallow_left m)

  let set_linearity_max m =
    S.apply (Obj.obj_s Regionality.Index.innermost)
      (S.Pos_Pos (C.Set (Product.SAxis1, C.Const_max Linearity)))
      (S.disallow_left m)

  let set_linearity_min m =
    S.apply (Obj.obj_s Regionality.Index.innermost)
      (S.Pos_Pos (C.Set (Product.SAxis1, C.Const_min Linearity)))
      (S.disallow_right m)

  let constrain_legacy = constrain_lower
  let legacy = min

  (* overriding to report the offending axis *)
  let submode m0 m1 =
    match submode m0 m1 with
    | Ok () -> Ok ()
    | Error () ->
        (* find out the offending axis *)
        match Regionality.submode (regionality m0) (regionality m1) with
        | Error () -> Error `Regionality
        | Ok () ->
            match Linearity.submode (linearity m0) (linearity m1) with
            | Error () -> Error `Linearity
            | Ok () -> assert false (* sanity *)

  (* override to report the offending axis *)
  let equate m0 m1 =
    match equate m0 m1 with
    | Ok () -> Ok ()
    | Error () -> (
        (* find out the offending axis *)
        match Regionality.equate (regionality m0) (regionality m1) with
        | Error () -> Error `Regionality
        | Ok () -> (
            match Linearity.equate (linearity m0) (linearity m1) with
            | Ok () -> assert false (* sanity *)
            | Error () -> Error `Linearity))

  (** overriding to check per-axis *)
  let check_const i m =
    let regionality = Regionality.check_const i (regionality m) in
    let linearity = Linearity.check_const (linearity m) in
    (regionality, linearity)
end

module Comonadic_with_locality = struct
  module Const = struct
    include C.Comonadic_with_locality
  end

  module Obj = struct
    type const = Const.t
    type const_s = Const.t S.pos

    let obj : const C.obj = C.Comonadic_with_locality
    let obj_s : const_s S.obj = S.Positive obj
    let unpack (S.Pos a) = a
    let pack a = S.Pos a
  end

  include Common (Obj)

  (* TODO: Attach the gap in the offending axis causing the submode error. *)
  type error = [ `Locality | `Linearity ]

  let locality m =
    S.apply Obj.obj_s
      (S.Pos_Pos (C.Proj Axis0)) m

  let min_with_locality m =
    S.apply (Locality.Obj.obj_s)
      (S.Pos_Pos (C.Min_with (Axis0, Obj.obj))) (S.disallow_right m)

  let max_with_locality m =
    S.apply Locality.Obj.obj_s
      (S.Pos_Pos (C.Max_with (Axis0, Obj.obj))) (S.disallow_left m)

  let set_locality_max m =
    S.apply Obj.obj_s
      (S.Pos_Pos (C.Set (Product.SAxis0, C.Const_max Locality)))
      (S.disallow_left m)

  let set_locality_min m =
    S.apply Obj.obj_s
      (S.Pos_Pos (C.Set (Product.SAxis0, C.Const_min Locality)))
      (S.disallow_right m)

  let linearity m =
    S.apply Obj.obj_s
      (S.Pos_Pos (C.Proj Axis1)) m

  let min_with_linearity m =
    S.apply Linearity.Obj.obj_s
      (S.Pos_Pos (C.Min_with (Axis1, Obj.obj))) (S.disallow_right m)

  let max_with_linearity m =
    S.apply Linearity.Obj.obj_s
      (S.Pos_Pos (C.Max_with (Axis1, Obj.obj))) (S.disallow_left m)

  let set_linearity_max m =
    S.apply Obj.obj_s
      (S.Pos_Pos (C.Set (Product.SAxis1, C.Const_max Linearity)))
      (S.disallow_left m)

  let set_linearity_min m =
    S.apply Obj.obj_s
      (S.Pos_Pos (C.Set (Product.SAxis1, C.Const_min Linearity)))
      (S.disallow_right m)

  let constrain_legacy = constrain_lower
  let legacy = min

  (* overriding to report the offending axis *)
  let submode m0 m1 =
    match submode m0 m1 with
    | Ok () -> Ok ()
    | Error () -> (
        (* find out the offending axis *)
        match Locality.submode (locality m0) (locality m1) with
        | Error () -> Error `Locality
        | Ok () -> (
            match Linearity.submode (linearity m0) (linearity m1) with
            | Ok () -> assert false (* sanity *)
            | Error () -> Error `Linearity))

  (* override to report the offending axis *)
  let equate m0 m1 =
    match equate m0 m1 with
    | Ok () -> Ok ()
    | Error () -> (
        (* find out the offending axis *)
        match Locality.equate (locality m0) (locality m1) with
        | Error () -> Error `Locality
        | Ok () -> (
            match Linearity.equate (linearity m0) (linearity m1) with
            | Ok () -> assert false (* sanity *)
            | Error () -> Error `Linearity))

  (** overriding to check per-axis *)
  let check_const m =
    let locality = Locality.check_const (locality m) in
    let linearity = Linearity.check_const (linearity m) in
    (locality, linearity)
end

module Monadic = struct
  let uniqueness m = m

  (* secretly just uniqueness *)
  include Uniqueness

  type error = [ `Uniqueness ]

  let max_with_uniqueness m = S.disallow_left m
  let min_with_uniqueness m = S.disallow_right m
  let set_uniqueness_max _ = Uniqueness.max |> S.disallow_left |> S.allow_right
  let set_uniqueness_min _ = Uniqueness.min |> S.disallow_right |> S.allow_left

  let submode m0 m1 =
    match submode m0 m1 with Ok () -> Ok () | Error () -> Error `Uniqueness

  let equate m0 m1 =
    match equate m0 m1 with Ok () -> Ok () | Error () -> Error `Uniqueness
end

type ('mo, 'como) monadic_comonadic = {monadic : 'mo; comonadic : 'como}

(* packed version where axes are packed into two groups, positvie and negative *)
module Value = struct
  module Comonadic = Comonadic_with_regionality
  module Monadic = Monadic

  (* type a1 = Uniqueness.Const.t S.neg

     let obj1 : a1 S.obj = S.Negative C.Uniqueness_op *)

  type 'd t = ('d Monadic.t, 'd Comonadic.t) monadic_comonadic
  type l = (allowed * disallowed) t
  type r = (disallowed * allowed) t
  type lr = (allowed * allowed) t

  let min = { comonadic = Comonadic.min; monadic = Monadic.min }
  let max i = { comonadic = Comonadic.max i; monadic =
    Monadic.max |> Monadic.allow_left |> Monadic.allow_right }
  let disallow_right = Obj.magic
  let disallow_left = Obj.magic
  let allow_right = Obj.magic
  let allow_left = Obj.magic

  let newvar i ?hint () =
    let comonadic = Comonadic.newvar i ?hint () in
    let monadic = Monadic.newvar ?hint () in
    { comonadic; monadic }

  let newvar_above i ?hint { comonadic; monadic } =
    let comonadic, b0 = Comonadic.newvar_above i ?hint comonadic in
    let monadic, b1 = Monadic.newvar_above ?hint monadic in
    ({ monadic; comonadic }, b0 || b1)

  let newvar_below i ?hint { comonadic; monadic } =
    let comonadic, b0 = Comonadic.newvar_below i ?hint comonadic in
    let monadic, b1 = Monadic.newvar_below ?hint monadic in
    ({ monadic; comonadic }, b0 || b1)

  let uniqueness { monadic; _ } = Monadic.uniqueness monadic
  let linearity { comonadic; _ } = Comonadic.linearity comonadic
  let regionality { comonadic; _ } = Comonadic.regionality comonadic

  type error = [ `Regionality | `Uniqueness | `Linearity ]

  (* NB: state mutated when error *)
  let submode { monadic = monadic0; comonadic = comonadic0 }
      { monadic = monadic1; comonadic = comonadic1 } =
    (* comonadic before monadic, so that locality errors dominate
       (error message backward compatibility) *)
    match Comonadic.submode comonadic0 comonadic1 with
      | Error e -> Error e
      | Ok () ->
        match Monadic.submode monadic0 monadic1 with
        | Error e -> Error e
        | Ok () -> Ok ()

  let equate m0 m1 =
    match submode m0 m1 with Error e -> Error e | Ok () -> submode m1 m0

  let submode_exn m0 m1 =
    match submode m0 m1 with
    | Ok () -> ()
    | Error _ -> invalid_arg "submode_exn"

  let equate_exn m0 m1 =
    match equate m0 m1 with
    | Ok () -> ()
    | Error _ -> invalid_arg "equate_exn"

  let print ?(verbose = true) ppf { monadic; comonadic } =
    Format.fprintf ppf "%a,%a"
      (Comonadic.print ~verbose ?axis:None)
      comonadic
      (Monadic.print ~verbose ?axis:None)
      monadic

  let print_simple ppf m = print ~verbose:false ppf m

  let constrain_lower i { comonadic; monadic } =
    match
      ( Monadic.constrain_lower monadic,
        Comonadic.constrain_lower i comonadic )
    with
    | uniqueness, (locality, linearity) -> (locality, linearity, uniqueness)

  let constrain_upper i { comonadic; monadic } =
    match
      ( Monadic.constrain_upper monadic,
        Comonadic.constrain_upper i comonadic )
    with
    | uniqueness, (locality, linearity) -> (locality, linearity, uniqueness)

  let constrain_legacy i { comonadic; monadic } =
    match
      ( Monadic.constrain_legacy monadic,
        Comonadic.constrain_legacy i comonadic )
    with
    | uniqueness, (locality, linearity) -> (locality, linearity, uniqueness)

  let check_const i { comonadic; monadic } =
    let locality, linearity = Comonadic.check_const i comonadic in
    let uniqueness = Monadic.check_const monadic in
    (locality, linearity, uniqueness)

  let of_const (locality, linearity, uniqueness) =
    let comonadic = Comonadic.of_const (locality, linearity) in
    let monadic = Monadic.of_const uniqueness in
    { comonadic; monadic }

  let legacy =
    let comonadic = Comonadic.legacy in
    let monadic = Monadic.legacy in
    { comonadic; monadic }

  (* Below we package up the complex projection from alloc to three axes as if
     they live under alloc directly and uniformly. We define functions that operate
     on modes numerically, instead of defining symbolic functions *)
  (* type const = (LR.Const.t, Linearity.Const.t, Uniqueness.Const.t) modes *)

  let max_with_uniqueness i uniqueness =
    let comonadic =
      Comonadic.max i |> Comonadic.disallow_left |> Comonadic.allow_right
    in
    let monadic = Monadic.max_with_uniqueness uniqueness in
    { comonadic; monadic }

  let min_with_uniqueness uniqueness =
    let comonadic =
      Comonadic.min |> Comonadic.disallow_right |> Comonadic.allow_left
    in
    let monadic = Monadic.min_with_uniqueness uniqueness in
    { comonadic; monadic }

  let set_uniqueness_max { monadic; comonadic } =
    let comonadic = Comonadic.disallow_left comonadic in
    let monadic = Monadic.set_uniqueness_max monadic in
    { monadic; comonadic }

  let set_uniqueness_min { monadic; comonadic } =
    let comonadic = Comonadic.disallow_right comonadic in
    let monadic = Monadic.set_uniqueness_min monadic in
    { monadic; comonadic }

  let min_with_regionality regionality =
    let comonadic = Comonadic.min_with_regionality regionality in
    let monadic =
      Monadic.min |> Monadic.disallow_right |> Monadic.allow_left
    in
    { comonadic; monadic }

  let max_with_regionality regionality =
    let comonadic = Comonadic.max_with_regionality regionality in
    let monadic =
      Monadic.max |> Monadic.disallow_left |> Monadic.allow_right
    in
    { comonadic; monadic }

  let set_regionality_min { monadic; comonadic } =
    let monadic = Monadic.disallow_right monadic in
    let comonadic = Comonadic.set_regionality_min comonadic in
    { comonadic; monadic }

  let set_regionality_max i { monadic; comonadic } =
    let monadic = Monadic.disallow_left monadic in
    let comonadic = Comonadic.set_regionality_max i comonadic in
    { comonadic; monadic }

  let min_with_linearity linearity =
    let comonadic = Comonadic.min_with_linearity linearity in
    let monadic =
      Monadic.min |> Monadic.disallow_right |> Monadic.allow_left
    in
    { comonadic; monadic }

  let max_with_linearity i linearity =
    let comonadic = Comonadic.max_with_linearity i linearity in
    let monadic =
      Monadic.max |> Monadic.disallow_left |> Monadic.allow_right
    in
    { comonadic; monadic }

  let set_linearity_max { monadic; comonadic } =
    let monadic = Monadic.disallow_left monadic in
    let comonadic = Comonadic.set_linearity_max comonadic in
    { comonadic; monadic }

  let set_linearity_min { monadic; comonadic } =
    let monadic = Monadic.disallow_right monadic in
    let comonadic = Comonadic.set_linearity_min comonadic in
    { comonadic; monadic }

  let join l =
    let como, mo =
      List.fold_left
        (fun (como, mo) { comonadic; monadic } ->
          (comonadic :: como, monadic :: mo))
        ([], []) l
    in
    let comonadic = Comonadic.join como in
    let monadic = Monadic.join mo in
    { comonadic; monadic }

  let meet l =
    let como, mo =
      List.fold_left
        (fun (como, mo) { comonadic; monadic } ->
          (comonadic :: como, monadic :: mo))
        ([], []) l
    in
    let comonadic = Comonadic.meet como in
    let monadic = Monadic.meet mo in
    { comonadic; monadic }

  module Const = struct
    type t = Regionality.Const.t * Linearity.Const.t * Uniqueness.Const.t

    let min = (Regionality.Const.min, Linearity.Const.min, Uniqueness.Const.min)
    let max i = (Regionality.Const.max i, Linearity.Const.max, Uniqueness.Const.max)

    let le (locality0, linearity0, uniqueness0)
        (locality1, linearity1, uniqueness1) =
      Regionality.Const.le locality0 locality1
      && Uniqueness.Const.le uniqueness0 uniqueness1
      && Linearity.Const.le linearity0 linearity1

    let print ppf m = print_simple ppf (of_const m)

    let legacy =
      (Regionality.Const.legacy, Linearity.Const.legacy, Uniqueness.Const.legacy)

    let meet (l0, l1, l2) (r0, r1, r2) =
      ( Regionality.Const.meet l0 r0,
        Linearity.Const.meet l1 r1,
        Uniqueness.Const.meet l2 r2 )

    let join (l0, l1, l2) (r0, r1, r2) =
      ( Regionality.Const.join l0 r0,
        Linearity.Const.join l1 r1,
        Uniqueness.Const.join l2 r2 )
  end
end

module Alloc = struct
  module Comonadic = Comonadic_with_locality
  module Monadic = Monadic

  (* type a1 = Uniqueness.Const.t S.neg

     let obj1 : a1 S.obj = S.Negative C.Uniqueness_op *)

  type 'd t = ('d Monadic.t, 'd Comonadic.t) monadic_comonadic
  type l = (allowed * disallowed) t
  type r = (disallowed * allowed) t
  type lr = (allowed * allowed) t

  let min = { comonadic = Comonadic.min; monadic = Monadic.min }
  let max = { comonadic = Comonadic.min; monadic = Monadic.max }
  let disallow_right = Obj.magic
  let disallow_left = Obj.magic
  let allow_right = Obj.magic
  let allow_left = Obj.magic

  let newvar ?hint () =
    let comonadic = Comonadic.newvar ?hint () in
    let monadic = Monadic.newvar ?hint () in
    { comonadic; monadic }

  let newvar_above ?hint { comonadic; monadic } =
    let comonadic, b0 = Comonadic.newvar_above ?hint comonadic in
    let monadic, b1 = Monadic.newvar_above ?hint monadic in
    ({ monadic; comonadic }, b0 || b1)

  let newvar_below ?hint { comonadic; monadic } =
    let comonadic, b0 = Comonadic.newvar_below ?hint comonadic in
    let monadic, b1 = Monadic.newvar_below ?hint monadic in
    ({ monadic; comonadic }, b0 || b1)

  let uniqueness { monadic; _ } = Monadic.uniqueness monadic
  let linearity { comonadic; _ } = Comonadic.linearity comonadic
  let locality { comonadic; _ } = Comonadic.locality comonadic

  type error = [ `Locality | `Uniqueness | `Linearity ]

  (* NB: state mutated when error *)
  let submode { monadic = monadic0; comonadic = comonadic0 }
      { monadic = monadic1; comonadic = comonadic1 } =
    match Monadic.submode monadic0 monadic1 with
    | Error e -> Error e
    | Ok () -> (
        match Comonadic.submode comonadic0 comonadic1 with
        | Error e -> Error e
        | Ok () -> Ok ())

  let equate m0 m1 =
    match submode m0 m1 with Error e -> Error e | Ok () -> submode m1 m0

  let submode_exn m0 m1 =
    match submode m0 m1 with
    | Ok () -> ()
    | Error _ -> invalid_arg "submode_exn"

  let equate_exn m0 m1 =
    match equate m0 m1 with
    | Ok () -> ()
    | Error _ -> invalid_arg "equate_exn"

  let print ?(verbose = true) ppf { monadic; comonadic } =
    Format.fprintf ppf "%a,%a"
      (Comonadic.print ~verbose ?axis:None)
      comonadic
      (Monadic.print ~verbose ?axis:None)
      monadic

  let print_simple ppf m = print ~verbose:false ppf m

  let constrain_lower { comonadic; monadic } =
    match
      ( Monadic.constrain_lower monadic,
        Comonadic.constrain_lower comonadic )
    with
    | uniqueness, (locality, linearity) -> (locality, linearity, uniqueness)

  let constrain_upper { comonadic; monadic } =
    match
      ( Monadic.constrain_upper monadic,
        Comonadic.constrain_upper comonadic )
    with
    | uniqueness, (locality, linearity) -> (locality, linearity, uniqueness)

  let constrain_legacy { comonadic; monadic } =
    match
      ( Monadic.constrain_legacy monadic,
        Comonadic.constrain_legacy comonadic )
    with
    | uniqueness, (locality, linearity) -> (locality, linearity, uniqueness)

  let check_const { comonadic; monadic } =
    let locality, linearity = Comonadic.check_const comonadic in
    let uniqueness = Monadic.check_const monadic in
    (locality, linearity, uniqueness)

  let of_const (locality, linearity, uniqueness) =
    let comonadic = Comonadic.of_const (locality, linearity) in
    let monadic = Monadic.of_const uniqueness in
    { comonadic; monadic }

  let legacy =
    let comonadic = Comonadic.legacy in
    let monadic = Monadic.legacy in
    { comonadic; monadic }

  (* Below we package up the complex projection from alloc to three axes as if
     they live under alloc directly and uniformly. We define functions that operate
     on modes numerically, instead of defining symbolic functions *)
  (* type const = (LR.Const.t, Linearity.Const.t, Uniqueness.Const.t) modes *)

  let max_with_uniqueness uniqueness =
    let comonadic =
      Comonadic.max |> Comonadic.disallow_left |> Comonadic.allow_right
    in
    let monadic = Monadic.max_with_uniqueness uniqueness in
    { comonadic; monadic }

  let min_with_uniqueness uniqueness =
    let comonadic =
      Comonadic.min |> Comonadic.disallow_right |> Comonadic.allow_left
    in
    let monadic = Monadic.min_with_uniqueness uniqueness in
    { comonadic; monadic }

  let set_uniqueness_max { monadic; comonadic } =
    let comonadic = Comonadic.disallow_left comonadic in
    let monadic = Monadic.set_uniqueness_max monadic in
    { monadic; comonadic }

  let set_uniqueness_min { monadic; comonadic } =
    let comonadic = Comonadic.disallow_right comonadic in
    let monadic = Monadic.set_uniqueness_min monadic in
    { monadic; comonadic }

  let min_with_locality locality =
    let comonadic = Comonadic.min_with_locality locality in
    let monadic =
      Monadic.min |> Monadic.disallow_right |> Monadic.allow_left
    in
    { comonadic; monadic }

  let max_with_locality locality =
    let comonadic = Comonadic.max_with_locality locality in
    let monadic =
      Monadic.max |> Monadic.disallow_left |> Monadic.allow_right
    in
    { comonadic; monadic }

  let set_locality_min { monadic; comonadic } =
    let monadic = Monadic.disallow_right monadic in
    let comonadic = Comonadic.set_locality_min comonadic in
    { comonadic; monadic }

  let set_locality_max { monadic; comonadic } =
    let monadic = Monadic.disallow_left monadic in
    let comonadic = Comonadic.set_locality_max comonadic in
    { comonadic; monadic }

  let min_with_linearity linearity =
    let comonadic = Comonadic.min_with_linearity linearity in
    let monadic =
      Monadic.min |> Monadic.disallow_right |> Monadic.allow_left
    in
    { comonadic; monadic }

  let max_with_linearity linearity =
    let comonadic = Comonadic.max_with_linearity linearity in
    let monadic =
      Monadic.max |> Monadic.disallow_left |> Monadic.allow_right
    in
    { comonadic; monadic }

  let set_linearity_max { monadic; comonadic } =
    let monadic = Monadic.disallow_left monadic in
    let comonadic = Comonadic.set_linearity_max comonadic in
    { comonadic; monadic }

  let set_linearity_min { monadic; comonadic } =
    let monadic = Monadic.disallow_right monadic in
    let comonadic = Comonadic.set_linearity_min comonadic in
    { comonadic; monadic }

  let join l =
    let como, mo =
      List.fold_left
        (fun (como, mo) { comonadic; monadic } ->
          (comonadic :: como, monadic :: mo))
        ([], []) l
    in
    let comonadic = Comonadic.join como in
    let monadic = Monadic.join mo in
    { comonadic; monadic }

  let meet l =
    let como, mo =
      List.fold_left
        (fun (como, mo) { comonadic; monadic } ->
          (comonadic :: como, monadic :: mo))
        ([], []) l
    in
    let comonadic = Comonadic.meet como in
    let monadic = Monadic.meet mo in
    { comonadic; monadic }

  module Const = struct
    type t = Locality.Const.t * Linearity.Const.t * Uniqueness.Const.t

    let min = (Locality.Const.min, Linearity.Const.min, Uniqueness.Const.min)
    let max = (Locality.Const.max, Linearity.Const.max, Uniqueness.Const.max)

    let le (locality0, linearity0, uniqueness0)
        (locality1, linearity1, uniqueness1) =
      Locality.Const.le locality0 locality1
      && Uniqueness.Const.le uniqueness0 uniqueness1
      && Linearity.Const.le linearity0 linearity1

    let print ppf m = print_simple ppf (of_const m)

    let legacy =
      (Locality.Const.legacy, Linearity.Const.legacy, Uniqueness.Const.legacy)

    let meet (l0, l1, l2) (r0, r1, r2) =
      ( Locality.Const.meet l0 r0,
        Linearity.Const.meet l1 r1,
        Uniqueness.Const.meet l2 r2 )

    let join (l0, l1, l2) (r0, r1, r2) =
      ( Locality.Const.join l0 r0,
        Linearity.Const.join l1 r1,
        Uniqueness.Const.join l2 r2 )

    (** constrain uncurried function ret_mode from arg_mode *)
    let close_over (locality, linearity, uniqueness) =
      let locality' = locality in
      (* uniqueness of the returned function is not constrained *)
      let uniqueness' = Uniqueness.Const.min in
      let linearity' =
        Linearity.Const.join linearity
          (* In addition, unique argument make the returning function once.
             In other words, if argument <= unique, returning function >= once.
             That is, returning function >= (dual of argument) *)
          (Const.unique_to_linear uniqueness)
      in
      (locality', linearity', uniqueness')

    (** constrain uncurried function ret_mode from the mode of the whole function *)
    let partial_apply (locality, linearity, _) =
      let locality' = locality in
      let uniqueness' = Uniqueness.Const.min in
      let linearity' = linearity in
      (locality', linearity', uniqueness')
  end

  (** constrain uncurried function ret_mode from arg_mode *)
  let close_over comonadic monadic =
    let locality = min_with_locality (Comonadic.locality comonadic) in
    (* uniqueness of the returned function is not constrained *)
    let linearity0 =
      min_with_linearity (Comonadic.linearity  comonadic)
    in
    let linearity1 =
      min_with_linearity (unique_to_linear (Monadic.uniqueness monadic))
    in
    (* In addition, unique argument make the returning function once.
        In other words, if argument <= unique, returning function >= once.
        That is, returning function >= (dual of argument) *)
    join [ locality; linearity0; linearity1 ]

  (** constrain uncurried function ret_mode from the mode of the whole function *)
  let partial_apply alloc_mode = set_uniqueness_min alloc_mode
end


(* module Consts_mono_padded (L : Const) = struct
  type index = unit
  type nonrec t = L.t

  let min () = L.min
  let max () = L.max
  let join () = L.join
  let meet () = L.meet
  let le () = L.le
  let print () = L.print
  let legacy () = L.legacy
end *)


let alloc_as_value i m =
  let { comonadic; monadic } = Alloc.disallow_right m in
  let comonadic =
    S.apply Alloc.Comonadic.Obj.obj_s
      (S.Pos_Pos (C.Set (Product.SAxis0, C.Locality_as_regionality i)))
      comonadic
  in
  { comonadic; monadic }

let alloc_to_value_l2r i m =
  assert (Regionality.Index.valid i);
  let { comonadic; monadic } = Alloc.disallow_right m in
   let comonadic =
     S.apply Alloc.Comonadic.Obj.obj_s
       (S.Pos_Pos (C.Set (Product.SAxis0, C.Local_to_regional i)))
       comonadic
   in
   { comonadic; monadic }

(* let alloc_to_value_g2r n (m0, m1) =
   let m0 =
     S.apply Alloc.obj0 Value.obj0
       (S.Pos_Pos (C.Set (C.Product.SAxis0, C.Global_to_regional n)))
       (S.disallow_left m0)
   in
   (m0, S.disallow_left m1) *)

(* let value_to_alloc i m =
  let { Value.comonadic; monadic } = Value.disallow_left m in
  let comonadic =
    S.apply (Value.Comonadic.Obj_indexed.obj_s i) (Alloc.Comonadic.Obj_indexed.obj_s ())
      (S.Pos_Pos (C.Set (Product.SAxis0, C.Regionality_to_locality)))
      comonadic
  in
  { Alloc.comonadic; monadic }

let alloc_to_value ~outer_region m =
  let { Alloc.comonadic; monadic } = Alloc.disallow_left m in
  let comonadic =
    S.apply Alloc.Comonadic.Obj.obj_s Value.Comonadic.Obj.obj_s
      (S.Pos_Pos
         (C.Set (C.Product.SAxis0, C.Locality_to_regionality outer_region)))
      comonadic
  in
  { Value.comonadic; monadic } *)

let value_to_alloc_r2g i m =
  let { comonadic; monadic } = Alloc.disallow_right m in
  let comonadic =
    S.apply (Value.Comonadic.Obj.obj_s i)
      (S.Pos_Pos (C.Set (Product.SAxis0, C.Regional_to_global)))
      comonadic
  in
  { comonadic; monadic }

let value_to_alloc_r2l m =
  let { comonadic; monadic } = m in
  let comonadic =
    (* Cheat: Regional_to_local doesn't care about index *)
    S.apply (Value.Comonadic.Obj.obj_s Regionality.Index.innermost)
      (S.Pos_Pos
         (C.Set
            ( Product.SAxis0,
              C.Regional_to_local
                )))
      comonadic
  in
  { comonadic; monadic }
