include Solver_intf

type ('a, 'b) var' = {
  mutable upper : 'a;
  mutable lower : 'a;
  (* TODO: consider using hashset for quicker deduplication *)
  mutable vlower : 'b list;
  (* hint not used for anything interesting; just for debuging.
     modes are identified by physical equality *)
  hint : string option;
}

type change =
  | Cupper : ('a, 'b) var' * 'a -> change
  | Clower : ('a, 'b) var' * 'a -> change
  | Cvlower : ('a, 'b) var' * 'b list -> change

type changes = change list

let undo_change = function
  | Cupper (v, u) -> v.upper <- u
  | Clower (v, l) -> v.lower <- l
  | Cvlower (v, vs) -> v.vlower <- vs

let undo_changes l = List.iter undo_change l

(* to be filled in by types.ml *)
let append_changes : (changes ref -> unit) ref = ref (fun _ -> ())

module Solver_mono (C : Lattices_mono) = (* C for category *)
struct
  (* best attempt was made so that this solver looks very similar to the
     original one by stephen *)

  type 'a var = ('a, 'a lmorphvar) var'
  and 'b lmorphvar = ('b, left_only) morphvar

  and ('b, 'd) morphvar =
    | Amorphvar : 'a C.obj * 'a var * ('a, 'b, 'd) C.morph -> ('b, 'd) morphvar

  type ('a, 'd) mode =
    | Amode : 'a -> ('a, 'l * 'r) mode
    | Amodevar : ('a, 'd) morphvar -> ('a, 'd) mode
    | Amodejoin :
        'a * ('a, allowed * disallowed) morphvar list
        -> ('a, allowed * disallowed) mode
    | Amodemeet :
        'a * ('a, disallowed * allowed) morphvar list
        -> ('a, disallowed * allowed) mode

  (** Explains why submode failed. Calling [submode x y] might trigger this
      error, where [hi] is the highest value [y] can be, and [lo] is the lowest
      value [x] can be. We will have that "[lo] <= [hi] is false", which caused
      the failure *)
  (* type 'a error = {
    lo : 'a;
    hi : 'a;
  } *)

  let address_of : 'a var -> int = Obj.magic

  let print_var obj ppf v =
    match v.hint with
    | None -> Format.fprintf ppf "%x[%a,%a]" (address_of v) (C.print obj) v.lower (C.print obj) v.upper
    | Some s -> Format.fprintf ppf "%s@@%x" s (address_of v)

  let print_morphvar ppf (Amorphvar (src, v, f)) =
    Format.fprintf ppf "%a(%a)" (C.print_morph src) f (print_var src) v

  let print_raw :
      type a l r.
      ?verbose:bool ->
      ?axis:string ->
      a C.obj ->
      Format.formatter ->
      (a, l * r) mode ->
      unit =
   fun  ?(verbose = true) ?axis (obj : a C.obj) ppf m ->
    let print_axis () =
      match axis with None -> () | Some s -> Format.fprintf ppf "%s:" s
    in
    match m with
    | Amode a -> C.print obj ppf a
    | Amodevar mv ->
        print_axis ();
        if verbose then print_morphvar ppf mv else Format.fprintf ppf "?"
    | Amodejoin (a, mvs) ->
        print_axis ();
        Format.fprintf ppf "join(%a,%a)" (C.print obj) a
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ",")
             print_morphvar)
          mvs
    | Amodemeet (a, mvs) ->
        print_axis ();
        Format.fprintf ppf "meet(%a,%a)" (C.print obj) a
          (Format.pp_print_list
             ~pp_sep:(fun ppf () -> Format.fprintf ppf ",")
             print_morphvar)
          mvs

  (* let allow_right = function
     | Amode a -> Amode a
     | Amodevar (Amorphvar (obj, v, f)) -> Amodevar (Amorphvar (obj, v,
     C.allow_right f)) *)

  let disallow_right : type a l r. (a, l * r) mode -> (a, l * disallowed) mode =
    Obj.magic

  let disallow_left : type a l r. (a, l * r) mode -> (a, disallowed * r) mode =
    Obj.magic

  let allow_right : type a l r. (a, l * allowed) mode -> (a, l * r) mode =
    Obj.magic

  let allow_left : type a l r. (a, allowed * r) mode -> (a, l * r) mode =
    Obj.magic

  let mlower (Amorphvar (src, var, morph)) = C.apply src morph var.lower
  let mupper (Amorphvar (src, var, morph)) = C.apply src morph var.upper
  let min (type a) (obj : a C.obj) =
    Amode (C.min obj)

  let max (type a) (obj : a C.obj) =
    Amode (C.max obj)

  let of_const a = Amode a

  let apply_morphvar mid morph (Amorphvar (src, var, morph')) =
    Amorphvar (src, var, C.compose mid morph morph')

  let apply :
      type a b l r.
      a C.obj ->
      (a, b, l * r) C.morph ->
      (a, l * r) mode ->
      (b, l * r) mode =
   fun src morph -> function
    | Amode a -> Amode (C.apply src morph a)
    | Amodevar mv -> Amodevar (apply_morphvar src morph mv)
    | Amodejoin (a, vs) ->
        Amodejoin
          (C.apply src morph a, List.map (apply_morphvar src morph) vs)
    | Amodemeet (a, vs) ->
        Amodemeet
          (C.apply src morph a, List.map (apply_morphvar src morph) vs)

  let update_lower (type a) ~log (obj : a C.obj) v a =
    (match log with
    | None -> ()
    | Some log -> log := Clower (v, v.lower) :: !log
    );
    v.lower <- C.join obj v.lower a

  let update_upper (type a) ~log (obj : a C.obj) v a =
    (match log with
    | None -> ()
    | Some log -> log := Cupper (v, v.upper) :: !log
    );
    v.upper <- C.meet obj v.upper a

  let set_vlower ~log v vlower =
    (match log with
    | None -> ()
    | Some log -> log := Cvlower (v, v.vlower) :: !log
    );
    v.vlower <- vlower

  let submode_cv : type a. log:_ -> a C.obj -> a -> a var -> a option =
    fun (type a) ~log (obj : a C.obj) a' v ->
     if C.le obj a' v.lower then None
     else if not (C.le obj a' v.upper) then Some v.upper
     else (
       update_lower ~log obj v a';
       if C.le obj v.upper v.lower then set_vlower ~log v [];
       None)

  let submode_cmv :
      type a l. log:_ -> a C.obj -> a -> (a, l * allowed) morphvar -> a option =
   fun ~log obj a (Amorphvar (src, v, f) as mv) ->
    (*
    We now justify our choice of implementing the polarization outside of this
    core solver:
    This function makes a <= mv = f v
     the following line says that if the lower bound of mv is already higher
    than a, there is nothing to do.

    if v is normal but a is upside-down, which means
      - f is anti-tone
      - v.lower is actually the lower bound of v
      - (mlower mv) = f (v.lower) is actually the higher bound of (f v)
    Therefore, this check would only make sense if we do both  of the following
    flipping:
      - C.le is actaully ge if obj is upside-down
      - submode_cv actually means submode_vc if obj is upside-down.

    And both flipping are actaully easier to implement outside the current
    solver as a thin layer
        *)
    (* want a <= f v
       therefore f' a <= v *)
    if not (C.le obj a (mupper mv)) then
      Some (mupper mv)
    else
      let dst, f' = C.left_adjoint src f in
      let a' = C.apply dst f' a in
      Option.map (C.apply src f) (submode_cv ~log src a' v)

  (* None if success; Some x if failed; x is the next best attempt that MIGHT succeed.
     log and log' separate: log directly related to the operation and should be
     backtracked. log' only for optimization and might keep. *)
  let rec submode_vc :
      type a. log:_ -> log': (_ option) -> a C.obj -> a var -> a -> a option =
    fun (type a) ~log ~log' (obj : a C.obj) v a' ->
     if C.le obj v.upper a' then None
     else if not (C.le obj v.lower a') then Some v.lower
     else (
       update_upper ~log obj v a';
       let r =
         v.vlower
         |> List.find_map (fun mu ->
                let r = submode_mvc ~log ~log' obj mu v.upper in
                (* update v.lower based on mu.lower, almost free *)
                let mu_lower = mlower mu in
                if not (C.le obj mu_lower v.lower) then
                  update_lower ~log:log' obj v mu_lower;
                r)
       in
       if C.le obj v.upper v.lower then set_vlower ~log v [];
       r)

  and submode_mvc :
        'a 'r.
        log:_ ->
        log':(_ option) ->
        ('a C.obj)->
        ('a, allowed * 'r) morphvar ->
        'a ->
        'a option =
   fun ~log ~log' obj (Amorphvar (src, v, f) as mv) a ->
    (* let module L = (val C.obj obj0) in *)
    (* want f v <= a
       therefore v <= f' a
    *)
    if not (C.le obj (mlower mv) a) then
      Some (mlower mv)
    else
      let dst, f' = C.right_adjoint src f in
      let a' = C.apply dst f' a in
      Option.map (C.apply src f) (submode_vc ~log ~log' src v a')

  (* calculate the precise lower bound *)
  let constrain_lower_try (type a) (obj : a C.obj) (v : a var) =
    let rec loop lower =
      let log = ref [] in
      let log' = ref [] in
      let r = submode_vc ~log:(Some log) ~log':(Some log') obj v lower in
      !append_changes log';
      match r with
      | None -> (log, lower)
      | Some a ->
          undo_changes !log;
          loop (C.join obj a lower)
    in
    loop v.lower

  let constrain_mlower_try (Amorphvar (src, v, f)) =
    let log, lower = constrain_lower_try src v in
    (log, C.apply src f lower)

  let eq_morphvar :
      type a l0 r0 l1 r1. (a, l0 * r0) morphvar -> (a, l1 * r1) morphvar -> bool
      =
   fun (Amorphvar (obj0, v0, f0)) (Amorphvar (obj1, v1, f1)) ->
    match C.eq_obj obj0 obj1 with
    | None -> false
    | Some Refl ->
        v0 == v1
        && C.disallow_left (C.disallow_right f0)
           = C.disallow_left (C.disallow_right f1)

  let submode_mvmv (type a) ~log ~log' (dst : a C.obj)
      (Amorphvar (src0, v, f) as mv) (Amorphvar (src1, u, g) as mu) =
    if C.le dst (mupper mv) (mlower mu) then None
    else if eq_morphvar mv mu then None
    else
      (* we have f v <= g u
         which gives g' (f v) <= u where g' is LA of g.
         On the other hand, we also have
         v <= f' (g u)
      *)

      (* let newvar = Amorphvar (obj0, v, ) in *)
      match submode_mvc ~log ~log' dst mv (mupper mu) with
      | Some a -> Some (a, mupper mu)
      | None ->
          match submode_cmv ~log dst (mlower mv) mu with
          | Some a -> Some (mlower mv, a)
          | None ->
            let dst1, g' = C.left_adjoint src1 g in
            let g'f = C.compose dst1 g' (C.disallow_right f) in
            let x = Amorphvar (src0, v, g'f) in
            if not (List.exists (fun mv -> eq_morphvar mv x) u.vlower) then
              set_vlower ~log u (x :: u.vlower);
            None


  let fresh (type a) ?hint (obj : a C.obj) =
    {
      upper = C.max obj;
      lower = C.min obj;
      vlower = [];
      hint (* mark = false  *);
    }

  let newvar ?hint obj = Amodevar (Amorphvar (obj, fresh ?hint obj, C.id))

  let submode_try (type a r l) ?(logging=true) (obj : a C.obj) (a : (a, allowed * r) mode)
      (b : (a, l * allowed) mode) =
    (* Format.eprintf "submode_try %a %a\n" (print_raw obj) a (print_raw obj) b; *)
    let log, log' =
      if logging then Some (ref []), Some (ref [])
      else None, None
    in
    match
      match (a, b) with
      | Amode a, Amode b -> C.le obj a b
      | Amodevar v, Amode c -> Option.is_none (submode_mvc ~log ~log' obj v c)
      | Amode c, Amodevar v -> Option.is_none (submode_cmv ~log obj c v)
      | Amodevar v, Amodevar u ->
          Option.is_none (submode_mvmv ~log ~log' obj v u)
      | Amode a, Amodemeet (b, mvs) ->
          C.le obj a b
          && Option.is_none
               (List.find_map (fun mv -> submode_cmv ~log obj a mv) mvs)
      | Amodevar mv, Amodemeet (b, mvs) ->
          Option.is_none (submode_mvc ~log ~log' obj mv b)
          && Option.is_none
               (List.find_map
                  (fun mv' -> submode_mvmv ~log ~log' obj mv mv')
                  mvs)
      | Amodejoin (a, mvs), Amode b ->
          C.le obj a b
          && Option.is_none
               (List.find_map (fun mv' -> submode_mvc ~log ~log' obj mv' b) mvs)
      | Amodejoin (a, mvs), Amodevar mv ->
          Option.is_none (submode_cmv ~log obj a mv)
          && Option.is_none
               (List.find_map
                  (fun mv' -> submode_mvmv ~log ~log' obj mv' mv)
                  mvs)
      | Amodejoin (a, mvs), Amodemeet (b, mus) ->
          (* TODO: mabye create a intermediate variable? *)
          C.le obj a b
          && Option.is_none
              (List.find_map (fun mv -> submode_mvc ~log ~log' obj mv b) mvs)
          && Option.is_none
              (List.find_map (fun mu -> submode_cmv ~log obj a mu) mus)
          && Option.is_none
              (List.find_map (fun mu -> List.find_map
                (fun mv -> submode_mvmv ~log ~log' obj mv mu) mvs) mus)
    with
    | true ->
        Option.iter (!append_changes) log';
        Ok log
    | false ->
        (* in any case, we want to make permanent the changes in log' *)
        Option.iter (!append_changes) log';
        (* we mutated some states and found conflict;
           need to revert those mutation to keep the state consistent.
           A nice by-effect is that this function doesn't mutate state in failure
        *)
        Option.iter (fun log -> undo_changes !log) log;
        Error ()

  let submode obj a b =
    try
    match submode_try obj a b with
    | Ok log ->
        Option.iter (!append_changes) log;
        Ok ()
    | Error () -> Error ()
    with e ->
      Format.eprintf "submode: %a <= %a\n"
      (print_raw obj ~verbose:true ?axis:None) a
      (print_raw obj ~verbose:true ?axis:None) b
    ;
      raise e

  let submode_exn obj m n =
    match submode obj m n with
    | Ok () -> ()
    | Error () -> invalid_arg "submode_exn"

  let equate obj a b =
    match (submode obj a b, submode obj b a) with
    | Ok (), Ok () -> Ok ()
    | Error (), _ | _, Error () -> Error ()

  let equate_exn obj a b =
    match equate obj a b with
    | Ok () -> ()
    | Error () -> invalid_arg "equate_exn"

  let constrain_upper_morphvar obj mv =
    submode_exn obj (Amode (mupper mv)) (Amodevar mv);
    mupper mv

  let constrain_upper : type a l. a C.obj -> (a, l * allowed) mode -> a =
   fun obj -> function
    | Amode m -> m
    | Amodevar mv -> constrain_upper_morphvar obj mv
    | Amodemeet (a, mvs) ->
        List.fold_left
          (fun acc mv -> C.meet obj acc (constrain_upper_morphvar obj mv))
          a mvs

  let join :
      type a r.
      a C.obj -> (a, allowed * r) mode list -> (a, allowed * disallowed) mode =
   fun obj l ->
    let rec loop a mvs =
      if C.le obj (C.max obj) a then fun _ -> Amode (C.max obj)
      else function
        | [] -> Amodejoin (a, mvs)
        | mv :: xs -> (
            match disallow_right mv with
            | Amode b -> loop (C.join obj a b) mvs xs
            | Amodevar mv -> loop a (mv :: mvs) xs
            | Amodejoin (b, mvs') -> loop (C.join obj a b) (mvs' @ mvs) xs)
    in
    loop (C.min obj) [] l

  let meet :
      type a l.
      a C.obj -> (a, l * allowed) mode list -> (a, disallowed * allowed) mode =
   fun obj l ->
    let rec loop a mvs =
      if C.le obj a (C.min obj) then fun _ -> Amode (C.min obj)
      else function
        | [] -> Amodemeet (a, mvs)
        | mv :: xs -> (
            match disallow_left mv with
            | Amode b -> loop (C.meet obj a b) mvs xs
            | Amodevar mv -> loop a (mv :: mvs) xs
            | Amodemeet (b, mvs') -> loop (C.meet obj a b) (mvs' @ mvs) xs)
    in
    loop (C.max obj) [] l

  let constrain_lower_morphvar ~commit mv =
    let log, lower = constrain_mlower_try mv in
    if commit then !append_changes log
    else undo_changes !log;
    lower

  let constrain_lower : type a r. a C.obj -> (a, allowed * r) mode -> a =
   fun obj -> function
    | Amode a -> a
    | Amodevar mv -> constrain_lower_morphvar ~commit:true mv
    | Amodejoin (a, mvs) ->
        List.fold_left
          (fun acc mv ->
            C.join obj acc (constrain_lower_morphvar ~commit:true mv))
          a mvs

  (* because lower bound conservative, this check is also conservative.
     if it returns Some, then definitely a constant.
     if it returns None, then we don't know anything *)
  let check_const : type a l r. a C.obj -> (a, l * r) mode -> a option =
   fun obj ->
    function
    | Amode a -> Some a
    | Amodevar mv ->
        let lower = constrain_lower_morphvar ~commit:false mv in
        if C.le obj (mupper mv) lower then Some lower else None
    | Amodemeet (a, mvs) ->
        let upper =
          List.fold_left (fun x mv -> C.meet obj x (mupper mv)) a mvs
        in
        let lower =
          List.fold_left
            (fun x mv ->
              C.meet obj x (constrain_lower_morphvar ~commit:false mv))
            a mvs
        in
        if C.le obj upper lower then Some upper else None
    | Amodejoin (a, mvs) ->
        let upper =
          List.fold_left (fun x mv -> C.join obj x (mupper mv)) a mvs
        in
        let lower =
          List.fold_left
            (fun x mv ->
              C.join obj x (constrain_lower_morphvar ~commit:false mv))
            a mvs
        in
        if C.le obj upper lower then Some lower else None

  let print :
      type a l r.
      ?verbose:bool ->
      ?axis:string ->
      a C.obj ->
      Format.formatter ->
      (a, l * r) mode ->
      unit =
   fun ?(verbose = true) ?axis obj ppf m ->
    print_raw obj ~verbose ?axis ppf
      (match check_const obj m with None -> m | Some a -> Amode a)

  let newvar_above (type a) ?hint (obj : a C.obj) =
    function
    | Amode a when C.le obj (C.max obj) a -> (Amode a, false)
    | m ->
        let m' = newvar ?hint obj in
        let r = submode_try ~logging:false obj m m' in
        (match r with
        | Ok None -> ()
        | _ -> assert false
        );
        (allow_right m', true)

  let newvar_below (type a) ?hint (obj : a C.obj) =
    function
    | Amode a when C.le obj a (C.min obj) -> (Amode a, false)
    | m ->
        let m' = newvar ?hint obj in
        let r = submode_try ~logging:false obj m' m in
        (match r with
        | Ok None -> ();
        | Ok (Some _ ) -> assert false;
        | Error () -> begin
          Format.eprintf "%a\n" (print_raw obj ~verbose:true ?axis:None) m;
          assert false
        end);
        (allow_left m', true)
end

module Solver_polarized (C : Lattices_mono) = struct
  (* We do a small generalization of mono_lattices and mono_solver.
     First, we construct a new category of lattices out of (C : Mono_lattices).
     The objects are two copies of the objects in C via constructors Positive and
     Negative. The morphisms are four copies of the morphisms via constructors
     Pos_Pos, Pos_Neg, Neg_Pos, Neg_Neg.

     `Negative obj` represents the dual lattice of obj where orders are flipped.
     Correspondingly, `Pos_Neg f` still represents (f : a -> b), but now that it
     goes from (Pos a) to (Neg b), it becomes an anti-tone function. Same with
     `Neg_Pos f`. On the other hand, `Pos_Pos f` and `Neg_Neg f` are still
     monotone functions.

     The good thing is, we can just run Mono_solver on the original category
     C, and translate submoding on the new category to submoding on the original
     category. For example, `submode (Neg obj) m0 m1` translates to `submode obj
     m1 m0`. This whole thing is needed because the morphisms between
     uniqueness and linearity can be anti-tone.

     Hopefully everything here will be inlined and optimized away.
  *)

  module S = Solver_mono (C)

  type 'a neg = Neg of 'a [@@unboxed]
  type 'a pos = Pos of 'a [@@unboxed]

  (* This category contains three kinds of objects:
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

  type ('a, 'd) mode =
    | Positive : ('a, 'd) S.mode -> ('a pos, 'd positive) mode
    | Negative : ('a, 'd) S.mode -> ('a neg, 'd negative) mode

  (* id and compose not used, but just for fun *)
  let id : type a l r. a obj -> (a, l * r, a, l * r) morph = function
    | Positive _ -> Pos_Pos C.id
    | Negative _ -> Neg_Neg C.id

  let compose :
      type a b c al ar bl br cl cr.
      b obj ->
      (b, bl * br, c, cl * cr) morph ->
      (a, al * ar, b, bl * br) morph ->
      (a, al * ar, c, cl * cr) morph =
   fun mid f g ->
    match (mid, f, g) with
    | Positive mid, Pos_Pos f, Pos_Pos g -> Pos_Pos (C.compose mid f g)
    | Positive mid, Pos_Pos f, Neg_Pos g -> Neg_Pos (C.compose mid f g)
    | Positive mid, Pos_Neg f, Neg_Pos g -> Neg_Neg (C.compose mid f g)
    | Positive mid, Pos_Neg f, Pos_Pos g -> Pos_Neg (C.compose mid f g)
    | Negative mid, Neg_Pos f, Pos_Neg g -> Pos_Pos (C.compose mid f g)
    | Negative mid, Neg_Pos f, Neg_Neg g -> Neg_Pos (C.compose mid f g)
    | Negative mid, Neg_Neg f, Neg_Neg g -> Neg_Neg (C.compose mid f g)
    | Negative mid, Neg_Neg f, Pos_Neg g -> Pos_Neg (C.compose mid f g)

  let apply :
      type a b d0 d1 e0 e1.
      a obj ->
      (a, d0 * d1, b, e0 * e1) morph ->
      (a, d0 * d1) mode ->
      (b, e0 * e1) mode =
   fun src f ->
    match (src, f) with
    | Positive src, Pos_Pos f ->
        fun (Positive m) -> Positive (S.apply src f m)
    | Positive src, Pos_Neg f ->
        fun (Positive m) -> Negative (S.apply src f m)
    | Negative src, Neg_Pos f ->
        fun (Negative m) -> Positive (S.apply src f m)
    | Negative src, Neg_Neg f ->
        fun (Negative m) -> Negative (S.apply src f m)

  let newvar : type a l r. ?hint:string -> a obj -> (a, l * r) mode =
   fun ?hint -> function
    | Positive obj ->
        let m = S.newvar ?hint obj in
        Positive m
    | Negative obj ->
        let m = S.newvar ?hint obj in
        Negative m

  let submode :
      type a l r.
      a obj ->
      (a, allowed * r) mode ->
      (a, l * allowed) mode ->
      (unit, unit) result = function
    | Positive obj -> (
        fun m0 m1 ->
          match (m0, m1) with Positive m0, Positive m1 -> S.submode obj m0 m1)
    | Negative obj -> (
        fun m0 m1 ->
          match (m0, m1) with Negative m0, Negative m1 -> S.submode obj m1 m0)

  let join :
      type a r. a obj -> (a, allowed * r) mode list -> (a, left_only) mode =
    function
    | Positive obj ->
        fun l ->
          let l = List.map (fun (Positive m) -> m) l in
          Positive (S.join obj l)
    | Negative obj ->
        fun l ->
          let l = List.map (fun (Negative m) -> m) l in
          Negative (S.meet obj l)

  let meet :
      type a l. a obj -> (a, l * allowed) mode list -> (a, right_only) mode =
    function
    | Positive obj ->
        fun l ->
          let l = List.map (fun (Positive m) -> m) l in
          Positive (S.meet obj l)
    | Negative obj ->
        fun l ->
          let l = List.map (fun (Negative m) -> m) l in
          Negative (S.join obj l)

  let submode_exn obj m0 m1 =
    match submode obj m0 m1 with
    | Ok () -> ()
    | Error () -> invalid_arg "submode_exn"

  let equate :
      type a. a obj -> (a, both) mode -> (a, both) mode -> (unit, unit) result =
    function
    | Positive obj -> fun (Positive m0) (Positive m1) -> S.equate obj m0 m1
    | Negative obj -> fun (Negative m0) (Negative m1) -> S.equate obj m0 m1

  let equate_exn obj m0 m1 =
    match equate obj m0 m1 with
    | Ok () -> ()
    | Error () -> invalid_arg "equate_exn"

  let of_const : type a l r. a obj -> a -> (a, l * r) mode = function
    | Positive _ -> fun (Pos a) -> Positive (S.of_const a)
    | Negative _ -> fun (Neg a) -> Negative (S.of_const a)

  let min : type a l r. a obj -> (a, l * r) mode = function
    | Positive obj -> Positive (S.min obj)
    | Negative obj -> Negative (S.max obj)

  let max : type a l r. a obj -> (a, l * r) mode = function
    | Positive obj -> Positive (S.max obj)
    | Negative obj -> Negative (S.min obj)

  let constrain_lower : type a r. a obj -> (a, allowed * r) mode -> a = function
    | Positive obj -> fun (Positive m) -> Pos (S.constrain_lower obj m)
    | Negative obj -> fun (Negative m) -> Neg (S.constrain_upper obj m)

  let constrain_upper : type a l. a obj -> (a, l * allowed) mode -> a = function
    | Positive obj -> fun (Positive m) -> Pos (S.constrain_upper obj m)
    | Negative obj -> fun (Negative m) -> Neg (S.constrain_lower obj m)

  let newvar_above :
      type a r_ l r.
      ?hint:string -> a obj -> (a, allowed * r_) mode -> (a, l * r) mode * bool
      =
   fun ?hint -> function
    | Positive obj ->
        fun (Positive m) ->
          let m, b = S.newvar_above ?hint obj m in
          (Positive m, b)
    | Negative obj ->
        fun (Negative m) ->
          let m, b = S.newvar_below ?hint obj m in
          (Negative m, b)

  let newvar_below :
      type a l_ l r.
      ?hint:string -> a obj -> (a, l_ * allowed) mode -> (a, l * r) mode * bool
      =
   fun ?hint -> function
    | Positive obj ->
        fun (Positive m) ->
          let m, b = S.newvar_below ?hint obj m in
          (Positive m, b)
    | Negative obj ->
        fun (Negative m) ->
          let m, b = S.newvar_above ?hint obj m in
          (Negative m, b)

  let disallow_left : type a l r. (a, l * r) mode -> (a, disallowed * r) mode =
    function
    | Positive m -> Positive (S.disallow_left m)
    | Negative m -> Negative (S.disallow_right m)

  let disallow_right : type a l r. (a, l * r) mode -> (a, l * disallowed) mode =
    function
    | Positive m -> Positive (S.disallow_right m)
    | Negative m -> Negative (S.disallow_left m)

  let allow_left : type a l r. (a, allowed * r) mode -> (a, l * r) mode =
    function
    | Positive m -> Positive (S.allow_left m)
    | Negative m -> Negative (S.allow_right m)

  let allow_right : type a l r. (a, l * allowed) mode -> (a, l * r) mode =
    function
    | Positive m -> Positive (S.allow_right m)
    | Negative m -> Negative (S.allow_left m)

  let check_const : type a l r. a obj -> (a, l * r) mode -> a option = function
    | Positive obj ->
        fun (Positive m) -> Option.map (fun x -> Pos x) (S.check_const obj m)
    | Negative obj ->
        fun (Negative m) -> Option.map (fun x -> Neg x) (S.check_const obj m)

  let print :
      type a.  ?verbose:bool -> ?axis:string -> a obj -> _ -> (a, _) mode -> unit
      =
   fun ?(verbose = false) ?axis obj ppf m ->
    match (obj, m) with
    | Positive obj, Positive m -> S.print ~verbose ?axis obj ppf m
    | Negative obj, Negative m -> S.print ~verbose ?axis obj ppf m
end
