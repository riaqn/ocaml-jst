(* TEST
   * expect
*)

(* CR layouts: all tests from this file moved to [void_alpha.ml].  Move back
   here when the stuff from v5 no longer needs extension flags. *)
type t_void [@@void];;
[%%expect {|
Line 1, characters 12-20:
1 | type t_void [@@void];;
                ^^^^^^^^
Error: Layout void is used here, but the appropriate layouts extension is not enabled
|}]