open Term
open Nj_proof

(* priority:
 * atom, () : 0
 * function application : 1, left associative
 * (->) : 2, right associative
 *)

let rec pp_print_pterm_haskell_internal env pr ppf = function
  | PVar n ->
      begin try
        Format.fprintf ppf "%s"
          (String.uncapitalize_ascii (Hashtbl.find env.reverse_dict n))
      with Not_found ->
        Format.fprintf ppf "?%d" n
      end
  | PArrow (t1,t2) ->
      Format.fprintf ppf "@[%s%a@ ->@ %a%s@]"
        (if pr < 2 then "(" else "")
        (pp_print_pterm_haskell_internal env 1) t1
        (pp_print_pterm_haskell_internal env 2) t2
        (if pr < 2 then ")" else "")
  | PAnd (t1,t2) ->
      Format.fprintf ppf "@[(%a,@ %a)@]"
        (pp_print_pterm_haskell_internal env 5) t1
        (pp_print_pterm_haskell_internal env 5) t2
  | POr (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 1 then Format.fprintf ppf "(";
      Format.fprintf ppf "Either@ %a@ %a"
        (pp_print_pterm_haskell_internal env 0) t1
        (pp_print_pterm_haskell_internal env 0) t2;
      if pr < 1 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PTop ->
      Format.fprintf ppf "()"
  | PBot ->
      Format.fprintf ppf "Void"

let fresh stack =
  try
    List.find (fun name ->
      not (List.exists (fun n -> n = name) stack)
    ) ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]
  with Not_found ->
    let num = ref 0 in
    while let name = Printf.sprintf "x%d" !num in
      List.exists (fun n -> n = name) stack do
      num := !num + 1
    done;
    Printf.sprintf "x%d" !num

let rec pp_print_nj_haskell_internal env stack pr ppf = function
  | NJ_var (_, x) ->
      Format.fprintf ppf "%s" (List.nth stack x)
  | NJ_app (_, t1, t2) ->
      Format.fprintf ppf "@[<1>%s%a@ %a%s@]@,"
        (if pr < 1 then "(" else "")
        (pp_print_nj_haskell_internal env stack 1) t1
        (pp_print_nj_haskell_internal env stack 0) t2
        (if pr < 1 then ")" else "")
  | NJ_abs (_, _, _) as t ->
      Format.fprintf ppf "@[<1>(\\%a)@]@,"
        (pp_print_nj_haskell_binders env stack "->") t
  | NJ_tt -> Format.fprintf ppf "()"
  | NJ_ab (_, t1) ->
      Format.fprintf ppf "@[<1>%sabsurd %a%s@]@,"
        (if pr < 1 then "(" else "")
        (pp_print_nj_haskell_internal env stack 0) t1
        (if pr < 1 then ")" else "")
  | NJ_conj (_, t1, t2) ->
      Format.fprintf ppf "@[<1>(%a,@ %a)@]@,"
        (pp_print_nj_haskell_internal env stack 5) t1
        (pp_print_nj_haskell_internal env stack 5) t2
  | NJ_fst (_, t1) ->
      Format.fprintf ppf "@[<1>%sfst@ %a%s@]@,"
        (if pr < 1 then "(" else "")
        (pp_print_nj_haskell_internal env stack 0) t1
        (if pr < 1 then ")" else "")
  | NJ_snd (_, t1) ->
      Format.fprintf ppf "@[<1>%ssnd@ %a%s@]@,"
        (if pr < 1 then "(" else "")
        (pp_print_nj_haskell_internal env stack 0) t1
        (if pr < 1 then ")" else "")
  | NJ_left (_, t1) ->
      Format.fprintf ppf "@[<1>%sLeft@ %a%s@]@,"
        (if pr < 1 then "(" else "")
        (pp_print_nj_haskell_internal env stack 0) t1
        (if pr < 1 then ")" else "")
  | NJ_right (_, t1) ->
      Format.fprintf ppf "@[<1>%sRight@ %a%s@]@,"
        (if pr < 1 then "(" else "")
        (pp_print_nj_haskell_internal env stack 0) t1
        (if pr < 1 then ")" else "")
  | NJ_disj (_,t1,t2,t3) ->
      Format.fprintf ppf "@[<1>%seither@ %a@ %a@ %a%s@]@,"
        (if pr < 1 then "(" else "")
        (pp_print_nj_haskell_internal env stack 0) t2
        (pp_print_nj_haskell_internal env stack 0) t3
        (pp_print_nj_haskell_internal env stack 0) t1
        (if pr < 1 then ")" else "")
and pp_print_nj_haskell_binders env stack op ppf = function
  | NJ_abs (_, _, ta) ->
      let freshname = fresh stack in
      let stack = freshname :: stack in
      Format.fprintf ppf "%s@ %a"
        freshname
        (pp_print_nj_haskell_binders env stack op) ta
  | t ->
      Format.fprintf ppf "%s@ %a"
        op
        (pp_print_nj_haskell_internal env stack 5) t

let haskell_of_nj env t =
  Format.asprintf
    ("@[<1>import@ Data.Void@]@." ^^
    "@." ^^
    "@[<1>answer@ ::@ %a@]@." ^^
    "@[<1>answer@ %a@]@.")
    (pp_print_pterm_haskell_internal env 5) (nj_type t)
    (pp_print_nj_haskell_binders env [] "=") t
