type pnterm =
  | PNVarName of string
  | PNArrow of pnterm * pnterm
  | PNOr of pnterm * pnterm
  | PNAnd of pnterm * pnterm
  | PNTop
  | PNBot

val pp_print_pnterm : int -> Format.formatter -> pnterm -> unit


type pterm =
  | PVar of int
  | PArrow of pterm * pterm
  | POr of pterm * pterm
  | PAnd of pterm * pterm
  | PTop
  | PBot

type name_env = {
  dict : (string, int) Hashtbl.t;
  reverse_dict : (int, string) Hashtbl.t;
}

val new_name_env : unit -> name_env
val empty_env : name_env

val convert_name_impl : name_env -> int ref -> pnterm -> pterm
val convert_name : pnterm -> pterm * name_env * int

val pp_print_pterm : name_env -> int -> Format.formatter -> pterm -> unit
val pterm_short_string : name_env -> int -> pterm -> string
val pp_print_pterm_latex_internal :
  name_env -> int -> Format.formatter -> pterm -> unit
val pp_print_pterm_latex :
  name_env -> int -> Format.formatter -> pterm -> unit
