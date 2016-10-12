open Term

type kripke_result =
    Refutable of int * bool array array * (pterm, bool array) Hashtbl.t
  | Irrefutable
  | NotDetermined

val solve_n : name_env -> int -> pterm -> kripke_result
val solve : name_env -> pterm -> kripke_result
