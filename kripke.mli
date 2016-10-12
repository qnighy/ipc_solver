open Term
open Sat

type kripke_env = {
  n : int;
  accessibility : int array array
}

val new_kripke_env : sat_env -> int -> kripke_env
val make_clauses :
  sat_env -> kripke_env -> (pterm, int array) Hashtbl.t -> pterm -> int array

type kripke_result =
    KripkeRefutable of int * bool array array * (pterm, bool array) Hashtbl.t
  | KripkeIrrefutable
  | KripkeNotDetermined

val solve_n : name_env -> int -> pterm -> kripke_result
val solve : name_env -> pterm -> kripke_result
