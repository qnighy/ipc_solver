open Term

type sat_env = {
  mutable maxvar: int;
  mutable clauses: int array list
}

val new_sat_env : unit -> sat_env
val fresh_var : sat_env -> int
val add_clause : sat_env -> int array -> unit

type sat_result =
    Satisfiable of bool array
  | Unsatisfiable
  | NotDetermined

val invoke_minisat : sat_env -> sat_result

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
