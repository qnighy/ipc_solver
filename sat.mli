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
