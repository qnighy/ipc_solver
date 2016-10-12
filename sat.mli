type environment

val new_environment : unit -> environment
val fresh_var : environment -> int
val add_clause : environment -> int array -> unit

type result =
  | Satisfiable of bool array
  | Unsatisfiable
  | NotDetermined

val invoke_minisat : environment -> result
