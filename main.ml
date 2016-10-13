open Term
open Format

let verbose = ref false
let latex_output = ref None

let usage_msg =
  "ipc_solver is a solver for intuitionistic propositional formulas.\n" ^
  "\n" ^
  "usage:"

let speclist = [
  ("--latex", Arg.String (fun path -> latex_output := Some path),
    "Sets a path for latex output");
  ("--no-latex", Arg.Unit (fun _ -> latex_output := None),
    "Cancels latex output");
  ("--verbose", Arg.Set verbose, "Enables verbose output");
  ("-v", Arg.Set verbose, "Enables verbose output")
]

let () =
  Arg.parse speclist (fun _ -> ()) usage_msg;
  let lexbuf = Lexing.from_channel stdin in
  begin try
    let tn = Parser.main Lexer.token lexbuf in
    if !verbose then eprintf "Term is %a@." pp_print_pnterm tn;
    let (t,env,num) = convert_name tn in
    if !verbose then eprintf "Term is %a@." (pp_print_pterm env) t;
    let solver_result = Solver.solve num t in
    let classical_result = begin match solver_result with
      | Some _ -> Kripke.Irrefutable
      | None -> Kripke.solve_n env 1 t end in
    let kripke_result = begin match solver_result, classical_result with
      | Some _, _ -> Kripke.Irrefutable
      | _, Kripke.Irrefutable -> Kripke.solve env t
      | _, r -> r end in
    let message =
      begin match solver_result, classical_result with
      | Some _, _ -> "Provable."
      | _, Kripke.Refutable _ -> "Not provable in intuitionistic logic; not provable in classical logic neither."
      | _, Kripke.Irrefutable -> "Not provable in intuitionistic logic; provable in classical logic however."
      | _, _ -> "Not provable in intuitionistic logic."
      end in
    Printf.printf "%s\n" message;
    begin match !latex_output with
    | Some latex_path ->
        let f = open_out latex_path in
        let ff = formatter_of_out_channel f in
        fprintf ff "%s@." "\\documentclass[preview,varwidth=10000px,12pt]{standalone}";
        fprintf ff "%s@." "\\usepackage{bussproofs}";
        fprintf ff "%s@." "\\usepackage{color}";
        fprintf ff "%s@." "\\usepackage{latexsym}";
        fprintf ff "%s@." "\\begin{document}";
        fprintf ff "%a:@.@." (pp_print_pterm_latex env 5) t;
        fprintf ff "%s@.@." message;
        begin match Solver.solve num t with
        | Some pr ->
            if !verbose then eprintf "proof(LF, plain): %a@."
              Lf_proof.pp_print_proofitem pr;
            if !verbose then eprintf "proof(LF):@,%a@."
              (Lf_proof.pp_print_proof env num t) pr;
            let npr = Nj_proof.convert_lf t pr in
            if !verbose then eprintf "proof(NJ):@,%a@."
              (Nj_proof.pp_print_lambda env) npr;
            ignore (Nj_proof.nj_check_type [] npr);
            let npr = Nj_proof.postproc_proof npr in
            ignore (Nj_proof.nj_check_type [] npr);
            if !verbose then eprintf "proof(NJ):@,%a@."
              (Nj_proof.pp_print_lambda env) npr;

            fprintf ff "%s@.@." "Proof tree (intuitionistic):";
            fprintf ff "%a@." (Nj_proof.print_nj_latex env) npr
        | None -> ()
        end;
        begin match kripke_result with
        | Kripke.Refutable (n, accessibility, term_asgn) ->
            if n == 1 then begin
              fprintf ff "%s" "Counterexample: ";
              for i = 0 to (num-1) do
                if i <> 0 then fprintf ff ", ";
                fprintf ff "$%a = %d$"
                  (pp_print_pterm_latex_internal env 5) (PVar i)
                  (if (Hashtbl.find term_asgn (PVar i)).(0) then 1 else 0)
              done;
              fprintf ff "@.@."
            end else begin
              fprintf ff "%s" "Kripke counterexample: ";
              fprintf ff "$\\mathcal{W} = \\{";
              for j = 0 to (n-1) do
                if j <> 0 then fprintf ff ", ";
                fprintf ff "W_{%d}" j
              done;
              fprintf ff "\\}$, ";
              for i = 0 to (n-1) do
                for j = i+1 to (n-1) do
                  if accessibility.(i).(j) then begin
                    let ok = ref true in
                    for k = i+1 to (j-1) do
                      if accessibility.(i).(j) && accessibility.(j).(k) then
                        ok := false
                    done;
                    if !ok then fprintf ff "$(W_{%d} \\leadsto W_{%d})$, " i j
                  end
                done
              done;
              for i = 0 to (num-1) do
                if i <> 0 then fprintf ff ", ";
                fprintf ff "$%a = \\{"
                  (pp_print_pterm_latex_internal env 5) (PVar i);
                let comma = ref false in
                for j = 0 to (n-1) do
                  if (Hashtbl.find term_asgn (PVar i)).(j) then begin
                    if !comma then fprintf ff ", ";
                    fprintf ff "W_{%d}" j;
                    comma := true
                  end
                done;
                fprintf ff "\\}$"
              done;
              fprintf ff "@.@."
            end
        | _ -> ()
        end;
        fprintf ff "%s@." "\\end{document}";
        close_out f
    | None -> ()
    end
  with
  | Parsing.Parse_error ->
      Printf.printf "Parse Error\n";
      begin match !latex_output with
      | Some latex_path ->
          let f = open_out latex_path in
          let ff = formatter_of_out_channel f in
          fprintf ff "%s@." "%parse_error";
          fprintf ff "%s@." "\\documentclass[preview,varwidth=4000px]{standalone}";
          fprintf ff "%s@." "\\begin{document}";
          fprintf ff "%s@." "Parse Error";
          fprintf ff "%s@." "\\end{document}";
          close_out f
      | None -> ()
      end
  end

