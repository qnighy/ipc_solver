open Term
open Format

let latex_output = ref None

let usage_msg =
  "ipc_solver is a solver for intuitionistic propositional formulas.\n" ^
  "\n" ^
  "usage:"

let speclist = [
  ("--latex", Arg.String (fun path -> latex_output := Some path),
    "Sets a path for latex output");
  ("--no-latex", Arg.Unit (fun _ -> latex_output := None),
    "Cancels latex output")
]

let () =
  Arg.parse speclist (fun _ -> ()) usage_msg;
  let lexbuf = Lexing.from_channel stdin in
  begin try
    let tn = Parser.main Lexer.token lexbuf in
    (* eprintf "Term is %a@." (pp_print_pnterm 5) tn; *)
    let (t,env,num) = convert_name tn in
    (* eprintf "Term is %a@." (pp_print_pterm env 5) t; *)
    begin match Solver.solve num t with
    | Some pr ->
        eprintf "solved. provable@.";
        begin match !latex_output with
        | Some latex_path ->
            (* eprintf "proof(LF, plain): %a@."
              Lf_proof.pp_print_proofitem pr; *)
            (* eprintf "proof(LF):@,%a@."
              (Lf_proof.pp_print_proof env num t) pr; *)
            let npr = Nj_proof.convert_lf t pr in
            (* eprintf "proof(NJ):@,%a@."
              (Nj_proof.pp_print_lambda env) npr; *)
            ignore (Nj_proof.nj_check_type [] npr);
            let npr = Nj_proof.postproc_proof npr in
            ignore (Nj_proof.nj_check_type [] npr);
            (* eprintf "proof(NJ):@,%a@."
              (Nj_proof.pp_print_lambda env) npr; *)

            (* printf "%s@." "\\documentclass[preview]{standalone}"; *)
            let f = open_out latex_path in
            let ff = formatter_of_out_channel f in
            fprintf ff "%s@." "%provable";
            fprintf ff "%s@." "\\documentclass[preview,varwidth=10000px,12pt]{standalone}";
            fprintf ff "%s@." "\\usepackage{bussproofs}";
            fprintf ff "%s@." "\\usepackage{color}";
            fprintf ff "%s@." "\\begin{document}";
            fprintf ff "%a@." (Nj_proof.print_nj_latex env) npr;
            fprintf ff "%s@." "\\end{document}";
            close_out f
        | None -> ()
        end
    | None ->
        eprintf "solved. unprovable@.";
        begin match !latex_output with
        | Some latex_path ->
            let f = open_out latex_path in
            let ff = formatter_of_out_channel f in
            fprintf ff "%s@." "%unprovable";
            fprintf ff "%s@." "\\documentclass[preview,varwidth=4000px]{standalone}";
            fprintf ff "%s@." "\\begin{document}";
            fprintf ff "%s@." "unprovable";
            fprintf ff "%s@." "\\end{document}"
        | None -> ()
        end
    end
  with
  | Parsing.Parse_error ->
      eprintf "Parse Error@.";
      begin match !latex_output with
      | Some latex_path ->
          printf "%s@." "%parse_error";
          printf "%s@." "\\documentclass[preview,varwidth=4000px]{standalone}";
          printf "%s@." "\\begin{document}";
          printf "%s@." "Parse Error";
          printf "%s@." "\\end{document}"
      | None -> ()
      end
  end

