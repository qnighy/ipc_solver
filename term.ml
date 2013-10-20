open Format

type pnterm =
  | PNVarName of string
  | PNArrow of pnterm * pnterm
  | PNOr of pnterm * pnterm
  | PNAnd of pnterm * pnterm
  | PNTop
  | PNBot


let rec pp_print_pnterm pr ppf = function
  | PNVarName s ->
      fprintf ppf "%s" s
  | PNArrow (t,PNBot) ->
      fprintf ppf "@[~%a@]"
        (pp_print_pnterm 1) t
  | PNArrow (t1,t2) ->
      fprintf ppf "@[";
      if pr < 4 then fprintf ppf "(";
      fprintf ppf "%a@ ->@ %a"
        (pp_print_pnterm 3) t1
        (pp_print_pnterm 4) t2;
      if pr < 4 then fprintf ppf ")";
      fprintf ppf "@]"
  | PNAnd (PNArrow (t1,t2),PNArrow (t2t,t1t))
        when t1=t1t && t2=t2t ->
      fprintf ppf "@[";
      if pr < 5 then fprintf ppf "(";
      fprintf ppf "%a@ <->@ %a"
        (pp_print_pnterm 4) t1
        (pp_print_pnterm 4) t2;
      if pr < 5 then fprintf ppf ")";
      fprintf ppf "@]"
  | PNAnd (t1,t2) ->
      fprintf ppf "@[";
      if pr < 2 then fprintf ppf "(";
      fprintf ppf "%a@ /\\@ %a"
        (pp_print_pnterm 1) t1
        (pp_print_pnterm 2) t2;
      if pr < 2 then fprintf ppf ")";
      fprintf ppf "@]"
  | PNOr (t1,t2) ->
      fprintf ppf "@[";
      if pr < 3 then fprintf ppf "(";
      fprintf ppf "%a@ \\/@ %a"
        (pp_print_pnterm 2) t1
        (pp_print_pnterm 3) t2;
      if pr < 3 then fprintf ppf ")";
      fprintf ppf "@]"
  | PNTop ->
      fprintf ppf "True"
  | PNBot ->
      fprintf ppf "False"

type pterm =
  | PVar of int
  | PArrow of pterm * pterm
  | POr of pterm * pterm
  | PAnd of pterm * pterm
  | PTop
  | PBot

type name_env = {
  dict : (string,int) Hashtbl.t;
  reverse_dict : (int,string) Hashtbl.t
}

let new_name_env () = {
  dict = Hashtbl.create 10;
  reverse_dict = Hashtbl.create 100
}
let empty_env = {
  dict = Hashtbl.create 10;
  reverse_dict = Hashtbl.create 100
}

let rec convert_name_impl env num = function
  | PNVarName s ->
      begin try
        PVar (Hashtbl.find env.dict s)
      with Not_found ->
        let t = PVar !num in
        Hashtbl.add env.dict s !num;
        Hashtbl.add env.reverse_dict !num s;
        num := !num + 1;
        t
      end
  | PNArrow (t1,t2) ->
      PArrow (convert_name_impl env num t1,
        convert_name_impl env num t2)
  | PNAnd (PNArrow (t1,t2),PNArrow(t2t,t1t))
      when t1=t1t && t2=t2t ->
      let ct1 = convert_name_impl env num t1 in
      let ct2 = convert_name_impl env num t2 in
      PAnd (PArrow (ct1,ct2),PArrow(ct2,ct1))
  | PNAnd (t1,t2) ->
      PAnd (convert_name_impl env num t1,
        convert_name_impl env num t2)
  | PNOr (t1,t2) ->
      POr (convert_name_impl env num t1,
        convert_name_impl env num t2)
  | PNTop -> PTop
  | PNBot -> PBot

let convert_name tn =
  let env = new_name_env () in
  let num = ref 0 in
  let t = convert_name_impl env num tn in
  t, env, !num

let rec pp_print_pterm env pr ppf = function
  | PVar n ->
      begin try
        fprintf ppf "%s" (Hashtbl.find env.reverse_dict n)
      with Not_found ->
        fprintf ppf "?%d" n
      end
  | PArrow (t,PBot) ->
      fprintf ppf "@[~%a@]"
        (pp_print_pterm env 1) t
  | PArrow (t1,t2) ->
      fprintf ppf "@[";
      if pr < 4 then fprintf ppf "(";
      fprintf ppf "%a@ ->@ %a"
        (pp_print_pterm env 3) t1
        (pp_print_pterm env 4) t2;
      if pr < 4 then fprintf ppf ")";
      fprintf ppf "@]"
  | PAnd (PArrow (t1,t2),PArrow (t2t,t1t))
        when t1=t1t && t2=t2t ->
      fprintf ppf "@[";
      if pr < 5 then fprintf ppf "(";
      fprintf ppf "%a@ <->@ %a"
        (pp_print_pterm env 4) t1
        (pp_print_pterm env 4) t2;
      if pr < 5 then fprintf ppf ")";
      fprintf ppf "@]"
  | PAnd (t1,t2) ->
      fprintf ppf "@[";
      if pr < 2 then fprintf ppf "(";
      fprintf ppf "%a@ /\\@ %a"
        (pp_print_pterm env 1) t1
        (pp_print_pterm env 2) t2;
      if pr < 2 then fprintf ppf ")";
      fprintf ppf "@]"
  | POr (t1,t2) ->
      fprintf ppf "@[";
      if pr < 3 then fprintf ppf "(";
      fprintf ppf "%a@ \\/@ %a"
        (pp_print_pterm env 2) t1
        (pp_print_pterm env 3) t2;
      if pr < 3 then fprintf ppf ")";
      fprintf ppf "@]"
  | PTop ->
      fprintf ppf "True"
  | PBot ->
      fprintf ppf "False"

let rec pp_print_pterm_latex_internal env pr ppf = function
  | PVar n ->
      begin try
        fprintf ppf "%s" (Hashtbl.find env.reverse_dict n)
      with Not_found ->
        fprintf ppf "?%d" n
      end
  | PArrow (t,PBot) ->
      fprintf ppf "@[\\lnot@ %a@]"
        (pp_print_pterm_latex_internal env 1) t
  | PArrow (t1,t2) ->
      fprintf ppf "@[";
      if pr < 4 then fprintf ppf "(";
      fprintf ppf "%a@ \\to@ %a"
        (pp_print_pterm_latex_internal env 3) t1
        (pp_print_pterm_latex_internal env 4) t2;
      if pr < 4 then fprintf ppf ")";
      fprintf ppf "@]"
  | PAnd (PArrow (t1,t2),PArrow (t2t,t1t))
        when t1=t1t && t2=t2t ->
      fprintf ppf "@[";
      if pr < 5 then fprintf ppf "(";
      fprintf ppf "%a@ \\iff@ %a"
        (pp_print_pterm_latex_internal env 4) t1
        (pp_print_pterm_latex_internal env 4) t2;
      if pr < 5 then fprintf ppf ")";
      fprintf ppf "@]"
  | PAnd (t1,t2) ->
      fprintf ppf "@[";
      if pr < 2 then fprintf ppf "(";
      fprintf ppf "%a@ \\land@ %a"
        (pp_print_pterm_latex_internal env 1) t1
        (pp_print_pterm_latex_internal env 2) t2;
      if pr < 2 then fprintf ppf ")";
      fprintf ppf "@]"
  | POr (t1,t2) ->
      fprintf ppf "@[";
      if pr < 3 then fprintf ppf "(";
      fprintf ppf "%a@ \\lor@ %a"
        (pp_print_pterm_latex_internal env 2) t1
        (pp_print_pterm_latex_internal env 3) t2;
      if pr < 3 then fprintf ppf ")";
      fprintf ppf "@]"
  | PTop ->
      fprintf ppf "\\top"
  | PBot ->
      fprintf ppf "\\bot"

let pp_print_pterm_latex env pr ppf t =
  fprintf ppf "@[$";
  pp_print_pterm_latex_internal env pr ppf t;
  fprintf ppf "$@]"
