type pnterm =
  | PNVarName of string
  | PNArrow of pnterm * pnterm
  | PNOr of pnterm * pnterm
  | PNAnd of pnterm * pnterm
  | PNTop
  | PNBot

let rec pp_print_pnterm_pr pr ppf = function
  | PNVarName s ->
      Format.fprintf ppf "%s" s
  | PNArrow (t,PNBot) ->
      Format.fprintf ppf "@[~%a@]"
        (pp_print_pnterm_pr 1) t
  | PNArrow (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 4 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ ->@ %a"
        (pp_print_pnterm_pr 3) t1
        (pp_print_pnterm_pr 4) t2;
      if pr < 4 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PNAnd (PNArrow (t1,t2),PNArrow (t2t,t1t))
        when t1=t1t && t2=t2t ->
      Format.fprintf ppf "@[";
      if pr < 5 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ <->@ %a"
        (pp_print_pnterm_pr 4) t1
        (pp_print_pnterm_pr 4) t2;
      if pr < 5 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PNAnd (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 2 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ /\\@ %a"
        (pp_print_pnterm_pr 1) t1
        (pp_print_pnterm_pr 2) t2;
      if pr < 2 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PNOr (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 3 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ \\/@ %a"
        (pp_print_pnterm_pr 2) t1
        (pp_print_pnterm_pr 3) t2;
      if pr < 3 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PNTop ->
      Format.fprintf ppf "True"
  | PNBot ->
      Format.fprintf ppf "False"

let pp_print_pnterm = pp_print_pnterm_pr 5

type pterm =
  | PVar of int
  | PArrow of pterm * pterm
  | POr of pterm * pterm
  | PAnd of pterm * pterm
  | PTop
  | PBot

type name_env = {
  mutable maxvar : int;
  dict : (string,int) Hashtbl.t;
  reverse_dict : (int,string) Hashtbl.t
}

let new_name_env () = {
  maxvar = 0;
  dict = Hashtbl.create 10;
  reverse_dict = Hashtbl.create 100
}
let empty_env = new_name_env ()

let rec convert_name_impl env = function
  | PNVarName s ->
      begin try
        PVar (Hashtbl.find env.dict s)
      with Not_found ->
        let t = PVar env.maxvar in
        Hashtbl.add env.dict s env.maxvar;
        Hashtbl.add env.reverse_dict env.maxvar s;
        env.maxvar <- env.maxvar + 1;
        t
      end
  | PNArrow (t1,t2) ->
      PArrow (convert_name_impl env t1,
        convert_name_impl env t2)
  | PNAnd (PNArrow (t1,t2),PNArrow(t2t,t1t))
      when t1=t1t && t2=t2t ->
      let ct1 = convert_name_impl env t1 in
      let ct2 = convert_name_impl env t2 in
      PAnd (PArrow (ct1,ct2),PArrow(ct2,ct1))
  | PNAnd (t1,t2) ->
      PAnd (convert_name_impl env t1,
        convert_name_impl env t2)
  | PNOr (t1,t2) ->
      POr (convert_name_impl env t1,
        convert_name_impl env t2)
  | PNTop -> PTop
  | PNBot -> PBot

let convert_name tn =
  let env = new_name_env () in
  let t = convert_name_impl env tn in
  t, env

let rec pp_print_pterm_pr env pr ppf = function
  | PVar n ->
      begin try
        Format.fprintf ppf "%s" (Hashtbl.find env.reverse_dict n)
      with Not_found ->
        Format.fprintf ppf "?%d" n
      end
  | PArrow (t,PBot) ->
      Format.fprintf ppf "@[~%a@]"
        (pp_print_pterm_pr env 1) t
  | PArrow (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 4 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ ->@ %a"
        (pp_print_pterm_pr env 3) t1
        (pp_print_pterm_pr env 4) t2;
      if pr < 4 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PAnd (PArrow (t1,t2),PArrow (t2t,t1t))
        when t1=t1t && t2=t2t ->
      Format.fprintf ppf "@[";
      if pr < 5 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ <->@ %a"
        (pp_print_pterm_pr env 4) t1
        (pp_print_pterm_pr env 4) t2;
      if pr < 5 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PAnd (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 2 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ /\\@ %a"
        (pp_print_pterm_pr env 1) t1
        (pp_print_pterm_pr env 2) t2;
      if pr < 2 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | POr (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 3 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ \\/@ %a"
        (pp_print_pterm_pr env 2) t1
        (pp_print_pterm_pr env 3) t2;
      if pr < 3 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PTop ->
      Format.fprintf ppf "True"
  | PBot ->
      Format.fprintf ppf "False"

let pp_print_pterm env = pp_print_pterm_pr env 5

let rec pp_print_pterm_latex_internal env pr ppf = function
  | PVar n ->
      begin try
        Format.fprintf ppf "%s" (Hashtbl.find env.reverse_dict n)
      with Not_found ->
        Format.fprintf ppf "?%d" n
      end
  | PArrow (t,PBot) ->
      Format.fprintf ppf "@[\\lnot@ %a@]"
        (pp_print_pterm_latex_internal env 1) t
  | PArrow (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 4 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ \\to@ %a"
        (pp_print_pterm_latex_internal env 3) t1
        (pp_print_pterm_latex_internal env 4) t2;
      if pr < 4 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PAnd (PArrow (t1,t2),PArrow (t2t,t1t))
        when t1=t1t && t2=t2t ->
      Format.fprintf ppf "@[";
      if pr < 5 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ \\iff@ %a"
        (pp_print_pterm_latex_internal env 4) t1
        (pp_print_pterm_latex_internal env 4) t2;
      if pr < 5 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PAnd (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 2 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ \\land@ %a"
        (pp_print_pterm_latex_internal env 1) t1
        (pp_print_pterm_latex_internal env 2) t2;
      if pr < 2 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | POr (t1,t2) ->
      Format.fprintf ppf "@[";
      if pr < 3 then Format.fprintf ppf "(";
      Format.fprintf ppf "%a@ \\lor@ %a"
        (pp_print_pterm_latex_internal env 2) t1
        (pp_print_pterm_latex_internal env 3) t2;
      if pr < 3 then Format.fprintf ppf ")";
      Format.fprintf ppf "@]"
  | PTop ->
      Format.fprintf ppf "\\top"
  | PBot ->
      Format.fprintf ppf "\\bot"

let pp_print_pterm_latex env pr ppf t =
  Format.fprintf ppf "@[$";
  pp_print_pterm_latex_internal env pr ppf t;
  Format.fprintf ppf "$@]"
