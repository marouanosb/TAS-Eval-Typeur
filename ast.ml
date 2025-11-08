(* Termes *)
type pterm = Var of string | App of pterm * pterm | Abs of string * pterm | N of int | Add of pterm * pterm 
(* Types *) 
type ptype = TVar of string | Arr of ptype * ptype | Nat 
(* Environnements de typage *) 
type env = (string * ptype) list 
(* Listes d'équations *) 
type equa = (ptype * ptype) list  
(* pretty printer de termes*)     
let rec print_term (t : pterm) : string =
  match t with
    Var x -> x
    | App (t1, t2) -> "(" ^ (print_term t1) ^" "^ (print_term t2) ^ ")"
    | Abs (x, t) -> "(fun "^ x ^" -> " ^ (print_term t) ^")" 
    | N n -> string_of_int n
    | Add (t1, t2) -> "(" ^ (print_term t1) ^" + "^ (print_term t2) ^ ")"
(* pretty printer de types*)                    
let rec print_type (t : ptype) : string =
  match t with
    TVar x -> x
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | Nat -> "Nat" 

(* générateur de noms frais de variables de types *)
let compteur_var : int ref = ref 0                    

let nouvelle_var () : string = compteur_var := !compteur_var + 1; 
  "T"^(string_of_int !compteur_var)


exception VarPasTrouve

(* cherche le type d'une variable dans un environnement *)
let rec cherche_type (v : string) (e : env) : ptype =
  match e with
    [] -> raise VarPasTrouve
  | (v1, t1)::q when v1 = v -> t1
  | (_, _):: q -> (cherche_type v q) 

(* vérificateur d'occurence de variables *)  
let rec appartient_type (v : string) (t : ptype) : bool =
  match t with
    TVar v1 when v1 = v -> true
  | Arr (t1, t2) -> (appartient_type v t1) || (appartient_type v t2) 
  | _ -> false

(* remplace une variable par un type dans type *)
let rec substitue_type (t : ptype) (v : string) (t0 : ptype) : ptype =
  match t with
    TVar v1 when v1 = v -> t0
  | TVar v2 -> TVar v2
  | Arr (t1, t2) -> Arr (substitue_type t1 v t0, substitue_type t2 v t0) 
  | Nat -> Nat 

(* remplace une variable par un type dans une liste d'équations*)
let substitue_type_partout (e : equa) (v : string) (t0 : ptype) : equa =
  List.map (fun (x, y) -> (substitue_type x v t0, substitue_type y v t0)) e

(* genere des equations de typage à partir d'un terme *)  
let rec genere_equa (te : pterm) (ty : ptype) (e : env) : equa =
  match te with 
    Var v -> let tv : ptype = cherche_type v e in [(ty, tv)] 
  | App (t1, t2) -> let nv : string = nouvelle_var () in
    let eq1 : equa = genere_equa t1 (Arr (TVar nv, ty)) e in
    let eq2 : equa = genere_equa t2 (TVar nv) e in
      eq1 @ eq2
  | Abs (x, t) -> let nv1 : string = nouvelle_var () 
      and nv2 : string = nouvelle_var () in
    (ty, Arr (TVar nv1, TVar nv2))::(genere_equa t (TVar nv2) ((x, TVar nv1)::e))  
  | N _ -> [(ty, Nat)]
  | Add (t1, t2) -> let eq1 : equa = genere_equa t1 Nat e in
      let eq2 : equa = genere_equa t2 Nat e in
      (ty, Nat)::(eq1 @ eq2)
      
exception Echec_unif of string      

(* zipper d'une liste d'équations *)
type equa_zip = equa * equa
  
(* rembobine le zipper *)
let rec rembobine (e : equa_zip) =
  match e with
    ([], _) -> e
  | (c::e1, e2) -> (e1, c::e2)

(* remplace unee variable par un type dans un zipper d'équations *)
let substitue_type_zip (e : equa_zip) (v : string) (t0 : ptype) : equa_zip =
  match e with
    (e1, e2) -> (substitue_type_partout e1 v t0, substitue_type_partout e2 v t0)

(* trouve un type associé à une variable dans un zipper d'équation *)
let rec trouve_but (e : equa_zip) (but : string) = 
  match e with
    (_, []) -> raise VarPasTrouve
  | (_, (TVar v, t)::_) when v = but -> t
  | (_, (t, TVar v)::_) when v = but -> t 
  | (e1, c::e2) -> trouve_but (c::e1, e2) but 
                     
(* résout un système d'équations *) 
let rec unification (e : equa_zip) (but : string) : ptype = 
  match e with 
    (* on a passé toutes les équations : succes *)
    (_, []) -> (try trouve_but (rembobine e) but with VarPasTrouve -> raise (Echec_unif "but pas trouvé"))
    (* equation avec but : on passe *)
  | (e1, (TVar v1, t2)::e2) when v1 = but ->  unification ((TVar v1, t2)::e1, e2) but
    (* deux variables : remplacer l'une par l'autre *)
  | (e1, (TVar v1, TVar v2)::e2) ->  unification (substitue_type_zip (rembobine (e1,e2)) v2 (TVar v1)) but
    (* une variable à gauche : vérification d'occurence puis remplacement *)
  | (e1, (TVar v1, t2)::e2) ->  if appartient_type v1 t2 then raise (Echec_unif ("occurence de "^ v1 ^" dans "^(print_type t2))) else  unification (substitue_type_zip (rembobine (e1,e2)) v1 t2) but
    (* une variable à droite : vérification d'occurence puis remplacement *)
  | (e1, (t1, TVar v2)::e2) ->  if appartient_type v2 t1 then raise (Echec_unif ("occurence de "^ v2 ^" dans " ^(print_type t1))) else  unification (substitue_type_zip (rembobine (e1,e2)) v2 t1) but 
    (* types fleche des deux cotes : on decompose  *)
  | (e1, (Arr (t1,t2), Arr (t3, t4))::e2) -> unification (e1, (t1, t3)::(t2, t4)::e2) but 
    (* types fleche à gauche pas à droite : echec  *)
  | (e1, (Arr (_,_), t3)::e2) -> raise (Echec_unif ("type fleche non-unifiable avec "^(print_type t3)))     
    (* types fleche à droite pas à gauche : echec  *)
  | (e1, (t3, Arr (_,_))::e2) -> raise (Echec_unif ("type fleche non-unifiable avec "^(print_type t3)))     
    (* types nat des deux cotes : on passe *)
  | (e1, (Nat, Nat)::e2) -> unification (e1, e2) but 
    (* types nat à gauche pas à droite : échec *)
  | (e1, (Nat, t3)::e2) -> raise (Echec_unif ("type entier non-unifiable avec "^(print_type t3)))     
    (* types à droite pas à gauche : échec *)
  | (e1, (t3, Nat)::e2) -> raise (Echec_unif ("type entier non-unifiable avec "^(print_type t3)))     
                                       
(* enchaine generation d'equation et unification *)                                   
let inference (t : pterm) : string =
  let e : equa_zip = ([], genere_equa t (TVar "but") []) in
  try (let res = unification e "but" in
       (print_term t)^" ***TYPABLE*** avec le type "^(print_type res))
  with Echec_unif bla -> (print_term t)^" ***PAS TYPABLE*** : "^bla
                         
(* ***EXEMPLES*** *)  
let ex_id : pterm = Abs ("x", Var "x") 
let inf_ex_id : string = inference ex_id 
let ex_k : pterm = Abs ("x", Abs ("y", Var "x")) 
let inf_ex_k : string = inference ex_k
let ex_s : pterm = Abs ("x", Abs ("y", Abs ("z", App (App (Var "x", Var "z"), App (Var "y", Var "z")))))
let inf_ex_s : string = inference ex_s 
let ex_nat1 : pterm = App (Abs ("x", Add(Var "x", N 1)), N 3)
let inf_ex_nat1 : string = inference ex_nat1
let ex_nat2 : pterm = Abs ("x", Add( Var "x", Var "x"))
let inf_ex_nat2 : string = inference ex_nat2
let ex_omega : pterm = App (Abs ("x", App (Var "x", Var "x")), Abs ("y", App (Var "y", Var "y")))
let inf_ex_omega : string = inference ex_omega
let ex_nat3 : pterm = App (ex_nat2, ex_id)
let inf_ex_nat3 : string = inference ex_nat3

(* =================== EVALUATION (call-by-value, capture-avoiding) =================== *)

(* generator for fresh term variables *)
let compteur_var_term : int ref = ref 0
let nouvelle_var_term () : string = compteur_var_term := !compteur_var_term + 1; "x" ^ (string_of_int !compteur_var_term)

(* free variables *)
let rec free_vars t =
  match t with
    Var x -> [x]
  | App (t1, t2) -> List.concat [free_vars t1; free_vars t2]
  | Abs (x, t1) -> List.filter (fun y -> y <> x) (free_vars t1)
  | N _ -> []
  | Add (t1, t2) -> List.concat [free_vars t1; free_vars t2]

(* rename free occurrences of 'oldv' into 'newv' except when shadowed *)
let rec rename_bound t oldv newv =
  match t with
    Var x -> if x = oldv then Var newv else Var x
  | App (a, b) -> App (rename_bound a oldv newv, rename_bound b oldv newv)
  | Abs (x, body) ->
      if x = oldv then Abs (x, body) (* shadowing: stop *)
      else Abs (x, rename_bound body oldv newv)
  | N n -> N n
  | Add (a, b) -> Add (rename_bound a oldv newv, rename_bound b oldv newv)

(* capture-avoiding substitution [t[v := s]] *)
let rec subst t v s =
  match t with
    Var x -> if x = v then s else Var x
  | App (t1, t2) -> App (subst t1 v s, subst t2 v s)
  | Abs (x, body) ->
      if x = v then Abs (x, body) (* v is bound here; stop *)
      else
        if List.exists (fun y -> y = x) (free_vars s) then
          let x' = nouvelle_var_term () in
          let body' = rename_bound body x x' in
          Abs (x', subst body' v s)
        else Abs (x, subst body v s)
  | N n -> N n
  | Add (t1, t2) -> Add (subst t1 v s, subst t2 v s)

(* predicate: value *)
let is_value t =
  match t with Abs _ | N _ -> true | _ -> false

exception EvalStuck of string
exception Divergence of string

(* one-step call-by-value *)
let rec eval1 t =
  match t with
    App (Abs (x, body), v2) when is_value v2 -> Some (subst body x v2)
  | App (v1, t2) when is_value v1 ->
      (match eval1 t2 with None -> None | Some t2' -> Some (App (v1, t2')))
  | App (t1, t2) ->
      (match eval1 t1 with None -> None | Some t1' -> Some (App (t1', t2)))
  | Add (N n1, N n2) -> Some (N (n1 + n2))
  | Add (N n1, t2) ->
      (match eval1 t2 with None -> None | Some t2' -> Some (Add (N n1, t2')))
  | Add (t1, t2) ->
      (match eval1 t1 with None -> None | Some t1' -> Some (Add (t1', t2)))
  | _ -> None

(* full evaluation with step limit to avoid non-termination *)
let eval ?(max_steps=10000) t =
  let rec loop t steps =
    if steps > max_steps then raise (Divergence ("***PAS TYPABLE*** : exceeded " ^ string_of_int max_steps ^ " steps"))
    else match eval1 t with
      | None -> t
      | Some t' -> loop t' (steps + 1)
  in loop t 0

(* helpers to safely try evaluation and pretty print result *)
let eval_to_string ?(max_steps=10000) t =
  try
    let r = eval ~max_steps t in
    (print_term t) ^ " ==> " ^ (print_term r)
  with
    Divergence msg -> (print_term t) ^ " ==> <divergence: " ^ msg ^ ">"
  | EvalStuck msg -> (print_term t) ^ " ==> <stuck: " ^ msg ^ ">"

let main () =
 print_endline "======================";
 print_endline inf_ex_id;
 print_endline "======================";
 print_endline inf_ex_k;
 print_endline "======================";
 print_endline inf_ex_s;
 print_endline "======================";
 print_endline inf_ex_omega;
 print_endline "======================";
 print_endline inf_ex_nat1;
 print_endline "======================";
 print_endline inf_ex_nat2;
 print_endline "======================";
 print_endline inf_ex_nat3;
 print_endline "======================";
 (* Evaluation prints *)
 print_endline "=== EVALUATION ===";
 print_endline (eval_to_string ex_id);
 print_endline (eval_to_string ex_k);
 print_endline (eval_to_string ex_s);
 print_endline (eval_to_string ex_nat1);
 print_endline (eval_to_string ex_nat2);
 (* omega will diverge; demonstrate guarded evaluation *)
 print_endline (eval_to_string ~max_steps:200 ex_omega);
 print_endline (eval_to_string ex_nat3)

let _ = main ()