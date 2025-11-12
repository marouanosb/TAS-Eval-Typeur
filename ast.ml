(* Termes *)
type pterm = 
  | Var of string 
  | App of pterm * pterm 
  | Abs of string * pterm 
  | N of int 
  | Add of pterm * pterm
  | Sub of pterm * pterm
  | Nil
  | Cons of pterm * pterm
  | Hd of pterm
  | Tl of pterm
  | IfZero of pterm * pterm * pterm
  | IfEmpty of pterm * pterm * pterm
  | Fix of pterm
  | Let of string * pterm * pterm
  (* Imperative features *)
  | Unit
  | Ref of pterm
  | Deref of pterm
  | Assign of pterm * pterm
  | Loc of int  (* memory location/address *)
(* Types *) 
type ptype = 
  | TVar of string 
  | PolyFaible of string  (* Variable de type faible '_a pour polymorphisme faible *)
  | Arr of ptype * ptype 
  | Nat
  | List of ptype
  | Forall of string list * ptype
  (* Imperative types *)
  | TUnit
  | TRef of ptype 
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
    | Sub (t1, t2) -> "(" ^ (print_term t1) ^" - "^ (print_term t2) ^ ")"
    | Nil -> "[]"
    | Cons (h, tl) -> "(" ^ (print_term h) ^ " :: " ^ (print_term tl) ^ ")"
    | Hd t -> "(hd " ^ (print_term t) ^ ")"
    | Tl t -> "(tl " ^ (print_term t) ^ ")"
    | IfZero (c, t1, t2) -> "(ifzero " ^ (print_term c) ^ " then " ^ (print_term t1) ^ " else " ^ (print_term t2) ^ ")"
    | IfEmpty (c, t1, t2) -> "(ifempty " ^ (print_term c) ^ " then " ^ (print_term t1) ^ " else " ^ (print_term t2) ^ ")"
    | Fix u -> "(fix " ^ (print_term u) ^ ")"
    | Let (x, e1, e2) -> "(let " ^ x ^ " = " ^ (print_term e1) ^ " in " ^ (print_term e2) ^ ")"
    (* Imperative features *)
    | Unit -> "()"
    | Ref e -> "(ref " ^ (print_term e) ^ ")"
    | Deref e -> "(!" ^ (print_term e) ^ ")"
    | Assign (e1, e2) -> "(" ^ (print_term e1) ^ " := " ^ (print_term e2) ^ ")"
    | Loc r -> "loc" ^ (string_of_int r)
(* pretty printer de types*)                    
let rec print_type (t : ptype) : string =
  match t with
    TVar x -> x
  | PolyFaible x -> "'" ^ x  (* Variables de type faibles avec ' *)
  | Arr (t1, t2) -> "(" ^ (print_type t1) ^" -> "^ (print_type t2) ^")"
  | Nat -> "Nat"
  | List t1 -> "[" ^ (print_type t1) ^ "]"
  | Forall (vs, t) ->
      let vs_s = String.concat " " vs in
      "forall " ^ vs_s ^ ". " ^ (print_type t)
  (* Imperative types *)
  | TUnit -> "Unit"
  | TRef t1 -> "(Ref " ^ (print_type t1) ^ ")" 

(* générateur de noms frais de variables de types *)
let compteur_var : int ref = ref 0                    

let nouvelle_var () : string = compteur_var := !compteur_var + 1; 
  "T"^(string_of_int !compteur_var)


exception VarPasTrouve
exception TypingError of string

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
  | PolyFaible v1 when v1 = v -> true
  | Arr (t1, t2) -> (appartient_type v t1) || (appartient_type v t2) 
  | _ -> false

(* remplace une variable par un type dans type *)
let rec substitue_type (t : ptype) (v : string) (t0 : ptype) : ptype =
  match t with
    TVar v1 when v1 = v -> t0
  | TVar v2 -> TVar v2
  | PolyFaible v1 when v1 = v -> t0
  | PolyFaible v2 -> PolyFaible v2
  | Arr (t1, t2) -> Arr (substitue_type t1 v t0, substitue_type t2 v t0) 
  | Nat -> Nat
  | List u -> List (substitue_type u v t0)
  | Forall (vs, u) -> if List.mem v vs then Forall (vs, u) else Forall (vs, substitue_type u v t0)
  (* Imperative types *)
  | TUnit -> TUnit
  | TRef u -> TRef (substitue_type u v t0) 

(* remplace une variable par un type dans une liste d'équations*)
let substitue_type_partout (e : equa) (v : string) (t0 : ptype) : equa =
  List.map (fun (x, y) -> (substitue_type x v t0, substitue_type y v t0)) e

(* Determine si une expression est non-expansive (valeur) pour le polymorphisme faible *)
let rec is_non_expansive (te : pterm) : bool =
  match te with
  | Var _ -> true
  | Abs _ -> true
  | N _ -> true
  | Nil -> true
  | Unit -> true
  | Cons (e1, e2) -> is_non_expansive e1 && is_non_expansive e2
  (* Toutes les autres expressions sont expansives *)
  | App _ | Add _ | Sub _ | IfZero _ | Hd _ | Tl _ | IfEmpty _ 
  | Fix _ | Let _ | Ref _ | Deref _ | Assign _ | Loc _ -> false

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
  | Sub (t1, t2) -> let eq1 : equa = genere_equa t1 Nat e in
      let eq2 : equa = genere_equa t2 Nat e in
      (ty, Nat)::(eq1 @ eq2)
  | Nil -> let a = TVar (nouvelle_var ()) in [(ty, List a)]
  | Cons (h, tl) ->
      let a = TVar (nouvelle_var ()) in
      let eqsh = genere_equa h a e in
      let eqst = genere_equa tl (List a) e in
      (ty, List a) :: (eqsh @ eqst)
  | Hd u ->
      let a = TVar (nouvelle_var ()) in
      let eqsu = genere_equa u (List a) e in
      (ty, a) :: eqsu
  | Tl u ->
      let a = TVar (nouvelle_var ()) in
      let eqsu = genere_equa u (List a) e in
      (ty, List a) :: eqsu
  | IfZero (c, t1, t2) ->
      let eqc = genere_equa c Nat e in
      let eq1 = genere_equa t1 ty e in
      let eq2 = genere_equa t2 ty e in
      eqc @ eq1 @ eq2
  | IfEmpty (c, t1, t2) ->
      let a = TVar (nouvelle_var ()) in
      let eqc = genere_equa c (List a) e in
      let eq1 = genere_equa t1 ty e in
      let eq2 = genere_equa t2 ty e in
      eqc @ eq1 @ eq2
  | Fix u -> (
      match u with
      | Abs (phi, m) ->
          let a = TVar (nouvelle_var ()) in
          let eqm = genere_equa m a ((phi, a) :: e) in
          (ty, a) :: eqm
      | _ -> raise (TypingError "Fix attend une abstraction (Abs)")
    )
  | Let (x, e1, e2) ->
      (* Polymorphisme faible : utilise PolyFaible si e1 est expansive *)
      let a = if is_non_expansive e1 then TVar (nouvelle_var ()) else PolyFaible (nouvelle_var ()) in
      let eqs1 = genere_equa e1 a e in
      let eqs2 = genere_equa e2 ty ((x, a) :: e) in
      eqs1 @ eqs2
  (* Imperative features *)
  | Unit -> [(ty, TUnit)]
  | Loc _ -> 
      let a = TVar (nouvelle_var ()) in
      [(ty, TRef a)]
  | Ref t ->
      let a = TVar (nouvelle_var ()) in
      let eqst = genere_equa t a e in
      (ty, TRef a) :: eqst
  | Deref t ->
      let a = TVar (nouvelle_var ()) in
      let eqst = genere_equa t (TRef a) e in
      (ty, a) :: eqst
  | Assign (t1, t2) ->
      let a = TVar (nouvelle_var ()) in
      let eqs1 = genere_equa t1 (TRef a) e in
      let eqs2 = genere_equa t2 a e in
      (ty, TUnit) :: (eqs1 @ eqs2)
      
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
    (* PolyFaible : deux variables faibles *)
  | (e1, (PolyFaible v1, PolyFaible v2)::e2) -> unification (substitue_type_zip (rembobine (e1,e2)) v2 (PolyFaible v1)) but
    (* PolyFaible à gauche : vérification d'occurence puis remplacement *)
  | (e1, (PolyFaible v1, t2)::e2) ->  if appartient_type v1 t2 then raise (Echec_unif ("occurence de "^ v1 ^" dans "^(print_type t2))) else  unification (substitue_type_zip (rembobine (e1,e2)) v1 t2) but
    (* PolyFaible à droite : vérification d'occurence puis remplacement *)
  | (e1, (t1, PolyFaible v2)::e2) ->  if appartient_type v2 t1 then raise (Echec_unif ("occurence de "^ v2 ^" dans " ^(print_type t1))) else  unification (substitue_type_zip (rembobine (e1,e2)) v2 t1) but
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
    (* types List des deux cotes : on decompose *)
  | (e1, (List t1, List t2)::e2) -> unification (e1, (t1, t2)::e2) but
    (* types List à gauche pas à droite : échec *)
  | (e1, (List _, t3)::e2) -> raise (Echec_unif ("type liste non-unifiable avec "^(print_type t3)))
    (* types List à droite pas à gauche : échec *)
  | (e1, (t3, List _)::e2) -> raise (Echec_unif ("type liste non-unifiable avec "^(print_type t3)))
    (* types Forall des deux cotes : pour simplifier, on ignore le forall *)
  | (e1, (Forall (_, t1), Forall (_, t2))::e2) -> unification (e1, (t1, t2)::e2) but
    (* types Forall à gauche pas à droite : échec *)
  | (e1, (Forall _, t3)::e2) -> raise (Echec_unif ("type forall non-unifiable avec "^(print_type t3)))
    (* types Forall à droite pas à gauche : échec *)
  | (e1, (t3, Forall _)::e2) -> raise (Echec_unif ("type forall non-unifiable avec "^(print_type t3)))
    (* types Unit des deux cotes : on passe *)
  | (e1, (TUnit, TUnit)::e2) -> unification (e1, e2) but
    (* types Unit à gauche pas à droite : échec *)
  | (e1, (TUnit, t3)::e2) -> raise (Echec_unif ("type unit non-unifiable avec "^(print_type t3)))
    (* types Unit à droite pas à gauche : échec *)
  | (e1, (t3, TUnit)::e2) -> raise (Echec_unif ("type unit non-unifiable avec "^(print_type t3)))
    (* types Ref des deux cotes : on decompose *)
  | (e1, (TRef t1, TRef t2)::e2) -> unification (e1, (t1, t2)::e2) but
    (* types Ref à gauche pas à droite : échec *)
  | (e1, (TRef _, t3)::e2) -> raise (Echec_unif ("type ref non-unifiable avec "^(print_type t3)))
    (* types Ref à droite pas à gauche : échec *)
  | (e1, (t3, TRef _)::e2) -> raise (Echec_unif ("type ref non-unifiable avec "^(print_type t3)))     
                                       
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

(* New examples with subtraction *)
let ex_sub1 : pterm = Sub (N 10, N 3)
let inf_ex_sub1 : string = inference ex_sub1
let ex_sub2 : pterm = Abs ("x", Sub (Var "x", N 1))
let inf_ex_sub2 : string = inference ex_sub2

(* List examples *)
let ex_nil : pterm = Nil
let inf_ex_nil : string = inference ex_nil
let ex_list1 : pterm = Cons (N 1, Nil)
let inf_ex_list1 : string = inference ex_list1
let ex_list2 : pterm = Cons (N 1, Cons (N 2, Cons (N 3, Nil)))
let inf_ex_list2 : string = inference ex_list2
let ex_hd : pterm = Hd (Cons (N 42, Nil))
let inf_ex_hd : string = inference ex_hd
let ex_tl : pterm = Tl (Cons (N 1, Cons (N 2, Nil)))
let inf_ex_tl : string = inference ex_tl

(* IfZero examples *)
let ex_ifzero1 : pterm = IfZero (N 0, N 10, N 20)
let inf_ex_ifzero1 : string = inference ex_ifzero1
let ex_ifzero2 : pterm = IfZero (N 5, N 10, N 20)
let inf_ex_ifzero2 : string = inference ex_ifzero2
let ex_ifzero3 : pterm = Abs ("x", IfZero (Var "x", N 0, Sub (Var "x", N 1)))
let inf_ex_ifzero3 : string = inference ex_ifzero3

(* IfEmpty examples *)
let ex_ifempty1 : pterm = IfEmpty (Nil, N 0, N 1)
let inf_ex_ifempty1 : string = inference ex_ifempty1
let ex_ifempty2 : pterm = IfEmpty (Cons (N 1, Nil), N 0, N 1)
let inf_ex_ifempty2 : string = inference ex_ifempty2

(* Let examples *)
let ex_let1 : pterm = Let ("x", N 5, Add (Var "x", Var "x"))
let inf_ex_let1 : string = inference ex_let1
let ex_let2 : pterm = Let ("f", Abs ("x", Add (Var "x", N 1)), App (Var "f", N 10))
let inf_ex_let2 : string = inference ex_let2

(* Fix examples - factorial *)
let ex_fact : pterm = 
  Fix (Abs ("f", Abs ("n", 
    IfZero (Var "n", 
      N 1, 
      Add (Var "n", App (Var "f", Sub (Var "n", N 1)))))))
let inf_ex_fact : string = inference ex_fact
let ex_fact_3 : pterm = App (ex_fact, N 3)
let inf_ex_fact_3 : string = inference ex_fact_3

(* Fix examples - length of list *)
let ex_length : pterm =
  Fix (Abs ("len", Abs ("lst",
    IfEmpty (Var "lst",
      N 0,
      Add (N 1, App (Var "len", Tl (Var "lst")))))))
let inf_ex_length : string = inference ex_length
let ex_length_test : pterm = App (ex_length, ex_list2)
let inf_ex_length_test : string = inference ex_length_test

(* Imperative features examples *)
let ex_unit : pterm = Unit
let inf_ex_unit : string = inference ex_unit

let ex_ref1 : pterm = Ref (N 42)
let inf_ex_ref1 : string = inference ex_ref1

let ex_deref1 : pterm = Let ("r", Ref (N 10), Deref (Var "r"))
let inf_ex_deref1 : string = inference ex_deref1

let ex_assign1 : pterm = Let ("r", Ref (N 5), 
                              Let ("_", Assign (Var "r", N 10),
                                  Deref (Var "r")))
let inf_ex_assign1 : string = inference ex_assign1

let ex_ref_list : pterm = Let ("r", Ref Nil,
                               Let ("_", Assign (Var "r", Cons (N 1, Nil)),
                                   Deref (Var "r")))
let inf_ex_ref_list : string = inference ex_ref_list

(* Counter example *)
let ex_counter : pterm = Let ("r", Ref (N 0),
                              Let ("incr", Abs ("_", 
                                              Let ("v", Deref (Var "r"),
                                                   Let ("_", Assign (Var "r", Add (Var "v", N 1)),
                                                       Unit))),
                                  Let ("_", App (Var "incr", Unit),
                                      Let ("_", App (Var "incr", Unit),
                                          Deref (Var "r")))))
let inf_ex_counter : string = inference ex_counter

(* =================== POLYMORPHISME FAIBLE TESTS =================== *)

(* Example 1: OK - [] est une valeur, donc polymorphe *)
let ex_poly_faible_ok : pterm = 
  Let ("l", Nil,
       Let ("l1", Cons (N 1, Var "l"),
            Let ("l2", Cons (Abs ("x", Var "x"), Var "l"),
                 Unit)))

let poly_faible_test_ok : string = inference ex_poly_faible_ok

(* Example 2: BAD - ref [] est expansif, donc type faible '_a list ref
   Ce programme devrait être rejeté car on tente d'utiliser l avec deux types incompatibles *)
let ex_poly_faible_bad : pterm =
  Let ("l", Ref Nil,
       Let ("_", Assign (Var "l", Cons (Abs ("x", Var "x"), Nil)),
            Add (Hd (Deref (Var "l")), N 2)))

let poly_faible_test_bad : string = 
  try
    inference ex_poly_faible_bad
  with
  | Echec_unif msg -> "Echec d'unification (attendu pour polymorphisme faible): " ^ msg
  | TypingError msg -> "Erreur de typage: " ^ msg

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
  | Sub (t1, t2) -> List.concat [free_vars t1; free_vars t2]
  | Nil -> []
  | Cons (h, tl) -> List.concat [free_vars h; free_vars tl]
  | Hd t -> free_vars t
  | Tl t -> free_vars t
  | IfZero (c, t1, t2) -> List.concat [free_vars c; free_vars t1; free_vars t2]
  | IfEmpty (c, t1, t2) -> List.concat [free_vars c; free_vars t1; free_vars t2]
  | Fix u -> free_vars u
  | Let (x, e1, e2) -> List.concat [free_vars e1; List.filter (fun y -> y <> x) (free_vars e2)]
  (* Imperative features *)
  | Unit -> []
  | Loc _ -> []
  | Ref t -> free_vars t
  | Deref t -> free_vars t
  | Assign (t1, t2) -> List.concat [free_vars t1; free_vars t2]

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
  | Sub (a, b) -> Sub (rename_bound a oldv newv, rename_bound b oldv newv)
  | Nil -> Nil
  | Cons (h, tl) -> Cons (rename_bound h oldv newv, rename_bound tl oldv newv)
  | Hd u -> Hd (rename_bound u oldv newv)
  | Tl u -> Tl (rename_bound u oldv newv)
  | IfZero (c, t1, t2) -> IfZero (rename_bound c oldv newv, rename_bound t1 oldv newv, rename_bound t2 oldv newv)
  | IfEmpty (c, t1, t2) -> IfEmpty (rename_bound c oldv newv, rename_bound t1 oldv newv, rename_bound t2 oldv newv)
  | Fix u -> Fix (rename_bound u oldv newv)
  | Let (x, e1, e2) ->
      if x = oldv then Let (x, rename_bound e1 oldv newv, e2)
      else Let (x, rename_bound e1 oldv newv, rename_bound e2 oldv newv)
  (* Imperative features *)
  | Unit -> Unit
  | Loc r -> Loc r
  | Ref t -> Ref (rename_bound t oldv newv)
  | Deref t -> Deref (rename_bound t oldv newv)
  | Assign (t1, t2) -> Assign (rename_bound t1 oldv newv, rename_bound t2 oldv newv)

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
  | Sub (t1, t2) -> Sub (subst t1 v s, subst t2 v s)
  | Nil -> Nil
  | Cons (h, tl) -> Cons (subst h v s, subst tl v s)
  | Hd u -> Hd (subst u v s)
  | Tl u -> Tl (subst u v s)
  | IfZero (c, t1, t2) -> IfZero (subst c v s, subst t1 v s, subst t2 v s)
  | IfEmpty (c, t1, t2) -> IfEmpty (subst c v s, subst t1 v s, subst t2 v s)
  | Fix u -> Fix (subst u v s)
  | Let (y, e1, e2) ->
      let e1' = subst e1 v s in
      if y = v then Let (y, e1', e2)
      else
        if List.exists (fun z -> z = y) (free_vars s) then
          let y' = nouvelle_var_term () in
          let e2' = rename_bound e2 y y' in
          Let (y', e1', subst e2' v s)
        else Let (y, e1', subst e2 v s)
  (* Imperative features *)
  | Unit -> Unit
  | Loc r -> Loc r
  | Ref t -> Ref (subst t v s)
  | Deref t -> Deref (subst t v s)
  | Assign (t1, t2) -> Assign (subst t1 v s, subst t2 v s)

(* predicate: value *)
let rec is_value t =
  match t with 
  | Abs _ | N _ -> true
  | Nil -> true
  | Cons (vh, vt) when is_value vh && is_value vt -> true
  (* Imperative values *)
  | Unit -> true
  | Loc _ -> true
  | _ -> false

exception EvalStuck of string
exception Divergence of string

(* State for imperative features: maps region IDs to values *)
type state = (int * pterm) list

(* region counter for fresh region allocation *)
let compteur_region : int ref = ref 0
let nouvelle_region () : int = compteur_region := !compteur_region + 1; !compteur_region

(* lookup a region in the state *)
let rec lookup_state (s : state) (r : int) : pterm option =
  match s with
  | [] -> None
  | (r', v) :: rest -> if r = r' then Some v else lookup_state rest r

(* update a region in the state *)
let rec update_state (s : state) (r : int) (v : pterm) : state =
  match s with
  | [] -> [(r, v)]
  | (r', v') :: rest -> if r = r' then (r, v) :: rest else (r', v') :: update_state rest r v

(* one-step call-by-value with state *)
let rec eval1_with_state (t : pterm) (s : state) : (pterm * state) option =
  match t with
    App (Abs (x, body), v2) when is_value v2 -> Some (subst body x v2, s)
  | App (v1, t2) when is_value v1 ->
      (match eval1_with_state t2 s with None -> None | Some (t2', s') -> Some (App (v1, t2'), s'))
  | App (t1, t2) ->
      (match eval1_with_state t1 s with None -> None | Some (t1', s') -> Some (App (t1', t2), s'))
  | Add (N n1, N n2) -> Some (N (n1 + n2), s)
  | Add (N n1, t2) ->
      (match eval1_with_state t2 s with None -> None | Some (t2', s') -> Some (Add (N n1, t2'), s'))
  | Add (t1, t2) ->
      (match eval1_with_state t1 s with None -> None | Some (t1', s') -> Some (Add (t1', t2), s'))
  | Sub (N n1, N n2) -> Some (N (n1 - n2), s)
  | Sub (N n1, t2) ->
      (match eval1_with_state t2 s with None -> None | Some (t2', s') -> Some (Sub (N n1, t2'), s'))
  | Sub (t1, t2) ->
      (match eval1_with_state t1 s with None -> None | Some (t1', s') -> Some (Sub (t1', t2), s'))
  | Cons (h, tl) ->
      if is_value h then
        (match eval1_with_state tl s with None -> None | Some (tl', s') -> Some (Cons (h, tl'), s'))
      else
        (match eval1_with_state h s with None -> None | Some (h', s') -> Some (Cons (h', tl), s'))
  | Hd u ->
      (match eval1_with_state u s with
      | Some (u', s') -> Some (Hd u', s')
      | None ->
          match u with
          | Cons (vh, vt) when is_value vh && is_value vt -> Some (vh, s)
          | _ -> None)
  | Tl u ->
      (match eval1_with_state u s with
      | Some (u', s') -> Some (Tl u', s')
      | None ->
          match u with
          | Cons (vh, vt) when is_value vh && is_value vt -> Some (vt, s)
          | _ -> None)
  | IfZero (c, t1, t2) ->
      (match eval1_with_state c s with
      | Some (c', s') -> Some (IfZero (c', t1, t2), s')
      | None ->
          match c with
          | N 0 -> Some (t1, s)
          | N _ -> Some (t2, s)
          | _ -> None)
  | IfEmpty (c, t1, t2) ->
      (match eval1_with_state c s with
      | Some (c', s') -> Some (IfEmpty (c', t1, t2), s')
      | None ->
          match c with
          | Nil -> Some (t1, s)
          | Cons (vh, vt) when is_value vh && is_value vt -> Some (t2, s)
          | _ -> None)
  | Fix u ->
      (match u with
      | Abs (phi, m) -> Some (subst m phi (Fix u), s)
      | _ ->
          match eval1_with_state u s with
          | Some (u', s') -> Some (Fix u', s')
          | None -> None)
  | Let (x, e1, e2) ->
      if is_value e1 then Some (subst e2 x e1, s)
      else
        (match eval1_with_state e1 s with
        | Some (e1', s') -> Some (Let (x, e1', e2), s')
        | None -> None)
  (* Imperative features *)
  | Deref (Loc r) ->
      (match lookup_state s r with
      | Some v -> Some (v, s)
      | None -> None)
  | Deref t ->
      (match eval1_with_state t s with
      | Some (t', s') -> Some (Deref t', s')
      | None -> None)
  | Ref v when is_value v ->
      let r = nouvelle_region () in
      Some (Loc r, (r, v) :: s)
  | Ref t ->
      (match eval1_with_state t s with
      | Some (t', s') -> Some (Ref t', s')
      | None -> None)
  | Assign (Loc r, v) when is_value v ->
      let s' = update_state s r v in
      Some (Unit, s')
  | Assign (Loc r, t2) ->
      (match eval1_with_state t2 s with
      | Some (t2', s') -> Some (Assign (Loc r, t2'), s')
      | None -> None)
  | Assign (t1, t2) ->
      (match eval1_with_state t1 s with
      | Some (t1', s') -> Some (Assign (t1', t2), s')
      | None -> None)
  | _ -> None

(* full evaluation with step limit to avoid non-termination *)
let eval ?(max_steps=10000) t =
  let rec loop t s steps =
    if steps > max_steps then raise (Divergence ("exceeded " ^ string_of_int max_steps ^ " steps"))
    else match eval1_with_state t s with
      | None -> t
      | Some (t', s') -> loop t' s' (steps + 1)
  in loop t [] 0

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

 print_endline inf_ex_sub1;
 print_endline "======================";
 print_endline inf_ex_sub2;
 print_endline "======================";
 print_endline inf_ex_nil;
 print_endline "======================";
 print_endline inf_ex_list1;
 print_endline "======================";
 print_endline inf_ex_list2;
 print_endline "======================";
 print_endline inf_ex_hd;
 print_endline "======================";
 print_endline inf_ex_tl;
 print_endline "======================";
 print_endline inf_ex_ifzero1;
 print_endline "======================";
 print_endline inf_ex_ifzero2;
 print_endline "======================";
 print_endline inf_ex_ifzero3;
 print_endline "======================";
 print_endline inf_ex_ifempty1;
 print_endline "======================";
 print_endline inf_ex_ifempty2;
 print_endline "======================";
 print_endline inf_ex_let1;
 print_endline "======================";
 print_endline inf_ex_let2;
 print_endline "======================";
 print_endline inf_ex_fact;
 print_endline "======================";
 print_endline inf_ex_fact_3;
 print_endline "======================";
 print_endline inf_ex_length;
 print_endline "======================";
 print_endline inf_ex_length_test;
 print_endline "======================";
 print_endline inf_ex_unit;
 print_endline "======================";
 print_endline inf_ex_ref1;
 print_endline "======================";
 print_endline inf_ex_deref1;
 print_endline "======================";
 print_endline inf_ex_assign1;
 print_endline "======================";
 print_endline inf_ex_ref_list;
 print_endline "======================";
 print_endline inf_ex_counter;
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
 print_endline (eval_to_string ex_nat3);
 print_endline "======================";
 print_endline (eval_to_string ex_sub1);
 print_endline (eval_to_string ex_list1);
 print_endline (eval_to_string ex_list2);
 print_endline (eval_to_string ex_hd);
 print_endline (eval_to_string ex_tl);
 print_endline (eval_to_string ex_ifzero1);
 print_endline (eval_to_string ex_ifzero2);
 print_endline (eval_to_string ex_ifempty1);
 print_endline (eval_to_string ex_ifempty2);
 print_endline (eval_to_string ex_let1);
 print_endline (eval_to_string ex_let2);
 print_endline (eval_to_string ~max_steps:100 ex_fact_3);
 print_endline (eval_to_string ~max_steps:100 ex_length_test);
 print_endline "=== IMPERATIVE EVALUATION ===";
 print_endline (eval_to_string ex_unit);
 print_endline (eval_to_string ex_ref1);
 print_endline (eval_to_string ex_deref1);
 print_endline (eval_to_string ex_assign1);
 print_endline (eval_to_string ex_ref_list);
 print_endline (eval_to_string ex_counter);
 print_endline "=== POLYMORPHISME FAIBLE TESTS ===";
 print_endline poly_faible_test_ok;
 print_endline poly_faible_test_bad

let _ = main ()