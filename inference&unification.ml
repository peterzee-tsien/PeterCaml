(* TODO: Write a good set of tests for eval. *)
let eval_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Rec and Apply!
  *)
  (Let ("x", I 1, Primop (Plus, [Var "x"; I 5])), I 6);
  (Rec ("f", Arrow ([Int], Int), Primop (Plus, [I 1; I 2])), I 3);
  (Apply (Fn ([], I 3), []), I 3);
  (Apply (
      Let ("x", I 1,
           Fn ([("y", Int)], Primop (Plus, [Var "x"; Var "y"]))),
      [I 2]),
   I 3);
  (Apply (Fn ([("x", Bool)], Var "x"), [B true]), B true);
  (Apply (
      Fn ([("x", Int); ("y", Int)], Primop (LessThan, [Var "x"; Var "y"])),
      [Primop (Plus, [I 1; I 2]); Primop (Times, [I 3; I 4])]),
   B true);
  
  
]

(* TODO: Implement the missing cases of eval. *)
let rec eval exp =
  match exp with
  (* Values evaluate to themselves *)
  | I _ -> exp
  | B _ -> exp
  | Fn _ -> exp

  (* This evaluator is _not_ environment-based. Variables should never
     appear during evaluation since they should be substituted away when
     eliminating binding constructs, e.g. function applications and lets.
     Therefore, if we encounter a variable, we raise an error.
*)
  | Var x -> raise (Stuck (Free_variable x))

  (* Primitive operations: +, -, *, <, = *)
  | Primop (po, args) ->
      let args = List.map eval args in
      begin
        match eval_op po args with
        | None -> raise (Stuck Bad_primop_args)
        | Some v -> v
      end

  | If (e, e1, e2) ->
      begin
        match eval e with
        | B true -> eval e1
        | B false -> eval e2
        | _ -> raise (Stuck If_non_true_false)
      end

  | Let (x, e1, e2) ->
      let e1 = eval e1 in
      eval (subst (e1, x) e2)

  | Rec (f, _, e) -> 
      
      eval (subst (exp, f) e)

  | Apply (e, es) -> (
      match eval e with 
      | Fn (xs, e) ->
          if List.length xs = List.length es then 
            let subs = List.combine (List.map eval es) (List.map fst xs) in
            eval (subst_list subs e)
          else
            raise (Stuck Arity_mismatch) 
      | _ -> raise (Stuck Apply_non_fn)
    )


(* TODO: Write a good set of tests for infer. *)
let infer_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Rec, Fn, and Apply!
  *)
  (([("x", Int)], Var "x"), Int);
  (([("x", Int)], Rec ("f", Int, I 0)), Int);
  (([], Rec ("f", Arrow ([Int], Int), Var "f")), Arrow ([Int], Int));
  (([], Fn([("x", Int); ("y", Bool)],I 0)), Arrow([Int; Bool], Int));
  (([], Fn([("x", Int)],I 0)), Arrow([Int], Int));
  (([], Fn([],I 0)), Arrow([], Int)); 
  (([("f", Arrow([Int],Int))], Apply (Var "f", [I 4])), Int);
  (([("f", Arrow([Int;Int],Int))], Apply (Var "f", [I 4;I 5])), Int);
  (([("x", Int)], Apply (Fn ([], Var"x"), [])), Int)
  
]
(* TODO: Implement the missing cases of infer. *)
let rec infer ctx e =
  match e with
  | Var x ->
      begin
        try lookup x ctx
        with Not_found -> raise (TypeError (Free_variable x))
      end
  | I _ -> Int
  | B _ -> Bool

  | Primop (po, exps) ->
      let (domain, range) = primopType po in
      check ctx exps domain range

  | If (e, e1, e2) ->
      begin
        match infer ctx e with
        | Bool ->
            let t1 = infer ctx e1 in
            let t2 = infer ctx e2 in
            if t1 = t2 then t1
            else type_mismatch t1 t2
        | t -> type_mismatch Bool t
      end

  | Let (x, e1, e2) ->
      let t1 = infer ctx e1 in
      infer (extend ctx (x, t1)) e2

  | Rec (f, t, e) -> 
      if t =  (infer (extend ctx (f,t)) e) then t
      else type_mismatch t (infer (extend ctx (f,t)) e)

  | Fn (xs, e) -> 
      Arrow ((List.map snd xs), infer (extend_list ctx xs) e)

  | Apply (e, es) -> (
      match infer ctx e with
      | Arrow (ts, t) -> check ctx es ts t
      | t' -> raise (TypeError (Apply_non_arrow t'))
    )

and check ctx exps tps result =
  match exps, tps with
  | [], [] -> result
  | e :: es, t :: ts ->
      let t' = infer ctx e in
      if t = t' then check ctx es ts result
      else type_mismatch t t'
  | _ -> raise (TypeError Arity_mismatch)

(* TODO: Implement type unification. *)
let unify : utp -> utp -> utp UTVarMap.t =
  let rec unify (type_substitution : utp UTVarMap.t) (t1 : utp) (t2 : utp) : utp UTVarMap.t =
    match t1, t2 with
    (* Unifying identical concrete types does nothing *)
    | UInt, UInt
    | UBool, UBool -> type_substitution
    | UTVar a, UTVar a' when a = a' -> type_substitution

    (* For type constructors, recursively unify the parts *)
    | UArrow (t1, t1'), UArrow (t2, t2') ->
        let u2 = unify type_substitution t1 t2 in 
        unify u2 t1' t2' 
    | UCross ts1, UCross ts2 -> 
        if (List.length ts1) = (List.length ts2) then 
          let rec helper l l1 l2 =
            (match (l1,l2) with
             |([],[])-> l
             | (x::xs,y::ys) -> unify (helper l xs ys) x y
            )
          in helper type_substitution ts1 ts2
        else
          unif_error (UnifMismatch (UCross ts1, UCross ts2))
    | UTVar a, _ -> unifyVar type_substitution a t2
    | _, UTVar b -> unifyVar type_substitution b t1
    (* All other cases are mismatched types. *)
    | _, _ -> unif_error @@ UnifMismatch (t1, t2)
  
  (* Unify a variable with a type *)
  and unifyVar (type_substitution : utp UTVarMap.t) (a : string) (t : utp) : utp UTVarMap.t =
    let rec occurs : utp -> bool = function
      | UInt | UBool -> false
      | UArrow (t1, t2) -> occurs t1 || occurs t2
      | UCross ts -> List.exists occurs ts
      | UTVar b ->
          if a = b
          then true
          else
            match UTVarMap.find_opt b type_substitution with
            | None -> false
            | Some t' -> occurs t'
    in
    if occurs t then unif_error UnifOccursCheckFails
    else 
      let check_t = UTVarMap.find_opt a type_substitution in
      (match check_t with
       | Some x -> unify type_substitution t x
       | None -> UTVarMap.add a t type_substitution 
      )

  in
  fun t1 t2 -> unify UTVarMap.empty t1 t2
      