(**To DO: Write a good set of tests for free_variables **)
let free_variables_tests = [
  (* An example test case.
     Note that you are *only* required to write tests for Let, Rec, Fn, and Apply!
  *)
  (Let ("x", I 1, I 5), []);
  (Let ("f", ex1,
        Apply (Var "f", [I 3; I 4])),[]);
  (Fn ([("x", Int); ("y", Int)],
       Primop (Plus,
               [Primop (Times, [Var "x"; Var "x"]);
                Primop (Times, [Var "y"; Var "y"])])), []);
  ((Apply (Var "f", [I 3; I 4])),["f"]);
  
  ((Rec ("x", Arrow ([Int], Int), (Let ("f", Fn (["x", Int], Primop (Times, [Var "x";Var "x"])), Apply (Var "f", [Var "x"]))))),[]);
  (Apply (I 3, [I 3]), [])
  
]

(* TODO: Implement the missing cases of free_variables. *)
let rec free_variables : exp -> name list =
  (* Taking unions of lists.
     If the lists are in fact sets (all elements are unique),
     then the result will also be a set.
  *)
  let union l1 l2 = delete l2 l1 @ l2 in
  let union_fvs es =
    List.fold_left (fun acc exp -> union acc (free_variables exp)) [] es
  in
  function
  | Var y -> [y]
  | I _ | B _ -> []
  | If(e, e1, e2) -> union_fvs [e; e1; e2]
  | Primop (_, args) -> union_fvs args
  | Fn (xs, e) ->
      let ns = (List.map (fun (a,b) -> a) xs) in
      let c = union_fvs [e] in 
      (match xs with 
       | [] -> [] 
       | n-> delete ns c
      )
  | Rec (x, _, e) ->
      delete [x] (union_fvs [e])
  | Let (x, e1, e2) -> 
      union (free_variables e1) (delete [x] (free_variables e2))
  | Apply (e, es) ->  union_fvs (e::es)


(* TODO: Write a good set of tests for unused_vars. *)
let unused_vars_tests = [
  (* An example test case.
     N'ote that you are *only* required to write tests for Rec, Fn, and Apply!
  *)
  (Let ("x", I 1, I 5), ["x"]); (Fn ([("x", Int)], I 3), ["x"]); 
  ((Apply (Var "f", [I 3; I 4])),[]);
  ((Rec("x", Int,(Let ("x", I 1, I 5)))),["x";"x"]);
  (Fn ([("x", Int); ("y", Int)],
       Primop (Plus,
               [Primop (Times, [Var "x"; Var "x"]);
                Primop (Times, [Var "y"; Var "y"])])), []);
  (Rec ("f", Int,
        Primop (Plus, [Var "f";
                       Let ("x", I 5, Var "x")])),
   []);
  
]

(* TODO: Implement the missing cases of unused_vars. *)
let rec unused_vars =
  function
  | Var _ | I _ | B _ -> []
  | If (e, e1, e2) -> unused_vars e @ unused_vars e1 @ unused_vars e2
  | Primop (_, args) ->
      List.fold_left (fun acc exp -> acc @ unused_vars exp) [] args
  | Let (x, e1, e2) ->
      let unused = unused_vars e1 @ unused_vars e2 in
      if List.mem x (free_variables e2) then
        unused
      else
        x :: unused 
  | Rec (x, _, e) -> 
      let unused = unused_vars e in
      if List.mem x (free_variables e) then
        unused
      else 
        x :: unused

  | Fn (xs, e) -> 
      let ns = (List.map (fun (a,b) -> a) xs) in 
      (unused_vars e)@ (delete (free_variables e) ns)

  | Apply (e, es) -> 
      List.fold_left (fun acc e -> acc @ (unused_vars e)) [] (e :: es)
          
                            
(* TODO: Write a good set of tests for subst. *)
(* Note: we've added a type annotation here so that the compiler can help
   you write tests of the correct form. *)
let subst_tests : (((exp * name) * exp) * exp) list = [
  (* An example test case. If you have trouble writing test cases of the
     proper form, you can try copying this one and modifying it.
     Note that you are *only* required to write tests for Rec, Fn, and Apply!
  *)
  (((I 1, "x"), (* [1/x] *)
    (* let y = 2 in y + x *)
    Let ("y", I 2, Primop (Plus, [Var "y"; Var "x"]))),
   (* let y = 2 in y + 1 *)
   Let ("y", I 2, Primop (Plus, [Var "y"; I 1])));
  
  (((I 1, "x"), 
    
    (Fn ([("x", Int); ("y", Int)],
         Primop (Plus,
                 [Primop (Times, [Var "x"; Var "x"]);
                  Primop (Times, [Var "y"; Var "y"])])))),
   
   (Fn ([("x", Int); ("y", Int)],
        Primop (Plus,
                [Primop (Times, [Var "x"; Var "x"]);
                 Primop (Times, [Var "y"; Var "y"])])))) ;
  
  (((I 1, "x"), 
    
    Rec ("y", Int, Primop (Plus, [Var "y"; Var "x"]))),
   
   Rec ("y", Int, Primop (Plus, [Var "y"; I 1])));
  
  (((Var "g", "f"),
    
    Rec ("f", Int, Var "f")),
   
   Rec ("f", Int, Var "f"));
  
  (((Var "x", "y"), 
    
    Rec ("x", Int, Primop (Times, [Var "x"; Var "y"]))),
   
   Rec ("x2", Int, Primop (Times, [Var "x2"; Var "x"])));
  
  (((Var "y", "x"), 
                    
    Apply (Var "x", [Var "a"; I 9])),
   
   Apply (Var "y", [Var "a"; I 9]));
  
  (((Var "y", "x"), 
    
    Apply (Apply (Var "f", [Var "x"]),
           [Var "x"; Var "y"; Var "x"])),
   
   Apply (Apply (Var "f", [Var "y"]),
          [Var "y"; Var "y"; Var "y"]));
  
  (((Var "y", "x"), 
    
    Fn ([("a", Int); ("b", Int)],
        Primop (Plus, [Var "x";
                       Primop (Plus, [Var "x"; Var "a"])]))),
   
   Fn ([("a", Int); ("b", Int)],
       Primop (Plus, [Var "y";
                      Primop (Plus, [Var "y"; Var "a"])])));
  
  (((Primop (Times, [Var "x"; Var "y"]), "x"),
    
    Fn ([("y", Int); ("z", Int)],
        Primop (Times, [Var "y";
                        Primop (Plus, [Var "z"; Var "x"])]))),
   
   Fn ([("y1", Int); ("z1", Int)],
       Primop (Times, [Var "y1";
                       Primop (Plus, [Var "z1";
                                      Primop (Times, [Var "x"; Var "y"])])])));

]

(* TODO: Implement the missing cases of subst. *)
let rec subst ((e', x) as s) exp =
  match exp with
  | Var y ->
      if x = y then e'
      else Var y
  | I n -> I n
  | B b -> B b
  | Primop (po, args) -> Primop (po, List.map (subst s) args)
  | If (e, e1, e2) ->
      If (subst s e, subst s e1, subst s e2)
  | Let (y, e1, e2) ->
      let e1' = subst s e1 in
      if y = x then
        Let (y, e1', e2)
      else
        let (y, e2) =
          if List.mem y (free_variables e') then
            rename y e2
          else
            (y, e2)
        in
        Let (y, e1', subst s e2)

  | Rec (y, t, e) -> 
      if y = x then
        Rec (y, t, e)
      else
        let (y, e) =
          if List.mem y (free_variables e') then
            rename y e
          else
            (y, e)
        in
        Rec (y, t, subst s e)

  | Fn (xs, e) ->
      let free_var = free_variables e' in 
      let ns = (List.map (fun (a,b) -> a) xs) in 
      if List.mem x ns then 
        Fn (xs, e) 
      else 
        let (xs, e) = 
          if not ((List.map (fun a -> List.mem a free_var) ns) = [])  then 
            let (ns, e') = rename_all ns e in
            let tp= (List.map (fun (a,b) -> b) xs) in
            ((List.combine ns tp), e')
          else
            (xs, e)
        in
        Fn (xs, subst s e)
  | Apply (e, es) -> 
      let e' = subst s e in
      let es' = List.map (subst s) es in
      Apply (e', es')

and rename x e =
  let x' = freshVar x in
  (x', subst (Var x', x) e)

and rename_all names exp =
  List.fold_right
    (fun name (names, exp) ->
       let (name', exp') = rename name exp in
       (name' :: names, exp'))
    names
    ([], exp)

(* Applying a list of substitutions to an expression, leftmost first *)
let subst_list subs exp =
  List.fold_left (fun exp sub -> subst sub exp) exp subs
